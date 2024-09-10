package vct.col.rewrite

import hre.util.ScopedStack
import vct.col.ast._
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.util.AstBuildHelpers._
import vct.col.ast.RewriteHelpers._
import vct.col.origin.{AbstractApplicable, Origin, PanicBlame, TrueSatisfiable}
import vct.col.ref.Ref
import vct.col.rewrite.ConstantifyFinalFields.FinalFieldPerm
import vct.col.rewrite.lang.LangJavaToCol.{JavaInitializedFunctionOrigin, JavaInstanceClassOrigin, JavaStaticsClassOrigin, JavaTokenPredicateOrigin}
import vct.col.util.SuccessionMap
import vct.result.VerificationError.UserError

case object ConstantifyFinalFields extends RewriterBuilder {
  override def key: String = "constantFinalFields"
  override def desc: String = "Encode final fields with functions, so that they are not on the heap."

  case class FinalFieldPerm(loc: FieldLocation[_]) extends UserError {
    override def code: String = "finalFieldPerm"
    override def text: String =
      loc.o.messageInContext("Specifying permission over final fields is not allowed, since they are treated as constants.")
  }
}

case class ConstantifyFinalFields[Pre <: Generation]() extends Rewriter[Pre] {
  val currentClass: ScopedStack[Class[Pre]] = ScopedStack()
  var finalValueMap: Map[Declaration[Pre], Expr[Pre]] = Map()
  val fieldFunction: SuccessionMap[InstanceField[Pre], Function[Post]] = SuccessionMap()

  var tokenPredMap: Map[String, Predicate[Post]] = Map()
  var initializedFunctionMap: Map[String, Function[Post]] = Map()
  var classInvs: Map[String, Expr[Pre]] = Map()
  var classLevels = Map[String, BigInt]()
  var declLevels = Map[(String, String), BigInt]()
  var currentDecl: Declaration[Pre] = null
  var currentClassMarco: Class[Pre] = null

  def isFinal(field: InstanceField[Pre]): Boolean =
    field.flags.collectFirst { case _: Final[Pre] => () }.isDefined

  // This function is deliberately unclearly called isAllowedValue to avoid making the impression that we are implementing
  // java constexprs or something similar.
  // Below just happens to be the subset needed to encode string literals.
  def isAllowedValue(e: Expr[Pre]): Boolean = e match {
    case ThisObject(_) => true
    case IntegerValue(_) => true
    case LiteralSeq(_, vals) => vals.forall(isAllowedValue)
    case FunctionInvocation(func, args, _, givenMap, _) => func.decl.contract.decreases.isDefined &&
      func.decl.contract.contextEverywhere.t.equals(TBool[Pre]()) &&
      unfoldPredicate(func.decl.contract.requires).forall(_.t == TBool[Pre]()) &&
      args.forall(isAllowedValue) && givenMap.forall { case (_, e) => isAllowedValue(e) }
    case InstanceFunctionInvocation(obj, func, args, _, givenMap, Seq()) =>  func.decl.contract.decreases.isDefined &&
      func.decl.contract.contextEverywhere.t == TBool[Pre]() &&
      unfoldPredicate(func.decl.contract.requires).forall(_.t == TBool[Pre]()) &&
      isAllowedValue(obj) && args.forall(isAllowedValue) && givenMap.forall { case (_, e) => isAllowedValue(e) }
    case _ => false
  }

  override def dispatch(decl: Program[Pre]): Program[Post] = {
    finalValueMap = decl.transSubnodes.collect({
      // Note that we don't check the value of deref here, so if isClosedConstant is extended without care, this
      // might produce unsoundness in the future. E.g. if variables are present in the init value, this approach fails
      case Assign(Deref(_, Ref(field)), value) if isFinal(field) && isAllowedValue(value) =>
        (field, value)
    }).toMap

    decl.declarations.foreach{
      case cls: Class[Pre] =>
        val origin: JavaClassOrInterface[_] = cls.o match {
          case jico: JavaInstanceClassOrigin => jico.cls
          case jsco: JavaStaticsClassOrigin => jsco.cls
        }
        origin match {
          case jc: JavaClass[Pre] =>
            classLevels += jc.name -> (jc.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case None => 0
              case _ => throw new RuntimeException("Static level must be an integer.")
            })

            jc.staticInvariant match {
              case Some(inv) =>
                classInvs += jc.name -> inv
              case None =>
            }
            implicit val o: Origin = jc.o
            val initializedFunc =
              function[Post](
                blame = JavaInitializedFunctionOrigin(jc),
                contractBlame = TrueSatisfiable,
                returnType = TBool[Post](),
                args = Seq(),
              )

            initializedFunctionMap += jc.name -> initializedFunc

            val tokenPredicate = new Predicate[Post](Seq(), None, false, false)(JavaTokenPredicateOrigin(jc))
            tokenPredMap += jc.name -> tokenPredicate

            jc.decls.foreach(jd => jd match {
              case jm: JavaMethod[_] =>
                declLevels += (jc.name, jm.name) -> (jm.contract.staticLevel match {
                  case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
                  case None => 0
                  case _ => throw new RuntimeException("Static level must be an integer.")
                })
              case ji: JavaSharedInitialization[_] =>
                declLevels += (jc.name, "static") -> (ji.contract.staticLevel match {
                  case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
                  case None => 0
                  case _ => throw new RuntimeException("Static level must be an integer.")
                })
              case c: JavaConstructor[_] =>
                declLevels += (jc.name, "init") -> (c.contract.staticLevel match {
                  case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
                  case None => 0
                  case _ => throw new RuntimeException("Static level must be an integer.")
                })
              case _ =>
            })
          case _ =>
        }
      case _ =>
    }

    super.dispatch(decl)
  }

  override def dispatch(decl: Declaration[Pre]): Unit = decl match {
    case cls: Class[Pre] if cls.o.isInstanceOf[JavaStaticsClassOrigin] =>
      val origin: JavaClassOrInterface[_] = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      origin match {
        case jc: JavaClass[Pre] => {
          globalDeclarations.declare(initializedFunctionMap.get(jc.name).get)
          globalDeclarations.declare(tokenPredMap.get(jc.name).get)
        }
        case _ =>
      }
      currentClass.having(cls) { rewriteDefault(cls) }
    case field: InstanceField[Pre] =>
      implicit val o: Origin = field.o
      if(isFinal(field)) {
        fieldFunction(field) = globalDeclarations.declare(
          withResult((result: Result[Post]) => function[Post](
            blame = AbstractApplicable,
            contractBlame = TrueSatisfiable,
            returnType = dispatch(field.t),
            args = Seq(new Variable[Post](TClass(succ(currentClass.top)))),
            ensures = UnitAccountedPredicate(finalValueMap.get(field) match {
              case Some(value) => result === rewriteDefault(value)
              case None => tt[Post]
            })
          ))
        )
      } else {
        rewriteDefault(field)
      }
    case other =>
      //TODO: This is definitely not the right way to do this, but it works for now.
      if (other.isInstanceOf[AbstractMethod[_]] || other.isInstanceOf[JavaSharedInitialization[_]])
        currentDecl = other
      rewriteDefault(other)
  }

  override def dispatch(e: Expr[Pre]): Expr[Post] = e match {
    case Deref(obj, Ref(field)) =>
      implicit val o: Origin = e.o
      if(isFinal(field)) FunctionInvocation[Post](fieldFunction.ref(field), Seq(dispatch(obj)), Nil, Nil, Nil)(PanicBlame("requires nothing"))
      else rewriteDefault(e)
    case Initialized(cls) =>
      implicit val o: Origin = e.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      FunctionInvocation[Post](initializedFunctionMap.get(jc.name).get.ref, Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
    case Token(cls, prm) =>
      implicit val o: Origin = e.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, dispatch(prm))
    case other => rewriteDefault(other)
  }

  override def dispatch(location: Location[Pre]): Location[Post] = location match {
    case loc @ FieldLocation(_, Ref(field)) if isFinal(field) =>
      throw FinalFieldPerm(loc)
    case other => rewriteDefault(other)
  }

  def makeInhale(obj: Expr[Pre], field: InstanceField[Pre], value: Expr[Pre])(implicit o: Origin): Statement[Post] =
    Assume(FunctionInvocation[Post](fieldFunction.ref(field), Seq(dispatch(obj)), Nil, Nil, Nil)(PanicBlame("requires nothing")) === dispatch(value))

  override def dispatch(stat: Statement[Pre]): Statement[Post] = stat match {
    case Assign(Deref(obj, Ref(field)), value) if isFinal(field) && finalValueMap.contains(field) => Block(Nil)(stat.o)
    case Eval(PreAssignExpression(Deref(obj, Ref(field)), value)) if isFinal(field) && finalValueMap.contains(field) => Block(Nil)(stat.o)
    case Assign(Deref(obj, Ref(field)), value) if isFinal(field) => makeInhale(obj, field, value)(stat.o)
    case Eval(PreAssignExpression(Deref(obj, Ref(field)), value)) if isFinal(field) => makeInhale(obj, field, value)(stat.o)
    case OpenStaticInv(cls) =>
      implicit val o: Origin = stat.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val tokenPred = PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, WritePerm())

      val currentLevel = currentDecl.asInstanceOf[AbstractMethod[_]].contract.staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => BigInt(0)
        case _ => throw new RuntimeException("Static level must be an integer.")
      }
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => BigInt(0)
        case _ => throw new RuntimeException("Static level must be an integer.")
      }
      val levelOkay = Less[Post](IntegerValue(currentLevel), IntegerValue(clsLevel))
      Assert(foldStar(Seq(tokenPred, levelOkay)))(stat.o)
    case other => rewriteDefault(other)
  }
}