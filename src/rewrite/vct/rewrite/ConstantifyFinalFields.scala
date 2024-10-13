package vct.col.rewrite

import hre.util.ScopedStack
import vct.col.ast._
import vct.col.rewrite.{Generation, Rewriter, RewriterBuilder}
import vct.col.util.AstBuildHelpers._
import vct.col.ast.RewriteHelpers._
import vct.col.origin.{AbstractApplicable, Blame, InvocationFailure, Origin, PanicBlame, ReadableOrigin, TrueSatisfiable}
import vct.col.ref.{DirectRef, LazyRef, Ref}
import vct.col.rewrite.ConstantifyFinalFields.{AssumingInitializedOrigin, CheckingLevelGeOrigin, CheckingLevelGtOrigin, FinalFieldPerm, MarcoHelperOrigin}
import vct.col.rewrite.lang.LangJavaToCol.{JavaConstructorOrigin, JavaFieldOrigin, JavaInitializedFunctionOrigin, JavaInstanceClassOrigin, JavaMethodOrigin, JavaStaticsClassOrigin, JavaStaticsClassSingletonOrigin, JavaTokenPredicateOrigin}
import vct.col.util.SuccessionMap
import vct.result.VerificationError.UserError

import scala.collection.mutable

case object ConstantifyFinalFields extends RewriterBuilder {
  override def key: String = "constantFinalFields"
  override def desc: String = "Encode final fields with functions, so that they are not on the heap."

  case class FinalFieldPerm(loc: FieldLocation[_]) extends UserError {
    override def code: String = "finalFieldPerm"
    override def text: String =
      loc.o.messageInContext("Specifying permission over final fields is not allowed, since they are treated as constants.")
  }

  case class MarcoHelperOrigin(name: String) extends Origin {
    override def preferredName: String = name + "Helper"

    override def shortPosition: String = "marco"

    override def context: String = "[Nowhere, Marco added some things]"

    override def inlineContext: String = "[asserting and assuming helpers]"
  }

  case class AssumingInitializedOrigin(clsName: String) extends Origin {
    override def preferredName: String = "assumingInitialized" + clsName

    override def shortPosition: String = "assumeInit"

    override def context: String = "[where class gets initialized]"

    override def inlineContext: String = "[???]"
  }

  case object CheckingLevelGeOrigin extends Origin {
    override def preferredName: String = "checkingLevelGe"

    override def shortPosition: String = "checkingLevelGe"

    override def context: String = "checkingLevelGe"

    override def inlineContext: String = "[???]"
  }

  case object CheckingLevelGtOrigin extends Origin {
    override def preferredName: String = "checkingLevelGt"

    override def shortPosition: String = "checkingLevelGt"

    override def context: String = "checkingLevelGt"

    override def inlineContext: String = "[???]"
  }
}

case class ConstantifyFinalFields[Pre <: Generation]() extends Rewriter[Pre] {
  val currentClass: ScopedStack[Class[Pre]] = ScopedStack()
  var finalValueMap: Map[Declaration[Pre], Expr[Pre]] = Map()
  val fieldFunction: SuccessionMap[InstanceField[Pre], Function[Post]] = SuccessionMap()

  var tokenPredMap: Map[String, Predicate[Post]] = Map()
  var initializedFunctionMap: SuccessionMap[String, Function[Post]] = SuccessionMap()
  var classInvs: Map[String, Expr[Pre]] = Map()
  var classLevels = Map[String, BigInt]()
  var declLevels = Map[(String, String), BigInt]()
  var currentLevelVars = Map[Declaration[Pre], Variable[Post]]()
  var currentDecl: Declaration[Pre] = null
  var currentClassMarco: Class[Pre] = null
  var onceStuff : SuccessionMap[String, Function[Post]] = SuccessionMap()

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
            implicit val o: Origin = cls.o
            val initializedFunc =
              function[Post](
                blame = JavaInitializedFunctionOrigin(jc),
                contractBlame = TrueSatisfiable,
                returnType = TBool[Post](),
                args = Seq(),
              )

            initializedFunctionMap(jc.name) = initializedFunc

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

  def isJavaStdLin(decl: JavaClassDeclaration[_]): Boolean = {
    decl.o match {
      case ro: ReadableOrigin => ro.toString.contains("vercors/res/universal/res/jdk/java/lang")
      case _ => false
    }
  }

  def getCurrentLevelValue(o: Origin): Expr[Post] = {
    implicit val or: Origin = o
    assert(currentLevelVars.contains(currentDecl))
    val levelVar = currentLevelVars(currentDecl)
    SeqSubscript(levelVar.get, IntegerValue(0))(PanicBlame(""))
  }

  def pushCurrentLevel(newValue: Expr[Post])(implicit o: Origin): Statement[Post] = {
    val currentLevelVar = currentLevelVars(currentDecl)
    val currentLevelSeq = LiteralSeq(TInt[Post](), Seq(newValue))
    val newLevelSeq = Concat(currentLevelSeq, Local(new DirectRef[Post, Variable[Post]](currentLevelVar)))
    val newLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), newLevelSeq)(PanicBlame(""))
    // val initLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), initLevelSeq)(PanicBlame(""))
    newLevelAssign
  }

  def popCurrentLevel(expectedCurrentValue: Expr[Post])(implicit o: Origin): Statement[Post] = {
    val currentLevelVar = currentLevelVars(currentDecl)
    val currentOnStack = getCurrentLevelValue(o)
    val currentIsExpected = Exhale(currentOnStack === expectedCurrentValue)(o)
    val tail = Drop(currentLevelVar.get, IntegerValue(1))
    val newLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), tail)(PanicBlame(""))
    // val initLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), initLevelSeq)(PanicBlame(""))
    Block(Seq(currentIsExpected, newLevelAssign))(o)
  }

  override def dispatch(decl: Declaration[Pre]): Unit = {
    onceStuff.getOrElseUpdate("assuming", {
      implicit val o: Origin = MarcoHelperOrigin("assuming")
      val assumingPreVar = new Variable[Post](TBool[Post]())
      val assumingResTVar = new Variable[Post](TType[Post](TAny()))
      val assumingResVar = new Variable[Post](TVar[Post](assumingResTVar.ref))
      val assumingFunc = withResult((r: Result[Post]) =>
        function[Post](
          blame = PanicBlame("!!!!"),
          contractBlame = TrueSatisfiable,
          returnType = TVar[Post](assumingResTVar.ref),
          args = Seq(assumingPreVar, assumingResVar),
          typeArgs = Seq(assumingResTVar),
          ensures = SplitAccountedPredicate(UnitAccountedPredicate[Post](Local(new DirectRef[Post, Variable[Post]](assumingPreVar))), UnitAccountedPredicate[Post](Local(new DirectRef[Post, Variable[Post]](assumingResVar)) === r))
        ))
      globalDeclarations.declare(assumingFunc)
    })

    onceStuff.getOrElseUpdate("asserting", {
      implicit val o: Origin = MarcoHelperOrigin("asserting")
      val assertingPreVar = new Variable[Post](TBool[Post]())
      val assertingResTVar = new Variable[Post](TType[Post](TAny()))
      val assertingResVar = new Variable[Post](TVar[Post](assertingResTVar.ref))
      val assertingFunc = withResult((r: Result[Post]) =>
        function[Post](
          blame = PanicBlame("!!!!"),
          contractBlame = TrueSatisfiable,
          returnType = TVar(assertingResTVar.ref),
          args = Seq(assertingPreVar, assertingResVar),
          typeArgs = Seq(assertingResTVar),
          requires = UnitAccountedPredicate(Local(new DirectRef(assertingPreVar))),
          ensures = UnitAccountedPredicate(Local(new DirectRef[Post, Variable[Post]](assertingResVar)) === r)
        ))
      globalDeclarations.declare(assertingFunc)
    })
    decl match {
      case cls: Class[Pre] if !cls.o.isInstanceOf[JavaStaticsClassOrigin] =>
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
      case _ =>
    }
    decl match {
      case cls: Class[Pre] if cls.o.isInstanceOf[JavaStaticsClassOrigin] =>

        val origin: JavaClassOrInterface[_] = cls.o match {
          case jico: JavaInstanceClassOrigin => jico.cls
          case jsco: JavaStaticsClassOrigin => jsco.cls
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
      case jsi: JavaSharedInitialization[Pre] =>
        assert(false)  // we should never get here.
        currentDecl = jsi
        val initLevel = jsi.o match {
          case JavaConstructorOrigin(cons) => cons.contract.staticLevel match {
            case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
            case _ => BigInt.int2bigInt(0)
          }
          case JavaMethodOrigin(cons) => cons.contract.staticLevel match {
            case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
            case _ => BigInt.int2bigInt(0)
          }
          case _ => BigInt.int2bigInt(0)
        }
        val newOne = new JavaSharedInitialization[Post](jsi.isStatic, dispatch(jsi.initialization), dispatch(jsi.contract))(jsi.o)
        classDeclarations.succeed(jsi, newOne)
      case im: InstanceMethod[Pre] =>
        currentDecl = im
        implicit val o: Origin = im.o
        val newOne = labelDecls.scope {
          val currentLevelVar = new Variable[Post](TSeq[Post](TInt[Post]()))(im.o)
          currentLevelVars += im -> currentLevelVar
          val initLevel = im.o match {
            case JavaConstructorOrigin(cons) => cons.contract.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case _ => BigInt.int2bigInt(0)
            }
            case JavaMethodOrigin(cons) => cons.contract.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case _ => BigInt.int2bigInt(0)
            }
            case _ => BigInt.int2bigInt(0)
          }
          val newContract = im.o match {
            case JavaMethodOrigin(m) if m.name == "main" && m.modifiers.contains(JavaStatic()) && m.modifiers.contains(JavaPublic()) =>
              val origContract = dispatch(im.contract)
              val allTokens = foldStar(tokenPredMap.values.map(p => PredicateApply[Post](p.ref, Nil, WritePerm())).toSeq)
              origContract.copy(requires = SplitAccountedPredicate(UnitAccountedPredicate(allTokens), origContract.requires))(origContract.blame)
            case _=> dispatch(im.contract)
          }
          val initLevelSeq = LiteralSeq(TInt[Post](), Seq(IntegerValue[Post](initLevel)))
          val initLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), initLevelSeq)(PanicBlame(""))
          val newBody = im.body match {
            case None => None
            case Some(s) =>
              val newS = dispatch(s)
              Some(Scope(Seq(currentLevelVar), Block(Seq(initLevelAssign, newS)))(im.o))
          }
          new InstanceMethod[Post](dispatch(im.returnType), variables.collect(im.args.map(dispatch(_)))._1,
            variables.collect(im.outArgs.map(dispatch(_)))._1, variables.collect(im.typeArgs.map(dispatch(_)))._1,
            newBody, newContract, im.inline, im.pure)(im.o)(im.o)
        }
        classDeclarations.succeed(im, newOne)
      case p: Procedure[Pre] =>
        currentDecl = p
        var isStaticInitializer = false
        var assertLessThanClass: Option[Statement[Post]] = None
        var staticInitClassLevel: Option[BigInt] = None
        implicit val o: Origin = p.o
        val initLevel = p.o match {
          case jc@JavaConstructorOrigin(cons) =>
            isStaticInitializer = cons.name.endsWith("Statics") && !isJavaStdLin(jc.cons)
            staticInitClassLevel = if (isStaticInitializer) Some(classLevels(cons.name.dropRight(7))) else None
            cons.contract.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) =>
                iv.value
              case _ => BigInt.int2bigInt(0)
            }
          case _ =>
            BigInt.int2bigInt(0)
        }

        if (isStaticInitializer) {
          val classLevel: BigInt = staticInitClassLevel.get
          assertLessThanClass = Some(Exhale[Post](Less(IntegerValue(initLevel), IntegerValue(classLevel)))(CheckingLevelGtOrigin))
        }

        val newOne = labelDecls.scope {
          val currentLevelVar = new Variable[Post](TSeq[Post](TInt[Post]()))(p.o)
          currentLevelVars += p -> currentLevelVar
          val initLevelSeq = LiteralSeq(TInt[Post](), Seq(IntegerValue[Post](initLevel)))
          val initLevelAssign = Assign(Local(new DirectRef[Post, Variable[Post]](currentLevelVar)), initLevelSeq)(PanicBlame(""))
          val newBody = p.body match {
            case None => None
            case Some(s) =>
              val newS = dispatch(s)
              Some(Scope(Seq(currentLevelVar), Block(Seq(assertLessThanClass.getOrElse(Block(Seq())), initLevelAssign, newS))))
          }
          new Procedure[Post](dispatch(p.returnType), variables.collect(p.args.map(dispatch(_)))._1,
            variables.collect(p.outArgs.map(dispatch(_)))._1, variables.collect(p.typeArgs.map(dispatch(_)))._1,
            newBody, dispatch(p.contract), p.inline, p.pure)(p.o)(p.o)
        }
        globalDeclarations.succeed(p, newOne)
      case other =>
        //TODO: This is definitely not the right way to do this, but it works for now.
        if (other.isInstanceOf[AbstractMethod[_]] || other.isInstanceOf[JavaSharedInitialization[_]]) {
          println(other.getClass)
          currentDecl = other
        }
        rewriteDefault(other)
    }
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
      FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
    case OnInit(cls, ass) =>
      implicit val o: Origin = e.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val fi = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      Implies[Post](fi, dispatch(ass))
    case Token(cls, prm) =>
      implicit val o: Origin = e.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, dispatch(prm))
    case i: FunctionInvocation[Pre] if false && i.ref.decl.o.isInstanceOf[JavaStaticsClassSingletonOrigin] =>
      ???
//      implicit val o: Origin = i.o
//
//       i.ref.decl.o.asInstanceOf[JavaStaticsClassSingletonOrigin].cls match {
//        case jc: JavaClass[Pre] =>
//          val ip = rewriteDefault(i)
//          val initFI = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
//          val res = assuming(initFI, ip, i.t) //FunctionInvocation[Post](onceStuff.ref("assuming"), Seq(initFI, ip), Seq(dispatch(i.t)), Nil, Nil)(PanicBlame("requires nothing"))
//          res
//        case _ =>
//          val ip = rewriteDefault(i)
//          ip
//      }
    case jnc: JavaNewClass[_] =>
      rewriteDefault(jnc)
    case i: ProcedureInvocation[Pre] if i.ref.decl.o.isInstanceOf[JavaConstructorOrigin] =>
      val constrName = i.ref.decl.o.asInstanceOf[JavaConstructorOrigin].cons.name
      implicit val o: Origin = AssumingInitializedOrigin(constrName)

      val levelOkay = GreaterEq(getCurrentLevelValue(o), IntegerValue(declLevels(constrName, "init")))

      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(constrName), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))

      val nop: Expr[Post] = rewriteDefault(i)
      val nopAssertingLevelOkay = asserting(levelOkay, nop, i.t)(o)(o)

      assuming(initialized, nopAssertingLevelOkay, i.t)(o)
    case pi: ProcedureInvocation[Pre] =>
      implicit val o: Origin = CheckingLevelGeOrigin
      val pip = rewriteDefault(pi)
      val procedureLevel = pi.ref.decl match {
        case im: Procedure[Pre] => im.contract.staticLevel match {
          case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
          case _ => BigInt(0)
        }
      }
      val levelOkay = GreaterEq(getCurrentLevelValue(pip.o), IntegerValue(procedureLevel))
      asserting(levelOkay, pip, pi.t)(o)(o)
    case pi: MethodInvocation[Pre] =>
      implicit val o: Origin = CheckingLevelGeOrigin
      val pip = rewriteDefault(pi)
      val procedureLevel = pi.ref.decl match {
        case im: InstanceMethod[Pre] => im.contract.staticLevel match {
          case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
          case _ => BigInt(0)
        }
      }
      val levelOkay = GreaterEq(getCurrentLevelValue(pip.o), IntegerValue(procedureLevel))
      asserting(levelOkay, pip, pi.t)(o)(o)
    case no: NewObject[Pre] =>
      implicit val o: Origin = e.o
      val clsDecl = no.cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))

      val nop: Expr[Post] = rewriteDefault(no)
      assuming(initialized, nop, no.t)(o)
    case other => rewriteDefault(other)
  }

  override def dispatch(location: Location[Pre]): Location[Post] = location match {
    case loc @ FieldLocation(_, Ref(field)) if isFinal(field) =>
      throw FinalFieldPerm(loc)
    case other => rewriteDefault(other)
  }

  def assuming(toAssume: Expr[Post], value: Expr[Post], t: Type[Pre])(o: Origin): Expr[Post] = {
    FunctionInvocation[Post](onceStuff.ref("assuming"), Seq(toAssume, value), Seq(dispatch(t)), Nil, Nil)(PanicBlame("requires nothing"))(o)
  }

  def asserting(toAssert: Expr[Post], value: Expr[Post], t: Type[Pre])(b: Blame[InvocationFailure])(o: Origin): Expr[Post] = {
    FunctionInvocation[Post](onceStuff.ref("asserting"), Seq(toAssert, value), Seq(dispatch(t)), Nil, Nil)(b)(o)
  }

  def makeInhale(obj: Expr[Pre], field: InstanceField[Pre], value: Expr[Pre])(implicit o: Origin): Statement[Post] =
    Assume(FunctionInvocation[Post](fieldFunction.ref(field), Seq(dispatch(obj)), Nil, Nil, Nil)(PanicBlame("requires nothing")) === dispatch(value))

  override def dispatch(stat: Statement[Pre]): Statement[Post] = stat match {
    case Assign(Deref(obj, Ref(field)), value) if isFinal(field) && finalValueMap.contains(field) => Block(Nil)(stat.o)
    case Eval(PreAssignExpression(Deref(obj, Ref(field)), value)) if isFinal(field) && finalValueMap.contains(field) => Block(Nil)(stat.o)
    case Assign(Deref(obj, Ref(field)), value) if isFinal(field) => makeInhale(obj, field, value)(stat.o)
    case Assign(Deref(obj, Ref(field: InstanceField[Pre])), value) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      implicit val o: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      val assumeInit = Inhale[Post](initialized)
      Block(Seq(assumeInit, rewriteDefault(stat)))
    case Assign(trgt, Deref(obj, Ref(field: InstanceField[Pre]))) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      implicit val o: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      val assumeInit = Inhale[Post](initialized)
      Block(Seq(assumeInit, rewriteDefault(stat)))
    case Eval(PreAssignExpression(Deref(obj, Ref(field)), value)) if isFinal(field) => makeInhale(obj, field, value)(stat.o)
    case CloseStaticInv(cls, amt) =>
      implicit val o: Origin = stat.o
      val clsDecl = cls.asInstanceOf[TypeValue[Pre]].value.asInstanceOf[TClass[Pre]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => BigInt(0)
        case _ => throw new RuntimeException("Static level must be an integer.")
      }
      val currentLevel = getCurrentLevelValue(o)
      val levelExpected = Eq[Post](currentLevel, IntegerValue(clsLevel))
      val initFI = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      val amtPost = dispatch(amt)
      val inv = dispatch(clsDecl.staticInv)
      val invMult = Scale(amtPost, inv)(PanicBlame(""))
      val tokenPred = PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, amtPost)
      val in = Inhale(tokenPred)(stat.o)
      val oldLevelAssign = popCurrentLevel(IntegerValue(clsLevel))
      val ex = Exhale(foldStar(Seq(levelExpected, Implies(initFI, invMult))))(stat.o)
      Block(Seq(ex, oldLevelAssign, in))(stat.o)
    case OpenStaticInv(cls, amt) =>
      implicit val o: Origin = stat.o
      val clsDecl = cls.asInstanceOf[TypeValue[Pre]].value.asInstanceOf[TClass[Pre]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val amtPost = dispatch(amt)
      val tokenPred = PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, amtPost)

      val currentLevel = getCurrentLevelValue(o)
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => BigInt(0)
        case _ => throw new RuntimeException("Static level must be an integer.")
      }
      val initFI = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      val levelOkay = Less[Post](IntegerValue(clsLevel), currentLevel)
      val ex = Exhale(foldStar(Seq(tokenPred, levelOkay)))(stat.o)
      val inv = dispatch(clsDecl.staticInv)
      val invMult = Scale(amtPost, inv)(PanicBlame(""))
      val newLevelAssign = pushCurrentLevel(IntegerValue(clsLevel))
      val in = Inhale(Implies(initFI, invMult))(stat.o)
      Block(Seq(ex, newLevelAssign, in))(stat.o)
    case OpenDupStaticInv(cls) =>
      implicit val o: Origin = stat.o
      val clsDecl = cls.asInstanceOf[TypeValue[Pre]].value.asInstanceOf[TClass[Pre]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => BigInt(0)
        case _ => throw new RuntimeException("Static level must be an integer.")
      }
      val currentLevel = getCurrentLevelValue(o)
      val levelOkay = Less[Post](IntegerValue(clsLevel), currentLevel)
      val initFI = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
      val newVar = new Variable[Post](TRational[Post]()())
      val newVarPos = Less(NoPerm(), newVar.get)
      val scaledInv = Scale(newVar.get, dispatch(clsDecl.dupStaticInv))(PanicBlame(""))
      val ex = Exhale[Post](levelOkay)(stat.o)
      val in = Inhale[Post](Implies(initFI, foldStar(Seq(newVarPos, scaledInv))))(stat.o)
      Scope(Seq(newVar), Block(Seq(ex, in)))(stat.o)
    case other => rewriteDefault(other)
  }
}