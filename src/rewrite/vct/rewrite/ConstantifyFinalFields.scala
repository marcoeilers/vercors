package vct.col.rewrite

import hre.util.ScopedStack
import vct.col.ast._
import vct.col.util.AstBuildHelpers._
import vct.col.ast.node.NodeImpl
import vct.col.origin.{Blame, InvocationFailure, Origin, PanicBlame, ReadableOrigin, TrueSatisfiable}
import vct.col.ref.{DirectRef, Ref}
import vct.col.rewrite.ConstatifyFinalFieldsHelpers.{AssumingInitializedOrigin, CLASS_DEFAULT_LEVEL, CheckingLevelGeOrigin, CheckingLevelGtOrigin, METHOD_DEFAULT_LEVEL, MarcoHelperOrigin, initializerDefaultLevel}
import vct.col.rewrite.EncodeArrayValues.ArrayCreationOrigin
import vct.col.rewrite.exc.EncodeBreakReturn.ReturnClass
import vct.col.rewrite.lang.LangJavaToCol.{JavaConstructorOrigin, JavaFieldOrigin, JavaInitializedFunctionOrigin, JavaInstanceClassOrigin, JavaMethodOrigin, JavaStaticsClassOrigin, JavaStaticsClassSingletonOrigin, JavaTokenPredicateOrigin}
import vct.col.util.SuccessionMap

case object ConstatifyFinalFieldsHelpers {
  val CLASS_DEFAULT_LEVEL = BigInt.int2bigInt(1)
  val METHOD_DEFAULT_LEVEL = BigInt.int2bigInt(1)

  def initializerDefaultLevel(classLevel: BigInt) =
    if (classLevel > 0) classLevel - 1 else BigInt.int2bigInt(0)

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

case class ConstantifyFinalFieldsBuilder(sequential: Boolean) extends RewriterBuilder {

  override def apply[Pre <: Generation](): AbstractRewriter[Pre, _ <: Generation] = ConstantifyFinalFields(sequential)
  override def key: String = "constantFinalFields"
  override def desc: String = "Encode final fields with functions, so that they are not on the heap."

}

case class ConstantifyFinalFields[Pre <: Generation](sequential: Boolean = false) extends Rewriter[Pre] {
  val currentClass: ScopedStack[Class[Pre]] = ScopedStack()

  var tokenPredMap: Map[String, Predicate[Post]] = Map()
  var initializedFunctionMap: SuccessionMap[String, Function[Post]] = SuccessionMap()
  var classInvs: Map[String, Expr[Pre]] = Map()
  var classLevels = Map[String, BigInt]()
  var declLevels = Map[(String, String), BigInt]()
  var currentLevelVars = Map[Declaration[Pre], Variable[Post]]()
  var currentDecl: Declaration[Pre] = null
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
    decl.declarations.foreach{
      case cls: Class[Pre] if cls.o != ReturnClass =>
        val origin: JavaClassOrInterface[_] = cls.o match {
          case jico: JavaInstanceClassOrigin => jico.cls
          case jsco: JavaStaticsClassOrigin => jsco.cls
          case _ =>
            ???
        }
        origin match {
          case jc: JavaClass[Pre] =>
            classLevels += jc.name -> (jc.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case None => 1
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

  def isJavaStdLin(decl: NodeImpl[_]): Boolean = {
    decl.o match {
      case ro: ReadableOrigin => ro.toString.contains("jdk/java/lang")
      case _ =>
        ???
    }
  }

  def isNotInStdLib(): Boolean = {
    if (currentDecl != null) {
      currentDecl.o match {
        case _: ReadableOrigin => !isJavaStdLin(currentDecl)
        case JavaMethodOrigin(m) => !isJavaStdLin(m)
        case JavaConstructorOrigin(jc) => !isJavaStdLin(jc)
        case _ =>
          ???
      }
    } else if (currentClass.nonEmpty) {
      !isJavaStdLin(currentClass.top)
    } else {
      ???
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
      case cls: Class[Pre] if !cls.o.isInstanceOf[JavaStaticsClassOrigin] && cls.o != ReturnClass =>
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
      case cls: Class[Pre] =>
        currentClass.having(cls) { rewriteDefault(cls) }
      case field: InstanceField[Pre] =>
        implicit val o: Origin = field.o
        rewriteDefault(field)
      case im: InstanceMethod[Pre] =>
        currentDecl = im
        implicit val o: Origin = im.o
        val newOne = labelDecls.scope {
          val currentLevelVar = new Variable[Post](TSeq[Post](TInt[Post]()))(im.o)
          currentLevelVars += im -> currentLevelVar
          val initLevel = im.o match {
            case JavaConstructorOrigin(cons) => cons.contract.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case _ => METHOD_DEFAULT_LEVEL
            }
            case JavaMethodOrigin(cons) => cons.contract.staticLevel match {
              case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
              case _ => METHOD_DEFAULT_LEVEL
            }
            case _ =>
              METHOD_DEFAULT_LEVEL
          }
          val newContract = im.o match {
            case JavaMethodOrigin(m) if m.name == "main" && m.modifiers.contains(JavaStatic()) && m.modifiers.contains(JavaPublic()) =>
              val origContract = dispatch(im.contract)
              val allTokens = foldStar(tokenPredMap.values.map(p => PredicateApply[Post](p.ref, Nil, WritePerm())).toSeq)
              val curClassName = currentClass.top.o match {
                case JavaStaticsClassOrigin(cls) => cls.name
              }
              val curClassInit = FunctionInvocation[Post](initializedFunctionMap.ref(curClassName), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))
              origContract.copy(requires = SplitAccountedPredicate(SplitAccountedPredicate(UnitAccountedPredicate(curClassInit), UnitAccountedPredicate(allTokens)), origContract.requires))(origContract.blame)
            case JavaMethodOrigin(m) =>
              val curClassName = currentClass.top.o match {
                case JavaStaticsClassOrigin(cls) => cls.name
                case JavaInstanceClassOrigin(cls) => cls.name
              }
              val curClassInit = PolarityDependent(FunctionInvocation[Post](initializedFunctionMap.ref(curClassName), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing")), BooleanValue(true))
              val origContract = dispatch(im.contract)
              origContract.copy(requires = SplitAccountedPredicate(UnitAccountedPredicate(curClassInit), origContract.requires))(origContract.blame)
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
              case _ => if (isStaticInitializer) initializerDefaultLevel(staticInitClassLevel.get) else METHOD_DEFAULT_LEVEL
            }
          case _: ArrayCreationOrigin =>
            BigInt.int2bigInt(0)
          case _ =>
            METHOD_DEFAULT_LEVEL
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
      rewriteDefault(e)
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
      if (sequential)
        println("Warning: Token assertions not allowed in sequential mode")
      implicit val o: Origin = e.o
      val clsDecl = cls.asInstanceOf[TypeValue[_]].value.asInstanceOf[TClass[_]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, dispatch(prm))
    case jnc: JavaNewClass[_] =>
      rewriteDefault(jnc)
    case i: ProcedureInvocation[Pre] if i.ref.decl.o.isInstanceOf[JavaConstructorOrigin] && isNotInStdLib() =>
      val constrName = i.ref.decl.o.asInstanceOf[JavaConstructorOrigin].cons.name
      val assumeOrig: Origin = AssumingInitializedOrigin(constrName)
      implicit val o: Origin = i.o

      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(constrName), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(assumeOrig)
      val procedureLevel = IntegerValue[Post](declLevels.getOrElse((constrName, "init"), 0))
      val classLevel = IntegerValue[Post](classLevels.getOrElse(constrName, 0))
      val maxLevel = max(procedureLevel, classLevel)

      val calledLevel = Select[Post](initialized, procedureLevel, maxLevel)

      val levelOkay = GreaterEq(getCurrentLevelValue(o), calledLevel)


      val nop: Expr[Post] = rewriteDefault(i)
      val nopAssertingLevelOkay = asserting(levelOkay, nop, i.t)(o)(o)

      assuming(initialized, nopAssertingLevelOkay, i.t)(assumeOrig)
    case pi: ProcedureInvocation[Pre] if isNotInStdLib() =>
      implicit val o: Origin = CheckingLevelGeOrigin
      val pip = rewriteDefault(pi)
      val procedureLevel = pi.ref.decl match {
        case im: Procedure[Pre] => im.contract.staticLevel match {
          case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
          case _ =>
            if (im.o.isInstanceOf[ArrayCreationOrigin])
              BigInt.int2bigInt(0)
            else
              METHOD_DEFAULT_LEVEL
        }
      }
      val levelOkay = GreaterEq(getCurrentLevelValue(pip.o), IntegerValue(procedureLevel))
      asserting(levelOkay, pip, pi.t)(o)(o)
    case pi: MethodInvocation[Pre] if isNotInStdLib() =>
      implicit val o: Origin = pi.o // CheckingLevelGeOrigin
      val pip = rewriteDefault(pi)
      val procedureLevel = pi.ref.decl match {
        case im: InstanceMethod[Pre] => im.contract.staticLevel match {
          case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
          case _ =>
            METHOD_DEFAULT_LEVEL
        }
      }
      val isStaticMethod = pi.ref.decl match {
        case im: InstanceMethod[Pre] => im.o match {
          case JavaMethodOrigin(m) =>
            m.modifiers.contains(JavaStatic())
          case _ =>
            false
        }
        case _ => false
      }
      val (toAssume, toAssert) = if (isStaticMethod) {
        val className = pi.obj match {
          case fi: FunctionInvocation[_] =>
            fi.ref.decl match {
              case f: Function[_] =>
                f.o.asInstanceOf[JavaStaticsClassSingletonOrigin].cls match {
                  case jc: JavaClass[_] => jc.name
                }
            }
        }
        val assumeOrig: Origin = AssumingInitializedOrigin(className)
        val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(className), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(assumeOrig)
        val procedureLevelValue = IntegerValue[Post](procedureLevel)
        val classLevel = IntegerValue[Post](classLevels.getOrElse(className, CLASS_DEFAULT_LEVEL))
        val maxLevel = max(procedureLevelValue, classLevel)

        val calledLevel = Select[Post](initialized, procedureLevelValue, maxLevel)

        val levelOkay = GreaterEq(getCurrentLevelValue(o), calledLevel)
        (initialized, levelOkay)
      } else {
        val levelOkay = GreaterEq(getCurrentLevelValue(pip.o), IntegerValue(procedureLevel))
        (BooleanValue[Post](true), levelOkay)
      }
      val mip = pip.asInstanceOf[MethodInvocation[Post]]
      mip.copy(obj = assuming(toAssume, asserting(toAssert, mip.obj, pi.obj.t)(o)(o), pi.obj.t)(o))(o)
      //assuming(toAssume, asserting(toAssert, pip, pi.t)(o)(o), pi.t)(o)
    case no: NewObject[Pre] if no.cls.decl.o != ReturnClass && isNotInStdLib() =>
      implicit val o: Origin = e.o
      val clsDecl = no.cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
        case _ =>
          ???
      }
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(jc.name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))

      val nop: Expr[Post] = rewriteDefault(no)
      assuming(initialized, nop, no.t)(o)
    case other => rewriteDefault(other)
  }

  override def dispatch(location: Location[Pre]): Location[Post] = location match {
    case other => rewriteDefault(other)
  }

  def max(a: Expr[Post], b: Expr[Post])(implicit o: Origin): Expr[Post] = {
    Select(GreaterEq(a, b), a, b)
  }

  def assuming(toAssume: Expr[Post], value: Expr[Post], t: Type[Pre])(o: Origin): Expr[Post] = {
    FunctionInvocation[Post](onceStuff.ref("assuming"), Seq(toAssume, value), Seq(dispatch(t)), Nil, Nil)(PanicBlame("requires nothing"))(o)
  }

  def asserting(toAssert: Expr[Post], value: Expr[Post], t: Type[Pre])(b: Blame[InvocationFailure])(o: Origin): Expr[Post] = {
    FunctionInvocation[Post](onceStuff.ref("asserting"), Seq(toAssert, value), Seq(dispatch(t)), Nil, Nil)(b)(o)
  }

  override def dispatch(stat: Statement[Pre]): Statement[Post] = {
    stat match {
    case Assign(Deref(obj, Ref(field: InstanceField[Pre])), value) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) && isNotInStdLib() =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      val initOrigin: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(initOrigin)
      val assumeInit = Inhale[Post](initialized)(initOrigin)
      implicit val o: Origin = stat.o

      Block(Seq(assumeInit, rewriteDefault(stat)))
    case Eval(PreAssignExpression(Deref(obj, Ref(field: InstanceField[Pre])), value)) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) && isNotInStdLib() =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      val initOrigin: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(initOrigin)
      val assumeInit = Inhale[Post](initialized)(initOrigin)
      implicit val o: Origin = stat.o

      Block(Seq(assumeInit, rewriteDefault(stat)))
    case Assign(trgt, Deref(obj, Ref(field: InstanceField[Pre]))) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) && isNotInStdLib() =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      val initOrigin: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(initOrigin)
      val assumeInit = Inhale[Post](initialized)(initOrigin)
      implicit val o: Origin = stat.o

      Block(Seq(assumeInit, rewriteDefault(stat)))
    case Eval(PreAssignExpression(trgt, Deref(obj, Ref(field: InstanceField[Pre])))) if (field.o match {
      case jf: JavaFieldOrigin => jf.fields.isStatic
      case _ => false
    }) && isNotInStdLib() =>
      val objType = obj.t
      val cls = objType.asInstanceOf[TClass[Pre]].cls.decl
      val name = cls.o match {
        case jico: JavaInstanceClassOrigin => jico.cls.name
        case jsco: JavaStaticsClassOrigin => jsco.cls.name
      }
      val initOrigin: Origin = AssumingInitializedOrigin(name)
      val initialized = FunctionInvocation[Post](initializedFunctionMap.ref(name), Nil, Nil, Nil, Nil)(PanicBlame("requires nothing"))(initOrigin)
      val assumeInit = Inhale[Post](initialized)(initOrigin)
      implicit val o: Origin = stat.o

      Block(Seq(assumeInit, rewriteDefault(stat)))
    case CloseStaticInv(cls, amt) =>
      implicit val o: Origin = stat.o
      val clsDecl = cls.asInstanceOf[TypeValue[Pre]].value.asInstanceOf[TClass[Pre]].cls.decl
      val jc = clsDecl.o match {
        case jico: JavaInstanceClassOrigin => jico.cls
        case jsco: JavaStaticsClassOrigin => jsco.cls
      }
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => CLASS_DEFAULT_LEVEL
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
      val tokenPred = if (sequential) BooleanValue[Post](true) else PredicateApply[Post](tokenPredMap.get(jc.name).get.ref, Nil, amtPost)

      val currentLevel = getCurrentLevelValue(o)
      val clsLevel = jc.asInstanceOf[JavaClass[Pre]].staticLevel match {
        case Some(DecreasesClauseTuple(Seq(iv: IntegerValue[_]))) => iv.value
        case None => CLASS_DEFAULT_LEVEL
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
        case None => CLASS_DEFAULT_LEVEL
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
}