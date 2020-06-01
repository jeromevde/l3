package l3

import scala.collection.mutable.{Map => MutableMap}

abstract class CPSOptimizer[T <: CPSTreeModule {type Name = Symbol}]
(val treeModule: T) {

  import treeModule._

  protected def rewrite(tree: Tree): Tree = {
    val simplifiedTree = fixedPoint(tree)(shrink)
    val maxSize = size(simplifiedTree) * 3 / 2
    fixedPoint(simplifiedTree, 8) { t => inline(t, maxSize) }
  }


  private case class Count(applied: Int = 0, asValue: Int = 0)

  private case class State(
                            // count of name occurences in the tree
                            // (as applied function
                            // and used as value)
                            census: Map[Name, Count],
                            // atom substitutions to perform to be applied
                            aSubst: Subst[Atom] = emptySubst,
                            // name substitutions for continuations
                            cSubst: Subst[Name] = emptySubst,
                            //expression inverse environment, (p, args) -> n if (p,args)==n
                            eInvEnv: Map[(ValuePrimitive, Seq[Atom]), Atom] = Map.empty,
                            // continuations that will be inlined
                            cEnv: Map[Name, Cnt] = Map.empty,
                            // functions that will be inlined
                            fEnv: Map[Name, Fun] = Map.empty,
                            // block mapped to tag and length
                            bEnv: Map[Atom, (Atom, Atom)] = Map.empty,
                            // block name & index mapped to known value
                            bSetEnv : Map[(Atom, Atom), Atom] = Map.empty
                          ) {

    def dead(s: Name): Boolean = {
      !census.contains(s)
    }

    def appliedOnce(s: Name): Boolean =
      census.get(s).contains(Count(applied = 1, asValue = 0))

    def withASubst(from: Atom, to: Atom): State = {
      copy(aSubst = aSubst + (from -> aSubst(to)))
    }

    def withASubst(from: Name, to: Atom): State =
      withASubst(AtomN(from), to)

    def withASubst(from: Name, to: Literal): State =
      withASubst(from, AtomL(to))


    def withASubst(from: Seq[Name], to: Seq[Atom]): State =
      copy(aSubst = aSubst ++ (from.map(AtomN) zip to.map(aSubst)))


    def withCSubst(from: Name, to: Name): State =
      copy(cSubst = cSubst + (from -> cSubst(to)))

    def withExp(atom: Atom, prim: ValuePrimitive, args: Seq[Atom]): State =
      copy(eInvEnv = eInvEnv + ((prim, args) -> atom))

    def withExp(name: Name, prim: ValuePrimitive, args: Seq[Atom]): State =
      withExp(AtomN(name), prim, args)

    def withCnts(cnts: Seq[Cnt]): State =
      copy(cEnv = cEnv ++ (cnts.map(_.name) zip cnts))

    def withFuns(funs: Seq[Fun]): State =
      copy(fEnv = fEnv ++ (funs.map(_.name) zip funs))

    // Adds a block to the state
    def withBlock(name: Atom, tag: Atom, size: Atom) =
      copy(bEnv = bEnv + (name -> (tag, size)))
    // Adds a blockSet to the state
    def withBlockSet(name : Atom, index : Atom, value : Atom) =
      copy(bSetEnv = bSetEnv + ((name, index) -> value))

  }

  // Shrinking optimizations
  private def shrink(tree: Tree): Tree =
    shrinkS(tree, State(census(tree)))

  def isLeftNeutral(x: Atom, prim: ValuePrimitive)(implicit s: State): Boolean = {
    x.asLiteral.exists(a => leftNeutral.contains(a, prim))
  }

  def isRightNeutral(prim: ValuePrimitive, x: Atom)(implicit s: State): Boolean = {
    x.asLiteral.exists(a => rightNeutral.contains(prim, a))
  }

  def isLeftAbsorbing(x: Atom, prim: ValuePrimitive)(implicit s: State): Boolean = {
    x.asLiteral.exists(a => leftAbsorbing.contains(a, prim))
  }

  def isRightAbsorbing(prim: ValuePrimitive, x: Atom)(implicit s: State): Boolean = {
    x.asLiteral.exists(a => rightAbsorbing.contains((prim, a)))
  }

  def atomEqual(a1: Atom, a2: Atom): Boolean = {
    a1 == a2
  }

  def isBlockClosure(b : Atom)(implicit s : State) : Boolean =
    s.bEnv.get(b) match {
      case Some((AtomL(x), _)) => x == 202
      case _ => false
    }

  def isBlockSet(b : Atom, i : Atom)(implicit s : State) : Boolean =
    s.bSetEnv.get(b -> i) match {
      case Some(_) => true
      case _ => false
    }


  private def shrinkS(tree: Tree, s: State): Tree = {
    // DCE = Dead Code Elimination
    // N&A = Neutral & Absorbing elements
    // CSE = Common Sub-Expression Elimination
    // CF = Constant Folding
    // SI = Shrinking Inlining
    // BP =  Block Primitives
    //val p = Main.treePrinter("----------------------------------------")(formatter)(tree)

    // Substitution, no recursion
    val subsTree = tree match {
      case LetP(name, prim, args, body) => LetP(name, prim, args map s.aSubst, body)
      case LetC(cnts, body) => LetC(cnts, body)
      case LetF(funs, body) => LetF(funs, body)
      case AppC(cnt, args) => AppC(s.cSubst(cnt), args map s.aSubst)
      case AppF(fun, retC, args) => AppF(s.aSubst(fun), s.cSubst(retC), args map s.aSubst)
      case If(cond, args, thenC, elseC) => If(cond, args map s.aSubst , s.cSubst(thenC), s.cSubst(elseC))
      case Halt(arg) => Halt(s.aSubst(arg))
    }


    // Optimizations
    subsTree match {
      // DCE - remove dead primitive
      case LetP(name, prim, _, body) if s.dead(name) && !impure(prim)    =>
        shrinkS(body, s)
      // DCE - remove dead continuation
      case LetC(cnts, body) if cnts exists (c => s.dead(c.name)) =>
        shrinkS(LetC(cnts.filter(c => !s.dead(c.name)), body), s)
      // DCE -  remove dead function
      case LetF(funs, body) if funs.exists(f => s.dead(f.name)) =>
        shrinkS(LetF(funs.filter(f => !s.dead(f.name)), body), s)

      // N&A - left neutral
      case LetP(name, prim, Seq(x, y), body) if isLeftNeutral(x, prim)(s) =>
        shrinkS(body, s.withASubst(name, y))
      // N&A - right neutral
      case LetP(name, prim, Seq(x, y), body) if isRightNeutral(prim, y)(s) =>
        shrinkS(body, s.withASubst(name, x))
      // N&A - left absorbing
      case LetP(name, prim, Seq(x, y), body) if isLeftAbsorbing(x, prim)(s) =>
        shrinkS(body, s.withASubst(name, x))
      // N&A - right absorbing
      case LetP(name, prim, Seq(x, y), body) if isRightAbsorbing(prim, y)(s) =>
        shrinkS(body, s.withASubst(name, y))

      // CSE - removing constant expressions bindings in letp
      case LetP(name, prim, args, body) if s.eInvEnv.contains(prim, args) && !impure(prim) && !unstable(prim) => { //Todo
        shrinkS(body, s.withASubst(name, s.eInvEnv(prim, args)))
      }

      // IDENTITY PRIMITIVE
      case LetP(name, prim, Seq(x), body) if prim == identity =>
        shrinkS(body, s.withASubst(name, x))

      // CF - replace valuePrimitives with equal args
      case LetP(name, prim, Seq(arg1, arg2), body) if atomEqual(arg1, arg2) && sameArgReduce.isDefinedAt((prim, arg1)) =>
        shrinkS(body, s.withASubst(name, sameArgReduce(prim, arg1)))

      // CF - replace valuePrimitives with constant args
      case LetP(name, prim, args, body) if vEvaluator.isDefinedAt((prim, args.flatMap(_.asLiteral))) =>
        val argLiterals =  args.flatMap(_.asLiteral)
        shrinkS(body, s.withASubst(name, vEvaluator(prim, argLiterals)))



      // BP -  Registering block-alloc in state
      case LetP(name, prim, Seq(size), body) if blockAllocTag.isDefinedAt(prim) =>
        val newState = s.withBlock(AtomN(name), AtomL(blockAllocTag(prim)), size)
        LetP(name, prim, Seq(size), shrinkS(body, newState))

      // BP - Registering blockSet for closure blocks
      case LetP(name, prim,  Seq(b,i,v), body) if prim == blockSet && isBlockClosure(b)(s) =>
        val newState = s.withBlockSet(b, i, v)
        LetP(name, prim, Seq(b,i,v), shrinkS(body, newState))

      // BP - Optimizing block get when the block is known and read only
      case LetP(name, prim, Seq(b,i), body) if prim == blockGet  && isBlockClosure(b)(s)  && isBlockSet(b, i)(s)  =>
        shrinkS(body,s.withASubst(name, s.bSetEnv(b->i)))

      // BP - Optimizing block length when known
      case LetP(name, prim, Seq(bName), body) if prim == blockLength && s.bEnv.contains(bName) =>
        shrinkS(body,s.withASubst(name, s.bEnv(bName)._2))

      // BP - Optimizing block tag when known
      case LetP(name, prim, Seq(bName), body) if prim == blockTag && s.bEnv.contains(bName) =>
        shrinkS(body, s.withASubst(name, s.bEnv(bName)._1))


      // register expression
      case LetP(name, prim, args, body) =>
        LetP(name, prim, args, shrinkS(body, s.withExp(name, prim, args)))


      // CF - replace condition with testprimitives with EQUAL args
      case If(cond, Seq(arg1, arg2), thenC, elseC) if atomEqual(arg1, arg2) =>
        AppC(if (sameArgReduceC(cond)) thenC else elseC, Seq())
      // CF - replace condition with testprimitives with CONSTANT args

      case If(cond, args, thenC, elseC) if cEvaluator.isDefinedAt(cond, args.flatMap(arg => arg.asLiteral)) =>
        val argLiteral = args.flatMap(arg => arg.asLiteral)
        val cValue = cEvaluator(cond, argLiteral)
        if (cValue) AppC(thenC, Seq()) else AppC(elseC, Seq())

      // exhaustive case
      case If(cond, args, thenC, elseC) =>
        If(cond, args, thenC, elseC)


      // SI - registering inlineable continuations
      case LetC(cnts, body) if cnts.exists(x => s.appliedOnce(x.name)) =>
        val (inlined, notInlined) = cnts.partition(x => s.appliedOnce(x.name))
        shrinkS(LetC(notInlined, body), s.withCnts(inlined))

      // SI - passing recursively in non inlineable continuations
      case LetC(cnts, body) =>
        val myCnts = cnts.map { c =>
          val Cnt(name, args, body) = c
          Cnt(name, args, shrinkS(body, s))
        }
        if (myCnts.isEmpty) shrinkS(body, s)
        else LetC(myCnts, shrinkS(body, s))

      // SI - handling AppC for inlineable continuation
      case AppC(cnt, args) if s.cEnv.contains(cnt) =>
        val Cnt(_, formalArgs, body) = s.cEnv(cnt)
        val newState = s.withASubst(formalArgs, args)
        shrinkS(body, newState)

      // exhaustive case
      case AppC(cnt, args) =>
        AppC(cnt, args)


      // SI - registering linear inlineable functions
      case LetF(fun, body) if fun.exists(f => s.appliedOnce(f.name)) =>
        val (inlined, notInlined) = fun.partition(f => s.appliedOnce(f.name))
        shrinkS(LetF(notInlined, body), s.withFuns(inlined))

      // SI - passing recursively in non inlineable functions
      case LetF(fun, body) =>
        val myFuns = fun.map { f =>
          val Fun(name, retC, args, body) = f
          Fun(name, retC, args, shrinkS(body, s))
        }
        if (myFuns.isEmpty) shrinkS(body, s)
        else LetF(myFuns, shrinkS(body, s))

      // SI - handling AppF inlineable functions
      case AppF(fun, c, args) if s.fEnv.contains(fun.asName.get) =>
        val Fun(_, formalC, formalArgs, body) = s.fEnv(fun.asName.get)
        val newState = s.withASubst(formalArgs, args).withCSubst(formalC, c)
        shrinkS(body, newState)

      // exhaustive case
      case AppF(fun, c, args) =>
        AppF(fun, c, args  )


      // exhaustive case
      case Halt(arg) => {
        Halt(arg)
      }
    }
  }

  // (Non-shrinking) inlining

  private def inline(tree: Tree, maxSize: Int): Tree = {
    def copyT(tree: Tree, subV: Subst[Atom], subC: Subst[Name]): Tree = {
      (tree: @unchecked) match {
        case LetP(name, prim, args, body) =>
          val name1 = name.copy
          LetP(name1, prim, args map subV,
            copyT(body, subV + (AtomN(name) -> AtomN(name1)), subC))
        case LetC(cnts, body) =>
          val names = cnts map (_.name)
          val names1 = names map (_.copy)
          val subC1 = subC ++ (names zip names1)
          LetC(cnts map (copyC(_, subV, subC1)), copyT(body, subV, subC1))
        case LetF(funs, body) =>
          val names = funs map (_.name)
          val names1 = names map (_.copy)
          val subV1 = subV ++ ((names map AtomN) zip (names1 map AtomN))
          LetF(funs map (copyF(_, subV1, subC)), copyT(body, subV1, subC))
        case AppC(cnt, args) =>
          AppC(subC(cnt), args map subV)
        case AppF(fun, retC, args) =>
          AppF(subV(fun), subC(retC), args map subV)
        case If(cond, args, thenC, elseC) =>
          If(cond, args map subV, subC(thenC), subC(elseC))
        case Halt(arg) =>
          Halt(subV(arg))
      }
    }

    def copyC(cnt: Cnt, subV: Subst[Atom], subC: Subst[Name]): Cnt = {
      val args1 = cnt.args map (_.copy)
      val subV1 = subV ++ ((cnt.args map AtomN) zip (args1 map AtomN))
      Cnt(subC(cnt.name), args1, copyT(cnt.body, subV1, subC))
    }

    def copyF(fun: Fun, subV: Subst[Atom], subC: Subst[Name]): Fun = {
      val retC1 = fun.retC.copy
      val subC1 = subC + (fun.retC -> retC1)
      val args1 = fun.args map (_.copy)
      val subV1 = subV ++ ((fun.args map AtomN) zip (args1 map AtomN))
      val AtomN(funName1) = subV(AtomN(fun.name))
      Fun(funName1, retC1, args1, copyT(fun.body, subV1, subC1))
    }

    val fibonacci = Seq(1, 2, 3, 5, 8, 13)

    val trees = LazyList.iterate((0, tree), fibonacci.length) { case (i, tree) =>
      val funLimit = fibonacci(i)
      val cntLimit = i

      def sameLen[T, U](formalArgs: Seq[T], actualArgs: Seq[U]): Boolean =
        formalArgs.length == actualArgs.length

      def shouldInlineC(cnt: Cnt): Boolean = cnt match {
        case Cnt(name, args, body: Tree) => size(body) <= cntLimit
      }
      def isInlinedC(cnt: Name)(implicit s: State): Boolean = s.cEnv.contains(cnt)

      def shouldInlineF(f: Fun): Boolean = f match {
        case Fun(name, retc, args, body) => size(body) <= funLimit
      }
      def isInlinedF(f: Name)(implicit s: State): Boolean = s.fEnv.contains(f)

      def inlineT(tree: Tree)(implicit s: State): Tree = {
        tree match {
          case LetP(name, prim, args, body) =>
            LetP(name, prim, args map s.aSubst, inlineT(body)(s))
          case LetC(cnts, body) =>
            val (yes, nope) = cnts.partition(c => shouldInlineC(c))
            val newState = s.withCnts(yes)
            val cs = nope.map {
              case Cnt(name: Name, args: Seq[Name], body: Tree) =>
                Cnt(name, args, inlineT(body)(newState))
            } ++ yes
            LetC(cs, inlineT(body)(newState))
          case LetF(funs, body) =>
            val (yes, nope) = funs.partition(f => shouldInlineF(f))
            val newState = s.withFuns(yes)
            val cs = nope.map {
              case Fun(name: Name, retC, args: Seq[Name], body: Tree) =>
                Fun(name, retC, args, inlineT(body)(newState))
            } ++ yes
            LetF(cs, inlineT(body)(newState))
          case AppC(cnt, args) if isInlinedC(s.cSubst(cnt)) =>
            val newCnt = s.cSubst(cnt)
            val Cnt(_, formalArgs, body) = s.cEnv(newCnt)
            val newArgs = args map s.aSubst
            val newState = s.withASubst(formalArgs, newArgs)
            // stop recursivity
            copyT(body, newState.aSubst, newState.cSubst)
          case AppC(cnt, args) =>
            AppC(s.cSubst(cnt), args map s.aSubst)
          case AppF(fun, c, args) if isInlinedF(s.aSubst(fun).asName.get) =>
            val newFun = s.aSubst(fun)
            val Fun(_, formalC, formalArgs, body) = s.fEnv(newFun.asName.get)
            val newArgs = args map s.aSubst
            val newC = s.cSubst(c)
            val newState = s.withASubst(formalArgs, newArgs).withCSubst(formalC, newC)
            // stop recursivity
            copyT(body, newState.aSubst, newState.cSubst)
          case AppF(fun, c, args) =>
            AppF(s.aSubst(fun), s.cSubst(c), args map s.aSubst)
          case If(cond, args, thenC, elseC) => If(cond, args map s.aSubst, s.cSubst(thenC), s.cSubst(elseC))
          case Halt(arg) => Halt(s.aSubst(arg))
        }
      }

      (i + 1, fixedPoint(inlineT(tree)(State(census(tree))))(shrink)) //shrink untill fixed point is reached
    }

    trees.takeWhile { case (_, tree) => size(tree) <= maxSize }.last._2
  }


  // Census computation
  private def census(tree: Tree): Map[Name, Count] = {
    val census = MutableMap[Name, Count]().withDefault(_ => Count())
    val rhs = MutableMap[Name, Tree]()

    def incAppUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(applied = currCount.applied + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incAppUseA(atom: Atom): Unit =
      atom.asName.foreach(incAppUseN(_))

    def incValUseN(name: Name): Unit = {
      val currCount = census(name)
      census(name) = currCount.copy(asValue = currCount.asValue + 1)
      rhs.remove(name).foreach(addToCensus)
    }

    def incValUseA(atom: Atom): Unit =
      atom.asName.foreach(incValUseN(_))

    def addToCensus(tree: Tree): Unit = (tree: @unchecked) match {
      case LetP(_, _, args, body) =>
        args foreach incValUseA; addToCensus(body)
      case LetC(cnts, body) =>
        rhs ++= (cnts map { c => (c.name, c.body) }); addToCensus(body)
      case LetF(funs, body) =>
        rhs ++= (funs map { f => (f.name, f.body) }); addToCensus(body)
      case AppC(cnt, args) =>
        incAppUseN(cnt); args foreach incValUseA
      case AppF(fun, retC, args) =>
        incAppUseA(fun); incValUseN(retC); args foreach incValUseA
      case If(_, args, thenC, elseC) =>
        args foreach incValUseA; incValUseN(thenC); incValUseN(elseC)
      case Halt(arg) =>
        incValUseA(arg)
    }

    addToCensus(tree)
    census.toMap
  }

  private def size(tree: Tree): Int = (tree: @unchecked) match {
    case LetP(_, _, _, body) => size(body) + 1
    case LetC(cs, body) => (cs map { c => size(c.body) }).sum + size(body)
    case LetF(fs, body) => (fs map { f => size(f.body) }).sum + size(body)
    case AppC(_, _) | AppF(_, _, _) | If(_, _, _, _) | Halt(_) => 1
  }

  protected val impure: ValuePrimitive => Boolean
  protected val unstable: ValuePrimitive => Boolean

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal]
  protected val blockTag: ValuePrimitive
  protected val blockLength: ValuePrimitive

  protected val blockGet : ValuePrimitive
  protected val blockSet : ValuePrimitive

  protected val identity: ValuePrimitive

  protected val leftNeutral: Set[(Literal, ValuePrimitive)]
  protected val rightNeutral: Set[(ValuePrimitive, Literal)]
  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)]
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)]

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom]
  protected val sameArgReduceC: TestPrimitive => Boolean

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal]
  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean]

  protected val myModule : CPSTreeModule
  protected object formatter extends CPSTreeFormatter(myModule)

}

object CPSOptimizerHigh extends CPSOptimizer(SymbolicCPSTreeModule)
  with (SymbolicCPSTreeModule.Tree => SymbolicCPSTreeModule.Tree) {

  import treeModule._

  def apply(tree: Tree): Tree =
    rewrite(tree)

  import scala.language.implicitConversions

  private[this] implicit def l3IntToLit(i: L3Int): Literal = IntLit(i)

  private[this] implicit def intToLit(i: Int): Literal = IntLit(L3Int(i))

  protected val impure: ValuePrimitive => Boolean =
    Set(L3BlockSet, L3ByteRead, L3ByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case L3BlockAlloc(_) | L3BlockGet | L3ByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case L3BlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = L3BlockTag
  protected val blockLength: ValuePrimitive = L3BlockLength

  protected val blockGet : ValuePrimitive = L3BlockGet
  protected val blockSet : ValuePrimitive = L3BlockSet

  protected val identity: ValuePrimitive = L3Id

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, L3IntAdd),
      (1, L3IntMul),
      (~0, L3IntBitwiseAnd), /*-1 = 1111..111 in 2-compl*/
      (0, L3IntBitwiseOr),
      (0, L3IntBitwiseXOr))

  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((L3IntAdd, 0), (L3IntSub, 0), (L3IntMul, 1), (L3IntDiv, 1),
      (L3IntShiftLeft, 0), (L3IntShiftRight, 0),
      (L3IntBitwiseAnd, ~0), (L3IntBitwiseOr, 0), (L3IntBitwiseXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, L3IntMul), (0, L3IntDiv),
      (0, L3IntShiftLeft), (0, L3IntShiftRight),
      (0, L3IntBitwiseAnd), (~0, L3IntBitwiseOr))

  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((L3IntMul, 0), (L3IntBitwiseAnd, 0), (L3IntBitwiseOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (L3IntBitwiseAnd | L3IntBitwiseOr, a) => a
    case (L3IntSub | L3IntMod | L3IntBitwiseXOr, _) => AtomL(0)
    case (L3IntDiv, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case L3IntLe | L3Eq => true
    case L3IntLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal] = {
    case (L3IntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x + y)
    case (L3IntSub, Seq(IntLit(x), IntLit(y))) => IntLit(x - y)
    case (L3IntMul, Seq(IntLit(x), IntLit(y))) => IntLit(x * y)
    case (L3IntDiv, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => IntLit(x / y)
    case (L3IntMod, Seq(IntLit(x), IntLit(y))) if y.toInt != 0 => IntLit(x % y)

    case (L3IntShiftLeft, Seq(IntLit(x), IntLit(y))) => IntLit(x << y)
    case (L3IntShiftRight, Seq(IntLit(x), IntLit(y))) => IntLit(x >> y)
    case (L3IntAdd, Seq(IntLit(x), IntLit(y))) => IntLit(x & y)
    case (L3IntBitwiseOr, Seq(IntLit(x), IntLit(y))) => IntLit(x | y)
    case (L3IntBitwiseXOr, Seq(IntLit(x), IntLit(y))) => IntLit(x ^ y)

  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean] = {
    case (L3IntLt, Seq(IntLit(x), IntLit(y))) => x < y
    case (L3IntLe, Seq(IntLit(x), IntLit(y))) => x <= y
    case (L3Eq, Seq(x, y)) => x == y

    case (L3BlockP, Seq(IntLit(_) | CharLit(_) | BooleanLit(_) | UnitLit)) => false
    case (L3IntP, Seq(IntLit(_))) => true
    case (L3IntP, Seq(_)) => false
    case (L3CharP, Seq(CharLit(_))) => true
    case (L3CharP, Seq(_)) => false
    case (L3BoolP, Seq(BooleanLit(_))) => true
    case (L3BoolP, Seq(_)) => false
    case (L3UnitP, Seq(UnitLit)) => true
    case (L3UnitP, Seq(_)) => false
  }
  protected val myModule = SymbolicCPSTreeModule
}

override object CPSOptimizerLow extends CPSOptimizer(SymbolicCPSTreeModuleLow)
  with (SymbolicCPSTreeModuleLow.LetF => SymbolicCPSTreeModuleLow.LetF) {

  import treeModule._

  def apply(tree: LetF): LetF = rewrite(tree) match {
    case tree@LetF(_, _) => tree
    case other => LetF(Seq(), other)
  }

  protected val impure: ValuePrimitive => Boolean =
    Set(CPSBlockSet, CPSByteRead, CPSByteWrite)

  protected val unstable: ValuePrimitive => Boolean = {
    case CPSBlockAlloc(_) | CPSBlockGet | CPSByteRead => true
    case _ => false
  }

  protected val blockAllocTag: PartialFunction[ValuePrimitive, Literal] = {
    case CPSBlockAlloc(tag) => tag
  }
  protected val blockTag: ValuePrimitive = CPSBlockTag
  protected val blockLength: ValuePrimitive = CPSBlockLength

  protected val blockGet : ValuePrimitive = CPSBlockGet
  protected val blockSet : ValuePrimitive = CPSBlockSet

  protected val identity: ValuePrimitive = CPSId

  protected val leftNeutral: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSAdd), (1, CPSMul), (~0, CPSAnd), (0, CPSOr), (0, CPSXOr))
  protected val rightNeutral: Set[(ValuePrimitive, Literal)] =
    Set((CPSAdd, 0), (CPSSub, 0), (CPSMul, 1), (CPSDiv, 1),
      (CPSShiftLeft, 0), (CPSShiftRight, 0),
      (CPSAnd, ~0), (CPSOr, 0), (CPSXOr, 0))

  protected val leftAbsorbing: Set[(Literal, ValuePrimitive)] =
    Set((0, CPSMul), (0, CPSDiv),
      (0, CPSShiftLeft), (0, CPSShiftRight),
      (0, CPSAnd), (~0, CPSOr))
  protected val rightAbsorbing: Set[(ValuePrimitive, Literal)] =
    Set((CPSMul, 0), (CPSAnd, 0), (CPSOr, ~0))

  protected val sameArgReduce: PartialFunction[(ValuePrimitive, Atom), Atom] = {
    case (CPSAnd | CPSOr, a) => a
    case (CPSSub | CPSMod | CPSXOr, _) => AtomL(0)
    case (CPSDiv, _) => AtomL(1)
  }

  protected val sameArgReduceC: PartialFunction[TestPrimitive, Boolean] = {
    case CPSLe | CPSEq => true
    case CPSLt => false
  }

  protected val vEvaluator: PartialFunction[(ValuePrimitive, Seq[Literal]),
    Literal] = {
    case (CPSAdd, Seq(x, y)) => x + y
    case (CPSSub, Seq(x, y)) => x - y
    case (CPSMul, Seq(x, y)) => x * y
    case (CPSDiv, Seq(x, y)) if y.toInt != 0 => x / y
    case (CPSMod, Seq(x, y)) if y.toInt != 0 => x % y

    case (CPSShiftLeft, Seq(x, y)) => x << y
    case (CPSShiftRight, Seq(x, y)) => x >> y
    case (CPSAnd, Seq(x, y)) => x & y
    case (CPSOr, Seq(x, y)) => x | y
    case (CPSXOr, Seq(x, y)) => x ^ y
  }

  protected val cEvaluator: PartialFunction[(TestPrimitive, Seq[Literal]),
    Boolean] = {
    case (CPSLt, Seq(x, y)) => x < y
    case (CPSLe, Seq(x, y)) => x <= y
    case (CPSEq, Seq(x, y)) => x == y
  }
  protected val myModule = SymbolicCPSTreeModuleLow
}

