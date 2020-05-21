package l3

import l3.{SymbolicCL3TreeModule => S}
import l3.{SymbolicCPSTreeModule => C}

object CL3ToCPSTranslator extends (S.Tree => C.Tree) {
  def apply(tree: S.Tree): C.Tree =
    nonTail(tree) { v: C.Atom =>
      C.Halt(C.AtomL(IntLit(L3Int(0))))
    }

  private def nonTail(tree: S.Tree)(context: C.Atom => C.Tree): C.Tree = {
    implicit val position = tree.pos

    tree match {
      case S.Let(bindings: Seq[(S.Name, S.Tree)], body: S.Tree) =>

        bindings match {
          case Seq(b, r@_*) =>
            nonTail(b._2) { v =>
              C.LetP(b._1, L3Id, Seq(v), nonTail(S.Let(r, body))(context))
            }
          case Seq() =>
            nonTail(body)(context)
        }

      case S.LetRec(functions: Seq[S.Fun], body: S.Tree) =>
        C.LetF(functions map { f =>
          val cntName = Symbol.fresh("c1")
          C.Fun(f.name, cntName, f.args, tail(f.body, cntName))
        }, nonTail(body)(context))

      case S.If(condTree: S.Tree, thenE: S.Tree, elseE: S.Tree) => {
        val c = Symbol.fresh("c")
        val r = Symbol.fresh("r")
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        C.LetC(Seq(C.Cnt(c, Seq(r), context(C.AtomN(r)))),
          C.LetC(Seq(C.Cnt(ct, Seq(), tail(thenE, c))),
            C.LetC(Seq(C.Cnt(cf, Seq(), tail(elseE, c))),
              cond(condTree, ct, cf))))
      }

      case S.App(fun: S.Tree, args: Seq[S.Tree]) =>
        nonTail(fun) { v =>
          recursiveNonTail(args) { newArgs =>
            val cName = Symbol.fresh("c")
            val rName = Symbol.fresh("r")
            C.LetC(Seq(C.Cnt(cName, Seq(rName), context(C.AtomN(rName)))), C.AppF(v, cName, newArgs))
          }
        }

      case S.Prim(prim: S.Primitive, args: Seq[S.Tree]) =>
        prim match {

          case tp: L3TestPrimitive => nonTail(S.If(S.Prim(tp, args),
            S.Lit(BooleanLit(true)),
            S.Lit(BooleanLit(false))))(context)

          case vp: L3ValuePrimitive => recursiveNonTail(args) { newArgs =>
            val primName = Symbol.fresh("p")
            C.LetP(primName, vp, newArgs, context(C.AtomN(primName)))
          }
        }

      case S.Halt(arg: S.Tree) =>
        nonTail(arg) { v =>
          C.Halt(v)
        }

      case S.Ident(name) =>
        context(C.AtomN(name))

      case S.Lit(value: CL3Literal) =>
        context(C.AtomL(value))
    }
  }

  private def tail(tree: S.Tree, storedCnt: C.Name): C.Tree = {
    implicit val pos = tree.pos

    tree match {
      case S.Let(bindings: Seq[(S.Name, S.Tree)], body: S.Tree) =>
        bindings match {

          case Seq(b, r@_*) =>
            nonTail(b._2) { v =>
              C.LetP(b._1, L3Id, Seq(v), tail(S.Let(r, body)(tree.pos), storedCnt))
            }

          case Seq() =>
            tail(body, storedCnt)
        }

      case S.LetRec(functions: Seq[S.Fun], body: S.Tree) =>
        C.LetF(functions map { f =>
          val cntName = Symbol.fresh("LetFCnt")
          C.Fun(f.name, cntName, f.args, tail(f.body, cntName))
        }, tail(body, storedCnt))

      case S.If(condTree: S.Tree, thenE: S.Tree, elseE: S.Tree) => {
        val ct = Symbol.fresh("ct")
        val cf = Symbol.fresh("cf")
        C.LetC(Seq(C.Cnt(ct, Seq(), tail(thenE, storedCnt))),
          C.LetC(Seq(C.Cnt(cf, Seq(), tail(elseE, storedCnt))),
            cond(condTree, ct, cf)))
      }

      case S.App(fun: S.Tree, args: Seq[S.Tree]) =>
        nonTail(fun) { v =>
          recursiveNonTail(args) { newArgs =>
            C.AppF(v, storedCnt, newArgs)
          }
        }

      case S.Prim(prim: S.Primitive, args: Seq[S.Tree]) =>
        prim match {
          case tp: L3TestPrimitive => tail(S.If(S.Prim(tp, args),
            S.Lit(BooleanLit(true)),
            S.Lit(BooleanLit(false))), storedCnt)

          case vp: L3ValuePrimitive => recursiveNonTail(args) { newArgs =>
            val primName = Symbol.fresh("p")
            C.LetP(primName, vp, newArgs, C.AppC(storedCnt, Seq(C.AtomN(primName))))
          }
        }

      case S.Halt(arg: S.Tree) =>
        nonTail(arg) { v =>
          C.Halt(v)
        }

      case S.Ident(name) =>
        C.AppC(storedCnt, Seq(C.AtomN(name)))

      case S.Lit(value: CL3Literal) =>
        C.AppC(storedCnt, Seq(C.AtomL(value)))
    }
  }

  private def cond(tree: S.Tree, ct: C.Name, cf: C.Name): C.Tree = {
    implicit val pos = tree.pos

    def litToCont(l: CL3Literal): Symbol =
      if (l != BooleanLit(false)) ct else cf

    tree match {
      case S.If(e1, S.Lit(tl), S.Lit(fl)) =>
        cond(e1, litToCont(tl), litToCont(fl))

      case S.If(e1, S.Lit(BooleanLit(true)), e3) =>
        val ac = Symbol.fresh("ac")
        C.LetC(
          Seq(C.Cnt(ac, Seq(), cond(e3, ct, cf))),
          cond(e1, ct, ac)
        )

      case S.If(e1, e2, S.Lit(BooleanLit(true))) =>
        val ac = Symbol.fresh("ac")
        C.LetC(
          Seq(C.Cnt(ac, Seq(), cond(e2, ct, cf))),
          cond(e1, ac, ct)
        )

      case S.If(e1, S.Lit(BooleanLit(false)), e3) =>
        val ac = Symbol.fresh("ac")
        C.LetC(
          Seq(C.Cnt(ac, Seq(), cond(e3, ct, cf))),
          cond(e1, cf, ac)
        )

      case S.If(e1, e2, S.Lit(BooleanLit(false))) =>
        val ac = Symbol.fresh("ac")
        C.LetC(
          Seq(C.Cnt(ac, Seq(), cond(e2, ct, cf))),
          cond(e1, ac, cf)
        )

      // regular case
      case S.Prim(p: L3TestPrimitive, args) =>
        recursiveNonTail(args)( newArgs => C.If(p, newArgs, ct, cf) )

      // regular case
      case other =>
        nonTail(other) { o =>
          C.If(L3Eq, Seq(o, C.AtomL(BooleanLit(false))), cf, ct)
        }
    }
  }

  private def recursiveNonTail(argsLeft: Seq[S.Tree],
                               accumulatedResults: Seq[C.Atom] = Seq())
                              (lambda: Seq[C.Atom] => C.Tree): C.Tree =
    argsLeft match {
      case Seq(a, r@_*) => nonTail(a) { v =>
        recursiveNonTail(r, accumulatedResults :+ v)(lambda)
      }

      case Seq() => lambda(accumulatedResults)
    }
}