package l3

import l3.{SymbolicCPSTreeModule => H}
import l3.{SymbolicCPSTreeModuleLow => L}

import scala.collection.immutable.ListMap

object CPSValueRepresenter extends (H.Tree => L.Tree) {

  private def closedFunctionGetters(freeVars: Seq[L.Name], env: L.Name, body: H.Tree): L.Tree = {
    freeVars.zipWithIndex.foldRight(apply(body))((x, acc) => {
      L.LetP(x._1, CPSBlockGet, Seq(L.AtomN(env), L.AtomL(x._2 + 1)), acc)
    })
  }

  private def closureAllocation(fun: Seq[(H.Fun, L.Name)], environmentVars: Map[L.Name, Seq[H.Name]], myBody: H.Tree): L.Tree = {

    def letBlockAlloc(f1: H.Name, w1: L.Name, environmentVars: Seq[H.Name], cont: L.Tree): L.Tree = {
      L.LetP(f1, CPSBlockAlloc(202), Seq(L.AtomL(environmentVars.length)), cont)

    }

    def letBlockSet(f1:H.Name, freeVariables: Seq[L.Name], cont:L.Tree): L.Tree = {
      freeVariables.zipWithIndex.foldRight(cont) {
        case ((fv1, i0), body) =>
          tempLetP(CPSBlockSet, Seq(L.AtomN(f1), L.AtomL(i0), L.AtomN(fv1))) { _ => body }
      }
    }

    // multiple setters per function
    val setters = fun.foldRight(apply(myBody)) {
      case ((f, wName), body) =>
        letBlockSet(f.name, environmentVars(wName), body)
    }

    //one alloc per function
    val allocers = fun.foldRight(setters){
      case ((f, wName), body) =>
        letBlockAlloc(f.name, wName, environmentVars(wName), body)
    }

    allocers

  }


  def apply(tree: H.Tree): L.Tree = tree match {
    case H.LetC(cnts, body) => {
      L.LetC(cnts map { case H.Cnt(name, args, body) => L.Cnt(name, args, apply(body)) }, apply(body))
    }

    case H.AppC(name, args) => {
      L.AppC(name, args map apply)
    }

    case H.LetF(funs, body) => {

      val newFuns_freeVars = funs map {
        f: H.Fun =>
          val w1 = Symbol.fresh("w1")
          val env = Symbol.fresh("env")
          val freeVars: Seq[L.Name] = getFreeVarsF(f).toSeq
          val subFreeVars = freeVars.foldRight(Map.empty[Symbol,Symbol])((x, acc) => {acc.+(x -> Symbol.fresh("v1"))})
          (
            L.Fun(w1, f.retC, env +: f.args, closedFunctionGetters(subFreeVars.values.toSeq, env, substitute(f.body, subFreeVars + (f.name -> env))))
            , w1 +: subFreeVars.keys.toSeq
          )
      }

      // first block on slides = list with all function definitions (augmented with env and BLOCK-GET free variables)
      // second block on slides = one big let* of closure ALLOCATION and BLOCK-SET for free variables
      val environmentVars = newFuns_freeVars.map(x => (x._1.name, x._2)).toMap
      val definitions = newFuns_freeVars.map(_._1)
      L.LetF(definitions, closureAllocation(funs.zip(definitions.map(_.name)), environmentVars, body))

    }


    case H.AppF(fun, retC, args) =>
      val tf = apply(fun)
      tempLetP(CPSBlockGet, Seq(tf, L.AtomL(0))) { newFun =>
        L.AppF(newFun, retC, tf +: args.map(apply))
      }

    case H.Halt(arg) =>
      tempLetP(CPSShiftRight, Seq(apply(arg), L.AtomL(1))) { r =>
        L.Halt(r)
      }



    /////////////////////////////
    // Convert Test Primitives
    /////////////////////////////

    case H.If(L3IntP, Seq(x), thenE, elseE) =>
      tempLetP(CPSAnd, Seq(apply(x), L.AtomL(0x1))) { lsb =>
        L.If(CPSEq, Seq(lsb, L.AtomL(0x1)), thenE, elseE)
      }

    case H.If(L3CharP, Seq(x), thenE, elseE) =>
      tempLetP(CPSAnd, Seq(apply(x), L.AtomL(0x7))) { lsb =>
        L.If(CPSEq, Seq(lsb, L.AtomL(0x6)), thenE, elseE)
      }

    case H.If(L3BoolP, Seq(x), thenE, elseE) =>
      tempLetP(CPSAnd, Seq(apply(x), L.AtomL(0xf))) { lsb =>
        L.If(CPSEq, Seq(lsb, L.AtomL(0xa)), thenE, elseE)
      }

    case H.If(L3UnitP, Seq(x), thenE, elseE) =>
      L.If(CPSEq, Seq(apply(x), L.AtomL(0x2)), thenE, elseE)

    case H.If(L3BlockP, Seq(x), thenE, elseE) =>
      tempLetP(CPSAnd, Seq(apply(x), L.AtomL(0x3))) { lsb =>
        L.If(CPSEq, Seq(lsb, L.AtomL(0x0)), thenE, elseE)
      }

    case H.If(L3IntLt, Seq(x, y), thenE, elseE) =>
      L.If(CPSLt, Seq(apply(x), apply(y)), thenE, elseE)

    case H.If(L3IntLe, Seq(x, y), thenE, elseE) =>
      L.If(CPSLe, Seq(apply(x), apply(y)), thenE, elseE)

    case H.If(L3Eq, Seq(x, y), thenE, elseE) =>
      L.If(CPSEq, Seq(apply(x), apply(y)), thenE, elseE)


    /////////////////////////////
    // Convert Value Primitives
    /////////////////////////////

    case H.LetP(name, L3IntAdd, Seq(x, y), body) =>
      tempLetP(CPSSub, Seq(apply(x), L.AtomL(1))) { ux =>
        L.LetP(name, CPSAdd, Seq(ux, apply(y)), apply(body))
      }

    case H.LetP(name, L3IntSub, Seq(x, y), body) =>
      tempLetP(CPSAdd, Seq(apply(x), L.AtomL(1))) { ux =>
        L.LetP(name, CPSSub, Seq(ux, apply(y)), apply(body))
      }

    case H.LetP(name, L3IntMul, Seq(x, y), body) =>
      tempLetP(CPSSub, Seq(apply(x), L.AtomL(1))) { ux =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { uy =>
          tempLetP(CPSMul, Seq(ux, uy)) { mulRes =>
            L.LetP(name, CPSAdd, Seq(mulRes, L.AtomL(1)), apply(body))
          }
        }
      }

    case H.LetP(name, L3IntDiv, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { num =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { div =>
          tempLetP(CPSDiv, Seq(num, div)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3IntMod, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { num =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { div =>
          tempLetP(CPSMod, Seq(num, div)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3BlockAlloc(tag), Seq(x), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { t1 =>
        L.LetP(name, CPSBlockAlloc(tag), Seq(t1), apply(body))
      }

    case H.LetP(name, L3BlockTag, Seq(x), body) =>
      tempLetP(CPSBlockTag, Seq(apply(x))) { t1 =>
        tempLetP(CPSShiftLeft, Seq(t1, L.AtomL(1))) { t2 =>
          L.LetP(name, CPSAdd, Seq(t2, L.AtomL(0x1)), apply(body))
        }
      }

    case H.LetP(name, L3BlockLength, Seq(x), body) =>
      tempLetP(CPSBlockLength, Seq(apply(x))) { t1 =>
        tempLetP(CPSShiftLeft, Seq(t1, L.AtomL(1))) { t2 =>
          L.LetP(name, CPSAdd, Seq(t2, L.AtomL(0x1)), apply(body))
        }
      }

    case H.LetP(name, L3BlockGet, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
        L.LetP(name, CPSBlockGet, Seq(apply(x), newY), apply(body))
      }

    case H.LetP(name, L3BlockSet, Seq(x, y, z), body) =>
      tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
        L.LetP(name, CPSBlockSet, Seq(apply(x), newY, apply(z)), apply(body))
      }

    case H.LetP(name, L3IntShiftLeft, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { newX =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
          tempLetP(CPSShiftLeft, Seq(newX, newY)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3IntShiftRight, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { newX =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
          tempLetP(CPSShiftRight, Seq(newX, newY)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3IntBitwiseAnd, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { newX =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
          tempLetP(CPSAnd, Seq(newX, newY)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3IntBitwiseOr, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { newX =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
          tempLetP(CPSOr, Seq(newX, newY)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3IntBitwiseXOr, Seq(x, y), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { newX =>
        tempLetP(CPSShiftRight, Seq(apply(y), L.AtomL(1))) { newY =>
          tempLetP(CPSXOr, Seq(newX, newY)) { res =>
            tempLetP(CPSShiftLeft, Seq(res, L.AtomL(1))) { newRes =>
              L.LetP(name, CPSAdd, Seq(newRes, L.AtomL(0x1)), apply(body))
            }
          }
        }
      }

    case H.LetP(name, L3ByteRead, Seq(), body) =>
      tempLetP(CPSByteRead, Seq()) { b =>
        tempLetP(CPSShiftLeft, Seq(b, L.AtomL(1))) { res =>
          L.LetP(name, CPSAdd, Seq(res, L.AtomL(0x1)), apply(body))
        }
      }

    case H.LetP(name, L3ByteWrite, Seq(x), body) =>
      tempLetP(CPSShiftRight, Seq(apply(x), L.AtomL(1))) { b =>
        L.LetP(name, CPSByteWrite, Seq(b), apply(body))
      }

    case H.LetP(name, L3IntToChar, Seq(x), body) =>
      tempLetP(CPSShiftLeft, Seq(apply(x), L.AtomL(2))) { t1 =>
        L.LetP(name, CPSAdd, Seq(t1, L.AtomL(0x2)), apply(body))
      }

    case H.LetP(name, L3CharToInt, Seq(x), body) =>
      L.LetP(name, CPSShiftRight, Seq(apply(x), L.AtomL(2)), apply(body))

    case H.LetP(name, L3Id, Seq(x), body) =>
      L.LetP(name, CPSId, Seq(apply(x)), apply(body))
  }

  private def apply(a: H.Atom): L.Atom = a match {
    case H.AtomN(n) => L.AtomN(n)
    case H.AtomL(IntLit(v)) => L.AtomL((v.toInt << 1) + 0x1)
    case H.AtomL(CharLit(v)) => L.AtomL((v.toInt << 3) + 0x6)
    case H.AtomL(BooleanLit(true)) => L.AtomL(0x1a)
    case H.AtomL(BooleanLit(false)) => L.AtomL(0x0a)
    case H.AtomL(UnitLit) => L.AtomL(0x2)
  }


  private def getFT(tree: H.Tree): Set[Symbol] = tree match {

    case H.LetP(name, prim, args, body) => (getFT(body) - name) union ((args flatMap getFreeVarsA).toSet)
    case H.LetC(cnts, body) => getFT(body) union cnts.flatMap(getFreeVarsC).toSet
    case H.LetF(funs, body) => (getFT(body) union (funs.flatMap(getFreeVarsF).toSet)) diff funs.map(_.name).toSet
    case H.AppC(cnt, args) => (args flatMap getFreeVarsA).toSet
    case H.AppF(fun, retC, args) => ((fun +: args) flatMap getFreeVarsA).toSet
    case H.If(cond, args, thenC, elseC) => (args flatMap getFreeVarsA).toSet
    case H.Halt(arg) => getFreeVarsA(arg)
  }

  private def getFreeVarsF(f: H.Fun): Set[Symbol] = f match {
    case H.Fun(name, retC, args, body) => getFT(body) diff args.toSet diff Set(name)
    // !! added diff Set(name) !!
    // does not match slides but doesn't matter as result is the same
    // and we use this function another time where we don't want the name of
    // the function in free variables
  }

  private def getFreeVarsC(c: H.Cnt): Set[Symbol] = c match {
    case H.Cnt(name, args, body) => getFT(body) diff args.toSet
  }

  private def getFreeVarsA(a: H.Atom): Set[Symbol] = a match {
    case H.AtomN(n) => Set(n)
    case H.AtomL(l) => Set()
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])
                      (body: L.AtomN => L.Tree): L.Tree = {
    val temp = Symbol.fresh("t")
    L.LetP(temp, p, args, body(L.AtomN(temp)))
  }

  private def substitute(tree: H.Tree, s: Map[Symbol, Symbol]): H.Tree = {

    def substT(tree: H.Tree): H.Tree = tree match {
      case H.LetP(name, prim, args, body) => H.LetP(name, prim, args map substA, substT(body))
      case H.LetC(cnts, body) => H.LetC(cnts map substC, substT(body))
      case H.LetF(funs, body) => H.LetF(funs map substF, substT(body))
      case H.AppC(cnt, args) => H.AppC(replaceIfPossible(cnt), args map substA)
      case H.AppF(fun, retC, args) => H.AppF(substA(fun), replaceIfPossible(retC), args map substA)
      case H.If(cond, args, thenC, elseC) => H.If(cond, args map substA, replaceIfPossible(thenC), replaceIfPossible(elseC))
      case H.Halt(arg) => H.Halt(substA(arg))
    }

    def substC(cnt: H.Cnt): H.Cnt =
      H.Cnt(cnt.name, cnt.args map replaceIfPossible, substT(cnt.body))

    def substF(fun: H.Fun): H.Fun =
      H.Fun(fun.name, replaceIfPossible(fun.retC), fun.args map replaceIfPossible, substT(fun.body))

    def substA(atom: H.Atom): H.Atom = atom match {
      case H.AtomN(n) => H.AtomN(replaceIfPossible(n))
      case _ => atom
    }

    def replaceIfPossible(sym: Symbol): Symbol =
      s.get(sym) getOrElse sym

    substT(tree)

  }
}