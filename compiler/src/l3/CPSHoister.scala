package l3

import SymbolicCPSTreeModuleLow._

object CPSHoister extends (Tree => LetF) {
  def apply(tree: Tree): LetF = tree match {

    case LetP(name, prim, args, body) => {
      val hoistedLetf = apply(body)
      LetF(hoistedLetf.funs, LetP(name, prim, args, hoistedLetf.body))
    }

    case LetC(cnts, body) => {
      val accumulatedCnts = cnts.map(cnt => {
        val hoistedCnt = apply(cnt.body)
        Cnt(cnt.name, cnt.args, hoistedCnt.body)
      })

      val accumulatedFuns = cnts.flatMap(cnt => { apply(cnt.body).funs })

      val hoistedLetf = apply(body)
      LetF(accumulatedFuns ++ hoistedLetf.funs, LetC(accumulatedCnts, hoistedLetf.body))
    }

    case LetF(funs, body) => {
      val accumulatedFuns = funs.flatMap(f => {
        val hoistedF = apply(f.body)
        Fun(f.name, f.retC, f.args, hoistedF.body) +: hoistedF.funs
      })

      val hoistedLetf = apply(body)
      LetF(accumulatedFuns ++ hoistedLetf.funs, hoistedLetf.body)
    }

    case _ => LetF(Seq(), tree)
  }
}