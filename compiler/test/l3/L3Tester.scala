package l3

import java.io.{ ByteArrayOutputStream, PrintStream }
import java.nio.file.{ Paths }

import scala.util.Using.{resource => using}

import SymbolicCL3TreeModule.Tree

object L3Tester {
  def compile[T](backEnd: Tree => Either[String, T])
             (inFileNames: Seq[String]): Either[String, T] = {
    val basePath = Paths.get(".").toAbsolutePath.normalize
    Right(inFileNames)
      .flatMap(L3FileReader.readFilesExpandingModules(basePath, _))
      .flatMap(p => L3Parser.parse(p._1, p._2))
      .flatMap(CL3NameAnalyzer)
      .flatMap(backEnd)
  }

  def compileNoFail[T](backEnd: Tree => T)
                   (inFileNames: Seq[String]): Either[String, T] =
    compile(t => Right(backEnd(t)))(inFileNames)

  def compileAndRun(backEnd: Tree => TerminalPhaseResult)
                   (inFileNames: Seq[String]): Either[String, String] = {
    def outputCapturingBackend(t: Tree): Either[String, String] = {
      val outBS = new ByteArrayOutputStream()
      using(new PrintStream(outBS)) { outPS =>
        val out0 = System.out
        try {
          System.setOut(outPS)
          backEnd(t)
            .flatMap(_ => Right(outBS.toString("UTF-8")))
        } finally {
          System.setOut(out0)
        }
      }
    }

    compile(outputCapturingBackend(_))(inFileNames)
  }

  val backEnd1 = (
    CL3Interpreter
  )

  val backEnd2 = (
    CL3ToCPSTranslator
      andThen CPSInterpreterHigh
  )

  val backEnd3 = (
    CL3ToCPSTranslator
      andThen CPSValueRepresenter
      andThen CPSHoister
      andThen CPSInterpreterLow
  )

  val backEnd4 = (
    CL3ToCPSTranslator
      andThen CPSOptimizerHigh
      andThen CPSValueRepresenter
      andThen CPSHoister
      andThen CPSOptimizerLow
      andThen CPSInterpreterLow
  )

  val backEnd5 = (
    CL3ToCPSTranslator
      andThen CPSValueRepresenter
      andThen CPSHoister
      andThen CPSConstantNamer
      andThen CPSRegisterAllocator
      andThen CPSToASMTranslator
      andThen ASMLabelResolver
      andThen ASMInterpreter
  )

  val backEnd6 = (
    CL3ToCPSTranslator
      andThen CPSOptimizerHigh
      andThen CPSValueRepresenter
      andThen CPSHoister
      andThen CPSOptimizerLow
      andThen CPSConstantNamer
      andThen CPSRegisterAllocator
      andThen CPSToASMTranslator
      andThen ASMLabelResolver
      andThen ASMInterpreter
  )



  /* THIS LAST PART WAS ADDED */
  /* CAN BE REMOVED */
  /* ADDED FOR TREEPRINTING */

  import java.io.PrintWriter
  import java.nio.file.{Files, Paths}

  import l3.SymbolicCL3TreeModule.Tree

  import CL3TreeFormatter._ // Implicits required for CL3 tree printing
  import CPSTreeFormatter._ // Implicits required for CPS tree printing
  import CPSTreeChecker._ // Implicits required for CPS tree checking

  private lazy val outPrintWriter =
    new PrintWriter(System.out, true)

  private def treeChecker[T <: CPSTreeModule](implicit c: CPSTreeChecker[T]) =
    passThrough(c)

  private def treePrinter[T](msg: String)(implicit f: Formatter[T]): T => T =
    passThrough { tree =>
      outPrintWriter.println(msg)
      f.toDoc(tree).writeTo(80, outPrintWriter)
      outPrintWriter.println()
    }

  private def seqPrinter[T](msg: String): Seq[T] => Seq[T] =
    passThrough { program =>
      outPrintWriter.println(msg)
      program foreach outPrintWriter.println
    }

  private def passThrough[T](f: T => Unit): T => T = { t: T => f(t); t }

}
