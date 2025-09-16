package vct.test.integration.examples

import vct.test.integration.helper.VercorsSpec

import java.io.File
import scala.collection.immutable

class SIFUCEvaluationSpec extends VercorsSpec {

  val failureMap = immutable.Map[String, String](
    "Figure3_02.java" -> "2ndVerificationPostFailed:false",
    "Figure3_02_low_inv.java" -> "assignFailedSIFUC",
    "Figure3_03.java" -> "invocationSIFUCFailure:false",
    "Figure3_04.java"-> "highBranchFail",
    "Figure3_05.java"-> "highBranchFail",
    "Figure3_05_array.java" -> "invocationSIFUCFailure:false",
    "Figure3_06.java"-> "highBranchFail",
    "Figure3_07.java"-> "highBranchFail",
    "Figure3_07_array.java" -> "invocationSIFUCFailure:false",
    "Figure3_08.java"-> "highBranchFail",
    "Figure3_08_array.java" -> "invocationSIFUCFailure:false",
    "Figure3_08_nonmod.java"-> "highBranchFail",
    "Figure3_08_nonmod_array.java" -> "invocationSIFUCFailure:false",
    "Figure3_09.java" -> "assignFailedSIFUC",
    "Figure3_10.java"-> "highBranchFail",
    "Figure3_11.java"-> "highBranchFail",
    "Figure3_11_array.java" -> "assignFailedSIFUC",
    "Figure3_12.java"-> "highBranchFail",
    "Figure3_13.java"-> "highBranchFail",
    "Figure3_13_array.java" -> "assignFailedSIFUC",
    "Figure3_15.java" -> "leakFailed",
    "Figure3_15_mod.java" -> "leakFailed",
    "Figure3_15_nonmod.java" -> "leakFailed",
    "Figure3_16_run2.java"-> "highBranchFail",
  )


  val dir = new File("examples/concepts/sif-uc-evaluation")

  vercors should verify using anyBackend example "concepts/sif/WarmUpExample.java"
  vercors should verify using anyBackend example "concepts/sif/WarmUpExample2.java"
  vercors should verify using anyBackend example "concepts/sif/WarmUpExample3.java"
  dir.listFiles.filter(_.isFile).sortBy(_.getName).toSeq.foreach(f => {
    val fileName = f.getName
    if(fileName.endsWith("declassified.java") || fileName.endsWith("no_getter.java") || fileName.contains("secure")){
      vercors should verify using anyBackend example "concepts/sif-uc-evaluation/"+f.getName
    } else {
      vercors should fail withCode failureMap(fileName) using anyBackend example "concepts/sif-uc-evaluation/" + f.getName
    }
  })

}
