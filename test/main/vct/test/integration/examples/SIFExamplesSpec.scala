package vct.test.integration.examples

import vct.test.integration.helper.VercorsSpec

class SIFExamplesSpec extends VercorsSpec {
  vercors should verify using anyBackend example "concepts/sif/LowLoopExample.java"
  vercors should fail withCode "postFailed:false" using anyBackend  example "concepts/sif/SimpleLowExample.java"
  vercors should verify using anyBackend example "concepts/sif/nagini-examples/TestTryCatch.java"
  vercors should fail withCode "postFailed:false" using anyBackend example "concepts/sif/nagini-examples/TestTryCatchFailing.java"

  //lowEvent
  vercors should verify using anyBackend example "concepts/sif/LowEventExample.java"
  // TODO failing atm:
  // vercors should verify using anyBackend example "concepts/sif/nagini-examples/JoanaFig1Adjusted.java"

}
