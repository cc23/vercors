package vct.test.integration.examples

import vct.test.integration.helper.VercorsSpec

class SIFExamplesSpec extends VercorsSpec {
  vercors should verify using anyBackend example "concepts/sif/LowLoopExample.java"
  vercors should fail withCode "postFailed:false" using anyBackend example "concepts/sif/SimpleLowExample.java"
  vercors should verify using anyBackend example "concepts/sif/nagini-examples/TestTryCatch.java"
  vercors should fail withCode "postFailed:false" using anyBackend example "concepts/sif/nagini-examples/TestTryCatchFailing.java"
  vercors should verify using anyBackend example "concepts/sif/nagini-examples/HighReferencesLowValues.java"

  //lowEvent
  vercors should verify using anyBackend example "concepts/sif/LowEventExample.java"
  vercors should verify using anyBackend example "concepts/sif/AssertLowEvent.java"
  vercors should fail withCode "assertFailed:false" using anyBackend example "concepts/sif/AssertLowEventFailing.java"
  // TODO failing atm:
  // vercors should verify using anyBackend example "concepts/sif/nagini-examples/JoanaFig1Adjusted.java"

  //declassify
  vercors should verify using anyBackend example "concepts/sif/SimpleDeclassifyExample.java"
  vercors should verify using anyBackend example "concepts/sif/DeclassifyAlias.java"
  vercors should fail withCode "postFailed:false" using anyBackend example "concepts/sif/SimpleDeclassifyExampleFailing.java"

  //break, continue, return
  vercors should verify using anyBackend example "concepts/sif/BreakExample.java"
  vercors should verify using anyBackend example "concepts/sif/BreakLowExample.java"
  vercors should verify using anyBackend example "concepts/sif/BreakExampleBreakAfterAssign.java"
  vercors should verify using anyBackend example "concepts/sif/ContinueExample.java"
  vercors should verify using anyBackend example "concepts/sif/ReturnExample.java"
  vercors should verify using anyBackend example "concepts/sif/ReturnLoopExample.java"

  //TODO check how to do the encoding for labeled breaks
  vercors should fail withCode "notMaintained:false"  using anyBackend example "concepts/sif/BreakLblEncodedExample.java"
  vercors should verify using anyBackend example "concepts/sif/BreakLblEncodedExampleFixed.java"
  //TODO failing atm: enable java labels & break outer loops
  //vercors should verify using anyBackend example "concepts/sif/BreakLblExample.java"


}
