package integration.`new`

import integration.helper.VercorsSpec

class BasicExamplesSpec extends VercorsSpec {
  vercors should verify using anyBackend in "trivial inline example" pvl """
  void test() {
    assert 1 + 2 == 3;
  }
  """

  vercors should verify using anyBackend example "basic/AddAssignJava.java"
  vercors should error withCode "resolutionError" example "basic/ArrayAsObject.java"
  vercors should verify using anyBackend example "basic/BasicAssert.java"
  vercors should verify using anyBackend example "basic/BasicAssert-e1.java"
  vercors should verify using anyBackend example "basic/BooleanOperators.java"
  vercors should error withCode "resolutionError" example "basic/Boxing.java"
  vercors should verify using anyBackend example "basic/CollectionTest.pvl"
  vercors should verify using anyBackend example "basic/ContractUnsatisfiableIntentional.java"
  vercors should verify using anyBackend example "basic/ContractUnsatisfiableIntentional.pvl"
  vercors should fail withCode "?" using anyBackend example "basic/ContractUnsatisfiableUnintentional.java"
  vercors should fail withCode "?" using anyBackend example "basic/ContractUnsatisfiableUnintentional.pvl"
  vercors should verify using anyBackend example "basic/For.java"
  vercors should verify using anyBackend example "basic/for.pvl"
  vercors should verify using anyBackend example "basic/frac1.pvl"
  vercors should verify using anyBackend example "basic/frac2.pvl"
  vercors should verify using anyBackend example "basic/fraction-comparison.pvl"
  vercors should verify using anyBackend example "basic/InlineFunctions.pvl"
  vercors should verify using anyBackend example "basic/JavaAnnotation.java"
  vercors should verify using anyBackend example "basic/MultiDimArray.java"
  vercors should verify using anyBackend example "basic/NewClassGhost.java"
  vercors should verify using anyBackend example "basic/pointer.c"
  vercors should verify using anyBackend example "basic/postfix-increment.pvl"
  vercors should verify using anyBackend example "basic/predicate.pvl"
  vercors should error withCode "?" example "basic/pure.pvl"
  vercors should verify using anyBackend example "basic/pvl-array.pvl"
  vercors should error withCode "?" example "basic/seq-immutable.pvl"
  vercors should verify using anyBackend example "basic/seq-item-access.pvl"
  vercors should verify using anyBackend example "basic/seq-length.pvl"
  vercors should verify using anyBackend example "basic/seq-seq-length.pvl"
  vercors should verify using anyBackend example "basic/sumints.pvl"
  vercors should verify using anyBackend example "basic/TernaryOperator.java"
  vercors should verify using anyBackend example "basic/test-1.c"
  vercors should verify using anyBackend example "basic/test-scale.java"
  vercors should verify using anyBackend example "basic/TurnOffContractSatisfiable.java"
  vercors should verify using anyBackend example "basic/yield.pvl"
}
