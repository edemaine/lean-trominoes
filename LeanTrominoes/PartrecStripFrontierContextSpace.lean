import LeanTrominoes.PartrecFrontierIndexDecodeSpace
import LeanTrominoes.PartrecPeriodicStripDecodeSpace
import LeanTrominoes.PartrecStripFrontierContext

/-!
# Evaluator-space certificate for the strip frontier context

This file composes fitted strip-header decoding with fitted period division
of both frontier indices.  The final seven native fields are the complete
fixed-width context consumed by subsequent streaming motif checks.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def stripFrontierHeaderAtCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  periodicStripHeaderCost periodicStrip +
    getCost 0
      [Encodable.encode periodicStrip, first, last]

theorem stripFrontierHeaderAt
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits Code.stripFrontierHeaderAtCode
      [Encodable.encode periodicStrip, first, last]
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif]
      (stripFrontierHeaderAtCost
        periodicStrip first last) := by
  simpa [Code.stripFrontierHeaderAtCode,
    stripFrontierHeaderAtCost] using
    comp (periodicStripHeader periodicStrip)
      (get 0
        [Encodable.encode periodicStrip, first, last])

def stripFrontierHeaderFieldCost
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  getCost field
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif] +
    stripFrontierHeaderAtCost periodicStrip first last

theorem stripFrontierHeaderField
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.stripFrontierHeaderFieldCode field)
      [Encodable.encode periodicStrip, first, last]
      [[periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif][field]?.getD 0]
      (stripFrontierHeaderFieldCost
        field periodicStrip first last) := by
  simpa [Code.stripFrontierHeaderFieldCode,
    stripFrontierHeaderFieldCost] using
    comp
      (get field
        [periodicStrip.width, periodicStrip.period,
          Encodable.encode periodicStrip.motif])
      (stripFrontierHeaderAt periodicStrip first last)

def stripFrontierPairArgumentsTailCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [first] [last]
    (getCost 1 values) (getCost 2 values)

theorem stripFrontierPairArgumentsTail
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend (Code.get 1) (Code.get 2))
      [Encodable.encode periodicStrip, first, last]
      [first, last]
      (stripFrontierPairArgumentsTailCost
        periodicStrip first last) := by
  simpa [stripFrontierPairArgumentsTailCost,
    prependCost] using
    prepend
      (get 1
        [Encodable.encode periodicStrip, first, last])
      (get 2
        [Encodable.encode periodicStrip, first, last])

def stripFrontierPairArgumentsCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [periodicStrip.period]
    [first, last]
    (stripFrontierHeaderFieldCost
      1 periodicStrip first last)
    (stripFrontierPairArgumentsTailCost
      periodicStrip first last)

theorem stripFrontierPairArguments
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits Code.stripFrontierPairArgumentsCode
      [Encodable.encode periodicStrip, first, last]
      [periodicStrip.period, first, last]
      (stripFrontierPairArgumentsCost
        periodicStrip first last) := by
  simpa [Code.stripFrontierPairArgumentsCode,
    stripFrontierPairArgumentsCost, prependCost] using
    prepend
      (stripFrontierHeaderField
        1 periodicStrip first last)
      (stripFrontierPairArgumentsTail
        periodicStrip first last)

def stripFrontierPairViewCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  frontierPairViewCost periodicStrip.period first last +
    stripFrontierPairArgumentsCost
      periodicStrip first last

theorem stripFrontierPairView
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits Code.stripFrontierPairViewCode
      [Encodable.encode periodicStrip, first, last]
      [first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierPairViewCost
        periodicStrip first last) := by
  simpa [Code.stripFrontierPairViewCode,
    stripFrontierPairViewCost] using
    comp
      (frontierPairView
        periodicStrip.period first last)
      (stripFrontierPairArguments
        periodicStrip first last)

def stripFrontierPairFieldCost
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  getCost field
      [first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period] +
    stripFrontierPairViewCost
      periodicStrip first last

theorem stripFrontierPairField
    (field : Nat) (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.stripFrontierPairFieldCode field)
      [Encodable.encode periodicStrip, first, last]
      [[first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period][field]?.getD 0]
      (stripFrontierPairFieldCost
        field periodicStrip first last) := by
  simpa [Code.stripFrontierPairFieldCode,
    stripFrontierPairFieldCost] using
    comp
      (get field
        [first / periodicStrip.period,
          first % periodicStrip.period,
          last / periodicStrip.period,
          last % periodicStrip.period])
      (stripFrontierPairView periodicStrip first last)

def stripFrontierContextLastCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [last / periodicStrip.period]
    [last % periodicStrip.period]
    (stripFrontierPairFieldCost
      2 periodicStrip first last)
    (stripFrontierPairFieldCost
      3 periodicStrip first last)

theorem stripFrontierContextLast
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.stripFrontierPairFieldCode 2)
        (Code.stripFrontierPairFieldCode 3))
      [Encodable.encode periodicStrip, first, last]
      [last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextLastCost
        periodicStrip first last) := by
  simpa [stripFrontierContextLastCost,
    prependCost] using
    prepend
      (stripFrontierPairField
        2 periodicStrip first last)
      (stripFrontierPairField
        3 periodicStrip first last)

def stripFrontierContextFirstPhaseCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [first % periodicStrip.period]
    [last / periodicStrip.period,
      last % periodicStrip.period]
    (stripFrontierPairFieldCost
      1 periodicStrip first last)
    (stripFrontierContextLastCost
      periodicStrip first last)

theorem stripFrontierContextFirstPhase
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.stripFrontierPairFieldCode 1)
        (Code.prepend
          (Code.stripFrontierPairFieldCode 2)
          (Code.stripFrontierPairFieldCode 3)))
      [Encodable.encode periodicStrip, first, last]
      [first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextFirstPhaseCost
        periodicStrip first last) := by
  simpa [stripFrontierContextFirstPhaseCost,
    prependCost] using
    prepend
      (stripFrontierPairField
        1 periodicStrip first last)
      (stripFrontierContextLast
        periodicStrip first last)

def stripFrontierContextFirstWordCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [first / periodicStrip.period]
    [first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
    (stripFrontierPairFieldCost
      0 periodicStrip first last)
    (stripFrontierContextFirstPhaseCost
      periodicStrip first last)

theorem stripFrontierContextFirstWord
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.stripFrontierPairFieldCode 0)
        (Code.prepend
          (Code.stripFrontierPairFieldCode 1)
          (Code.prepend
            (Code.stripFrontierPairFieldCode 2)
            (Code.stripFrontierPairFieldCode 3))))
      [Encodable.encode periodicStrip, first, last]
      [first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextFirstWordCost
        periodicStrip first last) := by
  simpa [stripFrontierContextFirstWordCost,
    prependCost] using
    prepend
      (stripFrontierPairField
        0 periodicStrip first last)
      (stripFrontierContextFirstPhase
        periodicStrip first last)

def stripFrontierContextMotifCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values
    [Encodable.encode periodicStrip.motif]
    [first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
    (stripFrontierHeaderFieldCost
      2 periodicStrip first last)
    (stripFrontierContextFirstWordCost
      periodicStrip first last)

theorem stripFrontierContextMotif
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.stripFrontierHeaderFieldCode 2)
        (Code.prepend
          (Code.stripFrontierPairFieldCode 0)
          (Code.prepend
            (Code.stripFrontierPairFieldCode 1)
            (Code.prepend
              (Code.stripFrontierPairFieldCode 2)
              (Code.stripFrontierPairFieldCode 3)))))
      [Encodable.encode periodicStrip, first, last]
      [Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextMotifCost
        periodicStrip first last) := by
  simpa [stripFrontierContextMotifCost,
    prependCost] using
    prepend
      (stripFrontierHeaderField
        2 periodicStrip first last)
      (stripFrontierContextFirstWord
        periodicStrip first last)

def stripFrontierContextPeriodCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [periodicStrip.period]
    [Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
    (stripFrontierHeaderFieldCost
      1 periodicStrip first last)
    (stripFrontierContextMotifCost
      periodicStrip first last)

theorem stripFrontierContextPeriod
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits
      (Code.prepend
        (Code.stripFrontierHeaderFieldCode 1)
        (Code.prepend
          (Code.stripFrontierHeaderFieldCode 2)
          (Code.prepend
            (Code.stripFrontierPairFieldCode 0)
            (Code.prepend
              (Code.stripFrontierPairFieldCode 1)
              (Code.prepend
                (Code.stripFrontierPairFieldCode 2)
                (Code.stripFrontierPairFieldCode 3))))))
      [Encodable.encode periodicStrip, first, last]
      [periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextPeriodCost
        periodicStrip first last) := by
  simpa [stripFrontierContextPeriodCost,
    prependCost] using
    prepend
      (stripFrontierHeaderField
        1 periodicStrip first last)
      (stripFrontierContextMotif
        periodicStrip first last)

def stripFrontierContextCost
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  let values :=
    [Encodable.encode periodicStrip, first, last]
  prependCost values [periodicStrip.width]
    [periodicStrip.period,
      Encodable.encode periodicStrip.motif,
      first / periodicStrip.period,
      first % periodicStrip.period,
      last / periodicStrip.period,
      last % periodicStrip.period]
    (stripFrontierHeaderFieldCost
      0 periodicStrip first last)
    (stripFrontierContextPeriodCost
      periodicStrip first last)

theorem stripFrontierContext
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    EvaluatorCodeFits Code.stripFrontierContextCode
      [Encodable.encode periodicStrip, first, last]
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif,
        first / periodicStrip.period,
        first % periodicStrip.period,
        last / periodicStrip.period,
        last % periodicStrip.period]
      (stripFrontierContextCost
        periodicStrip first last) := by
  simpa [Code.stripFrontierContextCode,
    stripFrontierContextCost, prependCost] using
    prepend
      (stripFrontierHeaderField
        0 periodicStrip first last)
      (stripFrontierContextPeriod
        periodicStrip first last)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
