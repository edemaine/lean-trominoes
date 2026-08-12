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

/-- A shared arithmetic envelope for decoding the strip header and both
frontier indices from `[stripCode, first, last]`. -/
def stripFrontierContextPolynomialSpaceLimit
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  64 * (Encodable.encode periodicStrip + first + last + 100) + 1000

/-- Native workspace unit for the complete seven-field strip context. -/
def stripFrontierContextPolynomialSpaceUnit
    (periodicStrip : PeriodicStrip)
    (first last : Nat) : Nat :=
  encodedListSpace
    [stripFrontierContextPolynomialSpaceLimit
      periodicStrip first last] + 1

set_option maxHeartbeats 1600000 in
/-- The complete strip-header and frontier-index context decoder uses
workspace linear in its three encoded input fields. -/
theorem stripFrontierContextCost_le_polynomialSpaceBound
    (periodicStrip : PeriodicStrip)
    (first last : Nat) :
    stripFrontierContextCost periodicStrip first last ≤
      1000000000000000000000000000000000000000000000 *
        stripFrontierContextPolynomialSpaceUnit
          periodicStrip first last := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let limit := stripFrontierContextPolynomialSpaceLimit
    periodicStrip first last
  let unit := stripFrontierContextPolynomialSpaceUnit
    periodicStrip first last
  have stripBound : stripCode ≤ limit := by
    simp only [stripCode, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have firstBound : first ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have lastBound : last ≤ limit := by
    simp only [limit, stripFrontierContextPolynomialSpaceLimit]
    omega
  have widthStrip : periodicStrip.width ≤ stripCode := by
    simp only [stripCode, PeriodicStrip.encode_eq_pair]
    exact Nat.left_le_pair _ _
  have restStrip :
      Nat.pair periodicStrip.period motifCode ≤ stripCode := by
    simp only [stripCode, motifCode, PeriodicStrip.encode_eq_pair]
    exact Nat.right_le_pair _ _
  have periodStrip : periodicStrip.period ≤ stripCode :=
    (Nat.left_le_pair _ _).trans restStrip
  have motifStrip : motifCode ≤ stripCode :=
    (Nat.right_le_pair _ _).trans restStrip
  have widthBound := widthStrip.trans stripBound
  have periodBound := periodStrip.trans stripBound
  have motifBound := motifStrip.trans stripBound
  have firstQuotientBound : first / periodicStrip.period ≤ limit :=
    (Nat.div_le_self first periodicStrip.period).trans firstBound
  have firstRemainderBound : first % periodicStrip.period ≤ limit :=
    (Nat.mod_le first periodicStrip.period).trans firstBound
  have lastQuotientBound : last / periodicStrip.period ≤ limit :=
    (Nat.div_le_self last periodicStrip.period).trans lastBound
  have lastRemainderBound : last % periodicStrip.period ≤ limit :=
    (Nat.mod_le last periodicStrip.period).trans lastBound
  have pairLimitBound :
      frontierPairPolynomialSpaceLimit
          periodicStrip.period first last ≤ limit := by
    simp only [frontierPairPolynomialSpaceLimit, limit,
      stripFrontierContextPolynomialSpaceLimit]
    omega
  have stripBits := encodeNat_length_mono stripBound
  have firstBits := encodeNat_length_mono firstBound
  have lastBits := encodeNat_length_mono lastBound
  have widthBits := encodeNat_length_mono widthBound
  have periodBits := encodeNat_length_mono periodBound
  have motifBits := encodeNat_length_mono motifBound
  have firstQuotientBits := encodeNat_length_mono firstQuotientBound
  have firstRemainderBits := encodeNat_length_mono firstRemainderBound
  have lastQuotientBits := encodeNat_length_mono lastQuotientBound
  have lastRemainderBits := encodeNat_length_mono lastRemainderBound
  have pairLimitBits := encodeNat_length_mono pairLimitBound
  have stripSuccBits := encodeNat_length_mono
    (show stripCode + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit,
        stripCode]
      omega)
  have firstSuccBits := encodeNat_length_mono
    (show first + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastSuccBits := encodeNat_length_mono
    (show last + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have widthSuccBits := encodeNat_length_mono
    (show periodicStrip.width + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have periodSuccBits := encodeNat_length_mono
    (show periodicStrip.period + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have motifSuccBits := encodeNat_length_mono
    (show motifCode + 1 ≤ limit by
      simp only [limit, stripFrontierContextPolynomialSpaceLimit,
        motifCode]
      omega)
  have firstQuotientSuccBits := encodeNat_length_mono
    (show first / periodicStrip.period + 1 ≤ limit by
      have raw := Nat.div_le_self first periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have firstRemainderSuccBits := encodeNat_length_mono
    (show first % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le first periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastQuotientSuccBits := encodeNat_length_mono
    (show last / periodicStrip.period + 1 ≤ limit by
      have raw := Nat.div_le_self last periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have lastRemainderSuccBits := encodeNat_length_mono
    (show last % periodicStrip.period + 1 ≤ limit by
      have raw := Nat.mod_le last periodicStrip.period
      simp only [limit, stripFrontierContextPolynomialSpaceLimit]
      omega)
  have headerCost := periodicStripHeaderCost_le_linear periodicStrip
  have pairCost := frontierPairViewCost_le_linear
    periodicStrip.period first last
  have headerUnitLe :
      encodedListSpace [Encodable.encode periodicStrip] + 1 ≤ unit := by
    have bits := encodeNat_length_mono
      (show Encodable.encode periodicStrip ≤ limit by
        simpa only [stripCode] using stripBound)
    simpa [unit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil] using bits
  have pairUnitLe :
      frontierPairPolynomialSpaceUnit
          periodicStrip.period first last ≤ unit := by
    have bits := encodeNat_length_mono pairLimitBound
    simpa [unit, frontierPairPolynomialSpaceUnit,
      stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil] using bits
  have headerCostGlobal :
      periodicStripHeaderCost periodicStrip ≤
        100000000000 * unit :=
    headerCost.trans (Nat.mul_le_mul_left _ headerUnitLe)
  have pairCostGlobal :
      frontierPairViewCost periodicStrip.period first last ≤
        1000000000000000000000000000000 * unit :=
    pairCost.trans (Nat.mul_le_mul_left _ pairUnitLe)
  have stripBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [stripCode] using stripBits
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [motifCode] using motifBits
  have stripSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [stripCode] using stripSuccBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode periodicStrip.motif + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [motifCode] using motifSuccBits
  have stripPairBitsRaw :
      (Computability.encodeNat
        (Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)))).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [PeriodicStrip.encode_eq_pair] using stripBitsRaw
  have stripPairSuccBitsRaw :
      (Computability.encodeNat
        (Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)) + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa only [PeriodicStrip.encode_eq_pair] using stripSuccBitsRaw
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, limit, stripFrontierContextPolynomialSpaceUnit,
      encodedListSpace_cons, encodedListSpace_nil]
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  simp [stripFrontierContextCost,
    stripFrontierContextPeriodCost,
    stripFrontierContextMotifCost,
    stripFrontierContextFirstWordCost,
    stripFrontierContextFirstPhaseCost,
    stripFrontierContextLastCost,
    stripFrontierPairFieldCost,
    stripFrontierPairViewCost,
    stripFrontierPairArgumentsCost,
    stripFrontierPairArgumentsTailCost,
    stripFrontierHeaderFieldCost,
    stripFrontierHeaderAtCost,
    prependCost, getCost, dropCost, headCost, idCost,
    nilCost, tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    zeroBits]
  clear * - stripBits firstBits lastBits widthBits periodBits motifBits
    firstQuotientBits firstRemainderBits
    lastQuotientBits lastRemainderBits pairLimitBits
    stripSuccBits firstSuccBits lastSuccBits
    widthSuccBits periodSuccBits motifSuccBits
    firstQuotientSuccBits firstRemainderSuccBits
    lastQuotientSuccBits lastRemainderSuccBits
    headerCostGlobal pairCostGlobal unitEq
    stripBitsRaw motifBitsRaw stripSuccBitsRaw motifSuccBitsRaw
    stripPairBitsRaw stripPairSuccBitsRaw
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
