import LeanTrominoes.PartrecPeriodicStripDecode
import LeanTrominoes.PartrecUnpairSpace
import LeanTrominoes.PartrecBinaryLengthSpace

/-!
# Evaluator-space certificate for periodic-strip header decoding

The certificate follows the two standard unpairing operations in the strip
encoding and preserves the decoded width with the direct list `prepend`
combinator.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

def periodicStripHeaderTailCost (width rest : Nat) : Nat :=
  unpairCost rest + getCost 1 [width, rest]

theorem periodicStripHeaderTail
    (width rest : Nat) :
    EvaluatorCodeFits
      (Code.unpairCode.comp (Code.get 1))
      [width, rest] [rest.unpair.1, rest.unpair.2]
      (periodicStripHeaderTailCost width rest) := by
  simpa [periodicStripHeaderTailCost] using
    comp (unpair rest) (get 1 [width, rest])

def periodicStripHeaderRestCost
    (width period motifCode : Nat) : Nat :=
  prependCost
    [width, Nat.pair period motifCode] [width]
    [period, motifCode]
    (getCost 0 [width, Nat.pair period motifCode])
    (periodicStripHeaderTailCost width
      (Nat.pair period motifCode))

theorem periodicStripHeaderRest
    (width period motifCode : Nat) :
    EvaluatorCodeFits Code.periodicStripHeaderRestCode
      [width, Nat.pair period motifCode]
      [width, period, motifCode]
      (periodicStripHeaderRestCost width period motifCode) := by
  simpa [Code.periodicStripHeaderRestCode,
    periodicStripHeaderRestCost, prependCost] using
    prepend
      (get 0 [width, Nat.pair period motifCode])
      (periodicStripHeaderTail width
        (Nat.pair period motifCode))

def periodicStripHeaderCost
    (periodicStrip : PeriodicStrip) : Nat :=
  periodicStripHeaderRestCost periodicStrip.width
      periodicStrip.period
      (Encodable.encode periodicStrip.motif) +
    unpairCost (Encodable.encode periodicStrip)

theorem periodicStripHeader
    (periodicStrip : PeriodicStrip) :
    EvaluatorCodeFits Code.periodicStripHeaderCode
      [Encodable.encode periodicStrip]
      [periodicStrip.width, periodicStrip.period,
        Encodable.encode periodicStrip.motif]
      (periodicStripHeaderCost periodicStrip) := by
  have outer :
      EvaluatorCodeFits Code.unpairCode
        [Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif))]
        [periodicStrip.width,
          Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)]
        (unpairCost
          (Nat.pair periodicStrip.width
            (Nat.pair periodicStrip.period
              (Encodable.encode periodicStrip.motif)))) := by
    simpa using
      unpair
        (Nat.pair periodicStrip.width
          (Nat.pair periodicStrip.period
            (Encodable.encode periodicStrip.motif)))
  simpa [Code.periodicStripHeaderCode,
    periodicStripHeaderCost,
    PeriodicStrip.encode_eq_pair] using
    comp
      (periodicStripHeaderRest periodicStrip.width
        periodicStrip.period
        (Encodable.encode periodicStrip.motif))
      outer

set_option maxHeartbeats 800000 in
theorem periodicStripHeaderCost_le_linear
    (periodicStrip : PeriodicStrip) :
    periodicStripHeaderCost periodicStrip ≤
      100000000000 *
        (encodedListSpace
          [Encodable.encode periodicStrip] + 1) := by
  let stripCode := Encodable.encode periodicStrip
  let motifCode := Encodable.encode periodicStrip.motif
  let restCode :=
    Nat.pair periodicStrip.period motifCode
  have stripEq :
      stripCode =
        Nat.pair periodicStrip.width restCode := by
    simp [stripCode, restCode, motifCode,
      PeriodicStrip.encode_eq_pair]
  have widthBound :
      periodicStrip.width ≤ stripCode := by
    rw [stripEq]
    exact Nat.left_le_pair _ _
  have restBound : restCode ≤ stripCode := by
    rw [stripEq]
    exact Nat.right_le_pair _ _
  have periodBound :
      periodicStrip.period ≤ stripCode :=
    (Nat.left_le_pair _ _).trans restBound
  have motifBound : motifCode ≤ stripCode :=
    (Nat.right_le_pair _ _).trans restBound
  have widthBits := encodeNat_length_mono widthBound
  have restBits := encodeNat_length_mono restBound
  have periodBits := encodeNat_length_mono periodBound
  have motifBits := encodeNat_length_mono motifBound
  have widthSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.width + 1 ≤ 2 * stripCode + 4
        by omega)
  have restSuccBits :=
    encodeNat_length_mono
      (show restCode + 1 ≤ 2 * stripCode + 4 by omega)
  have periodSuccBits :=
    encodeNat_length_mono
      (show periodicStrip.period + 1 ≤
          2 * stripCode + 4 by omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ 2 * stripCode + 4 by omega)
  have scaledBits :=
    encodeNat_eight_mul_add_four_length_le stripCode
  have localScaledBits :=
    encodeNat_length_mono
      (show 2 * stripCode + 4 ≤ 8 * stripCode + 4 by omega)
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have outerUnpair := unpairCost_le_linear stripCode
  have innerUnpair := unpairCost_le_linear restCode
  have innerLimit :
      encodedListSpace [2 * restCode + 4] ≤
        encodedListSpace [2 * stripCode + 4] := by
    simpa only [encodedListSpace_cons,
      encodedListSpace_nil, Nat.add_le_add_iff_right] using
      encodeNat_length_mono
        (show 2 * restCode + 4 ≤ 2 * stripCode + 4 by omega)
  simp [periodicStripHeaderCost,
    periodicStripHeaderRestCost,
    periodicStripHeaderTailCost, prependCost,
    getCost, dropCost, headCost, idCost, nilCost,
    tailCost, zeroPrimeCost, succCost,
    encodedListSpace_cons, encodedListSpace_nil,
    stripCode, motifCode, restCode, zeroBits] at *
  omega

end EvaluatorCodeFits

end PartrecToTM2
end Turing
