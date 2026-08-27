/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanNumericSemantics

/-! # Decoding a packed retained carrier-span matrix to Figure 9 records -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

private def matrixOf {Value Output : Type*} (values : List Value)
    (function : Value → Value → Output) : List Output :=
  values.flatMap fun first => values.map (function first)

/-- A row-major packed span matrix decodes to the exact carrier tail-record
blocks whenever every selected span satisfies the lens clearance bound. -/
theorem decodedPackedSpanMatrix_eq_canonical
    (entries : List (CarrierNodeRankDatum × Nat))
    (large : ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat) :
    ((matrixOf entries.zipIdx fun first second =>
      if retainedPredicate first second then
        let span := (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat
        4 * span + 4 +
          2 * BooleanListUnaryFields.bitNat first.1.1.horizontal +
            BooleanListUnaryFields.bitNat
              (first.1.1.pairNextSlice second.1.1)
      else 0).flatMap fun code =>
        CarrierPackedSpanRouteTailRecords.blockOutput
          (UnaryFieldEncoderMachine.unaryField code)) =
      entries.zipIdx.flatMap fun first =>
        entries.zipIdx.flatMap fun second =>
          if retainedPredicate first second then
            PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.carrierLensRouteTailRecordBlock
              first.1.1.horizontal
              (first.1.1.pairNextSlice second.1.1)
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  unfold matrixOf
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro second secondMember
  cases retained : retainedPredicate first second with
  | false =>
      simp [retained,
        CarrierPackedSpanRouteTailRecords.blockOutput_unaryField_zero]
  | true =>
      have spanLarge := large first firstMember second secondMember retained
      simpa [retained] using
        CarrierPackedSpanRouteTailRecords.blockOutput_unaryField_packed
          first.1.1.horizontal
          (first.1.1.pairNextSlice second.1.1)
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          spanLarge

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
