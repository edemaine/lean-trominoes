/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalColumnSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanNumericSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Decoding a packed carrier-span matrix to terminal radial lengths -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open CarrierPackedSpanTerminalColumns

/-- A row-major packed span matrix decodes to the exact carrier terminal
radial-length fields whenever every selected span clears the lens. -/
theorem decodedPackedSpanRadialMatrix_eq_canonical
    (entries : List (CarrierNodeRankDatum × Nat))
    (large : ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat) :
    List.flatMap
        (fun code => radialLengthBlockOutput
          (UnaryFieldEncoderMachine.unaryField code))
        (entries.zipIdx.flatMap fun first =>
          entries.zipIdx.map fun second =>
            if retainedPredicate first second then
              let span := (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
              4 * span + 4 +
                2 * BooleanListUnaryFields.bitNat first.1.1.horizontal +
                  BooleanListUnaryFields.bitNat
                    (first.1.1.pairNextSlice second.1.1)
            else 0) =
      UnaryFieldEncoderMachine.unaryFields
        (List.flatten
          (List.map terminalDataRadialLengths
            (entries.zipIdx.flatMap fun first =>
              entries.zipIdx.map fun second =>
                if retainedPredicate first second then
                  carrierLensRouteTerminalDataBlock first.1.1.horizontal
                    (second.1.1.orderCoordinate -
                      first.1.1.orderCoordinate).toNat
                else []))) := by
  rw [UnaryFieldEncoderMachine.unaryFields_flatten,
    List.flatMap_map]
  rw [List.flatMap_assoc, List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map, List.flatMap_map]
  apply List.flatMap_congr
  intro second secondMember
  cases retained : retainedPredicate first second with
  | false =>
      simp [terminalDataRadialLengths,
        CarrierPackedSpanTerminalColumns.radialLengthBlockOutput_unaryField_zero]
  | true =>
      simpa [retained] using
        CarrierPackedSpanTerminalColumns.radialLengthBlockOutput_unaryField_packed
          first.1.1.horizontal
          (first.1.1.pairNextSlice second.1.1)
          (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          (large first firstMember second secondMember retained)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
