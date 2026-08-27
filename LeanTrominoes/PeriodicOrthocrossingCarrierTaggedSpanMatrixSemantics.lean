/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierTaggedSpanRouteDirectionDecoderSemantics

/-! # Decoding a retained carrier-span matrix -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- A row-major tagged span matrix decodes to the corresponding row-major
canonical route blocks whenever every retained span has the geometric size
required by the lens templates. -/
theorem decodedTaggedSpanMatrix_eq_canonical
    (entries : List (CarrierNodeRankDatum × Nat))
    (large : ∀ first ∈ entries.zipIdx, ∀ second ∈ entries.zipIdx,
      retainedPredicate first second = true →
        6 < (second.1.1.orderCoordinate -
          first.1.1.orderCoordinate).toNat) :
    ((entries.zipIdx.flatMap fun first =>
      entries.zipIdx.map fun second =>
        if retainedPredicate first second then
          let span := (second.1.1.orderCoordinate -
            first.1.1.orderCoordinate).toNat
          span + span + 2 +
            BooleanListUnaryFields.bitNat first.1.1.horizontal
        else 0).flatMap fun code =>
          CarrierTaggedSpanRouteDirections.blockOutput
            (UnaryFieldEncoderMachine.unaryField code)) =
      entries.zipIdx.flatMap fun first =>
        entries.zipIdx.flatMap fun second =>
          if retainedPredicate first second then
            CarrierSpanRouteDirections.canonicalBlock
              first.1.1.horizontal
              (second.1.1.orderCoordinate -
                first.1.1.orderCoordinate).toNat
          else [] := by
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro first firstMember
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro second secondMember
  cases retained : retainedPredicate first second with
  | false =>
      simp [CarrierTaggedSpanRouteDirections.blockOutput_unaryField_zero]
  | true =>
      have spanLarge := large first firstMember second secondMember retained
      let span := (second.1.1.orderCoordinate -
        first.1.1.orderCoordinate).toNat
      cases horizontal : first.1.1.horizontal with
      | false =>
          simp only [↓reduceIte]
          simpa [span, horizontal, BooleanListUnaryFields.bitNat,
            two_mul, Nat.add_assoc] using
            CarrierTaggedSpanRouteDirections.blockOutput_unaryField_even
              span spanLarge
      | true =>
          simp only [↓reduceIte]
          simpa [span, horizontal, BooleanListUnaryFields.bitNat,
            two_mul, Nat.add_assoc] using
            CarrierTaggedSpanRouteDirections.blockOutput_unaryField_odd
              span spanLarge

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
