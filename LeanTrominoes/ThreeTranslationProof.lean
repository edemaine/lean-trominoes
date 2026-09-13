/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.ThreeTranslationStatements
import LeanTrominoes.ThreeTranslationHardness
import LeanTrominoes.ThreeTranslationPlaneUpperBound
import LeanTrominoes.ThreeTranslationStripMembership
import LeanTrominoes.PolyominoConnectivitySymmetry
import LeanTrominoes.BumpyTrominoConnected

/-! # Corollary 5.6: three translation-only polyominoes -/

namespace LeanTrominoes.ThreeTranslationPolyominoes

theorem fixed_card (vertical : Bool) : (fixed vertical).card = 15 := by
  cases vertical with
  | false => exact PlusRefinement.bumpy_card
  | true =>
    change (PlusRefinement.bumpy.image SquareSymmetry.rotate90.act).card = 15
    rw [Finset.card_image_of_injective _ SquareSymmetry.rotate90.act_injective]
    exact PlusRefinement.bumpy_card

theorem fixed_connected (vertical : Bool) : Polyomino.IsConnected (fixed vertical) := by
  cases vertical with
  | false => exact PlusRefinement.bumpy_connected
  | true => exact PlusRefinement.bumpy_connected.symmetry .rotate90

theorem fixed_distinct : fixed false ≠ fixed true := by decide

/-- Plane tiling by the two fixed connected tiles and input disconnected Q is co-r.e.-complete. -/
theorem planeProved : planeStatement := ⟨plane_coRE,plane_coREHard⟩

/-- Strip tiling by translations of the three tiles is PSPACE-complete under the original unary encoding. -/
theorem stripProved : stripStatement := ⟨strip_inPSPACE,strip_PSPACEHard⟩

/-- Both assertions of Corollary 5.6. -/
theorem proved : statement := ⟨planeProved,stripProved⟩

end LeanTrominoes.ThreeTranslationPolyominoes
