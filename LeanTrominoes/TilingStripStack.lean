/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TilingTranslation
import LeanTrominoes.BumpyTrominoObstruction

/-! # Repeating a positive-height strip tiling throughout the plane -/

namespace LeanTrominoes

/-- The full horizontal lattice strip of the given height. -/
def horizontalStrip (height : Nat) : Set Cell := {c | 0 ≤ c.2 ∧ c.2 < height}

theorem plane_tileable_of_strip {ι : Type*} (tiles : ι → Polyomino)
    {height : Nat} (positive : 0 < height)
    (tileable : Tileable tiles (horizontalStrip height)) : Tileable tiles Set.univ := by
  obtain ⟨placements,band⟩ := tileable
  have pos : (0 : Int) < height := by omega
  have nonzero : (height : Int) ≠ 0 := by omega
  let stacked : Set (Placement ι) :=
    {p | ∃ k : Int, ∃ q ∈ placements, p = q.shift (0,(height : Int)*k)}
  refine ⟨stacked,?_,?_⟩
  · intro _ _ _ _
    trivial
  · intro c _
    let k : Int := c.2 / height
    let bandCell : Cell := (c.1,c.2 % height)
    have inside : bandCell ∈ horizontalStrip height :=
      ⟨Int.emod_nonneg _ nonzero,Int.emod_lt_of_pos _ pos⟩
    have translated : Cell.add (0,(height : Int)*k) bandCell = c := by
      apply Prod.ext
      · simp [bandCell,Cell.add]
      · simpa [bandCell,k,Cell.add,Int.add_comm] using Int.emod_add_mul_ediv c.2 height
    obtain ⟨p,⟨hp,hc⟩,unique⟩ := band.uniqueCover bandCell inside
    refine ⟨p.shift (0,(height : Int)*k),⟨⟨k,p,hp,rfl⟩,?_⟩,?_⟩
    · rw [← translated,Placement.mem_shift_cells]
      exact hc
    · rintro _ ⟨⟨l,q,hq,rfl⟩,hqc⟩
      let other : Cell := (c.1,c.2-(height : Int)*l)
      have moved : Cell.add (0,(height : Int)*l) other = c := by
        simp [other,Cell.add]
      have source : other ∈ q.cells tiles := by
        apply (Placement.mem_shift_cells tiles (0,(height : Int)*l) q other).mp
        rwa [moved]
      have bounds := band.tilesInside q hq other source
      have zero : other.2 / height = 0 := Int.ediv_eq_zero_of_lt bounds.1 bounds.2
      have same : l = k := by
        calc
          l = other.2 / height + l := by rw [zero]; omega
          _ = (other.2 + (height : Int)*l) / height := (Int.add_mul_ediv_left _ _ nonzero).symm
          _ = k := by simp [other,k]
      subst l
      have sameCell : other = bandCell := by
        apply Cell.add_left_injective (0,(height : Int)*k)
        exact moved.trans translated.symm
      exact congrArg (Placement.shift (0,(height : Int)*k))
        (unique q ⟨hq,by rwa [← sameCell]⟩)

/-- The fixed 15-omino cannot tile any nonempty full strip. -/
theorem PlusRefinement.bumpy_not_tileable_strip {height : Nat} (positive : 0 < height) :
    ¬ TileableBy PlusRefinement.bumpy (horizontalStrip height) := by
  intro tiled
  exact PlusRefinement.bumpy_not_tileable_plane (plane_tileable_of_strip _ positive tiled)

end LeanTrominoes
