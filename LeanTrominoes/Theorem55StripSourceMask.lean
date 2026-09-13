/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripSourcePreparation
import LeanTrominoes.Theorem55SourceMask

/-! # The exact admissible finite mask of a prepared strip source -/

namespace LeanTrominoes.Theorem55StripSource

noncomputable def holes (source : PeriodicStrip) : Polyomino :=
  KeyedPeriodicComplement.mask (3 * period source) (PlusRefinement.region (region source))

theorem refined_translate (source : PeriodicStrip) (i : Int) (c : Cell) :
    Cell.add (((3 * period source : Nat) : Int)*i,0) c ∈ PlusRefinement.region (region source) ↔
      c ∈ PlusRefinement.region (region source) := by
  have shifted_eq : {p | Cell.add ((period source : Int)*i,0) p ∈ region source} = region source :=
    Set.ext (translate_region source i)
  have h := PlusRefinement.region_translate_iff (region source) ((period source : Int)*i,0) c
  rw [shifted_eq] at h
  simpa [Cell.scale,Nat.cast_mul,mul_assoc] using h

theorem refined_inside (source : PeriodicStrip) (positive : 0 < source.period) :
    PlusRefinement.region (region source) ⊆ horizontalStrip (3 * period source) := by
  rintro _ ⟨parent,hp,u,hu,rfl⟩
  have bound := region_bounds source positive hp
  simp only [PlusRefinement.cross,Finset.mem_insert,Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    dsimp [horizontalStrip,PlusRefinement.pixel,Cell.add,Cell.scale] <;> omega

theorem holes_carrier (source : PeriodicStrip) (positive : 0 < source.period) :
    KeyedStripComplement.holesRegion (3 * period source) (holes source) =
      PlusRefinement.region (region source) := by
  have large := period_large source positive
  let n := 3 * period source
  have hn : 0 < n := by dsimp [n]; omega
  have periodic (c : Cell) : KeyedStripComplement.residue n c ∈ PlusRefinement.region (region source) ↔
      c ∈ PlusRefinement.region (region source) := by
    have h := refined_translate source (c.1 / n) (KeyedStripComplement.residue n c)
    have eq : Cell.add ((n : Int)*(c.1/n),0) (KeyedStripComplement.residue n c) = c := by
      apply Prod.ext
      · have h := Int.emod_add_mul_ediv c.1 n
        dsimp [Cell.add,KeyedStripComplement.residue]
        omega
      · simp [Cell.add,KeyedStripComplement.residue]
    change _ ∈ PlusRefinement.region (region source) ↔ _ at h
    rw [show Cell.add (((3 * period source : Nat) : Int)*(c.1/n),0) (KeyedStripComplement.residue n c) = c from eq] at h
    exact h.symm
  ext c
  change (c ∈ horizontalStrip n ∧ KeyedStripComplement.residue n c ∈ KeyedPeriodicComplement.mask n _) ↔ _
  rw [KeyedPeriodicComplement.mem_mask,periodic]
  constructor
  · exact fun h => h.2.2
  · intro h
    have inside := refined_inside source positive h
    exact ⟨inside,KeyedStripComplement.residue_mem_square hn inside,h⟩

theorem blank_corners (source : PeriodicStrip) (positive : 0 < source.period) (c : Cell)
    (hx : c.1 % (period source : Int) ≤ 6 ∨ (period source : Int) - 6 ≤ c.1 % (period source : Int))
    (hy : c.2 % (period source : Int) ≤ 6 ∨ (period source : Int) - 6 ≤ c.2 % (period source : Int)) :
    c ∉ region source := by
  intro hc
  have large := period_large source positive
  have bounds := region_bounds source positive hc
  have eq : c.2 % (period source : Int) = c.2 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [eq] at hy
  rcases hc with hs | hp
  · have hs := shifted_bounds source hs
    omega
  · have hp := hp.1
    omega

theorem holes_admissible (source : PeriodicStrip) (positive : 0 < source.period) :
    KeyedPeriodicComplement.AdmissibleHoles (3 * period source) (holes source) :=
  Theorem55Source.refined_mask_admissible _ _ (blank_corners source positive)

end LeanTrominoes.Theorem55StripSource
