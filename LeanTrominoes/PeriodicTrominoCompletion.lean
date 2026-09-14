/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrominoCompletion
import LeanTrominoes.ComputableSearch
import LeanTrominoes.TilingTranslation

/-! # Finite presentations of periodic preplaced trominoes

Only the prefill is required to be periodic. A completing tiling may be
aperiodic. Overlapping or out-of-region preplacements are rejected.
-/

namespace LeanTrominoes

theorem Tromino.IsFootprint.translate {t : Tromino} {f : Finset Cell}
    (h : t.IsFootprint f) (v : Cell) : t.IsFootprint (f.image (Cell.add v)) := by
  obtain ⟨p,rfl⟩ := h
  refine ⟨p.shift v,?_⟩
  simp [Placement.cells,Placement.shift,Finset.image_image,Function.comp_def,Cell.add,Int.add_assoc]

/-- A finite motif of preplaced tiles and two arbitrary period vectors. -/
structure PeriodicTrominoPrefill where
  motif : List (Placement Unit)
  period₁ : Cell
  period₂ : Cell

namespace PeriodicTrominoPrefill

/-- Standard computability encoding; the strip complexity encoding is separate. -/
def equivData : PeriodicTrominoPrefill ≃ List (Placement Unit) × Cell × Cell where
  toFun input := (input.motif,input.period₁,input.period₂)
  invFun data := ⟨data.1,data.2.1,data.2.2⟩
  left_inv input := by cases input; rfl
  right_inv data := by rcases data with ⟨m,p,q⟩; rfl

noncomputable instance : Primcodable PeriodicTrominoPrefill := Primcodable.ofEquiv _ equivData

/-- Repeated footprints identify different descriptions of the same tile. -/
def prescribed (input : PeriodicTrominoPrefill) (t : Tromino) : Set (Finset Cell) :=
  {f | ∃ p ∈ input.motif, ∃ i j : Int,
    f = (p.cells (fun _ => t.cells)).image
      (Cell.add (Cell.add (Cell.scale i input.period₁) (Cell.scale j input.period₂)))}

/-- An ordered, executable list of a preplacement's three cells. -/
def placementCells (t : Tromino) (p : Placement Unit) : List Cell :=
  (TrominoAssignment.trominoCellList t).map fun c => Cell.add p.offset (p.symmetry.act c)

theorem mem_placementCells (t : Tromino) (p : Placement Unit) (c : Cell) :
    c ∈ placementCells t p ↔ c ∈ p.cells (fun _ => t.cells) := by
  simp only [placementCells,List.mem_map,TrominoAssignment.mem_trominoCellList_iff,
    Placement.mem_cells_iff]

/-- The occupied cells, presented as an ordinary periodic region. -/
def occupiedRegion (input : PeriodicTrominoPrefill) (t : Tromino) : PeriodicRegion where
  motif := input.motif.flatMap (placementCells t)
  period₁ := input.period₁
  period₂ := input.period₂

theorem prescribed_legal (input : PeriodicTrominoPrefill) (t : Tromino)
    {f : Finset Cell} (hf : f ∈ input.prescribed t) : t.IsFootprint f := by
  obtain ⟨p,_,i,j,rfl⟩ := hf
  exact (Tromino.IsFootprint.translate ⟨p,rfl⟩ _)

theorem occupied_eq_carrier (input : PeriodicTrominoPrefill) (t : Tromino) :
    Tromino.occupied (input.prescribed t) = (input.occupiedRegion t).carrier := by
  ext c
  constructor
  · rintro ⟨f,⟨p,hp,i,j,rfl⟩,hc⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    refine ⟨q,List.mem_flatMap.mpr ⟨p,hp,(mem_placementCells t p q).mpr hq⟩,i,j,?_⟩
    apply Prod.ext <;> dsimp [occupiedRegion,Cell.add,Cell.scale] <;> omega
  · rintro ⟨q,hq,i,j,rfl⟩
    obtain ⟨p,hp,hq⟩ := List.mem_flatMap.mp hq
    refine ⟨_,⟨p,hp,i,j,rfl⟩,Finset.mem_image.mpr ⟨q,(mem_placementCells t p q).mp hq,?_⟩⟩
    apply Prod.ext <;> dsimp [occupiedRegion,Cell.add,Cell.scale] <;> omega

/-- Full-rank periodic prefill admitting an arbitrary full-plane completion. -/
def planeProblem (t : Tromino) (input : PeriodicTrominoPrefill) : Prop :=
  (input.occupiedRegion t).IsFullRank ∧ t.Completable Set.univ (input.prescribed t)

theorem planeProblem_iff (t : Tromino) (input : PeriodicTrominoPrefill) :
    planeProblem t input ↔ (input.occupiedRegion t).IsFullRank ∧
      t.IsPartialTiling Set.univ (input.prescribed t) ∧
      t.Tileable (input.occupiedRegion t).carrierᶜ := by
  rw [planeProblem,Tromino.completable_iff,occupied_eq_carrier,← Set.compl_eq_univ_sdiff]

end PeriodicTrominoPrefill

/-- A finite motif repeated horizontally in a bounded-height strip. -/
structure PeriodicStripTrominoPrefill where
  motif : List (Placement Unit)
  height : Nat
  period : Nat

namespace PeriodicStripTrominoPrefill

def periodic (input : PeriodicStripTrominoPrefill) : PeriodicTrominoPrefill :=
  ⟨input.motif,((input.period : Int),0),(0,0)⟩

def region (input : PeriodicStripTrominoPrefill) : Set Cell :=
  {c | 0 ≤ c.2 ∧ c.2 < (input.height : Int)}

/-- The prefill must fit the strip; it is never clipped at the boundary. -/
def problem (t : Tromino) (input : PeriodicStripTrominoPrefill) : Prop :=
  0 < input.height ∧ 0 < input.period ∧
    t.Completable input.region (input.periodic.prescribed t)

theorem problem_iff (t : Tromino) (input : PeriodicStripTrominoPrefill) :
    problem t input ↔ 0 < input.height ∧ 0 < input.period ∧
      t.IsPartialTiling input.region (input.periodic.prescribed t) ∧
      t.Tileable (input.region \ (input.periodic.occupiedRegion t).carrier) := by
  rw [problem,Tromino.completable_iff,PeriodicTrominoPrefill.occupied_eq_carrier]

end PeriodicStripTrominoPrefill
end LeanTrominoes
