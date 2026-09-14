/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion

/-! # Finite search for overlapping periodic preplacements

Repeated descriptions of the same geometric tile are allowed. Distinct
footprints sharing a cell are detected in some finite collection of repeats.
-/

namespace LeanTrominoes.PeriodicTrominoPrefill
open Computability TrominoAssignment

set_option maxHeartbeats 2000000

theorem motif_primrec : Primrec PeriodicTrominoPrefill.motif :=
  (Primrec.fst.comp (Primrec.of_equiv : Primrec equivData)).of_eq fun _ => rfl

theorem period₁_primrec : Primrec PeriodicTrominoPrefill.period₁ :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv : Primrec equivData))).of_eq fun _ => rfl

theorem period₂_primrec : Primrec PeriodicTrominoPrefill.period₂ :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv : Primrec equivData))).of_eq fun _ => rfl

theorem placementCells_primrec (t : Tromino) : Primrec (placementCells t) := by
  unfold placementCells
  exact Primrec.list_map (Primrec.const (trominoCellList t))
    (cell_add_primrec.comp₂ (placement_offset_primrec.comp₂ Primrec₂.left)
      (squareSymmetry_act_primrec.comp₂ (placement_symmetry_primrec.comp₂ Primrec₂.left) Primrec₂.right))

theorem occupiedRegion_primrec (t : Tromino) : Primrec (fun input : PeriodicTrominoPrefill => input.occupiedRegion t) := by
  have cells : Primrec fun input : PeriodicTrominoPrefill => input.motif.flatMap (placementCells t) :=
    Primrec.list_flatMap motif_primrec ((placementCells_primrec t).comp Primrec.snd)
  exact ((Primrec.of_equiv_symm : Primrec PeriodicRegion.equivData.symm).comp
    (Primrec.pair cells (Primrec.pair period₁_primrec period₂_primrec))).of_eq fun _ => rfl

def repeatOffset (input : PeriodicTrominoPrefill) (index : Cell) : Cell :=
  Cell.add (Cell.scale index.1 input.period₁) (Cell.scale index.2 input.period₂)

def repeatedCells (t : Tromino) (input : PeriodicTrominoPrefill)
    (index : Cell) (p : Placement Unit) : List Cell :=
  (placementCells t p).map (Cell.add (repeatOffset input index))

theorem repeatedCells_toFinset (t : Tromino) (input : PeriodicTrominoPrefill)
    (index : Cell) (p : Placement Unit) :
    (repeatedCells t input index p).toFinset =
      (p.cells (fun _ => t.cells)).image (Cell.add (repeatOffset input index)) := by
  ext c
  simp [repeatedCells,mem_placementCells]

def boundedFootprints (t : Tromino) (input : PeriodicTrominoPrefill) (radius : Nat) : List (List Cell) :=
  (boxCellList radius).flatMap fun index => input.motif.map (repeatedCells t input index)

theorem bounded_prescribed (t : Tromino) (input : PeriodicTrominoPrefill) {r : Nat} {f : List Cell}
    (hf : f ∈ boundedFootprints t input r) : f.toFinset ∈ input.prescribed t := by
  obtain ⟨index,_,hf⟩ := List.mem_flatMap.mp hf
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hf
  exact ⟨p,hp,index.1,index.2,repeatedCells_toFinset t input index p⟩

theorem prescribed_bounded (t : Tromino) (input : PeriodicTrominoPrefill) {f : Finset Cell}
    (hf : f ∈ input.prescribed t) : ∃ r xs, xs ∈ boundedFootprints t input r ∧ xs.toFinset = f := by
  obtain ⟨p,hp,i,j,rfl⟩ := hf
  refine ⟨i.natAbs + j.natAbs,repeatedCells t input (i,j) p,?_,repeatedCells_toFinset t input (i,j) p⟩
  apply List.mem_flatMap.mpr
  refine ⟨(i,j),?_,List.mem_map.mpr ⟨p,hp,rfl⟩⟩
  rw [mem_boxCellList_iff]
  dsimp [LeanWang.InBox]
  omega

theorem boundedFootprints_mono (t : Tromino) (input : PeriodicTrominoPrefill) {r s : Nat} (hrs : r ≤ s) :
    ∀ f ∈ boundedFootprints t input r, f ∈ boundedFootprints t input s := by
  intro f hf
  obtain ⟨index,hi,hf⟩ := List.mem_flatMap.mp hf
  apply List.mem_flatMap.mpr
  refine ⟨index,?_,hf⟩
  rw [mem_boxCellList_iff] at hi ⊢
  dsimp [LeanWang.InBox] at hi ⊢
  omega

def Compatible (xs ys : List Cell) : Prop :=
  (∀ c ∈ xs, c ∉ ys) ∨ ((∀ c ∈ xs, c ∈ ys) ∧ ∀ c ∈ ys, c ∈ xs)

theorem compatible_iff (xs ys : List Cell) :
    Compatible xs ys ↔ ∀ c ∈ xs.toFinset, c ∈ ys.toFinset → xs.toFinset = ys.toFinset := by
  classical
  simp only [List.mem_toFinset]
  constructor
  · rintro (disjoint | ⟨sub,sup⟩) c hc hd
    · exact False.elim (disjoint c hc hd)
    · ext d
      simp only [List.mem_toFinset]
      exact ⟨sub d,sup d⟩
  · intro h
    by_cases disjoint : ∀ c ∈ xs, c ∉ ys
    · exact Or.inl disjoint
    · have shared : ∃ c : Cell, c ∈ xs ∧ c ∈ ys := by simpa using disjoint
      obtain ⟨c,hc,hd⟩ := shared
      have eq := h c hc hd
      exact Or.inr ⟨fun d hx => List.mem_toFinset.mp (eq ▸ List.mem_toFinset.mpr hx),
        fun d hy => List.mem_toFinset.mp (eq.symm ▸ List.mem_toFinset.mpr hy)⟩

def BoundedValid (t : Tromino) (input : PeriodicTrominoPrefill) (radius : Nat) : Prop :=
  ∀ xs ∈ boundedFootprints t input radius, ∀ ys ∈ boundedFootprints t input radius, Compatible xs ys

theorem partial_iff_bounded (t : Tromino) (input : PeriodicTrominoPrefill) :
    t.IsPartialTiling Set.univ (input.prescribed t) ↔ ∀ r, BoundedValid t input r := by
  constructor
  · intro valid r xs hx ys hy
    exact (compatible_iff xs ys).mpr (valid.nonoverlap _ (bounded_prescribed t input hx)
      _ (bounded_prescribed t input hy))
  · intro valid
    refine ⟨fun f hf => ⟨input.prescribed_legal t hf,fun _ _ => trivial⟩,?_⟩
    intro f hf g hg c hc hd
    obtain ⟨r,xs,hx,rfl⟩ := prescribed_bounded t input hf
    obtain ⟨s,ys,hy,rfl⟩ := prescribed_bounded t input hg
    exact (compatible_iff xs ys).mp (valid (max r s) xs
      (boundedFootprints_mono t input (Nat.le_max_left _ _) xs hx) ys
      (boundedFootprints_mono t input (Nat.le_max_right _ _) ys hy)) c hc hd

end LeanTrominoes.PeriodicTrominoPrefill
