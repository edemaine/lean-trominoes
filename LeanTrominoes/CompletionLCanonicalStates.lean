/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLConnectorConsistency

/-! # Canonical local states from a single global completion -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def outsideAt (completed : Set (Finset Cell)) (location : Cell) (entry : Atom × Cell) : Finset Cell :=
  (Tromino.outsideCells completed (regionAt location entry)).image
    (Cell.add (Cell.sub (0,0) (atomOffset location entry)))

theorem canonical_local_completion (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.L.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) :
    Tromino.outsideCells completed (regionAt location entry) ⊆
      entry.1.boundary.image (Cell.add (atomOffset location entry)) ∧
    Tromino.L.Completable
      (regionAt location entry \ Tromino.outsideCells completed (regionAt location entry) : Finset Cell)
      (atomPrescribed location entry) := by
  apply h.local_completion_canonical (regionAt location entry)
    (entry.1.boundary.image (Cell.add (atomOffset location entry))) (atomPrescribed location entry)
  · exact Set.subset_univ _
  · rintro f ⟨p,hp,rfl⟩
    exact retained (atom_prescribed palette location he hp)
  · rintro f ⟨p,hp,rfl⟩
    exact shifted_motif_inside location entry hp
  · intro f hf c hfc hc
    obtain ⟨inside,notBoundary⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp inside
    apply completed_tile_contained palette location he h retained hf _ hfc
    exact Finset.mem_sdiff.mpr ⟨hd,fun hb => notBoundary (Finset.mem_image.mpr ⟨d,hb,rfl⟩)⟩

/-- These local states are all taken from the same completed tiling, and
therefore also satisfy the connector-complement theorem. -/
theorem canonical_local_state (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.L.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) :
    outsideAt completed location entry ⊆ entry.1.boundary ∧
      entry.1.pattern.Completable (outsideAt completed location entry) := by
  obtain ⟨subset,localCompletion⟩ := canonical_local_completion palette location he h retained
  let outside := Tromino.outsideCells completed (regionAt location entry)
  let v := atomOffset location entry
  let inv := Cell.add (Cell.sub (0,0) v)
  have translated := localCompletion.translate (Cell.sub (0,0) v)
  have regionEq : inv '' (↑(entry.1.pattern.region.image (Cell.add v) \ outside) : Set Cell) =
      (↑(entry.1.pattern.region \ outside.image inv) : Set Cell) := by
    rw [← Finset.coe_image,Finset.image_sdiff _ _ (Cell.add_left_injective _)]
    dsimp [inv]
    rw [Cell.image_translate_cancel]
  change Tromino.L.Completable
    (inv '' (↑(entry.1.pattern.region.image (Cell.add v) \ outside) : Set Cell))
    ((fun f => f.image inv) '' atomPrescribed location entry) at translated
  rw [regionEq] at translated
  have prescribedEq := atom_prescribed_recenter location entry
  change ((fun f => f.image inv) '' atomPrescribed location entry) = _ at prescribedEq
  rw [prescribedEq] at translated
  constructor
  · have bound := Finset.image_subset_image subset (f := inv)
    dsimp [inv,v] at bound
    rwa [Cell.image_translate_cancel] at bound
  · unfold Pattern.Completable Pattern.target
    rw [Atom.kind_eq]
    exact translated

/-- Local and global coordinates describe the same canonical outside cells. -/
theorem mem_outsideAt (completed : Set (Finset Cell)) (location : Cell) (entry : Atom × Cell)
    (c : Cell) : c ∈ outsideAt completed location entry ↔
      Cell.add (atomOffset location entry) c ∈ Tromino.outsideCells completed (regionAt location entry) := by
  constructor
  · intro hc
    obtain ⟨d,hd,eq⟩ := Finset.mem_image.mp hc
    have cancel : Cell.add (atomOffset location entry) c = d := by
      rw [← eq]
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega
    rwa [cancel]
  · intro hc
    exact Finset.mem_image.mpr ⟨Cell.add (atomOffset location entry) c,hc,by
      apply Prod.ext <;> dsimp [Cell.add,Cell.sub] <;> omega⟩

end LeanTrominoes.CompletionPattern.LBricks
