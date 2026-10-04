/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionICanonicalStates
import LeanTrominoes.CompletionAvoidanceTranslation

/-! # Local soundness from finitely many retained barriers -/
noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
open IBricks
set_option maxHeartbeats 2000000

/-- Only tiles covering this atom's finite barrier need to be retained. -/
def BarrierRetained (palette : Cell → Fin 24) (completed : Set (Finset Cell))
    (location : Cell) (entry : Atom × Cell) : Prop :=
  ∀ c ∈ entry.1.fixed, ∃ f ∈ globalPrescribed palette,
    f ∈ completed ∧ Cell.add (atomOffset location entry) c ∈ f

private theorem disjoint_barrier {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed)
    {location : Cell} {entry : Atom × Cell}
    (retained : BarrierRetained palette completed location entry)
    {f : Finset Cell} (hf : f ∈ completed) (absent : f ∉ globalPrescribed palette) :
    Disjoint f ((entry.1.fixed).image (Cell.add (atomOffset location entry))) := by
  apply Finset.disjoint_left.mpr
  intro d hd member
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp member
  obtain ⟨g,hg,completedG,covers⟩ := retained c hc
  have eq := (h.partial (Set.Subset.refl completed)).nonoverlap
    f hf g completedG _ hd covers
  exact absent (eq ▸ hg)

/-- A completion retaining the local finite barriers cannot cross the atom
interior, even when distant brick preplacements are absent. -/
theorem completed_tile_contained (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : BarrierRetained palette completed location entry)
    {f : Finset Cell} (hf : f ∈ completed) {c : Cell}
    (hc : c ∈ entry.1.pattern.region \ entry.1.boundary)
    (covers : Cell.add (atomOffset location entry) c ∈ f) :
    f ⊆ entry.1.pattern.region.image (Cell.add (atomOffset location entry)) := by
  by_cases prescribed : f ∈ globalPrescribed palette
  · obtain ⟨p,hp,rfl⟩ := prescribed_core_owner palette location he prescribed hc covers
    exact shifted_motif_inside location entry hp
  · have avoids := disjoint_barrier h retained hf prescribed
    have notFixed : c ∉ entry.1.fixed := by
      intro fixed
      apply Finset.disjoint_left.mp avoids covers
      exact Finset.mem_image.mpr ⟨c,fixed,rfl⟩
    have core : c ∈ entry.1.core :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,notFixed⟩,
        (Finset.mem_sdiff.mp hc).2⟩
    apply CompletionBarrier.containment_of_guarded_at h (atomOffset location entry)
      (fun _ _ => trivial) ?_ entry.1.guarded hf avoids covers core
    intro g hg d hd hgd
    apply disjoint_barrier h retained hg
    intro member
    exact atom_available_unfilled palette location he hd ⟨g,member,hgd⟩

/-- Canonical states require this atom's motif and finite barriers only. -/
theorem canonical_local_completion (palette : Cell → Fin 24) (location : Cell)
    {entry : Atom × Cell} (he : entry ∈ layout (palette location))
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : BarrierRetained palette completed location entry)
    (own : atomPrescribed location entry ⊆ completed) :
    Tromino.outsideCells completed (regionAt location entry) ⊆
      entry.1.boundary.image (Cell.add (atomOffset location entry)) ∧
    Tromino.I.Completable
      (regionAt location entry \ Tromino.outsideCells completed (regionAt location entry) : Finset Cell)
      (atomPrescribed location entry) := by
  apply h.local_completion_canonical (regionAt location entry)
    (entry.1.boundary.image (Cell.add (atomOffset location entry))) (atomPrescribed location entry)
  · exact Set.subset_univ _
  · exact own
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
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : BarrierRetained palette completed location entry)
    (own : atomPrescribed location entry ⊆ completed) :
    outsideAt completed location entry ⊆ entry.1.boundary ∧
      entry.1.pattern.Completable (outsideAt completed location entry) := by
  obtain ⟨subset,localCompletion⟩ := canonical_local_completion palette location he h retained own
  let outside := Tromino.outsideCells completed (regionAt location entry)
  let v := atomOffset location entry
  let inv := Cell.add (Cell.sub (0,0) v)
  have translated := localCompletion.translate (Cell.sub (0,0) v)
  have regionEq : inv '' (↑(entry.1.pattern.region.image (Cell.add v) \ outside) : Set Cell) =
      (↑(entry.1.pattern.region \ outside.image inv) : Set Cell) := by
    rw [← Finset.coe_image,Finset.image_sdiff _ _ (Cell.add_left_injective _)]
    dsimp [inv]
    rw [Cell.image_translate_cancel]
  change Tromino.I.Completable
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

end LeanTrominoes.CompletionPattern.IBricks.FiniteGuards
