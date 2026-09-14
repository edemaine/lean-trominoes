/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionICanonicalStates
import LeanTrominoes.TrominoCompletionAssembly

/-! # Global I-completion as compatible local gadget states -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000

structure Occurrence (palette : Cell → Fin 24) where
  location : Cell
  entry : Atom × Cell
  member : entry ∈ layout (palette location)

theorem Occurrence.ext {palette : Cell → Fin 24} {a b : Occurrence palette}
    (location : a.location = b.location) (entry : a.entry = b.entry) : a = b := by
  cases a
  cases b
  cases location
  cases entry
  rfl

def stateTarget {palette : Cell → Fin 24} (o : Occurrence palette) (outside : Finset Cell) : Finset Cell :=
  (o.entry.1.pattern.region \ outside).image (Cell.add (atomOffset o.location o.entry))

/-- Every local state is realizable, and its assigned cells partition the plane. -/
def CompatibleStates (palette : Cell → Fin 24) (outside : Occurrence palette → Finset Cell) : Prop :=
  (∀ o, outside o ⊆ o.entry.1.boundary ∧ o.entry.1.pattern.Completable (outside o)) ∧
  ∀ c : Cell, ∃! o : Occurrence palette, c ∈ stateTarget o (outside o)

theorem atom_prescribed_translate (location : Cell) (entry : Atom × Cell) :
    (fun f => f.image (Cell.add (atomOffset location entry))) ''
      (Tromino.I.finiteFootprints entry.1.pattern.prefill : Set (Finset Cell)) =
      atomPrescribed location entry := by
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hg
    exact ⟨p,(entry.1.prefill_mem p).mp hp,(Placement.shift_cells_image p .I _).symm⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨p.cells (fun _ => Tromino.I.cells),
      Finset.mem_image.mpr ⟨p,(entry.1.prefill_mem p).mpr hp,rfl⟩,
      (Placement.shift_cells_image p .I _).symm⟩

theorem state_completion {palette : Cell → Fin 24} (o : Occurrence palette) (outside : Finset Cell)
    (h : o.entry.1.pattern.Completable outside) :
    Tromino.I.Completable (stateTarget o outside : Set Cell) (atomPrescribed o.location o.entry) := by
  unfold Pattern.Completable Pattern.target at h
  rw [Atom.kind_eq] at h
  have shifted := h.translate (atomOffset o.location o.entry)
  rw [atom_prescribed_translate,← Finset.coe_image] at shifted
  exact shifted

theorem prescribed_union (palette : Cell → Fin 24) :
    {f | ∃ o : Occurrence palette, f ∈ atomPrescribed o.location o.entry} = globalPrescribed palette := by
  ext f
  constructor
  · rintro ⟨o,p,hp,rfl⟩
    exact atom_prescribed palette o.location o.member hp
  · intro hf
    obtain ⟨location,entry,he,p,hp,eq⟩ := prescribed_atom palette hf
    exact ⟨⟨location,entry,he⟩,p,hp,eq⟩

/-- Compatible realizable subbrick states assemble to a full plane completion. -/
theorem completion_of_compatible_states (palette : Cell → Fin 24)
    {outside : Occurrence palette → Finset Cell} (h : CompatibleStates palette outside) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  have assembled := Tromino.completable_assemble
    (fun o => state_completion o (outside o) (h.1 o).2) (by
      intro a b c ha hb
      obtain ⟨owner,_,unique⟩ := h.2 c
      exact (unique a ha).trans (unique b hb).symm)
  have covered : {c | ∃ o : Occurrence palette, c ∈ (stateTarget o (outside o) : Set Cell)} = (Set.univ : Set Cell) := by
    ext c
    exact iff_true_intro ((h.2 c).exists)
  rw [covered,prescribed_union] at assembled
  exact assembled

theorem canonical_target {palette : Cell → Fin 24} (o : Occurrence palette)
    (completed : Set (Finset Cell)) :
    (stateTarget o (outsideAt completed o.location o.entry) : Set Cell) =
      Tromino.occupied (Tromino.containedTiles completed (regionAt o.location o.entry)) := by
  classical
  have cancel : (outsideAt completed o.location o.entry).image (Cell.add (atomOffset o.location o.entry)) =
      Tromino.outsideCells completed (regionAt o.location o.entry) := by
    simp [outsideAt,Finset.image_image,Function.comp_def,Cell.add,Cell.sub]
  unfold stateTarget
  rw [Finset.image_sdiff _ _ (Cell.add_left_injective _),cancel]
  change (↑(regionAt o.location o.entry \ Tromino.outsideCells completed (regionAt o.location o.entry)) : Set Cell) = _
  ext c
  constructor
  · intro hc
    obtain ⟨inside,notOutside⟩ := Finset.mem_sdiff.mp hc
    by_contra absent
    exact notOutside (Finset.mem_filter.mpr ⟨inside,absent⟩)
  · rintro ⟨f,⟨hf,contained⟩,covers⟩
    exact Finset.mem_sdiff.mpr ⟨contained covers,
      fun absent => (Finset.mem_filter.mp absent).2 ⟨f,⟨hf,contained⟩,covers⟩⟩

/-- A full completion supplies compatible canonical states at all subbricks. -/
theorem compatible_states_of_completion (palette : Cell → Fin 24)
    {completed : Set (Finset Cell)} (h : Tromino.I.IsFootprintTiling Set.univ completed)
    (retained : globalPrescribed palette ⊆ completed) :
    CompatibleStates palette (fun o => outsideAt completed o.location o.entry) := by
  constructor
  · intro o
    exact canonical_local_state palette o.location o.member h retained
  · intro c
    obtain ⟨f,⟨hf,covers⟩,_⟩ := h.uniqueCover c trivial
    obtain ⟨location,entry,he,contained⟩ := completed_tile_owner palette h retained hf
    let o : Occurrence palette := ⟨location,entry,he⟩
    refine ⟨o,?_,?_⟩
    · change c ∈ (stateTarget o (outsideAt completed o.location o.entry) : Set Cell)
      rw [canonical_target]
      exact ⟨f,⟨hf,contained⟩,covers⟩
    · intro other hc
      change c ∈ (stateTarget other (outsideAt completed other.location other.entry) : Set Cell) at hc
      rw [canonical_target] at hc
      obtain ⟨g,⟨hg,inside⟩,hgc⟩ := hc
      have eq := (h.partial (Set.Subset.refl completed)).nonoverlap g hg f hf c hgc covers
      subst g
      obtain ⟨locEq,entryEq⟩ := tile_owner_unique palette (h.tilesInside f hf).1
        other.member he inside contained
      exact Occurrence.ext locEq entryEq

/-- Exact global geometric assembly criterion; no periodicity of a solution is assumed. -/
theorem completion_iff_compatible_states (palette : Cell → Fin 24) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) ↔
      ∃ outside : Occurrence palette → Finset Cell, CompatibleStates palette outside := by
  constructor
  · rintro ⟨completed,h,retained⟩
    exact ⟨_,compatible_states_of_completion palette h retained⟩
  · rintro ⟨outside,h⟩
    exact completion_of_compatible_states palette h

end LeanTrominoes.CompletionPattern.IBricks
