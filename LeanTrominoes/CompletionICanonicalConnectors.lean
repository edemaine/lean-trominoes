/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIBrickCompleteness

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem micro_occurrence_exists (palette : Cell → Fin 24) (i : Cell) :
    ∃ o : Occurrence palette, i ∈ groupAt o.location o.entry := by
  obtain ⟨location,entry,he,owned⟩ := global_groups_cover palette i
  exact ⟨⟨location,entry,he⟩,owned⟩

def microOccurrence (palette : Cell → Fin 24) (i : Cell) : Occurrence palette :=
  Classical.choose (micro_occurrence_exists palette i)

theorem micro_occurrence_owns (palette : Cell → Fin 24) (i : Cell) :
    i ∈ groupAt (microOccurrence palette i).location (microOccurrence palette i).entry :=
  Classical.choose_spec (micro_occurrence_exists palette i)

theorem micro_occurrence_eq {palette : Cell → Fin 24} (i : Cell) (o : Occurrence palette)
    (owned : i ∈ groupAt o.location o.entry) : microOccurrence palette i = o := by
  have mine := micro_occurrence_owns palette i
  have locEq := group_locations_eq palette (microOccurrence palette i).member o.member mine owned
  apply Occurrence.ext locEq
  have hm : (microOccurrence palette i).entry ∈ layout (palette o.location) := by
    simpa only [locEq] using (microOccurrence palette i).member
  have owned' : i ∈ groupAt o.location (microOccurrence palette i).entry := by rwa [locEq] at mine
  exact group_entries_eq palette o.location hm o.member owned' owned

def OutsideBelow (palette : Cell → Fin 24) (completed : Set (Finset Cell)) (i : Cell) (right : Bool) : Prop :=
  portalCell i right ∈ Tromino.outsideCells completed
    (regionAt (microOccurrence palette i).location (microOccurrence palette i).entry)

def ProperConnector (palette : Cell → Fin 24) (completed : Set (Finset Cell)) (i : Cell) : Prop :=
  OutsideBelow palette completed i false ↔ ¬ OutsideBelow palette completed i true

def canonicalValue (palette : Cell → Fin 24) (completed : Set (Finset Cell)) (i : Cell) : Bool := by
  classical
  exact decide (OutsideBelow palette completed i true)

theorem outside_below_owned {palette : Cell → Fin 24} (completed : Set (Finset Cell))
    (i : Cell) (right : Bool) (o : Occurrence palette) (owned : i ∈ groupAt o.location o.entry) :
    OutsideBelow palette completed i right ↔
      portalCell i right ∈ Tromino.outsideCells completed (regionAt o.location o.entry) := by
  unfold OutsideBelow
  rw [micro_occurrence_eq i o owned]

theorem outside_above_owned {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (i : Cell) (right : Bool) (o : Occurrence palette)
    (owned : aboveMicro i ∈ groupAt o.location o.entry) (absent : i ∉ groupAt o.location o.entry) :
    portalCell i right ∈ Tromino.outsideCells completed (regionAt o.location o.entry) ↔
      ¬ OutsideBelow palette completed i right := by
  have mine := micro_occurrence_owns palette i
  have distinct : ¬ ((microOccurrence palette i).location = o.location ∧
      (microOccurrence palette i).entry = o.entry) := by
    rintro ⟨hl,he⟩
    rw [hl,he] at mine
    exact absent mine
  have complement := portal_complement palette i right (microOccurrence palette i).member o.member
    mine owned distinct h retained
  change OutsideBelow palette completed i right ↔ _ at complement
  tauto

theorem portal_translation (delta p : Cell) (right : Bool) :
    portalCell (Cell.add delta p) right = Cell.add (microOrigin delta) (portalCell p right) := by
  cases right <;> apply Prod.ext <;> dsimp [portalCell,microOrigin,Cell.add] <;> omega

theorem above_micro_translation (delta p : Cell) :
    aboveMicro (Cell.add delta p) = Cell.add delta (aboveMicro p) := by
  apply Prod.ext <;> dsimp [aboveMicro,Cell.add] <;> omega

theorem Atom.port_ownership (a : Atom) : ∀ p ∈ a.portCells,
    if p.2 = 0 then p ∈ a.group ∧ aboveMicro p ∉ a.group
    else aboveMicro p ∈ a.group ∧ p ∉ a.group := by
  cases a <;> decide +kernel

theorem group_at_mem {palette : Cell → Fin 24} (o : Occurrence palette) (p : Cell) :
    Cell.add (atomMicroOffset o.location o.entry) p ∈ groupAt o.location o.entry ↔ p ∈ o.entry.1.group := by
  rw [group_at_image]
  simp only [Finset.mem_image,(Cell.add_left_injective (atomMicroOffset o.location o.entry)).eq_iff]
  simp

/-- Canonical states read one shared global connector, with complementary
outside conventions for the subbrick above and the subbrick below. -/
theorem canonical_port {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.I.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (o : Occurrence palette) (p : Cell) (hp : p ∈ o.entry.1.portCells) (right : Bool) :
    portalCell p right ∈ outsideAt completed o.location o.entry ↔
      if p.2 = 0 then OutsideBelow palette completed (Cell.add (atomMicroOffset o.location o.entry) p) right
      else ¬ OutsideBelow palette completed (Cell.add (atomMicroOffset o.location o.entry) p) right := by
  rw [mem_outsideAt,← atom_micro_offset palette o.location o.member,← portal_translation]
  have localOwner := o.entry.1.port_ownership p hp
  by_cases top : p.2 = 0
  · rw [if_pos top] at localOwner ⊢
    exact (outside_below_owned completed _ right o ((group_at_mem o p).mpr localOwner.1)).symm
  · rw [if_neg top] at localOwner ⊢
    apply outside_above_owned h retained _ right o
    · rw [above_micro_translation]
      exact (group_at_mem o (aboveMicro p)).mpr localOwner.1
    · exact fun member => localOwner.2 ((group_at_mem o p).mp member)

end LeanTrominoes.CompletionPattern.IBricks
