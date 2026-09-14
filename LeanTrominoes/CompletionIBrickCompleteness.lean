/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIGlobalTables

/-! # Realizing infinite networks of I-completion bricks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def Atom.portCells : Atom → Finset Cell
  | .copy => {(0,0),(1,0),(0,2),(1,2)}
  | .clause => {(0,0),(1,0),(0,1),(1,1)}
  | _ => {(0,0),(0,1)}

theorem Atom.boolean_relation_congr (a : Atom) (v w : Cell → Bool)
    (h : ∀ c ∈ a.portCells, v c = w c) : a.BooleanRelation v ↔ a.BooleanRelation w := by
  cases a <;> unfold Atom.BooleanRelation
  · rw [h (0,0) (by decide),h (0,1) (by decide)]
  · rw [h (0,0) (by decide),h (0,1) (by decide)]
  · rw [h (0,0) (by decide)]
  · rw [h (0,1) (by decide)]
  · rw [h (0,0) (by decide),h (1,0) (by decide),h (0,2) (by decide),h (1,2) (by decide)]
  · rw [h (0,0) (by decide),h (1,0) (by decide),h (0,1) (by decide),h (1,1) (by decide)]

theorem brick_port_window (i : Fin 24) : ∀ entry ∈ layout i, ∀ c ∈ entry.1.portCells,
    Cell.add (entryMicroOffset entry) c ∈ (Finset.Ico 0 2 ×ˢ Finset.Ico 0 7 : Finset Cell) := by
  revert i
  decide +kernel

theorem global_entry_relation (palette : Cell → Fin 24) (tables : Cell → BrickValues)
    (seams : TableSeams tables) (realized : ∀ location, BrickBooleanRelation (palette location) (tables location))
    (o : Occurrence palette) :
    o.entry.1.BooleanRelation
      (fun c => globalTableValue tables (Cell.add (atomMicroOffset o.location o.entry) c)) := by
  apply (o.entry.1.boolean_relation_congr _
    (fun c => tableValue (tables o.location) (Cell.add (entryMicroOffset o.entry) c)) ?_).mpr
  · exact realized o.location o.entry o.member
  · intro c hc
    have bound := brick_port_window (palette o.location) o.entry o.member c hc
    simp only [Finset.mem_product,Finset.mem_Ico] at bound
    have associate : Cell.add (atomMicroOffset o.location o.entry) c =
        Cell.add (brickMicroOrigin o.location) (Cell.add (entryMicroOffset o.entry) c) := by
      apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega
    rw [associate]
    exact global_table_window tables seams o.location _ ⟨bound.1.1,bound.1.2,bound.2.1,bound.2.2⟩

/-- A plane of locally valid Boolean tables with matching external rows
has a completion by the paper's I-tromino gadgets. -/
theorem completion_of_brick_tables (palette : Cell → Fin 24) (tables : Cell → BrickValues)
    (seams : TableSeams tables)
    (realized : ∀ location, BrickBooleanRelation (palette location) (tables location)) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  apply completion_of_boolean_states palette (globalTableValue tables)
  intro o
  rw [boolean_outside_local,Atom.boolean_completion_iff]
  exact global_entry_relation palette tables seams realized o

/-- External Boolean values agree across the two downward brick edges. -/
def ExternalSeams (external : Cell → Fin 4 → Bool) : Prop :=
  ∀ location : Cell, ∀ x : Fin 2,
    external location ⟨x.val + 2,by omega⟩ =
      external (belowBrick location x) ⟨(oppositeColumn x).val,by omega⟩

/-- Any satisfying infinite brick network yields a plane completion.
The Boolean values need not be periodic. -/
theorem completion_of_brick_network (palette : Cell → Fin 24) (external : Cell → Fin 4 → Bool)
    (seams : ExternalSeams external) (valid : ∀ location, Network (palette location) (external location)) :
    Tromino.I.Completable Set.univ (globalPrescribed palette) := by
  choose core coreValid using valid
  let tables : Cell → BrickValues := fun location => witnessTable (palette location) (external location) (core location)
  apply completion_of_brick_tables palette tables
  · intro location x
    change witnessTable _ _ _ x 6 = witnessTable _ _ _ (oppositeColumn x) 0
    rw [witness_table_bottom,witness_table_top]
    exact seams location x
  · intro location
    exact witness_table_valid _ _ _ (coreValid location)

end LeanTrominoes.CompletionPattern.IBricks
