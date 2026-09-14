/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionLBooleanExtraction
import LeanTrominoes.CompletionLBrickBooleanSoundness

/-! # Exact equivalence between L completions and infinite Boolean brick networks -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 2000000

def tableOfValue (value : Cell → Bool) (location : Cell) (x : Fin 2) (y : Fin 7) : Bool :=
  value (Cell.add (brickMicroOrigin location) (x.val,y.val))

theorem table_of_value_window (value : Cell → Bool) (location c : Cell)
    (bounds : 0 ≤ c.1 ∧ c.1 < 2 ∧ 0 ≤ c.2 ∧ c.2 < 7) :
    tableValue (tableOfValue value location) c = value (Cell.add (brickMicroOrigin location) c) := by
  unfold tableValue tableOfValue
  congr 1
  apply Prod.ext <;> dsimp [Cell.add] <;> omega

theorem canonical_table_valid {palette : Cell → Fin 24} {completed : Set (Finset Cell)}
    (h : Tromino.L.IsFootprintTiling Set.univ completed) (retained : globalPrescribed palette ⊆ completed)
    (location : Cell) :
    BrickBooleanRelation (palette location) (tableOfValue (canonicalValue palette completed) location) := by
  intro entry he
  let o : Occurrence palette := ⟨location,entry,he⟩
  apply (entry.1.boolean_relation_congr _
    (fun c => canonicalValue palette completed (Cell.add (atomMicroOffset location entry) c)) ?_).mpr
  · exact canonical_global_relations h retained o
  · intro c hc
    have bound := brick_port_window (palette location) entry he c hc
    simp only [Finset.mem_product,Finset.mem_Ico] at bound
    rw [table_of_value_window _ _ _ ⟨bound.1.1,bound.1.2,bound.2.1,bound.2.2⟩]
    congr 1
    apply Prod.ext <;> dsimp [atomMicroOffset,Cell.add] <;> omega

theorem table_external_top (v : BrickValues) (x : Fin 2) :
    tableExternal v ⟨x.val,by omega⟩ = v x 0 := by
  unfold tableExternal
  rw [dif_pos x.isLt]

theorem table_external_bottom (v : BrickValues) (x : Fin 2) :
    tableExternal v ⟨x.val + 2,by omega⟩ = v x 6 := by
  simp [tableExternal]

theorem value_external_seams (value : Cell → Bool) :
    ExternalSeams (fun location => tableExternal (tableOfValue value location)) := by
  intro location x
  dsimp only
  rw [table_external_bottom,table_external_top]
  unfold tableOfValue
  simpa using congrArg value (micro_bottom_coordinates location x)

/-- Every plane completion supplies a satisfying Boolean network with
matching external connectors. -/
theorem brick_network_of_completion (palette : Cell → Fin 24)
    (completed : Tromino.L.Completable Set.univ (globalPrescribed palette)) :
    ∃ external : Cell → Fin 4 → Bool, ExternalSeams external ∧
      ∀ location, Network (palette location) (external location) := by
  obtain ⟨tiles,h,retained⟩ := completed
  refine ⟨fun location => tableExternal (tableOfValue (canonicalValue palette tiles) location),
    value_external_seams _,?_⟩
  intro location
  exact network_of_brick_table _ _ (canonical_table_valid h retained location)

/-- Full, unconditional geometric correctness of the 24-entry L-brick palette. -/
theorem completion_iff_brick_network (palette : Cell → Fin 24) :
    Tromino.L.Completable Set.univ (globalPrescribed palette) ↔
      ∃ external : Cell → Fin 4 → Bool, ExternalSeams external ∧
        ∀ location, Network (palette location) (external location) := by
  constructor
  · exact brick_network_of_completion palette
  · rintro ⟨external,seams,valid⟩
    exact completion_of_brick_network palette external seams valid

end LeanTrominoes.CompletionPattern.LBricks
