/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitGridGeometry
import LeanTrominoes.CompletionCircuitSoundness
import LeanTrominoes.CompletionCircuitWiring

/-! # Replacing every orientation cell by a certified Boolean circuit -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

def SourceHolds (kinds : Cell → CircuitKind) : Prop :=
  ∃ external : Cell → Fin 4 → Bool, SquareSeams external ∧
    ∀ location, (kinds location).SourceRelation (external location)

def macroPalette (kinds : Cell → CircuitKind) (c : Cell) : Fin 24 :=
  (circuitFor (kinds (macroIndex c))).labelAt (macroLocal c)

def macroValues (kinds : Cell → CircuitKind) (values : Cell → Fin 4 → Bool) (c : Cell) (p : Fin 4) : Bool :=
  (circuitFor (kinds (macroIndex c))).assignedValues (values (macroIndex c)) (macroLocal c) p

theorem macro_palette_at (kinds : Cell → CircuitKind) (location c : Cell) (inside : Inside c) :
    macroPalette kinds (Cell.add (macroOrigin location) c) = (circuitFor (kinds location)).labelAt c := by
  unfold macroPalette
  rw [macro_index_at location c inside,macro_local_at location c inside]

theorem macro_values_at (kinds : Cell → CircuitKind) (values : Cell → Fin 4 → Bool)
    (location c : Cell) (inside : Inside c) (p : Fin 4) :
    macroValues kinds values (Cell.add (macroOrigin location) c) p =
      (circuitFor (kinds location)).assignedValues (values location) c p := by
  unfold macroValues
  rw [macro_index_at location c inside,macro_local_at location c inside]

/-- A global macro-network model restricts to the checked circuit at each source cell. -/
theorem macro_model (kinds : Cell → CircuitKind) {external : Cell → Fin 4 → Bool}
    (model : SquareNetwork (macroPalette kinds) external) (location : Cell) :
    (circuitFor (kinds location)).Model (fun c => external (Cell.add (macroOrigin location) c)) := by
  constructor
  · intro c p
    have seam := model.1 (Cell.add (macroOrigin location) c) p
    simpa only [grid_neighbor_add] using seam
  · intro c inside
    have localValid := model.2 (Cell.add (macroOrigin location) c)
    rwa [macro_palette_at kinds location c inside] at localValid

/-- Every satisfying macro network induces a satisfying orientation-cell network. -/
theorem source_of_macros (kinds : Cell → CircuitKind) (h : SquareHolds (macroPalette kinds)) : SourceHolds kinds := by
  obtain ⟨external,model⟩ := h
  refine ⟨fun location p => external (Cell.add (macroOrigin location) (terminalPoint p)) p,?_,?_⟩
  · intro location p
    have seam := model.1 (Cell.add (macroOrigin location) (terminalPoint p)) p
    simpa only [macro_terminal_neighbor] using seam
  · intro location
    exact (macro_model kinds model location).source_sound (circuit_wiring_checked _) _ (circuit_truth_table _)

/-- Satisfying source terminals extend to all the finite circuits at once,
and the checked boundary expressions agree across every macro seam. -/
theorem macros_of_source (kinds : Cell → CircuitKind) (h : SourceHolds kinds) : SquareHolds (macroPalette kinds) := by
  obtain ⟨external,seams,valid⟩ := h
  have witnesses : ∀ location, ∃ value : Fin 4 → Bool,
      (circuitFor (kinds location)).Formula value ∧
        (circuitFor (kinds location)).TerminalRelation (external location) value := by
    intro location
    exact (circuit_truth_table (kinds location) _).mp (valid location)
  choose values formulas terminals using witnesses
  refine ⟨macroValues kinds values,?_,?_⟩
  · intro c p
    let location := macroIndex c
    let d := macroLocal c
    have inside : Inside d := macro_local_inside c
    have decomposition : Cell.add (macroOrigin location) d = c := macro_decomposition c
    rw [← decomposition,macro_values_at kinds values location d inside p]
    by_cases neighborInside : Inside (gridNeighbor d p)
    · rw [grid_neighbor_add,macro_values_at kinds values location (gridNeighbor d p) neighborInside]
      exact congrArg (fun signal : CircuitSignal => signal.eval (values location))
        ((circuit_wiring_checked (kinds location)).signals_inside d p inside neighborInside)
    · obtain ⟨wrappedInside,backOutside,terminalIff⟩ := wrapped_boundary d p inside neighborInside
      rw [macro_boundary_neighbor,macro_values_at kinds values (gridNeighbor location p) (wrappedNeighbor d p) wrappedInside]
      unfold assignedValues
      rw [(circuit_wiring_checked (kinds location)).signal_boundary d p neighborInside,
        (circuit_wiring_checked (kinds (gridNeighbor location p))).signal_boundary (wrappedNeighbor d p) (gridOpposite p) backOutside]
      by_cases terminal : d = terminalPoint p
      · rw [if_pos terminal,if_pos (terminalIff.mp terminal),← terminals location p,
          ← terminals (gridNeighbor location p) (gridOpposite p)]
        exact seams location p
      · rw [if_neg terminal,if_neg (fun here => terminal (terminalIff.mpr here))]
        rfl
  · intro c
    exact (circuit_wiring_checked (kinds (macroIndex c))).local_realized (values (macroIndex c))
      (formulas (macroIndex c)) (macroLocal c)

/-- Uniform correctness for arbitrary infinite assignments of source cell kinds. -/
theorem macro_reduction_correct (kinds : Cell → CircuitKind) :
    SourceHolds kinds ↔ SquareHolds (macroPalette kinds) :=
  ⟨macros_of_source kinds,source_of_macros kinds⟩

end LeanTrominoes.CompletionPattern.LBricks.Circuit
