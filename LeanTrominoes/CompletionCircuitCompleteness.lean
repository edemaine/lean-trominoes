/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitInterface

/-! # Realizing circuit variables and checking all internal seams -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

def assignedValues (circuit : Circuit) (value : Fin 4 → Bool) (c : Cell) (p : Fin 4) : Bool :=
  (circuit.signalAt c p).eval value

theorem blank_network : Network 0 (fun _ => false) := by decide +kernel

/-- Any satisfying assignment to the circuit clauses realizes every local
Boolean brick in the finite macro. Unlisted cells are blank. -/
theorem Checked.local_realized {circuit : Circuit} (checked : circuit.Checked)
    (value : Fin 4 → Bool) (formula : circuit.Formula value) (c : Cell) :
    Network (circuit.labelAt c) (circuit.assignedValues value c) := by
  change Network (circuit.labelAt c) (fun p => (circuit.signalAt c p).eval value)
  cases found : circuit.lookup c with
  | none =>
    simpa only [labelAt,assignedValues,signalAt,found,Option.map_none,Option.getD_none,CircuitSignal.eval] using blank_network
  | some node =>
    have member := lookup_mem found
    obtain ⟨index,bound,eq⟩ := List.mem_iff_getElem.mp member
    have atIndex : circuit.nodes[index]? = some node := List.getElem?_eq_some_iff.mpr ⟨bound,eq⟩
    have nodeValid : Network node.label (node.values value) := by
      by_cases clause : index < circuit.clauseCount
      · apply formula node
        apply List.mem_iff_getElem.mpr
        refine ⟨index,?_,?_⟩
        · simp only [List.length_take]
          omega
        · simpa only [List.getElem_take] using eq
      · have info := (checked.node_check_of_get atIndex).2.2
        rw [if_neg clause] at info
        obtain ⟨k,wire,copy,read,signals,parent⟩ := info
        exact copy_node_realized node k copy signals value
    change Network node.label (fun p => (node.signal p).eval value) at nodeValid
    simpa only [labelAt,signalAt,found,Option.map_some,Option.getD_some] using nodeValid

theorem grid_opposite_opposite (p : Fin 4) : gridOpposite (gridOpposite p) = p := by
  apply Fin.ext
  dsimp [gridOpposite]
  omega

theorem grid_neighbor_opposite (c : Cell) (p : Fin 4) :
    gridNeighbor (gridNeighbor c p) (gridOpposite p) = c := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;> simp [gridNeighbor,gridOpposite]

theorem grid_neighbor_add (v c : Cell) (p : Fin 4) :
    gridNeighbor (Cell.add v c) p = Cell.add v (gridNeighbor c p) := by
  rcases four_ports p with rfl | rfl | rfl | rfl <;>
    apply Prod.ext <;> simp [gridNeighbor,Cell.add] <;> omega

/-- The sparse seam certificate also controls seams touching unlisted cells. -/
theorem Checked.signals_inside {circuit : Circuit} (checked : circuit.Checked) (c : Cell) (p : Fin 4)
    (inside : Inside c) (neighborInside : Inside (gridNeighbor c p)) :
    circuit.signalAt c p = circuit.signalAt (gridNeighbor c p) (gridOpposite p) := by
  have seams := checked.2.2.2.2.2.1
  cases found : circuit.lookup c with
  | some node =>
    have supplied := seams node (lookup_mem found) p
    have position := lookup_position found
    rw [position,if_pos neighborInside] at supplied
    simpa only [signalAt,found,Option.map_some,Option.getD_some] using supplied
  | none =>
    cases other : circuit.lookup (gridNeighbor c p) with
    | none => simp only [signalAt,found,other,Option.map_none,Option.getD_none]
    | some node =>
      have supplied := seams node (lookup_mem other) (gridOpposite p)
      rw [lookup_position other,grid_neighbor_opposite,if_pos inside,grid_opposite_opposite] at supplied
      simpa only [signalAt,found,other,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none] using supplied.symm

/-- The only potentially nonzero signal crossing a macro boundary is its
designated terminal, with the exact expression recorded in the certificate. -/
theorem Checked.signal_boundary {circuit : Circuit} (checked : circuit.Checked) (c : Cell) (p : Fin 4)
    (outside : ¬ Inside (gridNeighbor c p)) :
    circuit.signalAt c p = if c = terminalPoint p then circuit.terminal p else none := by
  cases found : circuit.lookup c with
  | some node =>
    have supplied := checked.2.2.2.2.2.1 node (lookup_mem found) p
    rw [lookup_position found,if_neg outside] at supplied
    simpa only [signalAt,found,Option.map_some,Option.getD_some] using supplied
  | none =>
    by_cases terminalEq : c = terminalPoint p
    · rw [terminalEq,if_pos rfl]
      exact (checked.2.2.2.2.2.2 p).1
    · simp only [signalAt,found,Option.map_none,Option.getD_none,if_neg terminalEq]

end LeanTrominoes.CompletionPattern.LBricks.Circuit
