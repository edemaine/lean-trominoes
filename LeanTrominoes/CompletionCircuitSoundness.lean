/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitForest

/-! # Extracting source variables from a model of a checked circuit -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

theorem Model.clause_port_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked)
    {index : Nat} {node : CircuitNode} (atIndex : circuit.nodes[index]? = some node)
    (clause : index < circuit.clauseCount) (p : Fin 4) :
    external node.position p = (node.signal p).eval (circuit.extractedValue external) := by
  have info := (checked.node_check_of_get atIndex).2.2
  rw [if_pos clause] at info
  obtain ⟨wire,label,parent,inactive,supplied⟩ := info
  by_cases activePort : p.val < 3
  · obtain ⟨inside,supply⟩ := supplied p activePort
    exact (model.seams node.position p).trans (model.wire_signal_sound checked _ inside _ _ supply)
  · have last : p = 3 := by apply Fin.ext; omega
    subst p
    have valid := model.node_valid checked (List.mem_of_getElem? atIndex)
    rw [network_iff,if_neg (by omega)] at valid
    rw [inactive]
    exact valid.1

/-- Wire components supply variables satisfying all of the circuit clauses. -/
theorem Model.formula_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) :
    circuit.Formula (circuit.extractedValue external) := by
  intro node member
  obtain ⟨index,bound,eq⟩ := List.mem_iff_getElem.mp member
  have before : index < circuit.clauseCount := lt_of_lt_of_le bound (List.length_take_le _ _)
  have inList : index < circuit.nodes.length := lt_of_lt_of_le bound (List.length_take_le' _ _)
  simp only [List.getElem_take] at eq
  have atIndex : circuit.nodes[index]? = some node := List.getElem?_eq_some_iff.mpr ⟨inList,eq⟩
  have same : external node.position = node.values (circuit.extractedValue external) :=
    funext (model.clause_port_sound checked atIndex before)
  rw [← same]
  exact model.node_valid checked (List.mem_of_getElem? atIndex)

theorem terminal_inside (p : Fin 4) : Inside (terminalPoint p) := by
  revert p
  decide +kernel

/-- The source terminals read the declared wire-component variables. -/
theorem Model.terminals_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) :
    circuit.TerminalRelation (fun p => external (terminalPoint p) p) (circuit.extractedValue external) := by
  intro p
  exact model.wire_signal_sound checked _ (terminal_inside p) p _ (checked.2.2.2.2.2.2 p).2

/-- A checked circuit with the certified truth table enforces its source
orientation relation on the four terminals. -/
theorem Model.source_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) (kind : CircuitKind)
    (truth : circuit.TruthTableCorrect kind) :
    kind.SourceRelation (fun p => external (terminalPoint p) p) := by
  exact (truth _).mpr ⟨circuit.extractedValue external,model.formula_sound checked,model.terminals_sound checked⟩

end LeanTrominoes.CompletionPattern.LBricks.Circuit
