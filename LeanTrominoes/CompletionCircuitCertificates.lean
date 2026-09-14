/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuit

/-! # Checkable wiring and spanning-forest certificates for Boolean circuits -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

/-- A point supplies a wire value, or a forced-false inactive port. -/
def WireSignal (circuit : Circuit) (c : Cell) (p : Fin 4) (signal : CircuitSignal) : Prop :=
  match circuit.lookup c with
  | none => signal = none
  | some node => ∃ k : Fin 4, node.wire = some k ∧ node.label.val < 16 ∧
      signal = if active node.label p then some k else none

instance (circuit : Circuit) (c : Cell) (p : Fin 4) (signal : CircuitSignal) :
    Decidable (circuit.WireSignal c p signal) := by
  unfold WireSignal
  split <;> infer_instance

def NodeCheck (circuit : Circuit) (index : Nat) (node : CircuitNode) : Prop :=
  Inside node.position ∧ node.signals.length = 4 ∧
  if index < circuit.clauseCount then
    node.wire = none ∧ 16 ≤ node.label.val ∧ node.parent = none ∧ node.signal 3 = none ∧
    ∀ p : Fin 4, p.val < 3 →
      Inside (gridNeighbor node.position p) ∧
      circuit.WireSignal (gridNeighbor node.position p) (gridOpposite p) (node.signal p)
  else
    ∃ k : Fin 4, node.wire = some k ∧ node.label.val < 16 ∧
      active node.label node.readPort = true ∧
      (∀ p, node.signal p = if active node.label p then some k else none) ∧
      match node.parent with
      | none => index = (circuit.anchors[k.val]?).getD 0
      | some parent => parent < index ∧ ∃ earlier ∈ circuit.nodes[parent]?,
          earlier.wire = some k ∧
          earlier.position = gridNeighbor node.position node.parentPort ∧
          active node.label node.parentPort = true ∧
          active earlier.label (gridOpposite node.parentPort) = true

instance (circuit : Circuit) (index : Nat) (node : CircuitNode) : Decidable (circuit.NodeCheck index node) := by
  unfold NodeCheck
  split
  · infer_instance
  · cases parentEq : node.parent <;> simp only [parentEq] <;> infer_instance

/-- Each explicitly stored port agrees with its neighbor or with the
single exposed terminal on that side of the macro. -/
def SeamCheck (circuit : Circuit) : Prop :=
  ∀ node ∈ circuit.nodes, ∀ p : Fin 4,
    if Inside (gridNeighbor node.position p) then
      node.signal p = circuit.signalAt (gridNeighbor node.position p) (gridOpposite p)
    else node.signal p = if node.position = terminalPoint p then circuit.terminal p else none

instance (circuit : Circuit) : Decidable circuit.SeamCheck := by
  unfold SeamCheck
  infer_instance

/-- The finite checker contains no satisfiability assumption. -/
def Checked (circuit : Circuit) : Prop :=
  circuit.clauseCount ≤ circuit.nodes.length ∧ circuit.anchors.length = 4 ∧ circuit.terminals.length = 4 ∧
  (∀ node ∈ circuit.nodes, circuit.lookup node.position = some node) ∧
  (∀ i : Fin circuit.nodes.length, circuit.NodeCheck i.val circuit.nodes[i.val]) ∧
  circuit.SeamCheck ∧
  (∀ p : Fin 4, circuit.signalAt (terminalPoint p) p = circuit.terminal p ∧
    circuit.WireSignal (terminalPoint p) p (circuit.terminal p))

instance (circuit : Circuit) : Decidable circuit.Checked := by
  unfold Checked
  infer_instance

/-- A certified copy-node record realizes its signal expressions for every
assignment to the four circuit variables. -/
theorem copy_node_realized (node : CircuitNode) (k : Fin 4)
    (copy : node.label.val < 16)
    (signals : ∀ p, node.signal p = if active node.label p then some k else none)
    (value : Fin 4 → Bool) : Network node.label (node.values value) := by
  rw [network_iff,if_pos copy]
  constructor
  · intro p inactive
    unfold CircuitNode.values
    rw [signals p,inactive]
    rfl
  · refine ⟨value k,?_⟩
    intro p enabled
    unfold CircuitNode.values
    rw [signals p,enabled]
    rfl

end LeanTrominoes.CompletionPattern.LBricks.Circuit
