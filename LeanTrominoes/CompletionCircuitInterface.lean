/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitCertificates

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

theorem Checked.lookup_self {circuit : Circuit} (checked : circuit.Checked)
    {node : CircuitNode} (member : node ∈ circuit.nodes) : circuit.lookup node.position = some node :=
  checked.2.2.2.1 node member

theorem Checked.node_check {circuit : Circuit} (checked : circuit.Checked)
    (i : Fin circuit.nodes.length) : circuit.NodeCheck i.val circuit.nodes[i.val] :=
  checked.2.2.2.2.1 i

theorem Checked.node_check_of_get {circuit : Circuit} (checked : circuit.Checked)
    {index : Nat} {node : CircuitNode} (atIndex : circuit.nodes[index]? = some node) :
    circuit.NodeCheck index node := by
  obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp atIndex
  have supplied := checked.node_check ⟨index,bound⟩
  rwa [eq] at supplied

theorem Checked.node_inside {circuit : Circuit} (checked : circuit.Checked)
    {node : CircuitNode} (member : node ∈ circuit.nodes) : Inside node.position := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
  have supplied := checked.node_check ⟨i,hi⟩
  rw [eq] at supplied
  exact supplied.1

theorem lookup_mem {circuit : Circuit} {c : Cell} {node : CircuitNode}
    (found : circuit.lookup c = some node) : node ∈ circuit.nodes := List.mem_of_find?_eq_some found

theorem lookup_position {circuit : Circuit} {c : Cell} {node : CircuitNode}
    (found : circuit.lookup c = some node) : node.position = c := by
  have matched := List.find?_some found
  simpa only [beq_iff_eq] using matched

structure Model (circuit : Circuit) (external : Cell → Fin 4 → Bool) : Prop where
  seams : SquareSeams external
  valid : ∀ c, Inside c → Network (circuit.labelAt c) (external c)

theorem Model.node_valid {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) {node : CircuitNode}
    (member : node ∈ circuit.nodes) : Network node.label (external node.position) := by
  have supplied := model.valid node.position (checked.node_inside member)
  simpa only [labelAt,checked.lookup_self member,Option.map_some,Option.getD_some] using supplied

theorem Model.copy_relation {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) {node : CircuitNode}
    (member : node ∈ circuit.nodes) (copy : node.label.val < 16) :
    CopyRelation node.label (external node.position) := by
  have valid := model.node_valid checked member
  rwa [network_iff,if_pos copy] at valid

theorem Model.copy_equal {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) {node : CircuitNode}
    (member : node ∈ circuit.nodes) (copy : node.label.val < 16) {p q : Fin 4}
    (hp : active node.label p = true) (hq : active node.label q = true) :
    external node.position p = external node.position q := by
  obtain ⟨value,uniform⟩ := (model.copy_relation checked member copy).2
  exact (uniform p hp).trans (uniform q hq).symm

def ParentLink (circuit : Circuit) (index : Nat) (node : CircuitNode) (k : Fin 4) : Prop :=
  match node.parent with
  | none => index = (circuit.anchors[k.val]?).getD 0
  | some parent => parent < index ∧ ∃ earlier ∈ circuit.nodes[parent]?,
      earlier.wire = some k ∧ earlier.position = gridNeighbor node.position node.parentPort ∧
      active node.label node.parentPort = true ∧ active earlier.label (gridOpposite node.parentPort) = true

theorem Checked.copy_info {circuit : Circuit} (checked : circuit.Checked)
    {index : Nat} {node : CircuitNode} (atIndex : circuit.nodes[index]? = some node)
    {k : Fin 4} (wire : node.wire = some k) :
    node.label.val < 16 ∧ active node.label node.readPort = true ∧
      (∀ p, node.signal p = if active node.label p then some k else none) ∧
      circuit.ParentLink index node k := by
  have supplied := (checked.node_check_of_get atIndex).2.2
  by_cases clause : index < circuit.clauseCount
  · rw [if_pos clause] at supplied
    rw [wire] at supplied
    simp at supplied
  · rw [if_neg clause] at supplied
    obtain ⟨j,hj,copy,read,signals,parent⟩ := supplied
    have eq : j = k := Option.some.inj (hj.symm.trans wire)
    subst j
    exact ⟨copy,read,signals,parent⟩

end LeanTrominoes.CompletionPattern.LBricks.Circuit
