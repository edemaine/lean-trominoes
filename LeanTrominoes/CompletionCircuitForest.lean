/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionCircuitInterface

/-! # Soundness of certified wire spanning forests -/

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks.Circuit

set_option maxHeartbeats 2000000

def readValue (external : Cell → Fin 4 → Bool) (node : CircuitNode) : Bool :=
  external node.position node.readPort

def extractedValue (circuit : Circuit) (external : Cell → Fin 4 → Bool) (k : Fin 4) : Bool :=
  ((circuit.nodes[(circuit.anchors[k.val]?).getD 0]?).map (readValue external)).getD false

/-- Parent indices decrease strictly, so every wire node carries its
component anchor's value in any model of the circuit. -/
theorem Model.wire_read_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked)
    {index : Nat} {node : CircuitNode} (atIndex : circuit.nodes[index]? = some node)
    {k : Fin 4} (wire : node.wire = some k) :
    readValue external node = circuit.extractedValue external k := by
  have all : ∀ index : Nat, ∀ node : CircuitNode, circuit.nodes[index]? = some node →
      ∀ k : Fin 4, node.wire = some k → readValue external node = circuit.extractedValue external k := by
    intro index
    induction index using Nat.strong_induction_on with
    | h index ih =>
      intro node atIndex k wire
      have member := List.mem_of_getElem? atIndex
      obtain ⟨copy,read,signals,parent⟩ := checked.copy_info atIndex wire
      cases parentEq : node.parent with
      | none =>
        simp only [ParentLink,parentEq] at parent
        unfold extractedValue
        rw [← parent,atIndex]
        rfl
      | some previous =>
        simp only [ParentLink,parentEq] at parent
        obtain ⟨less,earlier,earlierMember,earlierWire,position,activeSelf,activeEarlier⟩ := parent
        change circuit.nodes[previous]? = some earlier at earlierMember
        have earlierInList := List.mem_of_getElem? earlierMember
        have earlierInfo := checked.copy_info earlierMember earlierWire
        calc
          readValue external node = external node.position node.parentPort :=
            model.copy_equal checked member copy read activeSelf
          _ = external (gridNeighbor node.position node.parentPort) (gridOpposite node.parentPort) := model.seams _ _
          _ = external earlier.position (gridOpposite node.parentPort) := by rw [position]
          _ = readValue external earlier :=
            model.copy_equal checked earlierInList earlierInfo.1 activeEarlier earlierInfo.2.1
          _ = circuit.extractedValue external k := ih previous less earlier earlierMember k earlierWire
  exact all index node atIndex k wire

/-- Every port of a wire node agrees with its declared signal expression. -/
theorem Model.wire_port_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked)
    {index : Nat} {node : CircuitNode} (atIndex : circuit.nodes[index]? = some node)
    {k : Fin 4} (wire : node.wire = some k) (p : Fin 4) :
    external node.position p = (node.signal p).eval (circuit.extractedValue external) := by
  obtain ⟨copy,read,signals,parent⟩ := checked.copy_info atIndex wire
  have member := List.mem_of_getElem? atIndex
  rw [signals p]
  cases enabled : active node.label p
  · change external node.position p = false
    exact (model.copy_relation checked member copy).1 p enabled
  · change external node.position p = circuit.extractedValue external k
    exact (model.copy_equal checked member copy enabled read).trans (model.wire_read_sound checked atIndex wire)

theorem active_zero (p : Fin 4) : active 0 p = false := by
  revert p
  decide +kernel

/-- A checked neighboring wire or inactive port supplies the declared value. -/
theorem Model.wire_signal_sound {circuit : Circuit} {external : Cell → Fin 4 → Bool}
    (model : circuit.Model external) (checked : circuit.Checked) (c : Cell) (inside : Inside c)
    (p : Fin 4) (signal : CircuitSignal) (supply : circuit.WireSignal c p signal) :
    external c p = signal.eval (circuit.extractedValue external) := by
  unfold WireSignal at supply
  cases found : circuit.lookup c with
  | none =>
    rw [found] at supply
    subst signal
    have valid := model.valid c inside
    simp only [labelAt,found,Option.map_none,Option.getD_none] at valid
    rw [network_iff,if_pos (by decide)] at valid
    exact valid.1 p (active_zero p)
  | some node =>
    rw [found] at supply
    obtain ⟨k,wire,copy,signalEq⟩ := supply
    have member := lookup_mem found
    obtain ⟨index,bound,eq⟩ := List.mem_iff_getElem.mp member
    have atIndex : circuit.nodes[index]? = some node := List.getElem?_eq_some_iff.mpr ⟨bound,eq⟩
    have info := checked.copy_info atIndex wire
    rw [← lookup_position found,model.wire_port_sound checked atIndex wire p,info.2.2.1 p,signalEq]

end LeanTrominoes.CompletionPattern.LBricks.Circuit
