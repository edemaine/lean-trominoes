/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMCandidateCoordinate

/-! # The conjunction and parity invariant of the fixed coordinate sequence -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Candidate
open ComplexityAbstract.RAM
variable {n d : ℕ}

structure Progress (B : BasisData n d) (u v : Fin n) (direction : Fin d) (done : List (Fin d)) (data : Data) : Prop where
  frame : Frame B u v data
  active : data.1 Collect.active≤1
  valid : 0< data.1 Collect.active ↔ ∀ coordinate∈done,
    B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)
  bits : ∀ coordinate∈done, data.2 (data.1 Collect.parities+coordinate.val)≤1
  parity : PaddedGraph.Active B u direction v → ∀ coordinate∈done,
    data.2 (data.1 Collect.parities+coordinate.val)=(PaddedGraph.coordinates B u direction v coordinate%2).toNat

theorem Frame.parity_before {B : BasisData n d} {u v : Fin n} {data : Data} (h : Frame B u v data)
    (coordinate : Fin d) : data.1 Collect.parities+coordinate.val< data.1 Reserve.frontier := by
  rw [h.parities]
  have hi := coordinate.isLt
  have positive : 1≤ WordRAM.precision B := by unfold WordRAM.precision; omega
  have mul := Nat.mul_le_mul_left coordinate.val positive
  have frontier := h.frontier
  have large := Nat.mul_le_mul_right (WordRAM.precision B) (Nat.succ_le_of_lt hi)
  nlinarith only [frontier,mul,large,positive]

theorem Progress.step {B : BasisData n d} {u v : Fin n} {direction coordinate : Fin d} {done : List (Fin d)}
    {before after : Data} (h : Progress B u v direction done before) (fresh : coordinate∉done)
    (frame : Frame B u v after) (active : after.1 Collect.active≤1)
    (valid : 0< after.1 Collect.active ↔ 0< before.1 Collect.active ∧
      B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v))
    (bit : after.1 Collect.parity≤1)
    (parity : B.basis.det∣(Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v) →
      ((Circuit.rawNumeratorCircuit d direction coordinate).eval (rawInputs B u v)/B.basis.det)%2=(after.1 Collect.parity : ℤ))
    (written : after.2 (before.1 Collect.parities+coordinate.val)=after.1 Collect.parity)
    (memory : ∀ address, address< before.1 Reserve.frontier → address≠before.1 Collect.parities+coordinate.val →
      after.2 address=before.2 address) : Progress B u v direction (coordinate::done) after := by
  have pointer : after.1 Collect.parities=before.1 Collect.parities := frame.parities.trans h.frame.parities.symm
  have preserved (other : Fin d) (member : other∈done) :
      after.2 (after.1 Collect.parities+other.val)=before.2 (before.1 Collect.parities+other.val) := by
    rw [pointer]
    apply memory _ (h.frame.parity_before other)
    intro equal
    have vals := Nat.add_left_cancel equal
    exact fresh ((Fin.ext vals) ▸ member)
  constructor
  · exact frame
  · exact active
  · rw [valid,h.valid]
    simp only [List.forall_mem_cons]
    exact and_comm
  · intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [pointer,written]; exact bit
    · rw [preserved other member]; exact h.bits other member
  · intro candidate other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [pointer,written]
      have divisible := (active_iff_rawNumerators B h.frame.nonzero u v direction).mp candidate other
      exact rawNumerator_parity B h.frame.nonzero u v direction other candidate _ (parity divisible)
    · rw [preserved other member]
      exact h.parity candidate other member

theorem Progress.done {B : BasisData n d} {u v : Fin n} {direction : Fin d} {done : List (Fin d)}
    {data : Data} (h : Progress B u v direction done data) (complete : ∀ coordinate, coordinate∈done) :
    (data.1 Collect.active≠0 ↔ PaddedGraph.Active B u direction v) ∧
      (∀ i : Fin d, data.2 (data.1 Collect.parities+i.val)≤1) ∧
      (PaddedGraph.Active B u direction v → ∀ i,
        data.2 (data.1 Collect.parities+i.val)=(PaddedGraph.coordinates B u direction v i%2).toNat) := by
  refine ⟨?_,fun i => h.bits i (complete i),fun active i => h.parity active i (complete i)⟩
  rw [show (data.1 Collect.active≠0 ↔ 0< data.1 Collect.active) by omega,h.valid,
    active_iff_rawNumerators B h.frame.nonzero]
  exact ⟨fun all i => all i (complete i),fun all i _ => all i⟩

end LeanTrominoes.Domino.WordRAM.Binary.Candidate
