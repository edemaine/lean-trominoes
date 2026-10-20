/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRepresentation
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSemantics

/-! # Reusing static register preservation in matching subprogram proofs -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

instance primitivePreservesRegisterDecidable {r : Nat} (i : Fin r) (op : Structured.Primitive r) :
    Decidable (op.PreservesRegister i) :=
  match op with
  | .constant dst _ | .copy dst _ | .arithmetic _ dst _ _ | .load dst _ =>
    inferInstanceAs (Decidable (i≠dst))
  | .store _ _ => inferInstanceAs (Decidable True)

instance codePreservesRegisterDecidable {r : Nat} (i : Fin r) (code : Structured.Code r) :
    Decidable (code.PreservesRegister i) :=
  match code with
  | .atom op => primitivePreservesRegisterDecidable i op
  | .seq a b | .branch _ a b =>
    letI := codePreservesRegisterDecidable i a
    letI := codePreservesRegisterDecidable i b
    inferInstanceAs (Decidable (a.PreservesRegister i ∧ b.PreservesRegister i))
  | .loop _ body => codePreservesRegisterDecidable i body

def PreservesLayout (code : Code) : Prop :=
  (∀ slot, code.PreservesRegister (pointer slot)) ∧
  code.PreservesRegister Reg.n ∧ code.PreservesRegister Reg.m ∧ code.PreservesRegister Reg.edges ∧
  code.PreservesRegister Reg.one ∧ code.PreservesRegister Reg.zero

theorem Representation.of_execution {B cost : Nat} {code : Code} (input : Input)
    (matching nextMatching : State (Fin input.1) (Fin input.2.1))
    (paths nextPaths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (data result : Data)
    (rep : Representation input matching paths data) (execution : Natural.Exec B code data result cost)
    (frame : PreservesLayout code) (memory : MemoryRep input nextMatching nextPaths result.2) :
    Representation input nextMatching nextPaths result := by
  constructor
  · intro slot
    rw [execution.register_eq (frame.1 slot)]
    exact rep.pointers slot
  · rw [execution.register_eq frame.2.1]; exact rep.n
  · rw [execution.register_eq frame.2.2.1]; exact rep.m
  · rw [execution.register_eq frame.2.2.2.1]; exact rep.edges
  · rw [execution.register_eq frame.2.2.2.2.1]; exact rep.one
  · rw [execution.register_eq frame.2.2.2.2.2]; exact rep.zero
  · exact memory

end LeanTrominoes.BipartiteMatching.DenseWordRAM
