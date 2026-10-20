/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRead

/-! # Recording the first reached edge to a free right vertex -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def Selected (input : Input) (found : Option (Fin input.1 × Fin input.2.1)) (d : Data) : Prop :=
  match found with
  | none => d.1 Reg.foundRight=0
  | some edge => d.1 Reg.foundLeft=edge.1.val ∧ d.1 Reg.foundRight=edge.2.val+1

instance selectedDecidable (input : Input) (found : Option (Fin input.1 × Fin input.2.1)) (d : Data) : Decidable (Selected input found d) :=
  match found with
  | none => inferInstanceAs (Decidable (d.1 Reg.foundRight=0))
  | some edge => inferInstanceAs (Decidable (d.1 Reg.foundLeft=edge.1.val ∧ d.1 Reg.foundRight=edge.2.val+1))

def record1 (d : Data) := d.set Reg.foundLeft (d.1 Reg.left)
def record2 (d : Data) := (record1 d).set Reg.foundRight (d.1 Reg.right)
def recordState (d : Data) := (record2 d).set Reg.foundRight (d.1 Reg.right+d.1 Reg.one)

attribute [local simp] Reg.one Reg.zero Reg.left Reg.right Reg.foundLeft Reg.foundRight
  record1 record2 recordState NaturalData.set

theorem recordTerminal_exec {B : Nat} (input : Input)
    (matching : State (Fin input.1) (Fin input.2.1)) (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input matching paths d) (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B)
    (l : Fin input.1) (r : Fin input.2.1) (left : d.1 Reg.left=l.val) (right : d.1 Reg.right=r.val) :
    Natural.Exec B recordTerminal d (recordState d) 3 ∧
      Representation input matching paths (recordState d) ∧ NaturalData.Bounded B (recordState d) ∧
      Selected input (some (l,r)) (recordState d) := by
  have rightBound : r.val+1≤B := by
    have bound : input.2.1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact (show r.val+1≤ input.2.1 by have := r.isLt; omega).trans (bound.trans room)
  have first : Natural.Exec B (copy Reg.foundLeft Reg.left) d (record1 d) 1 :=
    Natural.Exec.atom (Natural.Step.copy d Reg.foundLeft Reg.left (before.1 _))
  have second : Natural.Exec B (copy Reg.foundRight Reg.right) (record1 d) (record2 d) 1 :=
    Natural.Exec.atom (Natural.Step.copy (record1 d) Reg.foundRight Reg.right (by simpa using before.1 Reg.right))
  have third : Natural.Exec B (increment Reg.foundRight) (record2 d) (recordState d) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (record2 d) Reg.foundRight Reg.foundRight Reg.one (by simpa [right,rep.one] using rightBound))
  have trace : Natural.Exec B recordTerminal d (recordState d) 3 := first.seq (second.seq third)
  have frame : PreservesLayout recordTerminal := by
    constructor
    · intro slot; fin_cases slot <;> decide
    · decide
  exact ⟨trace,rep.of_execution input matching matching paths paths d _ trace frame rep.memory,trace.bounded before,
    by simp [Selected,left,right,rep.one]⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
