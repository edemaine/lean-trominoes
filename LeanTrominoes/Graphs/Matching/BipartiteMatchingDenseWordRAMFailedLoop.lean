/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRead

/-! # After a failed augmentation, the remaining outer iterations only skip -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.n Reg.one Reg.zero Reg.outer Reg.output

def outerBody : Code := .seq (.branch (.eq Reg.output Reg.zero) skip phase) (increment Reg.outer)

theorem failedLoop_exec {B n : Nat} (remaining : Nat) (d : Data)
    (before : NaturalData.Bounded B d) (room : n≤B)
    (vertices : d.1 Reg.n=n) (one : d.1 Reg.one=1) (zero : d.1 Reg.zero=0) (failed : d.1 Reg.output=0)
    (enough : d.1 Reg.outer+remaining=n) :
    ∃ result, Natural.Exec B (.loop (.lt Reg.outer Reg.n) outerBody) d result (5*remaining+2) ∧
      NaturalData.Bounded B result ∧ result.1 Reg.output=0 := by
  induction remaining generalizing d with
  | zero =>
    refine ⟨d,Natural.Exec.loop_done ?_,before,failed⟩
    simp only [Natural.Holds,vertices]
    omega
  | succ remaining ih =>
    have inside : d.1 Reg.outer<n := by omega
    have skipped := Natural.Exec.branch_yes (no := phase)
      (show Natural.Holds (.eq Reg.output Reg.zero) d by simp only [Natural.Holds,failed,zero]) (native_skip d before)
    let next := d.set Reg.outer (d.1 Reg.outer+d.1 Reg.one)
    have incremented : Natural.Exec B (increment Reg.outer) d next 1 :=
      Natural.Exec.atom (Natural.Step.add d Reg.outer Reg.outer Reg.one (by rw [one]; exact (show d.1 Reg.outer+1≤n by omega).trans room))
    have body : Natural.Exec B outerBody d next 3 := skipped.seq incremented
    obtain ⟨result,later,finalBound,finalOutput⟩ := ih next (body.bounded before)
      (by simp [next,NaturalData.set,vertices]) (by simp [next,NaturalData.set,one])
      (by simp [next,NaturalData.set,zero]) (by simp [next,NaturalData.set,failed])
      (by simp only [next,NaturalData.set,Function.update_self,one]; omega)
    have trace := Natural.Exec.loop_more (c := .lt Reg.outer Reg.n)
      (by simpa only [Natural.Holds,vertices] using inside) body later
    exact ⟨result,by convert trace using 1 <;> omega,finalBound,finalOutput⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
