/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMOuterLoop

/-! # The complete balanced-input decision block -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

theorem balanced_exec {B : Nat} (input : Input)
    (paths : DenseSearch.Paths (Fin input.1) (Fin input.2.1)) (d : Data)
    (rep : Representation input empty paths d) (pathsBound : PathsBound input paths)
    (before : NaturalData.Bounded B d) (room : (Layout.ofInput input).frontier≤B) :
    ∃ result cost, Natural.Exec B balanced d result cost ∧
      cost≤(120*(input.1+1)^2*(input.2.2.length+1)+5)*input.1+4 ∧ NaturalData.Bounded B result ∧
      result.1 Reg.output=(if (DenseSearch.solve input.2.2).isSome then 1 else 0) := by
  have unit : 1≤B := by
    have bound : 1≤(Layout.ofInput input).frontier := by dsimp [Layout.ofInput,Layout.frontier]; omega
    exact bound.trans room
  let d1 := d.set Reg.output 1
  have first : Natural.Exec B (constant Reg.output 1) d d1 1 := Natural.Exec.atom (Natural.Step.constant d Reg.output 1 unit)
  have rep1 := rep.set_scalar input empty paths d Reg.output 1 (scalarRegister_of_large _ (by decide)) (by decide)
  let d2 := d1.set Reg.outer 0
  have second : Natural.Exec B (constant Reg.outer 0) d1 d2 1 := Natural.Exec.atom (Natural.Step.constant d1 Reg.outer 0 (Nat.zero_le B))
  have rep2 := rep1.set_scalar input empty paths d1 Reg.outer 0 (scalarRegister_of_large _ (by decide)) (by decide)
  obtain ⟨result,cost,later,budget,finalBound,answer⟩ := outerLoop_exec input input.1 empty paths d2 rep2 pathsBound
    ((first.seq second).bounded before) room (by simp [d2,d1,NaturalData.set,Reg.outer,Reg.output])
    (by simp [d2,NaturalData.set])
  refine ⟨result,1+(1+cost),first.seq (second.seq later),by omega,finalBound,?_⟩
  simpa only [DenseSearch.solve,Fintype.card_fin] using answer

end LeanTrominoes.BipartiteMatching.DenseWordRAM
