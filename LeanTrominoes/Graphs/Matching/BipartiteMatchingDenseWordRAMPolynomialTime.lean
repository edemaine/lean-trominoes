/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMBalanced
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMInitialization
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMRuntime

/-! # A uniform polynomial-time bounded-word RAM matching algorithm

A single fixed finite program reads original endpoint records, allocates its
workspace, searches and rewrites augmenting paths, and halts with the correct
answer. The bound counts every primitive instruction, including allocation and
halt, and works for every larger word width.
-/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM

def predicate (input : Input) : Prop := HasFiniteMatching (DenseSearch.edgeBuckets input.2.2)

/-- Operational certificate exposing final data and the exact program execution,
for composition with callers that construct their own endpoint arrays. -/
theorem program_verified_quartic (input : Input) (w : Nat)
    (width : 8*Nat.log2 (size input+2)+2≤w) :
    program.size<2^w ∧ ∃ result : ComplexityAbstract.RAM.Data 64, ∃ steps,
      Structured.Exec w program (initial (r := 64) (encode input)).data result steps ∧
      steps+1≤1000*(size input+1)^4 ∧ Fits w (result.1 Reg.output) ∧
      (result.1 Reg.output=0 ∨ result.1 Reg.output=1) ∧
      (result.1 Reg.output=1 ↔ predicate input) := by
  have word := frontier_fits input width
  have log : 1≤Nat.log2 (size input+2) := by
    have bound := Nat.log_mono_right (b := 2) (show 2≤size input+2 by omega)
    simpa [← Nat.log2_eq_log_two] using bound
  have ten : 10≤w := by omega
  have capacity : program.size<2^w := by
    calc
      program.size<2^10 := by simpa only [show (2 : Nat)^10=1024 by decide] using program_capacity
      _≤2^w := pow_le_pow_right₀ (by decide : 1≤(2 : Nat)) ten
  have prepared := prepare_on_input input word
  have rep := preparedInput_represents input
  have bounded := preparedInput_bounded input
  have pathBound : PathsBound input (fun _ => none) := by intro l prior marked; contradiction
  by_cases equal : input.1=input.2.1
  · obtain ⟨result,cost,execution,budget,finalBound,answer⟩ := balanced_exec input (fun _ => none) (preparedInput input) rep pathBound bounded (le_refl _)
    have condition : Natural.Holds (.eq Reg.n Reg.m) (preparedInput input) := by simp only [Natural.Holds,rep.n,rep.m,equal]
    have branch := Natural.Exec.branch_yes (no := constant Reg.output 0) condition execution
    have run := prepared.seq (branch.compiles word)
    have boolNat : result.1 Reg.output=0 ∨ result.1 Reg.output=1 := by rw [answer]; split <;> simp
    have oneNat : result.1 Reg.output=1 ↔ predicate input := by
      have test : result.1 Reg.output=1 ↔ (DenseSearch.solve input.2.2).isSome=true := by
        rw [answer]
        cases (DenseSearch.solve input.2.2).isSome <;> decide
      exact test.trans (DenseSearch.solve_iff input.2.2 (by simpa using equal))
    refine ⟨capacity,result.word,4*(2*input.1+input.2.1+2*(input.1*input.1))+58+(cost+1),?_,?_,?_,?_,?_⟩
    · simpa only [program,initialData_word] using run
    · exact runtime_quartic input (cost+1) (by omega)
    · exact Allocation.nat_fits_le word (finalBound.1 Reg.output)
    · rcases boolNat with zero | one
      · left; simp only [NaturalData.word,zero,Int.natCast_zero]
      · right; simp only [NaturalData.word,one,Int.natCast_one]
    · change (result.1 Reg.output : Int)=1 ↔ predicate input
      rw [← Int.natCast_one,Int.natCast_inj]
      exact oneNat
  · let result := (preparedInput input).set Reg.output 0
    have constantRun : Natural.Exec (Layout.ofInput input).frontier (constant Reg.output 0) (preparedInput input) result 1 :=
      Natural.Exec.atom (Natural.Step.constant _ Reg.output 0 (Nat.zero_le _))
    have condition : ¬Natural.Holds (.eq Reg.n Reg.m) (preparedInput input) := by
      simpa only [Natural.Holds,rep.n,rep.m] using equal
    have branch := Natural.Exec.branch_no (yes := balanced) condition constantRun
    have run := prepared.seq (branch.compiles word)
    have absent : ¬predicate input := by
      rintro ⟨bijection,supported⟩
      have cardinality := Fintype.card_congr bijection
      simp only [Fintype.card_fin] at cardinality
      exact equal cardinality
    refine ⟨capacity,result.word,4*(2*input.1+input.2.1+2*(input.1*input.1))+58+3,?_,?_,?_,?_,?_⟩
    · simpa only [program,initialData_word,Nat.reduceAdd] using run
    · exact runtime_quartic input 3 (by omega)
    · exact Allocation.nat_fits_le word ((branch.bounded bounded).1 Reg.output)
    · left; simp [result,NaturalData.word,NaturalData.set]
    · simp [result,NaturalData.word,NaturalData.set,absent]

/-- Original weaker operational certificate, retained for existing callers. -/
theorem program_verified (input : Input) (w : Nat)
    (width : 8*Nat.log2 (size input+2)+2≤w) :
    program.size<2^w ∧ ∃ result : ComplexityAbstract.RAM.Data 64, ∃ steps,
      Structured.Exec w program (initial (r := 64) (encode input)).data result steps ∧
      steps+1≤1000*(size input+1)^5 ∧ Fits w (result.1 Reg.output) ∧
      (result.1 Reg.output=0 ∨ result.1 Reg.output=1) ∧
      (result.1 Reg.output=1 ↔ predicate input) := by
  obtain ⟨capacity,result,steps,run,budget,fits,boolean,correct⟩ := program_verified_quartic input w width
  have grow : (size input+1)^4≤(size input+1)^5 := by
    have bound := Nat.mul_le_mul_left ((size input+1)^4) (show 1≤size input+1 by omega)
    simpa only [Nat.mul_one,pow_succ] using bound
  exact ⟨capacity,result,steps,run,budget.trans (Nat.mul_le_mul_left 1000 grow),fits,boolean,correct⟩

/-- A quartic instruction bound for the same fixed bounded-word program. -/
theorem decidesWithin_quartic : DecidesWithin encode predicate (fun input => 1000*(size input+1)^4)
    (fun input => 8*Nat.log2 (size input+2)+2) :=
  Structured.decidesWithin program Reg.output encode _ _ _
    (fun input w width _ => program_verified_quartic input w width)

/-- The public instruction bound includes the final halt. -/
theorem decidesWithin : DecidesWithin encode predicate (fun input => 1000*(size input+1)^5)
    (fun input => 8*Nat.log2 (size input+2)+2) :=
  Structured.decidesWithin program Reg.output encode _ _ _
    (fun input w width _ => program_verified input w width)

/-- Actual finite bipartite perfect matching is decidable in polynomial time
with logarithmic words and explicit bounded addresses. -/
theorem polynomialTime : PolynomialTime encode size predicate := ⟨1000,4,8,decidesWithin_quartic⟩

end LeanTrominoes.BipartiteMatching.DenseWordRAM
