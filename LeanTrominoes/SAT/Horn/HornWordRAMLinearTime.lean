/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMPropagationExecution
import LeanTrominoes.SAT.Horn.HornWordRAMAnswer

/-! # A linear-time bounded-word RAM decision algorithm for Horn SAT

One fixed thirty-two-register program reads the original rule/occurrence
encoding, allocates its arrays, builds its index, propagates, and halts with the
correct Boolean answer. Every primitive instruction is included in the bound.
-/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

def propagationBound (input : Input) := stackBound (indexedBound input) input.2.rules.size

theorem propagationBound_frontier (input : Input) : (Layout.ofInput input).frontier≤ propagationBound input := by
  rw [Layout.frontier_eq]
  dsimp [propagationBound,stackBound,indexedBound,indexBound]
  omega

theorem propagationWidth {w : ℕ} (input : Input) (width : 27*Nat.log2 (size input+2)+2≤ w) :
    Fits w (128*propagationBound input : ℕ) := by
  apply WordBounds.polynomial_fits_uniform 524288 4 (size input) w
  · have log : Nat.log2 (524288+1)=19 := by decide
    simpa only [log,Nat.reduceMul,Nat.reduceAdd] using width
  · simp only [Int.natAbs_natCast]
    have bound := input_stack_bound input
    dsimp [propagationBound]
    omega

theorem startWork (input : Input) :
    Worklist.RAM.work (Worklist.index (Indexed.edges input.2).reverse).bucket (startState input)=
      input.2.rules.size+(Indexed.edges input.2).length := by
  have potential : Worklist.potential (startState input)=input.2.rules.size := by
    simpa only [startState,Fintype.card_fin] using
      Worklist.stackInitial_potential (Indexed.edges input.2).reverse (Indexed.head input.2)
  rw [Worklist.RAM.work,potential]
  simp [Worklist.RAM.unread,startState,Worklist.stackInitial,Worklist.initial,Worklist.initialWithIndex,
    Worklist.index_volume]

/-- Operational certificate for using the Horn code as a subroutine.
Unlike the decision wrapper, this exposes its final data and exact execution. -/
theorem program_verified (input : Input) (w : ℕ)
    (width : 27*Nat.log2 (size input+2)+2≤w) :
    program.size<2^w ∧ ∃ result : ComplexityAbstract.RAM.Data 32, ∃ steps,
      Structured.Exec w program (initial (r := 32) (encode input)).data result steps ∧
      steps+1≤120*(size input+1) ∧ Fits w (result.1 Reg.output) ∧
      (result.1 Reg.output=0 ∨ result.1 Reg.output=1) ∧
      (result.1 Reg.output=1 ↔ Satisfiable input.2.rules.toList) := by
  have word := propagationWidth input width
  have log : 1≤ Nat.log2 (size input+2) := by
    have mono := Nat.log_mono_right (b := 2) (show 2≤ size input+2 by omega)
    simpa [← Nat.log2_eq_log_two] using mono
  have nine : 9≤ w := by omega
  have capacity : program.size<2^w :=
    (by decide : program.size<2^9).trans_le (pow_le_pow_right₀ (by decide) nine)
  obtain ⟨contents,represented⟩ := stackedInput_represents input
  have initialBound : NaturalData.Bounded (propagationBound input) (stackedInput input) := stackedInput_bounded input
  have potential : Worklist.potential (startState input)=input.2.rules.size := by
    simpa only [startState,Fintype.card_fin] using
      Worklist.stackInitial_potential (Indexed.edges input.2).reverse (Indexed.head input.2)
  obtain ⟨result,finalContents,propCost,propExec,propBudget,finalRep,finalBound⟩ :=
    represented.propagate input input.2.rules.size (startState input) (stackedInput input) contents
      (by omega) (by omega) initialBound (propagationBound_frontier input) word
  have invariant : Worklist.Invariant (Indexed.edges input.2).reverse (Indexed.head input.2)
      (Worklist.stackRun (Worklist.index (Indexed.edges input.2).reverse).bucket (Indexed.head input.2)
        input.2.rules.size (startState input)) :=
    Worklist.stackRun_invariant _ _ _ _ (Worklist.stackInitial_invariant _ _)
  have empty := Worklist.stackRun_empty (Worklist.index (Indexed.edges input.2).reverse).bucket
    (Indexed.head input.2) input.2.rules.size (startState input) (by omega)
  have finalExec := answer_exec finalBound finalRep.one (Allocation.nat_fits_le word (by omega))
  have correct := answerState_output input _ result finalContents finalRep invariant empty
  have prepared := prepare_on_input input (w := w) (by omega)
  have indexed := buildIndex_on_input input width
  have stacked := initialStack_on_input input width
  have execution := prepared.seq (indexed.seq (stacked.seq (propExec.seq finalExec)))
  have boolean : ((answerState result).word.1 Reg.output=0 ∨ (answerState result).word.1 Reg.output=1) := by
    simp only [NaturalData.word,answerState,NaturalData.set,Function.update_self]
    split <;> simp
  have oneBound : 1≤ propagationBound input := by
    have bound := initialBound.1 Reg.one
    rw [represented.one] at bound
    exact bound
  have outputFits : Fits w ((answerState result).word.1 Reg.output) := by
    rcases boolean with zero | one
    · rw [zero]; exact Allocation.nat_fits_le word (Nat.zero_le _)
    · rw [one]; exact Allocation.nat_fits_le (a := 1) word (by omega)
  refine ⟨capacity,(answerState result).word,_,execution,?_,outputFits,boolean,?_⟩
  · have scanBudget := initialStackCost_le (indexedInput input)
    rw [(indexedInput_scalars input).1] at scanBudget
    rw [startWork] at propBudget
    have answerBudget := answerCost_le result
    dsimp [size]
    omega
  · change ((answerState result).1 Reg.output : ℤ)=1 ↔ Satisfiable input.2.rules.toList
    rw [← Int.natCast_one,Int.natCast_inj]
    exact correct

/-- The public execution property, including the final halt. -/
theorem decidesWithin :
    DecidesWithin encode (fun input => Satisfiable input.2.rules.toList)
      (fun input => 120*(size input+1)) (fun input => 27*Nat.log2 (size input+2)+2) :=
  Structured.decidesWithin program Reg.output encode _ _ _
    (fun input w width _ => program_verified input w width)

/-- Horn satisfiability has an actual uniform linear-time word-RAM algorithm. -/
theorem linearTime : LinearTime encode size (fun input => Satisfiable input.2.rules.toList) :=
  ⟨120,27,decidesWithin⟩

end LeanTrominoes.Horn.WordRAM
