/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterCoreSteps

/-! # Local loops of the unary successor-equality filter -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

private def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

theorem replicate_unary_unit_cons_comm (count : Nat)
    (tail : List UnarySymbol) :
    List.replicate count (.unit : UnarySymbol) ++
        (.unit : UnarySymbol) :: tail =
      (.unit : UnarySymbol) ::
        (List.replicate count (.unit : UnarySymbol) ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

theorem replicate_candidate_cons_comm (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: (List.replicate count () ++ tail) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append,
        List.cons.injEq, true_and]
      exact induction

def matchedUnits_evalsInTime (units : Nat)
    (rankTail sizeTail : List UnarySymbol) (data : TapeData)
    (ranksEq : data.ranks = List.replicate units .unit ++ rankTail)
    (sizesEq : data.sizes = List.replicate units .unit ++ sizeTail) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := List.replicate units () ++ data.candidate }))
      (3 * units) := by
  induction units generalizing data with
  | zero =>
      simp only [List.replicate_zero, List.nil_append] at ranksEq sizesEq ⊢
      have dataEq :
          { data with
            ranks := rankTail
            sizes := sizeTail
            candidate := List.replicate 0 () ++ data.candidate } = data := by
        simp only [List.replicate_zero, List.nil_append]
        rw [← ranksEq, ← sizesEq]
      refine
        { steps := 0
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_zero, id_eq, Option.some.injEq]
      exact congrArg scanRankCfg dataEq.symm
  | succ units induction =>
      rw [List.replicate_succ, List.cons_append] at ranksEq sizesEq
      let scanned := oneStep
        (step_scanRank_unit data _ ranksEq)
      let matched := oneStep
        (step_matchSizeUnit_unit
          { data with ranks := List.replicate units (.unit : UnarySymbol) ++ rankTail }
          _ sizesEq)
      let pushed := oneStep
        (step_pushMatchedUnit
          { data with
            ranks := List.replicate units (.unit : UnarySymbol) ++ rankTail
            sizes := List.replicate units (.unit : UnarySymbol) ++ sizeTail })
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ scanned matched
      let firstThree := EvalsToInTime.trans machine.step
        2 1 _ _ _ firstTwo pushed
      let nextData : TapeData :=
        { data with
          ranks := List.replicate units (.unit : UnarySymbol) ++ rankTail
          sizes := List.replicate units (.unit : UnarySymbol) ++ sizeTail
          candidate := () :: data.candidate }
      have nextRanks : nextData.ranks =
          List.replicate units .unit ++ rankTail := rfl
      have nextSizes : nextData.sizes =
          List.replicate units .unit ++ sizeTail := rfl
      let rest := induction nextData nextRanks nextSizes
      let whole := EvalsToInTime.trans machine.step
        3 (3 * units) _ _ _ firstThree rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_candidate_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def rejectDrainSize_evalsInTime (units : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (sizesEq : data.sizes =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (rejectDrainSizeCfg data)
      (some (clearCandidateCfg { data with sizes := tail }))
      (units + 1) := by
  induction units generalizing data with
  | zero =>
      have step := step_rejectDrainSize_delimiter data tail
        (by simpa using sizesEq)
      simpa using oneStep step
  | succ units induction =>
      rw [List.replicate_succ, List.cons_append] at sizesEq
      let first := oneStep
        (step_rejectDrainSize_unit data _ sizesEq)
      let nextData : TapeData :=
        { data with sizes :=
          List.replicate units .unit ++ .delimiter :: tail }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (units + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def rejectDrainRank_evalsInTime (units : Nat) (tail : List UnarySymbol)
    (data : TapeData)
    (ranksEq : data.ranks =
      List.replicate units .unit ++ .delimiter :: tail) :
    EvalsToInTime machine.step (rejectDrainRankCfg data)
      (some (clearCandidateCfg { data with ranks := tail }))
      (units + 1) := by
  induction units generalizing data with
  | zero =>
      have step := step_rejectDrainRank_delimiter data tail
        (by simpa using ranksEq)
      simpa using oneStep step
  | succ units induction =>
      rw [List.replicate_succ, List.cons_append] at ranksEq
      let first := oneStep
        (step_rejectDrainRank_unit data _ ranksEq)
      let nextData : TapeData :=
        { data with ranks :=
          List.replicate units .unit ++ .delimiter :: tail }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (units + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def clearCandidate_evalsInTime (candidate : List Unit) (data : TapeData)
    (candidateEq : data.candidate = candidate) :
    EvalsToInTime machine.step (clearCandidateCfg data)
      (some (emitDelimiterCfg { data with candidate := [] }))
      (candidate.length + 1) := by
  induction candidate generalizing data with
  | nil =>
      have step := step_clearCandidate_nil data candidateEq
      simpa using oneStep step
  | cons unitValue candidate induction =>
      rcases unitValue with ⟨⟩
      let first := oneStep
        (step_clearCandidate_cons data candidate candidateEq)
      let nextData : TapeData := { data with candidate := candidate }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        1 (candidate.length + 1) _ _ _ first rest
      simpa [whole, nextData, Nat.add_assoc] using whole

def drainCandidate_evalsInTime (candidate : List Unit) (data : TapeData)
    (candidateEq : data.candidate = candidate) :
    EvalsToInTime machine.step (drainCandidateCfg data)
      (some (emitDelimiterCfg
        { data with
          candidate := []
          outputReverse :=
            List.replicate candidate.length .unit ++ data.outputReverse }))
      (2 * candidate.length + 1) := by
  induction candidate generalizing data with
  | nil =>
      have step := step_drainCandidate_nil data candidateEq
      simpa using oneStep step
  | cons unitValue candidate induction =>
      rcases unitValue with ⟨⟩
      let popped := oneStep
        (step_drainCandidate_cons data candidate candidateEq)
      let pushed := oneStep
        (step_pushOutputUnit { data with candidate := candidate })
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let nextData : TapeData :=
        { data with
          candidate := candidate
          outputReverse := .unit :: data.outputReverse }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        2 (2 * candidate.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.replicate_succ, Nat.mul_add,
        replicate_unary_unit_cons_comm, List.append_assoc,
        Nat.add_assoc] using whole

def reverseOutput_evalsInTime (tokens : List UnarySymbol) (data : TapeData)
    (reverseEq : data.outputReverse = tokens) :
    EvalsToInTime machine.step (reverseOutputCfg data)
      (some ⟨none, .empty, tapes
        { data with
          outputReverse := []
          output := tokens.reverse ++ data.output }⟩)
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step := step_reverseOutput_nil data reverseEq
      simpa using oneStep step
  | cons symbol tokens induction =>
      let popped := oneStep
        (step_reverseOutput_cons data symbol tokens reverseEq)
      let pushed := oneStep
        (step_pushOutput { data with outputReverse := tokens } symbol)
      let firstTwo := EvalsToInTime.trans machine.step
        1 1 _ _ _ popped pushed
      let nextData : TapeData :=
        { data with
          outputReverse := tokens
          output := symbol :: data.output }
      let rest := induction nextData rfl
      let whole := EvalsToInTime.trans machine.step
        2 (2 * tokens.length + 1) _ _ _ firstTwo rest
      simpa [whole, nextData, List.reverse_cons, Nat.mul_add,
        List.append_assoc, Nat.add_assoc] using whole

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
