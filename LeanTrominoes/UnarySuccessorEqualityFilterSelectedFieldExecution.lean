/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterLocalExecution

/-! # Canonical successful unary successor comparisons -/

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

/-- When `size = rank + 1`, retain the complete size field. -/
def selectedField_evalsInTime (rank : Nat)
    (rankTail sizeTail : List UnarySymbol) (data : TapeData)
    (ranksEq : data.ranks =
      UnaryFieldEncoderMachine.unaryField rank ++ rankTail)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryField (rank + 1) ++ sizeTail)
    (candidateEq : data.candidate = []) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField (rank + 1)).reverse ++
              data.outputReverse }))
      (5 * rank + 8) := by
  have matched := matchedUnits_evalsInTime rank
    (.delimiter :: rankTail) (.unit :: .delimiter :: sizeTail) data
    (by simpa [UnaryFieldEncoderMachine.unaryField] using ranksEq)
    (by
      simpa [UnaryFieldEncoderMachine.unaryField,
        List.replicate_add, List.append_assoc] using sizesEq)
  let afterMatched : TapeData :=
    { data with
      ranks := .delimiter :: rankTail
      sizes := .unit :: .delimiter :: sizeTail
      candidate := List.replicate rank () }
  have afterMatchedEq :
      { data with
        ranks := .delimiter :: rankTail
        sizes := .unit :: .delimiter :: sizeTail
        candidate := List.replicate rank () ++ data.candidate } =
        afterMatched := by
    simp [afterMatched, candidateEq]
  rw [afterMatchedEq] at matched
  let scanned := oneStep
    (step_scanRank_delimiter afterMatched rankTail rfl)
  let extra := oneStep
    (step_checkExtraSize_unit
      { afterMatched with ranks := rankTail } (.delimiter :: sizeTail)
      (by simp [afterMatched]))
  let pushed := oneStep
    (step_pushExtraUnit
      { afterMatched with
        ranks := rankTail
        sizes := .delimiter :: sizeTail })
  let checked := oneStep
    (step_checkSizeDelimiter_delimiter
      { afterMatched with
        ranks := rankTail
        sizes := .delimiter :: sizeTail
        candidate := () :: afterMatched.candidate }
      sizeTail rfl)
  let firstTwo := EvalsToInTime.trans machine.step
    1 1 _ _ _ scanned extra
  let firstThree := EvalsToInTime.trans machine.step
    2 1 _ _ _ firstTwo pushed
  let firstFour := EvalsToInTime.trans machine.step
    3 1 _ _ _ firstThree checked
  let candidate := List.replicate (rank + 1) ()
  have candidateEq' :
      (() :: afterMatched.candidate) = candidate := by
    simp [afterMatched, candidate, List.replicate_succ]
  let drained := drainCandidate_evalsInTime candidate
    { data with
      ranks := rankTail
      sizes := sizeTail
      candidate := candidate }
    rfl
  let emitted := oneStep
    (step_emitDelimiter
      { data with
        ranks := rankTail
        sizes := sizeTail
        candidate := []
        outputReverse :=
          List.replicate candidate.length .unit ++ data.outputReverse })
  let throughCheck := EvalsToInTime.trans machine.step
    (3 * rank) 4 _ _ _ matched firstFour
  have throughCheck' : EvalsToInTime machine.step (scanRankCfg data)
      (some (drainCandidateCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := candidate }))
      (4 + 3 * rank) := by
    simpa [afterMatched, candidate, candidateEq', Nat.add_comm] using throughCheck
  let throughDrain := EvalsToInTime.trans machine.step
    (4 + 3 * rank) (2 * candidate.length + 1)
    _ _ _ throughCheck' drained
  let whole := EvalsToInTime.trans machine.step
    (2 * candidate.length + 1 + (4 + 3 * rank)) 1
    _ _ _ throughDrain emitted
  convert whole using 1
  ·
    simp [candidate, UnaryFieldEncoderMachine.unaryField,
      List.reverse_append, List.replicate_succ,
      replicate_unary_unit_cons_comm]
  · simp [candidate]
    omega

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
