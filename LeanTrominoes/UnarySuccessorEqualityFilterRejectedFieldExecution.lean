/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterLocalExecution

/-! # Canonical rejected unary successor comparisons -/

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

/-- When `size >= rank + 2`, emit the zero field. -/
def rejectedField_evalsInTime (rank extraUnits : Nat)
    (rankTail sizeTail : List UnarySymbol) (data : TapeData)
    (ranksEq : data.ranks =
      UnaryFieldEncoderMachine.unaryField rank ++ rankTail)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryField (rank + 2 + extraUnits) ++
        sizeTail)
    (candidateEq : data.candidate = []) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := []
          outputReverse := .delimiter :: data.outputReverse }))
      (4 * rank + extraUnits + 8) := by
  have matched := matchedUnits_evalsInTime rank
    (.delimiter :: rankTail)
    (List.replicate (2 + extraUnits) .unit ++ .delimiter :: sizeTail)
    data
    (by simpa [UnaryFieldEncoderMachine.unaryField] using ranksEq)
    (by
      simpa [UnaryFieldEncoderMachine.unaryField,
        List.replicate_add, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using sizesEq)
  let afterMatched : TapeData :=
    { data with
      ranks := .delimiter :: rankTail
      sizes := List.replicate (2 + extraUnits) .unit ++
        .delimiter :: sizeTail
      candidate := List.replicate rank () }
  have afterMatchedEq :
      { data with
        ranks := .delimiter :: rankTail
        sizes := List.replicate (2 + extraUnits) .unit ++
          .delimiter :: sizeTail
        candidate := List.replicate rank () ++ data.candidate } =
        afterMatched := by
    simp [afterMatched, candidateEq]
  rw [afterMatchedEq] at matched
  let scanned := oneStep
    (step_scanRank_delimiter afterMatched rankTail rfl)
  let extra := oneStep
    (step_checkExtraSize_unit
      { afterMatched with ranks := rankTail }
      (List.replicate (1 + extraUnits) .unit ++ .delimiter :: sizeTail)
      (by simp [afterMatched, List.replicate_add]))
  let pushed := oneStep
    (step_pushExtraUnit
      { afterMatched with
        ranks := rankTail
        sizes := List.replicate (1 + extraUnits) .unit ++
          .delimiter :: sizeTail })
  let checked := oneStep
    (step_checkSizeDelimiter_unit
      { afterMatched with
        ranks := rankTail
        sizes := List.replicate (1 + extraUnits) .unit ++
          .delimiter :: sizeTail
        candidate := () :: afterMatched.candidate }
      (List.replicate extraUnits .unit ++ .delimiter :: sizeTail)
      (by simp [List.replicate_add]))
  let firstTwo := EvalsToInTime.trans machine.step
    1 1 _ _ _ scanned extra
  let firstThree := EvalsToInTime.trans machine.step
    2 1 _ _ _ firstTwo pushed
  let firstFour := EvalsToInTime.trans machine.step
    3 1 _ _ _ firstThree checked
  let rejected := rejectDrainSize_evalsInTime extraUnits sizeTail
    { data with
      ranks := rankTail
      sizes := List.replicate extraUnits .unit ++ .delimiter :: sizeTail
      candidate := List.replicate (rank + 1) () }
    rfl
  let cleared := clearCandidate_evalsInTime
    (List.replicate (rank + 1) ())
    { data with
      ranks := rankTail
      sizes := sizeTail
      candidate := List.replicate (rank + 1) () }
    rfl
  let emitted := oneStep
    (step_emitDelimiter
      { data with
        ranks := rankTail
        sizes := sizeTail
        candidate := [] })
  let throughCheck := EvalsToInTime.trans machine.step
    (3 * rank) 4 _ _ _ matched firstFour
  have throughCheck' : EvalsToInTime machine.step (scanRankCfg data)
      (some (rejectDrainSizeCfg
        { data with
          ranks := rankTail
          sizes := List.replicate extraUnits .unit ++ .delimiter :: sizeTail
          candidate := List.replicate (rank + 1) () }))
      (4 + 3 * rank) := by
    simpa [afterMatched, List.replicate_succ, Nat.add_comm,
      List.append_assoc] using throughCheck
  let throughReject := EvalsToInTime.trans machine.step
    (4 + 3 * rank) (extraUnits + 1)
    _ _ _ throughCheck' rejected
  have throughReject' : EvalsToInTime machine.step (scanRankCfg data)
      (some (clearCandidateCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := List.replicate (rank + 1) () }))
      (extraUnits + 1 + (4 + 3 * rank)) := by
    simpa using throughReject
  have cleared' : EvalsToInTime machine.step
      (clearCandidateCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := List.replicate (rank + 1) () })
      (some (emitDelimiterCfg
        { data with
          ranks := rankTail
          sizes := sizeTail
          candidate := [] }))
      (rank + 2) := by
    simpa using cleared
  let throughClear := EvalsToInTime.trans machine.step
    (extraUnits + 1 + (4 + 3 * rank)) (rank + 2)
    _ _ _ throughReject' cleared'
  let whole := EvalsToInTime.trans machine.step
    (rank + 2 + (extraUnits + 1 + (4 + 3 * rank))) 1
    _ _ _ throughClear emitted
  convert whole using 1
  omega

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
