/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterInput
import LeanTrominoes.UnarySuccessorEqualityFilterSelectedFieldExecution
import LeanTrominoes.UnarySuccessorEqualityFilterRejectedFieldExecution

/-! # Executing aligned lists of unary successor comparisons -/

noncomputable section

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

open StateTransition Turing

/-- Process every aligned field pair, retaining exactly those sizes that are
the successor of their ranks. -/
def fields_evalsInTime (ranks sizes : List Nat)
    (ranksTail sizesTail : List UnarySymbol) (data : TapeData)
    (valid : Valid ranks sizes)
    (ranksEq : data.ranks =
      UnaryFieldEncoderMachine.unaryFields ranks ++ ranksTail)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryFields sizes ++ sizesTail)
    (candidateEq : data.candidate = []) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := ranksTail
          sizes := sizesTail
          candidate := []
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (selectedValues ranks sizes)).reverse ++
                data.outputReverse }))
      (fieldsTime ranks sizes) := by
  induction valid generalizing data with
  | nil =>
      rcases data with
        ⟨input, rankReverse, rankTokens, sizeReverse, sizeTokens,
          candidate, outputReverse, output⟩
      change rankTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ ranksTail at ranksEq
      change sizeTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ sizesTail at sizesEq
      change candidate = [] at candidateEq
      simp only [UnaryFieldEncoderMachine.unaryFields_nil,
        List.nil_append] at ranksEq sizesEq
      subst rankTokens
      subst sizeTokens
      subst candidate
      have zero := UnaryFieldEncoderMachine.zeroSteps
        (transition := machine.step)
        (scanRankCfg
          ⟨input, rankReverse, ranksTail, sizeReverse, sizesTail,
            [], outputReverse, output⟩)
      simpa [fieldsTime, selectedValues] using zero
  | @cons rank size ranks sizes rankLtSize valid induction =>
      let ranksRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields ranks ++ ranksTail
      let sizesRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields sizes ++ sizesTail
      have rankFieldEq : data.ranks =
          UnaryFieldEncoderMachine.unaryField rank ++ ranksRemaining := by
        simpa [ranksRemaining, UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using ranksEq
      have sizeFieldEq : data.sizes =
          UnaryFieldEncoderMachine.unaryField size ++ sizesRemaining := by
        simpa [sizesRemaining, UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using sizesEq
      by_cases selected : size = rank + 1
      · let nextData : TapeData :=
          { data with
            ranks := ranksRemaining
            sizes := sizesRemaining
            candidate := []
            outputReverse :=
              (UnaryFieldEncoderMachine.unaryField (rank + 1)).reverse ++
                data.outputReverse }
        have first := selectedField_evalsInTime rank
          ranksRemaining sizesRemaining data rankFieldEq
          (by simpa [selected] using sizeFieldEq) candidateEq
        have first' : EvalsToInTime machine.step (scanRankCfg data)
            (some (scanRankCfg nextData)) (fieldTime rank size) := by
          simpa [nextData, selected] using first
        have rest := induction nextData rfl rfl rfl
        let composed := EvalsToInTime.trans machine.step
          (fieldTime rank size) (fieldsTime ranks sizes)
          _ _ _ first' rest
        convert composed using 1 <;>
          simp [nextData, fieldsTime, selectedValues, selectedValue, selected,
            UnaryFieldEncoderMachine.unaryFields_cons,
            List.reverse_append, List.append_assoc, Nat.add_comm]
      · let extraUnits := size - (rank + 2)
        have sizeEq : size = rank + 2 + extraUnits := by
          simp only [extraUnits]
          omega
        let nextData : TapeData :=
          { data with
            ranks := ranksRemaining
            sizes := sizesRemaining
            candidate := []
            outputReverse := .delimiter :: data.outputReverse }
        have first := rejectedField_evalsInTime rank extraUnits
          ranksRemaining sizesRemaining data rankFieldEq
          (by simpa [sizeEq] using sizeFieldEq) candidateEq
        have first' : EvalsToInTime machine.step (scanRankCfg data)
            (some (scanRankCfg nextData)) (fieldTime rank size) := by
          simpa [nextData, sizeEq] using first
        have rest := induction nextData rfl rfl rfl
        let composed := EvalsToInTime.trans machine.step
          (fieldTime rank size) (fieldsTime ranks sizes)
          _ _ _ first' rest
        convert composed using 1 <;>
          simp [nextData, fieldsTime, selectedValues, selectedValue, selected,
            UnaryFieldEncoderMachine.unaryFields_cons,
            UnaryFieldEncoderMachine.unaryField,
            List.append_assoc, Nat.add_comm]

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
