/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksFieldExecution

/-! # Executing aligned lists of unary rotated ranks -/

noncomputable section

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

open StateTransition Turing

def fields_evalsInTime (ranks sizes : List Nat)
    (ranksTail sizesTail : List UnarySymbol) (data : TapeData)
    (valid : Valid ranks sizes)
    (ranksEq : data.ranks =
      UnaryFieldEncoderMachine.unaryFields ranks ++ ranksTail)
    (sizesEq : data.sizes =
      UnaryFieldEncoderMachine.unaryFields sizes ++ sizesTail) :
    EvalsToInTime machine.step (scanRankCfg data)
      (some (scanRankCfg
        { data with
          ranks := ranksTail
          sizes := sizesTail
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryFields
              (rotatedRanks ranks sizes)).reverse ++
                data.outputReverse }))
      (fieldsTime ranks sizes) := by
  induction valid generalizing data with
  | nil =>
      rcases data with
        ⟨input, rankReverse, rankTokens, sizeReverse, sizeTokens,
          outputReverse, output⟩
      change rankTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ ranksTail at ranksEq
      change sizeTokens =
        UnaryFieldEncoderMachine.unaryFields [] ++ sizesTail at sizesEq
      simp only [UnaryFieldEncoderMachine.unaryFields_nil,
        List.nil_append] at ranksEq sizesEq
      subst rankTokens
      subst sizeTokens
      have zero := EvalsToInTime.refl machine.step
        (scanRankCfg
          ⟨input, rankReverse, ranksTail, sizeReverse, sizesTail,
            outputReverse, output⟩)
      simpa [fieldsTime, rotatedRanks] using zero
  | @cons rank size ranks sizes rankLtSize valid induction =>
      let ranksRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields ranks ++ ranksTail
      let sizesRemaining : List UnarySymbol :=
        UnaryFieldEncoderMachine.unaryFields sizes ++ sizesTail
      let nextData : TapeData :=
        { data with
          ranks := ranksRemaining
          sizes := sizesRemaining
          outputReverse :=
            (UnaryFieldEncoderMachine.unaryField
              (rotatedRank rank size)).reverse ++ data.outputReverse }
      have rankFieldEq : data.ranks =
          UnaryFieldEncoderMachine.unaryField rank ++ ranksRemaining := by
        simpa [ranksRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using ranksEq
      have sizeFieldEq : data.sizes =
          UnaryFieldEncoderMachine.unaryField size ++ sizesRemaining := by
        simpa [sizesRemaining,
          UnaryFieldEncoderMachine.unaryFields_cons,
          List.append_assoc] using sizesEq
      have first := field_evalsInTime rank size ranksRemaining
        sizesRemaining data rankLtSize rankFieldEq sizeFieldEq
      have first' : EvalsToInTime machine.step (scanRankCfg data)
          (some (scanRankCfg nextData)) (fieldTime rank size) := by
        simpa [nextData] using first
      have rest := induction nextData rfl rfl
      have whole := EvalsToInTime.trans machine.step
        (fieldTime rank size) (fieldsTime ranks sizes)
        _ _ _ first' rest
      simpa [nextData, fieldsTime, rotatedRanks,
        UnaryFieldEncoderMachine.unaryFields_cons,
        List.reverse_append, List.append_assoc,
        Nat.add_comm] using whole

end UnaryRotatedRanksMachine
end LeanTrominoes
