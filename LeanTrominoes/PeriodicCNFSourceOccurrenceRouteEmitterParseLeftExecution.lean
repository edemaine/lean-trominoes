/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterExecutionSupport
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteEmitterParseLeftSteps

/-! # Execution of left-input parsing for source-occurrence route emission -/

noncomputable section

namespace LeanTrominoes

open StateTransition

namespace PeriodicCNF.SourceOccurrenceRouteEmitterMachine

open SourceOccurrenceRouteTokens

def countTape (selected : OccurrenceToken → Bool)
    (tokens : List OccurrenceToken) : List Unit :=
  List.replicate
    (UnaryPolynomialPaddingMachine.selectedCount selected tokens) ()

@[simp] private theorem replicate_unit_one_add_append (count : Nat)
    (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      List.replicate (1 + count) () ++ tail := by
  calc
    List.replicate count () ++ () :: tail =
        (List.replicate count () ++ List.replicate 1 ()) ++ tail := by
      simp [List.append_assoc]
    _ = List.replicate (count + 1) () ++ tail := by
      rw [List.replicate_add]
    _ = List.replicate (1 + count) () ++ tail := by
      rw [Nat.add_comm count 1]

def scanLeft_evalsInTime (cursor : Cursor)
    (tokens : List OccurrenceToken) (tail : List InputSymbol)
    (data : TapeData)
    (inputEq :
      data.input = tokens.map .left ++ .separator :: tail) :
    EvalsToInTime machine.step (scanLeftCfg cursor data)
      (some (scanRightCfg cursor
        { data with
          input := tail
          occurrenceReverse := tokens.reverse ++ data.occurrenceReverse
          clauseCount := countTape isClause tokens ++ data.clauseCount
          literalCount := countTape isLiteral tokens ++ data.literalCount }))
      (2 * tokens.length + 1) := by
  induction tokens generalizing data with
  | nil =>
      have step :=
        step_scanLeft_separator cursor data tail (by simpa using inputEq)
      simpa [countTape, UnaryPolynomialPaddingMachine.selectedCount] using
        oneStep step
  | cons token tokens induction =>
      have inputHead : data.input =
          .left token :: (tokens.map .left ++ .separator :: tail) := by
        simpa [List.map_cons] using inputEq
      let afterPop : TapeData :=
        { data with input := tokens.map .left ++ .separator :: tail }
      let popped := oneStep
        (step_scanLeft_left cursor data token
          (tokens.map .left ++ .separator :: tail) inputHead)
      cases token with
      | clause arity =>
          let nextData : TapeData :=
            { afterPop with
              occurrenceReverse := .clause arity :: data.occurrenceReverse
              clauseCount := () :: data.clauseCount }
          let pushed := oneStep
            (step_pushOccurrence_clause cursor afterPop arity)
          let rest := induction nextData rfl
          let firstTwo := EvalsToInTime.trans machine.step
            1 1 _ _ _ popped pushed
          let whole := EvalsToInTime.trans machine.step
            2 (2 * tokens.length + 1) _ _ _ firstTwo rest
          simpa [whole, nextData, afterPop, countTape,
            UnaryPolynomialPaddingMachine.selectedCount,
            isClause, isLiteral, List.reverse_cons, Nat.mul_add,
            List.append_assoc, Nat.add_assoc] using whole
      | literal index =>
          let nextData : TapeData :=
            { afterPop with
              occurrenceReverse := .literal index :: data.occurrenceReverse
              literalCount := () :: data.literalCount }
          let pushed := oneStep
            (step_pushOccurrence_literal cursor afterPop index)
          let rest := induction nextData rfl
          let firstTwo := EvalsToInTime.trans machine.step
            1 1 _ _ _ popped pushed
          let whole := EvalsToInTime.trans machine.step
            2 (2 * tokens.length + 1) _ _ _ firstTwo rest
          simpa [whole, nextData, afterPop, countTape,
            UnaryPolynomialPaddingMachine.selectedCount,
            isClause, isLiteral, List.reverse_cons, Nat.mul_add,
            List.append_assoc, Nat.add_assoc] using whole
      | offsetNext value =>
          let nextData : TapeData :=
            { afterPop with
              occurrenceReverse :=
                .offsetNext value :: data.occurrenceReverse }
          let pushed := oneStep
            (step_pushOccurrence_offset cursor afterPop value)
          let rest := induction nextData rfl
          let firstTwo := EvalsToInTime.trans machine.step
            1 1 _ _ _ popped pushed
          let whole := EvalsToInTime.trans machine.step
            2 (2 * tokens.length + 1) _ _ _ firstTwo rest
          simpa [whole, nextData, afterPop, countTape,
            UnaryPolynomialPaddingMachine.selectedCount,
            isClause, isLiteral, List.reverse_cons, Nat.mul_add,
            List.append_assoc, Nat.add_assoc] using whole
      | literalEnd =>
          let nextData : TapeData :=
            { afterPop with
              occurrenceReverse := .literalEnd :: data.occurrenceReverse }
          let pushed := oneStep
            (step_pushOccurrence_literalEnd cursor afterPop)
          let rest := induction nextData rfl
          let firstTwo := EvalsToInTime.trans machine.step
            1 1 _ _ _ popped pushed
          let whole := EvalsToInTime.trans machine.step
            2 (2 * tokens.length + 1) _ _ _ firstTwo rest
          simpa [whole, nextData, afterPop, countTape,
            UnaryPolynomialPaddingMachine.selectedCount,
            isClause, isLiteral, List.reverse_cons, Nat.mul_add,
            List.append_assoc, Nat.add_assoc] using whole

end PeriodicCNF.SourceOccurrenceRouteEmitterMachine
end LeanTrominoes
