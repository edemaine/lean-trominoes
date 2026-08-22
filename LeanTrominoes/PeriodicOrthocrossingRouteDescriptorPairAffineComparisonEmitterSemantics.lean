/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonEmitter

/-! # Exact semantics of signed affine comparison-word emission -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PeriodicCNF
open PeriodicCNF.AffineTemplateEmitterMachine
open PeriodicCNF.AffineEmitterPipeline
open PeriodicCNF.UnaryProgramTokens

theorem selectedCount_fieldToken
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (side : Side) (field : Fin 11) :
    UnaryPolynomialPaddingMachine.selectedCount
        (fun token => decide (token = .unit side field)) tokens =
      tokenFieldValue tokens side field := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      rw [UnaryPolynomialPaddingMachine.selectedCount_cons]
      by_cases tokenEq : token = .unit side field
      · subst token
        simp [tokenFieldValue, induction, Nat.add_comm]
      · simp [tokenEq, tokenFieldValue, induction]

theorem selectedCount_false
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    UnaryPolynomialPaddingMachine.selectedCount
        (fun _ : RouteDescriptorPairFieldTags.Token => false) tokens = 0 := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      simp [UnaryPolynomialPaddingMachine.selectedCount, induction]

theorem positionTokens_replicate_fixed
    (output : PeriodicCNF.UnaryProgramTokens.Token)
    (amount position : Nat) :
    positionTokens (List.replicate amount (.fixed output)) position =
      List.replicate amount output := by
  induction amount with
  | zero => rfl
  | succ amount induction =>
      rw [List.replicate_succ]
      unfold positionTokens at induction ⊢
      simp only [List.flatMap_cons, Recipe.tokens]
      rw [induction, List.replicate_succ]
      rfl

theorem positionRangeTokens_replicate_fixed
    (output : PeriodicCNF.UnaryProgramTokens.Token)
    (amount first count : Nat) :
    positionRangeTokens (List.replicate amount (.fixed output))
        first count =
      List.replicate (amount * count) output := by
  induction count generalizing first with
  | zero => rfl
  | succ count induction =>
      rw [positionRangeTokens_succ,
        positionTokens_replicate_fixed, induction,
        ← List.replicate_add]
      congr 1
      rw [Nat.mul_succ, Nat.add_comm]

@[simp] theorem fixedEndingPhase_emitted
    (ending : List PeriodicCNF.UnaryProgramTokens.Token)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (fixedEndingPhase ending).emitted tokens = ending := by
  unfold fixedEndingPhase Phase.emitted
  rw [selectedCount_false]
  rfl

theorem Term.countPhase_emitted
    (output : PeriodicCNF.UnaryProgramTokens.Token)
    (magnitude : Int → Nat) (expressionTerm : Term)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (expressionTerm.countPhase output magnitude).emitted tokens =
      List.replicate
        (magnitude expressionTerm.coefficient *
          tokenFieldValue tokens expressionTerm.side expressionTerm.field)
        output := by
  unfold Term.countPhase Phase.emitted
  rw [selectedCount_fieldToken]
  rw [positionRangeTokens_replicate_fixed]
  exact List.append_nil _

theorem emittedAll_append
    (first second :
      List (AffineEmitterPipeline.Phase RouteDescriptorPairFieldTags.Token))
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    AffineEmitterPipeline.emittedAll (first ++ second) tokens =
      AffineEmitterPipeline.emittedAll first tokens ++
        AffineEmitterPipeline.emittedAll second tokens := by
  induction first with
  | nil => rfl
  | cons phase first induction =>
      simp [AffineEmitterPipeline.emittedAll, induction, List.append_assoc]

theorem emittedAll_countPhases
    (output : PeriodicCNF.UnaryProgramTokens.Token)
    (magnitude : Int → Nat) (terms : List Term)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    AffineEmitterPipeline.emittedAll
        (terms.map (Term.countPhase output magnitude)) tokens =
      List.replicate
        ((terms.map fun expressionTerm =>
          magnitude expressionTerm.coefficient *
            tokenFieldValue tokens expressionTerm.side
              expressionTerm.field).sum)
        output := by
  induction terms with
  | nil => rfl
  | cons expressionTerm terms induction =>
      simp only [List.map_cons, List.sum_cons,
        AffineEmitterPipeline.emittedAll]
      rw [expressionTerm.countPhase_emitted, induction,
        ← List.replicate_add]

/-- The phase pipeline emits exactly the five-block program-token encoding of
the positive and negative affine totals. -/
theorem Expression.emittedAll_comparisonPhases
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    AffineEmitterPipeline.emittedAll expression.comparisonPhases tokens =
      [.clauseMarker] ++
        List.replicate
          (expression.positiveCount (tokenFieldValue tokens)) .atomUnit ++
        [.freshEnd] ++
        List.replicate
          (expression.negativeCount (tokenFieldValue tokens)) .freshUnit ++
        [.atomEnd] := by
  unfold Expression.comparisonPhases
  rw [emittedAll_append, emittedAll_append,
    emittedAll_append, emittedAll_append]
  rw [emittedAll_countPhases .atomUnit Int.toNat,
    emittedAll_countPhases .freshUnit
      (fun coefficient => (-coefficient).toNat)]
  simp only [AffineEmitterPipeline.emittedAll, fixedEndingPhase_emitted,
    List.append_nil]
  unfold Expression.positiveCount Expression.negativeCount
  rw [List.replicate_add, List.replicate_add]
  simp only [List.append_assoc]
  rfl

@[simp] theorem translateComparisonTokens_cons
    (token : PeriodicCNF.UnaryProgramTokens.Token)
    (tokens : List PeriodicCNF.UnaryProgramTokens.Token) :
    translateComparisonTokens (token :: tokens) =
      comparisonTokenBlock token ++ translateComparisonTokens tokens := by
  rfl

@[simp] theorem translateComparisonTokens_append
    (first second : List PeriodicCNF.UnaryProgramTokens.Token) :
    translateComparisonTokens (first ++ second) =
      translateComparisonTokens first ++ translateComparisonTokens second := by
  simp [translateComparisonTokens]

@[simp] theorem translateComparisonTokens_replicate_atomUnit
    (count : Nat) :
    translateComparisonTokens (List.replicate count .atomUnit) =
      List.replicate count (.firstBit false) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ]
      change .firstBit false ::
          translateComparisonTokens (List.replicate count .atomUnit) =
        .firstBit false :: List.replicate count (.firstBit false)
      rw [induction]

@[simp] theorem translateComparisonTokens_replicate_freshUnit
    (count : Nat) :
    translateComparisonTokens (List.replicate count .freshUnit) =
      List.replicate count (.secondBit false) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.replicate_succ]
      change .secondBit false ::
          translateComparisonTokens (List.replicate count .freshUnit) =
        .secondBit false :: List.replicate count (.secondBit false)
      rw [induction]

/-- The translated physical word is the canonical delimiter encoding of the
singleton positive/negative unary pair. -/
theorem Expression.comparisonTokens_eq_encode
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expression.comparisonTokens tokens =
      DelimitedBinaryWordPairs.encode (expression.comparisonInput tokens) := by
  unfold Expression.comparisonTokens Expression.comparisonInput
    Expression.tokenCounts
  rw [expression.emittedAll_comparisonPhases]
  simp [comparisonTokenBlock,
    DelimitedBinaryWordPairs.encode, DelimitedBinaryWordPairs.pairTokens]
  rfl

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
