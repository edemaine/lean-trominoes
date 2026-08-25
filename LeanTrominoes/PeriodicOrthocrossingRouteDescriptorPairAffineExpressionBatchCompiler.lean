/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineComparisonEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineSignedCountSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTags

/-! # Batched canonical unary evaluation of affine expressions -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags
open PeriodicCNF.AffineEmitterPipeline

/-- Unary positive/negative total pair for one affine expression. -/
def Expression.unaryPair (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List Bool × List Bool :=
  let counts := expression.tokenCounts tokens
  (List.replicate counts.1 false, List.replicate counts.2 false)

def expressionsComparisonPhases : List Expression →
    List (PeriodicCNF.AffineEmitterPipeline.Phase
      RouteDescriptorPairFieldTags.Token)
  | [] => []
  | expression :: expressions =>
      expression.comparisonPhases ++
        expressionsComparisonPhases expressions

def expressionsComparisonInput (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWordPairs.Input :=
  ⟨expressions.map fun expression => expression.unaryPair tokens⟩

def expressionsComparisonTokens (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWordPairs.Token :=
  translateComparisonTokens
    (emittedAll (expressionsComparisonPhases expressions) tokens)

@[simp] theorem expressionsComparisonTokens_nil
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expressionsComparisonTokens [] tokens = [] :=
  rfl

@[simp] theorem expressionsComparisonTokens_cons
    (expression : Expression) (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expressionsComparisonTokens (expression :: expressions) tokens =
      expression.comparisonTokens tokens ++
        expressionsComparisonTokens expressions tokens := by
  change translateComparisonTokens
      (emittedAll
        (expression.comparisonPhases ++
          expressionsComparisonPhases expressions) tokens) = _
  rw [emittedAll_append, translateComparisonTokens_append]
  rfl

@[simp] theorem Expression.comparisonInput_eq_unaryPair
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expression.comparisonInput tokens =
      ⟨[expression.unaryPair tokens]⟩ := by
  rfl

@[simp] theorem Expression.comparisonTokens_eq_pairTokens
    (expression : Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expression.comparisonTokens tokens =
      DelimitedBinaryWordPairs.pairTokens
        (expression.unaryPair tokens) := by
  rw [expression.comparisonTokens_eq_encode,
    expression.comparisonInput_eq_unaryPair]
  unfold DelimitedBinaryWordPairs.encode
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The batched physical word is the delimiter encoding of all affine unary
total pairs in expression order. -/
theorem expressionsComparisonTokens_eq_encode
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    expressionsComparisonTokens expressions tokens =
      DelimitedBinaryWordPairs.encode
        (expressionsComparisonInput expressions tokens) := by
  induction expressions with
  | nil => rfl
  | cons expression expressions induction =>
      rw [expressionsComparisonTokens_cons,
        expression.comparisonTokens_eq_pairTokens]
      change _ = DelimitedBinaryWordPairs.pairTokens
          (expression.unaryPair tokens) ++
        DelimitedBinaryWordPairs.encode
          (expressionsComparisonInput expressions tokens)
      rw [induction]

def expressionsComparisonTokensComputableInPolyTime
    (expressions : List Expression) :
    TM2ComputableInPolyTime id id
      (expressionsComparisonTokens expressions) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (emittedAllComputableInPolyTime
      (expressionsComparisonPhases expressions))
    translateComparisonTokensComputableInPolyTime
  unfold expressionsComparisonTokens
  exact composed

def expressionsComparisonInputComputableInPolyTime
    (expressions : List Expression) :
    @TM2ComputableInPolyTime
      (List RouteDescriptorPairFieldTags.Token)
      DelimitedBinaryWordPairs.Input
      RouteDescriptorPairFieldTags.Token DelimitedBinaryWordPairs.Token
      id DelimitedBinaryWordPairs.encode
      (expressionsComparisonInput expressions) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (expressionsComparisonTokensComputableInPolyTime expressions)
    (expressionsComparisonTokens_eq_encode expressions)

def normalizedFields (keepPositive : Bool)
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Nat :=
  DelimitedBinaryWordPairExcessMachine.excesses keepPositive
    (expressionsComparisonInput expressions tokens)

def normalizedFieldsComputableInPolyTime (keepPositive : Bool)
    (expressions : List Expression) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (normalizedFields keepPositive expressions) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (expressionsComparisonInputComputableInPolyTime expressions)
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime keepPositive)
  unfold normalizedFields
  exact composed

@[simp] theorem excess_replicate_eq_toNat (positive negative : Nat) :
    DelimitedBinaryWordPairExcessMachine.excess true
        (List.replicate positive false) (List.replicate negative false) =
      (signedOfUnaryFields positive negative).toNat := by
  simp [DelimitedBinaryWordPairExcessMachine.excess, signedOfUnaryFields]

@[simp] theorem excess_replicate_eq_neg_toNat (positive negative : Nat) :
    DelimitedBinaryWordPairExcessMachine.excess false
        (List.replicate positive false) (List.replicate negative false) =
      (-signedOfUnaryFields positive negative).toNat := by
  simp [DelimitedBinaryWordPairExcessMachine.excess, signedOfUnaryFields]

/-- Positive normalization evaluates every affine expression exactly. -/
@[simp] theorem normalizedFields_true_eq
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    normalizedFields true expressions tokens =
      expressions.map fun expression =>
        (expression.eval (tokenFieldValue tokens)).toNat := by
  unfold normalizedFields DelimitedBinaryWordPairExcessMachine.excesses
    expressionsComparisonInput
  rw [List.map_map]
  apply List.map_congr_left
  intro expression expressionMember
  simp only [Function.comp_apply, Expression.unaryPair,
    excess_replicate_eq_toNat]
  unfold Expression.tokenCounts
  rw [Expression.signedOfUnaryFields_counts]

/-- Negative normalization evaluates every negated affine expression
exactly. -/
@[simp] theorem normalizedFields_false_eq
    (expressions : List Expression)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    normalizedFields false expressions tokens =
      expressions.map fun expression =>
        (-expression.eval (tokenFieldValue tokens)).toNat := by
  unfold normalizedFields DelimitedBinaryWordPairExcessMachine.excesses
    expressionsComparisonInput
  rw [List.map_map]
  apply List.map_congr_left
  intro expression expressionMember
  simp only [Function.comp_apply, Expression.unaryPair,
    excess_replicate_eq_neg_toNat]
  unfold Expression.tokenCounts
  rw [Expression.signedOfUnaryFields_counts]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing

end
