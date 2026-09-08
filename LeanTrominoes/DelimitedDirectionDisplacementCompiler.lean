/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.SignedUnaryCoordinateRefinementCompiler

/-! # Signed displacement columns from delimited cardinal-direction words -/

noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing
abbrev Token := DelimitedRouteJoin.Token

/-- One end marker per route, including empty routes. -/
def word (directions : List AxisDirection) : List Token :=
  directions.map (fun direction => (.direction direction : Token)) ++ [.routeEnd]

def words (routes : List (List AxisDirection)) : List Token := routes.flatMap word

def axisDirection (horizontal positive : Bool) : AxisDirection :=
  if horizontal then (if positive then .east else .west)
  else (if positive then .north else .south)

def countBlock (direction : AxisDirection) : Token → List UnaryFieldEncoderMachine.Symbol
  | .direction next => if next = direction then [.unit] else []
  | .routeEnd => [.delimiter]

private theorem countBlock_directions (direction : AxisDirection) (directions : List AxisDirection) :
    (directions.map (fun direction => (.direction direction : Token))).flatMap (countBlock direction) =
      List.replicate (directions.count direction) UnaryFieldEncoderMachine.Symbol.unit := by
  induction directions with
  | nil => rfl
  | cons next directions induction =>
    by_cases equal : next = direction
    · subst next
      simp [countBlock, induction, List.replicate_succ]
    · simp [countBlock, equal, induction]

theorem countBlock_words (direction : AxisDirection) (routes : List (List AxisDirection)) :
    (words routes).flatMap (countBlock direction) =
      UnaryFieldEncoderMachine.unaryFields (routes.map (List.count direction)) := by
  induction routes with
  | nil => rfl
  | cons route routes induction =>
    simp only [words, List.flatMap_cons, List.map_cons, List.flatMap_append] at induction ⊢
    rw [induction]
    simp [word, List.flatMap_append, countBlock_directions, countBlock,
      UnaryFieldEncoderMachine.unaryFields, UnaryFieldEncoderMachine.unaryField]

/-- Counting one cardinal direction per route is a finite block scan. -/
noncomputable def countsComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection)) (direction : AxisDirection)
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => (routes input).map (List.count direction)) := by
  let physical := TM2CompositionMachine.computableInPolyTime compiler
    (FiniteBlockTransducer.computableInPolyTime (countBlock direction))
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (fun input => countBlock_words direction (routes input))

def component (horizontal : Bool) (point : Cell) : Int :=
  if horizontal then point.1 else point.2

def displacement (horizontal : Bool) (directions : List AxisDirection) : Int :=
  (directions.map (fun direction => component horizontal direction.step)).sum

/-- The signed geometric displacement is the difference of opposing counts. -/
theorem displacement_eq_counts (horizontal : Bool) (directions : List AxisDirection) :
    displacement horizontal directions =
      (directions.count (axisDirection horizontal true) : Int) -
        directions.count (axisDirection horizontal false) := by
  induction directions with
  | nil => simp [displacement]
  | cons direction directions induction =>
    simp only [displacement, List.map_cons, List.sum_cons] at induction ⊢
    rw [induction]
    cases horizontal <;> cases direction <;>
      simp [component, axisDirection, AxisDirection.step] <;> omega

def values (horizontal keepPositive : Bool) (routes : List (List AxisDirection)) : List Nat :=
  UnaryAlignedDifference.values keepPositive
    (routes.map (List.count (axisDirection horizontal true)))
    (routes.map (List.count (axisDirection horizontal false)))

noncomputable def valuesComputableInPolyTime {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection)) (horizontal keepPositive : Bool)
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun input => values horizontal keepPositive (routes input)) :=
  UnaryAlignedDifference.nativeListComputableInPolyTime keepPositive
    (fun input => (routes input).map (List.count (axisDirection horizontal true)))
    (fun input => (routes input).map (List.count (axisDirection horizontal false)))
    (fun input => by simp only [List.length_map])
    (countsComputableInPolyTime routes (axisDirection horizontal true) compiler)
    (countsComputableInPolyTime routes (axisDirection horizontal false) compiler)

theorem values_eq_displacements (horizontal keepPositive : Bool) (routes : List (List AxisDirection)) :
    values horizontal keepPositive routes =
      routes.map (fun route => SignedUnaryCoordinateRefinement.field keepPositive
        (displacement horizontal route)) := by
  rw [values, UnaryAlignedDifference.values_map]
  simp only [displacement_eq_counts, SignedUnaryCoordinateRefinement.field]

@[simp] theorem values_length (horizontal keepPositive : Bool) (routes : List (List AxisDirection)) :
    (values horizontal keepPositive routes).length = routes.length := by
  rw [values_eq_displacements, List.length_map]

end LeanTrominoes.DelimitedDirectionDisplacement
end
