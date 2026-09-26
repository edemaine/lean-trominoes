/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.DelimitedDirectionVertexCounts
import LeanTrominoes.FiniteBlockIndexLookupSemantics
import LeanTrominoes.UnaryIndexedValueLookupSemantics
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Broadcasting route metadata to all vertices in polynomial time -/
noncomputable section
namespace LeanTrominoes.DelimitedDirectionDisplacement
open Computability Turing
open UnaryFieldEncoderMachine (unaryField unaryFields)

private theorem markers_word (route : List AxisDirection) :
    (word route).map isRouteEnd = FiniteBlockIndices.endingMarkers (route.length + 1) := by
  simp [word, isRouteEnd, FiniteBlockIndices.endingMarkers, List.map_map,
    Function.comp_def, List.map_const']

theorem markers_words (routes : List (List AxisDirection)) :
    (words routes).map isRouteEnd =
      FiniteBlockIndices.markers (fun route => route.length + 1) routes := by
  simp only [words, List.map_flatMap, markers_word,
    FiniteBlockIndices.markers]
  rfl

/-- One parent-route index for every vertex, including both endpoints. -/
def vertexParents (routes : List (List AxisDirection)) : List Nat :=
  FiniteBlockIndices.indices (fun route => route.length + 1) routes

def vertexParentsCompiler {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection))
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id unaryFields (fun input => vertexParents (routes input)) := by
  let scan := TM2CompositionMachine.computableInPolyTime compiler
    (FiniteUnaryFieldMap.computableInPolyTime (fun token => (isRouteEnd token).toNat))
  let physical := TM2CompositionMachine.computableInPolyTime scan
    UnaryPrefixSumsMachine.computableInPolyTime
  apply TM2ComputableInPolyTime.of_eq physical
  intro input
  simp only [vertexParents, FiniteBlockIndices.indices, FiniteBlockIndices.increments,
    FiniteUnaryFieldMap.values, ← markers_words, List.map_map, Function.comp_def]

/-- Repeat the aligned route value once at each of that route's vertices. -/
def broadcastVertices (routes : List (List AxisDirection)) (values : List Nat) : List Nat :=
  FiniteBlockIndices.broadcastValues (fun route => route.length + 1) routes values

def broadcastVerticesCompiler {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
    (routes : List Symbol → List (List AxisDirection)) (values : List Symbol → List Nat)
    (aligned : ∀ input, (routes input).length = (values input).length)
    (routesCompiler : TM2ComputableInPolyTime id id (fun input => words (routes input)))
    (valuesCompiler : TM2ComputableInPolyTime id unaryFields values) :
    TM2ComputableInPolyTime id unaryFields
      (fun input => broadcastVertices (routes input) (values input)) := by
  let physical := UnaryIndexedValueLookup.valuesComputableInPolyTime id _ _
    (vertexParentsCompiler routes routesCompiler) valuesCompiler
  apply TM2ComputableInPolyTime.of_eq physical
  intro input
  rw [UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt _ _ (by
    intro query member
    rw [← aligned input]
    exact FiniteBlockIndices.mem_indices_lt_length _ _ query member)]
  rw [vertexParents, FiniteBlockIndices.indices_eq_expected]
  exact FiniteBlockIndices.expected_lookup_eq_broadcastValues _ _ _ 0 (aligned input) (by simp)

theorem broadcastVertices_map {Index : Type} (rows : List Index)
    (directions : Index → List AxisDirection) (value : Index → Nat) :
    broadcastVertices (rows.map directions) (rows.map value) =
      rows.flatMap (fun row => List.replicate ((directions row).length + 1) (value row)) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simpa [broadcastVertices, FiniteBlockIndices.broadcastValues] using
        congrArg (List.append (List.replicate ((directions row).length + 1) (value row))) ih

/-- Route point counts, including the starting point, are a finite scan. -/
def vertexLengthsCompiler {Symbol : Type} [Fintype Symbol]
    (routes : List Symbol → List (List AxisDirection))
    (compiler : TM2ComputableInPolyTime id id (fun input => words (routes input))) :
    TM2ComputableInPolyTime id unaryFields
      (fun input => (routes input).map (fun route => route.length + 1)) := by
  let scan := FiniteBlockTransducer.computableInPolyTime (fun token : Token =>
    match token with
    | .direction _ => [UnaryFieldEncoderMachine.Symbol.unit]
    | .routeEnd => [.unit, .delimiter])
  let physical := TM2CompositionMachine.computableInPolyTime compiler scan
  apply TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
  intro input
  have one (route : List AxisDirection) :
      (word route).flatMap (fun token : Token => match token with
        | .direction _ => [UnaryFieldEncoderMachine.Symbol.unit]
        | .routeEnd => [.unit, .delimiter]) = unaryField (route.length + 1) := by
    induction route with
    | nil => rfl
    | cons direction route ih =>
        simpa [word, unaryField, List.replicate_succ] using
          congrArg (List.cons UnaryFieldEncoderMachine.Symbol.unit) ih
  simp only [id_eq, words, List.flatMap_assoc, one, unaryFields, List.flatMap_map]

end LeanTrominoes.DelimitedDirectionDisplacement
end
