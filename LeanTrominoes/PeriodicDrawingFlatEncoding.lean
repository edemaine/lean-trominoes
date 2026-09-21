/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicDrawingArithmeticFields

/-! # A flat binary drawing encoding with cached segment records

The geometry prefix stores the period, a coordinate bound, all indexed
segments, and vertices. A length-delimited route trailer preserves empty and
singleton routes, so decoding recovers the entire original drawing.
-/
namespace LeanTrominoes.PeriodicGridDrawing.Arithmetic
open PeriodicStripFlatEncoding

def decodeRoutes : Nat → List Nat → Option (List (List Cell) × List Nat)
  | 0, rest => some ([],rest)
  | count+1, size::rest => do
      let (route,rest) ← decodeCells size rest
      let (routes,rest) ← decodeRoutes count rest
      return (route::routes,rest)
  | _+1, [] => none

theorem decodeRoutes_append (routes : List (List Cell)) (rest : List Nat) :
    decodeRoutes routes.length (routes.flatMap routeFields ++ rest) = some (routes,rest) := by
  induction routes with
  | nil => rfl
  | cons route routes ih =>
    simp only [List.length_cons,List.flatMap_cons,routeFields,List.cons_append,List.append_assoc,decodeRoutes]
    change ((decodeCells route.length (route.flatMap cellFields ++ (routes.flatMap routeFields ++ rest))).bind _) = _
    rw [decodeCells_flatMap_cellFields_append]
    simp [ih]

def decodeFields : List Nat → Option PeriodicGridDrawing
  | period :: _ :: segments :: vertices :: rest => do
      if period=0 then none else do
        let (positions,rest) ← decodeCells vertices (rest.drop (6*segments))
        match rest with
        | count::rest => do
            let (routes,rest) ← decodeRoutes count rest
            if rest=[] then some ⟨period-1,positions,routes⟩ else none
        | [] => none
  | _ => none

theorem decodeFields_fields (d : PeriodicGridDrawing) : decodeFields (fields d) = some d := by
  have period : d.gridSize≠0 := by simp [gridSize]
  have drop : (d.indexedSegments.flatMap segmentFields ++
      (d.vertexPositions.flatMap pointFields ++ trailer d)).drop (6*d.indexedSegments.length) =
        d.vertexPositions.flatMap pointFields ++ trailer d := by
    rw [← segmentFields_length,List.drop_left]
  simp only [fields,List.cons_append,List.nil_append,decodeFields,period,if_false,drop]
  change ((decodeCells d.vertexPositions.length
    (d.vertexPositions.flatMap cellFields ++ trailer d)).bind _) = _
  rw [decodeCells_flatMap_cellFields_append]
  simp only [Option.bind_some,trailer]
  have routes := decodeRoutes_append d.edgeRoutes []
  simp only [List.append_nil] at routes
  rw [routes]
  cases d
  rfl

def finEncoding : _root_.Computability.FinEncoding PeriodicGridDrawing :=
  PeriodicCNFFlatEncoding.finEncodingOfFields fields decodeFields decodeFields_fields

end LeanTrominoes.PeriodicGridDrawing.Arithmetic
