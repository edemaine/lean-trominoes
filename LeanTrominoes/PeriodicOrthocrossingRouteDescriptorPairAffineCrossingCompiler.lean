/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCrossingMarkerBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScan
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchCompiler

/-! # Polynomial-time finite affine crossing scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- One fixed predicate combines both route-shape guards with one occurrence-
pair crossing test. -/
def guardedCrossingPredicate
    (shapes : RouteShape × RouteShape)
    (occurrences : Occurrence × Occurrence) : Predicate :=
  all [shapes.1.guard .first, shapes.2.guard .second,
    crossingPredicate occurrences.1 occurrences.2]

/-- All guarded occurrence tests belonging to one route-shape pair. -/
def routeShapePairCrossingPredicates
    (shapes : RouteShape × RouteShape) : List Predicate :=
  (shapes.1.occurrences .first ×ˢ shapes.2.occurrences .second).map
    (guardedCrossingPredicate shapes)

/-- Complete compact predicate list for the twenty-eight-squared affine
shape scan. -/
def affineCrossingPredicates : List Predicate :=
  (allRouteShapes ×ˢ allRouteShapes).flatMap
    routeShapePairCrossingPredicates

@[simp] theorem guardedCrossingPredicate_evalTokens
    (shapes : RouteShape × RouteShape)
    (occurrences : Occurrence × Occurrence)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (guardedCrossingPredicate shapes occurrences).evalTokens tokens =
      (routeShapePairEnabled tokens shapes &&
        (crossingPredicate occurrences.1 occurrences.2).evalTokens tokens) := by
  simp [guardedCrossingPredicate, routeShapePairEnabled,
    Predicate.evalTokens, all, Predicate.eval]
  rw [Bool.and_assoc]

/-- Thirteen-marker blocks count exactly the accepted elements of any finite
Boolean-filtered list. -/
theorem flatMap_truthMarkerBlock_eq_replicate
    {Marker Item : Type} (marker : Marker)
    (predicate : Item → Bool) (items : List Item) :
    items.flatMap (fun item =>
      truthMarkerBlock marker (predicate item)) =
        List.replicate (13 * (items.filter predicate).length) marker := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      unfold truthMarkerBlock at induction ⊢
      rw [List.flatMap_cons]
      cases accepted : predicate item with
      | false =>
          simp only [Bool.false_eq_true,
            ↓reduceIte, List.nil_append]
          rw [induction]
          congr 2
          simp only [List.filter_cons, accepted, Bool.false_eq_true,
            ↓reduceIte]
      | true =>
          simp only [↓reduceIte]
          rw [induction, ← List.replicate_add]
          congr 2
          simp only [List.filter_cons, accepted, ↓reduceIte,
            List.length_cons]
          omega

@[simp] theorem filter_const_false
    {Item : Type} (items : List Item) :
    items.filter (fun _ => false) = [] := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.filter_cons, Bool.false_eq_true, ↓reduceIte,
        induction]

/-- The predicate sublist for one shape pair emits exactly thirteen markers
per guarded crossing counted by the original affine scan. -/
theorem routeShapePairCrossingPredicates_flatMap
    {Marker : Type} (marker : Marker)
    (shapes : RouteShape × RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (routeShapePairCrossingPredicates shapes).flatMap
        (fun predicate =>
          truthMarkerBlock marker (predicate.evalTokens tokens)) =
      List.replicate
        (13 * guardedRouteShapePairCrossingCount tokens shapes) marker := by
  unfold routeShapePairCrossingPredicates
  rw [List.flatMap_map]
  rw [flatMap_truthMarkerBlock_eq_replicate]
  congr 2
  unfold guardedRouteShapePairCrossingCount routeShapePairCrossingCount
    List.filteredProductCount
  cases enabled : routeShapePairEnabled tokens shapes with
  | false =>
      simp only [guardedCrossingPredicate_evalTokens, enabled,
        Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        filter_const_false, List.length_nil]
  | true =>
      simp only [guardedCrossingPredicate_evalTokens, enabled,
        Bool.true_and, ↓reduceIte]

/-- `flatMap` is the flattening of the corresponding mapped block list. -/
theorem flatMap_eq_flatten_map
    {Source Target : Type} (blocks : Source → List Target)
    (items : List Source) :
    items.flatMap blocks = (items.map blocks).flatten := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        induction]

/-- The complete compact predicate list emits the original affine crossing-
marker word exactly on every tagged input. -/
theorem affineCrossingPredicates_flatMap
    {Marker : Type} (marker : Marker)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    affineCrossingPredicates.flatMap
        (fun predicate =>
          truthMarkerBlock marker (predicate.evalTokens tokens)) =
      affineCrossingMarkers marker tokens := by
  unfold affineCrossingPredicates
  rw [List.flatMap_assoc]
  simp_rw [routeShapePairCrossingPredicates_flatMap marker]
  unfold affineCrossingMarkers affineCrossingCount
  rw [flatMap_eq_flatten_map]
  have exact := flatten_map_replicate_thirteen marker
    ((allRouteShapes ×ˢ allRouteShapes).map
      (guardedRouteShapePairCrossingCount tokens))
  have blockMapEq :
      (((allRouteShapes ×ˢ allRouteShapes).map
        (guardedRouteShapePairCrossingCount tokens)).map
          fun count => List.replicate (13 * count) marker) =
        ((allRouteShapes ×ˢ allRouteShapes).map fun shapes =>
          List.replicate
            (13 * guardedRouteShapePairCrossingCount tokens shapes)
            marker) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro shapes shapesMember
    rfl
  rw [← blockMapEq]
  exact exact

/-- Physical output of the compact batched compiler for one tagged route-
descriptor pair. -/
def compiledAffineCrossingMarkers
    {Marker : Type} (marker : Marker)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Marker :=
  predicateListMarkers marker affineCrossingPredicates tokens

/-- The compiled finite scan is extensionally the previously verified affine
crossing-marker specification. -/
@[simp] theorem compiledAffineCrossingMarkers_eq
    {Marker : Type} (marker : Marker)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    compiledAffineCrossingMarkers marker tokens =
      affineCrossingMarkers marker tokens := by
  unfold compiledAffineCrossingMarkers
  rw [predicateListMarkers_eq]
  exact affineCrossingPredicates_flatMap marker tokens

/-- The full twenty-eight-squared, bounded-occurrence affine crossing scan is
polynomial-time without expanding its fixed predicate list into a fork tree. -/
def compiledAffineCrossingMarkersComputableInPolyTime
    {Marker : Type} [Fintype Marker] [Inhabited Marker]
    (marker : Marker) :
    TM2ComputableInPolyTime id id
      (compiledAffineCrossingMarkers marker) :=
  predicateListMarkersComputableInPolyTime marker affineCrossingPredicates

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
