/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffinePredicateBatchSemantics

/-! # Polynomial-time batched affine-predicate evaluation -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open Computability Turing
open RouteDescriptorPairFieldTags

/-- Evaluate every fixed predicate after retaining its complete fixed-length
atom-ordering word in finite control. -/
def predicateListTruthValues
    (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Bool :=
  FixedLengthWordEvaluator.output
    (predicateListAtoms predicates).length
    (fun orderings =>
      (evalPredicateListOrderings predicates orderings).1)
    (atomsComparisonOrderings (predicateListAtoms predicates) tokens)

/-- The compact batched evaluator returns exactly the tagged-field semantic
truth value of every predicate in order. -/
@[simp] theorem predicateListTruthValues_eq
    (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    predicateListTruthValues predicates tokens =
      predicates.map fun predicate => predicate.evalTokens tokens := by
  unfold predicateListTruthValues
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq]
  · rw [atomsComparisonOrderings_eq]
    change
      (evalPredicateListOrderings predicates
        ((predicateListAtoms predicates).map
          (fun atom => atom.tokenOrdering tokens))).1 = _
    rw [predicateListAtoms_map_tokenOrdering]
    have exact :=
      evalPredicateListOrderings_tokenOrderings_append predicates tokens []
    simpa only [List.append_nil] using congrArg Prod.fst exact
  · rw [atomsComparisonOrderings_eq, List.length_map]

/-- A single affine phase list, comparison run, and finite-control terminal
pass evaluates any fixed predicate list in polynomial time. -/
def predicateListTruthValuesComputableInPolyTime
    (predicates : List Predicate) :
    TM2ComputableInPolyTime id id
      (predicateListTruthValues predicates) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (atomsComparisonOrderingsComputableInPolyTime
      (predicateListAtoms predicates))
    (FixedLengthWordEvaluator.computableInPolyTime
      (predicateListAtoms predicates).length
      (fun orderings =>
        (evalPredicateListOrderings predicates orderings).1))
  unfold predicateListTruthValues
  exact composed

/-- Thirteen marker symbols for an accepted predicate and none for a rejected
predicate. -/
def truthMarkerBlock {Marker : Type}
    (marker : Marker) (accepted : Bool) : List Marker :=
  if accepted then List.replicate 13 marker else []

/-- Marker stream produced from the compact batched truth word. -/
def predicateListMarkers
    {Marker : Type}
    (marker : Marker) (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) : List Marker :=
  (predicateListTruthValues predicates tokens).flatMap
    (truthMarkerBlock marker)

/-- Marker emission is exactly the ordered concatenation of the semantic
predicate blocks. -/
@[simp] theorem predicateListMarkers_eq
    {Marker : Type}
    (marker : Marker) (predicates : List Predicate)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    predicateListMarkers marker predicates tokens =
      predicates.flatMap fun predicate =>
        truthMarkerBlock marker (predicate.evalTokens tokens) := by
  unfold predicateListMarkers
  rw [predicateListTruthValues_eq]
  induction predicates with
  | nil => rfl
  | cons predicate predicates induction =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [induction]

/-- Batched thirteen-marker emission for any fixed predicate list is
polynomial-time. -/
def predicateListMarkersComputableInPolyTime
    {Marker : Type}
    [Fintype Marker] [Inhabited Marker]
    (marker : Marker) (predicates : List Predicate) :
    TM2ComputableInPolyTime id id
      (predicateListMarkers marker predicates) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (predicateListTruthValuesComputableInPolyTime predicates)
    (FiniteBlockTransducer.computableInPolyTime (truthMarkerBlock marker))
  unfold predicateListMarkers
  exact composed

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
