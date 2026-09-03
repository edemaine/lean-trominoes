/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicCNFStripHorizontalIncidenceBodyAtIndexSemantics

/-! # Horizontal incidence bodies in typed triple order -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM
open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

private instance : Inhabited (Triple RoutedVariable) :=
  ⟨.clause 0 .topLeftOuter⟩

private theorem flatMap_eq_of_pointwise
    {Index Value : Type} (indices : List Index)
    (first second : Index → List Value)
    (equal : ∀ index ∈ indices, first index = second index) :
    indices.flatMap first = indices.flatMap second := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      rw [List.flatMap_cons, List.flatMap_cons,
        equal index (by simp), induction]
      intro other otherMember
      exact equal other (by simp [otherMember])

private theorem flatMap_range_getD
    {Value Output : Type} [Inhabited Value]
    (values : List Value) (output : Value → List Output) :
    (List.range values.length).flatMap
        (fun index => output (values.getD index default)) =
      values.flatMap output := by
  rw [← List.flatMap_map]
  rw [List.map_range_getD]

/-- The route direction body for every typed triple and color, in the same
triple-major RGB order as the numbered incidence-tag presentation. -/
def horizontalTypedIncidenceBodiesInTripleOrder
    (source : PeriodicCNF Nat) : List (List AxisDirection) :=
  (horizontalThreeDMTypedTriplesComputed source).flatMap fun triple =>
    incidenceColors.map fun color =>
      unitSubdivisionDirections
        (horizontalTypedIncidenceRouteComputed ((source, triple), color))

/-- Evaluating the canonical tag selector in numbered triple order recovers
the direct typed-triple route-body presentation exactly. -/
theorem horizontalCanonicalIncidenceBodies_eq_typedTripleOrder
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMProblemComputed source).incidenceTags.map
        (fun tag =>
          (horizontalCanonicalIncidenceDirectionBlock
            source tag).directions) =
      horizontalTypedIncidenceBodiesInTripleOrder source := by
  rw [PeriodicThreeDM.incidenceTags_eq_range_flatMap]
  rw [show (horizontalThreeDMProblemComputed source).triples.length =
      (horizontalThreeDMTypedTriplesComputed source).length by
    simpa only [horizontalNormalizationInputComputed_problem] using
      horizontalNormalizationInputComputed_triples_length source]
  rw [List.map_flatMap]
  let indexedBodies : Nat → List (List AxisDirection) :=
    fun tripleIndex => incidenceColors.map fun color =>
      unitSubdivisionDirections
        (horizontalTypedIncidenceRouteComputed
          ((source,
            (horizontalThreeDMTypedTriplesComputed source).getD
              tripleIndex default), color))
  calc
    _ = (List.range
          (horizontalThreeDMTypedTriplesComputed source).length).flatMap
          indexedBodies := by
      exact flatMap_eq_of_pointwise
        (List.range
          (horizontalThreeDMTypedTriplesComputed source).length)
        (fun tripleIndex =>
          (tripleIncidenceTags tripleIndex).map fun tag =>
            (horizontalCanonicalIncidenceDirectionBlock
              source tag).directions)
        indexedBodies
        (fun tripleIndex tripleIndexMember =>
          horizontalCanonicalIncidenceBodiesAtTripleIndex
            source tripleIndex (List.mem_range.mp tripleIndexMember))
    _ = horizontalTypedIncidenceBodiesInTripleOrder source := by
      unfold indexedBodies horizontalTypedIncidenceBodiesInTripleOrder
      exact flatMap_range_getD
        (horizontalThreeDMTypedTriplesComputed source)
        (fun triple => incidenceColors.map fun color =>
          unitSubdivisionDirections
            (horizontalTypedIncidenceRouteComputed
              ((source, triple), color)))

end LeanTrominoes.PeriodicCNFStripReduction
