/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalCanonicalIncidenceDirectionBlockData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleLength

/-! # Canonical horizontal incidence bodies at one triple index -/

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

/-- At one in-range triple index and color, the canonical numbered selector
recovers the direction body of the typed route at that list position. -/
theorem horizontalCanonicalIncidenceBodyAtTripleIndex
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (tripleIndexLt : tripleIndex <
      (horizontalThreeDMTypedTriplesComputed source).length)
    (color : WireColor) :
    (horizontalCanonicalIncidenceDirectionBlock
        source ⟨tripleIndex, color⟩).directions =
      unitSubdivisionDirections
        (horizontalTypedIncidenceRouteComputed
          ((source,
            (horizontalThreeDMTypedTriplesComputed source).getD
              tripleIndex default), color)) := by
  rw [horizontalCanonicalIncidenceDirectionBlock_directions]
  · apply congrArg unitSubdivisionDirections
    apply horizontalAssembledRouteAtTagComputed_eq_typedRoute
    unfold horizontalAssembledRouteTriple?Computed
    rw [List.getElem?_eq_getElem tripleIndexLt,
      List.getD_eq_getElem _ _ tripleIndexLt]
  · apply PeriodicThreeDM.tripleIncidenceTag_mem_incidenceTags
    have encodedIndexLt : tripleIndex <
        (horizontalNormalizationInputComputed source).problem.triples.length := by
      rw [horizontalNormalizationInputComputed_triples_length]
      exact tripleIndexLt
    rw [horizontalNormalizationInputComputed_problem] at encodedIndexLt
    exact encodedIndexLt

/-- The preceding pointwise fact simultaneously identifies the stable RGB
block belonging to one in-range typed triple. -/
theorem horizontalCanonicalIncidenceBodiesAtTripleIndex
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (tripleIndexLt : tripleIndex <
      (horizontalThreeDMTypedTriplesComputed source).length) :
    (tripleIncidenceTags tripleIndex).map
        (fun tag =>
          (horizontalCanonicalIncidenceDirectionBlock
            source tag).directions) =
      incidenceColors.map fun color =>
        unitSubdivisionDirections
          (horizontalTypedIncidenceRouteComputed
            ((source,
              (horizontalThreeDMTypedTriplesComputed source).getD
                tripleIndex default), color)) := by
  simp only [tripleIncidenceTags, incidenceColors, List.map_cons,
    List.map_nil]
  rw [horizontalCanonicalIncidenceBodyAtTripleIndex
      source tripleIndex tripleIndexLt .red,
    horizontalCanonicalIncidenceBodyAtTripleIndex
      source tripleIndex tripleIndexLt .green,
    horizontalCanonicalIncidenceBodyAtTripleIndex
      source tripleIndex tripleIndexLt .blue]

end LeanTrominoes.PeriodicCNFStripReduction
