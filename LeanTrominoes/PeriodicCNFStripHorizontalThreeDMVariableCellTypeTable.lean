/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableCellTypeData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableIncidenceDirections
import LeanTrominoes.PeriodicThreeDMNormalizationReverseOrientation

/-! # Indexed variable triples use the finite local cell-type table -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Every color at an in-range computed horizontal triple is a stored
incidence tag. -/
theorem horizontalComputedTripleIncidenceTag_mem
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length)
    (color : WireColor) :
    (⟨tripleIndex, color⟩ : PeriodicThreeDM.IncidenceTag) ∈
      (horizontalThreeDMProblemComputed source).incidenceTags := by
  have problemIndexLt : tripleIndex <
      (horizontalThreeDMProblemComputed source).triples.length := by
    simpa only [horizontalNormalizationInputComputed_problem] using indexLt
  exact PeriodicThreeDM.tripleIncidenceTag_mem_incidenceTags
    (horizontalThreeDMProblemComputed source)
    tripleIndex problemIndexLt color

/-- A typed-list lookup is the same lookup used by every colored incidence
tag at that triple index. -/
theorem horizontalTypedTripleLookup_eq_routeTripleLookup
    (source : PeriodicCNF Nat) (tripleIndex : Nat)
    (triple : Triple RoutedVariable)
    (lookup :
      (horizontalThreeDMTypedTriplesComputed source)[tripleIndex]? =
        some triple)
    (color : WireColor) :
    horizontalAssembledRouteTriple?Computed
        (source, ⟨tripleIndex, color⟩) = some triple := by
  unfold horizontalAssembledRouteTriple?Computed
  exact lookup

/-- An indexed ordinary variable triple uses only its finite local
variable-site routes to select its final cell type. -/
theorem horizontalFinalOrdinaryVariableTripleCellTypeComputed_eq_table
    (source : PeriodicCNF Nat)
    (tripleIndex : Nat) (atom : RoutedVariable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length)
    (tripleLookup :
      (horizontalThreeDMTypedTriplesComputed source)[tripleIndex]? =
        some (.ordinary atom slot variant localTriple)) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalVariableTripleCellTypeComputed source atom
        (.ordinary atom slot variant localTriple) := by
  apply horizontalFinalVariableTripleCellTypeComputed_eq_of_directions
    source tripleIndex atom (.ordinary atom slot variant localTriple)
    indexLt
  intro color
  exact horizontalNormalizationOrdinaryIncidenceFirstDirectionComputed
    source ⟨tripleIndex, color⟩ atom slot variant localTriple
    (horizontalComputedTripleIncidenceTag_mem
      source tripleIndex indexLt color)
    (horizontalTypedTripleLookup_eq_routeTripleLookup
      source tripleIndex (.ordinary atom slot variant localTriple)
      tripleLookup color)

/-- An indexed fixed-red variable triple uses only its finite local
variable-site routes to select its final cell type. -/
theorem horizontalFinalFixedRedVariableTripleCellTypeComputed_eq_table
    (source : PeriodicCNF Nat)
    (tripleIndex : Nat) (atom : RoutedVariable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length)
    (tripleLookup :
      (horizontalThreeDMTypedTriplesComputed source)[tripleIndex]? =
        some (.fixedRed atom slot localTriple)) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalVariableTripleCellTypeComputed source atom
        (.fixedRed atom slot localTriple) := by
  apply horizontalFinalVariableTripleCellTypeComputed_eq_of_directions
    source tripleIndex atom (.fixedRed atom slot localTriple)
    indexLt
  intro color
  exact horizontalNormalizationFixedRedIncidenceFirstDirectionComputed
    source ⟨tripleIndex, color⟩ atom slot localTriple
    (horizontalComputedTripleIncidenceTag_mem
      source tripleIndex indexLt color)
    (horizontalTypedTripleLookup_eq_routeTripleLookup
      source tripleIndex (.fixedRed atom slot localTriple)
      tripleLookup color)

end PeriodicCNFStripReduction
end LeanTrominoes
