/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleLength
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableIncidenceDirections
import LeanTrominoes.PeriodicCNFStripHorizontalTypedIncidenceDirectionBlock

/-! # Compact direction blocks at stable horizontal incidence tags -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Every genuine stable incidence tag successfully selects one typed triple. -/
theorem exists_horizontalAssembledRouteTriple?Computed_of_tag_mem
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags) :
    ∃ triple : Triple RoutedVariable,
      horizontalAssembledRouteTriple?Computed (source, tag) = some triple := by
  have problemIndexLt := PeriodicThreeDM.incidenceTag_tripleIndex_lt
    (horizontalThreeDMProblemComputed source) tagMember
  have computedIndexLt :
      tag.tripleIndex < (horizontalThreeDMTypedTriplesComputed source).length := by
    rw [← horizontalNormalizationInputComputed_triples_length source]
    exact problemIndexLt
  have semanticIndexLt :
      tag.tripleIndex < (horizontalSemanticThreeDMTypedTriples source).length := by
    rw [← horizontalThreeDMTypedTriplesComputed_eq_semantic source]
    exact computedIndexLt
  let triple :=
    (horizontalSemanticThreeDMTypedTriples source)[tag.tripleIndex]
  refine ⟨triple, ?_⟩
  rw [horizontalAssembledRouteTriple?Computed_eq_semantic]
  simpa only [triple] using List.getElem?_eq_getElem semanticIndexLt

/-- Every assembled route selected by a genuine stable incidence tag has one
compact complete typed-incidence direction block. -/
theorem horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag)
    (tagMember :
      tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags) :
    ∃ block : HorizontalTypedIncidenceDirectionBlock,
      unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed (source, tag)) =
        block.directions := by
  rcases exists_horizontalAssembledRouteTriple?Computed_of_tag_mem
      source tag tagMember with
    ⟨triple, lookup⟩
  have member := horizontalAssembledRouteTriple?Computed_mem_semantic
    source tag triple lookup
  rcases horizontalTypedIncidenceRoute_directionBlock_of_mem
      source triple member tag.color with
    ⟨block, directions⟩
  refine ⟨block, ?_⟩
  rw [horizontalAssembledRouteAtTagComputed_eq_typedRoute
    source tag triple lookup]
  exact directions

end PeriodicCNFStripReduction
end LeanTrominoes

end
