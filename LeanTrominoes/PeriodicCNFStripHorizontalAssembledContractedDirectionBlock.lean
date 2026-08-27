/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionReversal
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteAssembledRequestData
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteDirectionBlock
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonRoutingFacts

/-! # Compact direction blocks for assembled contracted routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM
open PeriodicThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- A retained contracted edge uses one incidence word; a through edge uses
one incidence word followed by the reverse of another. -/
inductive HorizontalAssembledContractedDirectionBlock where
  | retained (route : HorizontalTypedIncidenceDirectionBlock)
  | through
      (first second : HorizontalTypedIncidenceDirectionBlock)

/-- Interpret one compact contracted-edge direction block. -/
def HorizontalAssembledContractedDirectionBlock.directions :
    HorizontalAssembledContractedDirectionBlock → List AxisDirection
  | .retained route => route.directions
  | .through first second =>
      first.directions ++ reverseDirections second.directions

/-- Every genuine contracted edge has one compact assembled direction block. -/
theorem horizontalAssembledContractedDirections_directionBlock_of_mem
    (source : PeriodicCNF Nat)
    (edge : ContractedEdge)
    (edgeMember : edge ∈
      (horizontalThreeDMProblemComputed source).contractedEdges) :
    ∃ block : HorizontalAssembledContractedDirectionBlock,
      horizontalAssembledContractedDirections source edge =
        block.directions := by
  have edgeData := contractedEdge_incidence_members_of_mem
    (horizontalThreeDMProblemComputed source) edgeMember
  cases edge with
  | retained color atom incidence =>
      have incidenceMember : incidence ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have tagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom incidenceMember
      rcases horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
          source ⟨incidence.tripleIndex, color⟩ tagMember with
        ⟨route, directions⟩
      refine ⟨.retained route, ?_⟩
      simpa only [horizontalAssembledContractedDirections,
        HorizontalAssembledContractedDirectionBlock.directions] using
        directions
  | through color atom first second =>
      have firstMember : first ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        simpa [ContractedEdge.sourceIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.1
      have secondMember : second ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        simpa [ContractedEdge.targetIncidence, ContractedEdge.color,
          ContractedEdge.atom] using edgeData.2.1
      have firstTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom firstMember
      have secondTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom secondMember
      rcases horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
          source ⟨first.tripleIndex, color⟩ firstTagMember with
        ⟨firstBlock, firstDirections⟩
      rcases horizontalAssembledRouteAtTag_directionBlock_of_tag_mem
          source ⟨second.tripleIndex, color⟩ secondTagMember with
        ⟨secondBlock, secondDirections⟩
      have width :=
        horizontalSemanticNormalizedRibbonSource_widthAtMostThree source
      have compatible :=
        horizontalSemanticNormalizedRibbonSource_fansCompatible source
      have secondOrthogonal : PeriodicOrthocrossing.OrthogonalPolyline
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩)) := by
        rw [horizontalAssembledRouteAtTagComputed_eq_semantic
          source width compatible]
        exact assembledRouteAtTag_orthogonal
          (coordinatedSourceRibbonThreeStrandRouting
            (horizontalSemanticNormalizedRibbonReadyPresentation source)
            width compatible)
          ⟨second.tripleIndex, color⟩
      refine ⟨.through firstBlock secondBlock, ?_⟩
      unfold horizontalAssembledContractedDirections
        HorizontalAssembledContractedDirectionBlock.directions
      change unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨first.tripleIndex, color⟩)) ++
          unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨second.tripleIndex, color⟩)).reverse =
        firstBlock.directions ++ reverseDirections secondBlock.directions
      rw [unitSubdivisionDirections_reverse _ secondOrthogonal,
        firstDirections, secondDirections]

end PeriodicCNFStripReduction
end LeanTrominoes

end
