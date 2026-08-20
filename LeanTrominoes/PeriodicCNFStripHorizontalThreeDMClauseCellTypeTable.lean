/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTripleCellTypeDirections
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMIncidenceRouteLookup
import LeanTrominoes.PeriodicThreeDMNormalizationReverseOrientation

/-! # Fixed clause-triple cell-type table -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget PlanarThreeDM

/-- Final normalized cell type of one clause-core triple, computed entirely
from the fixed finite clause route table. -/
def horizontalClauseTripleCellTypeComputed
    (set : X3CClauseSet) : OrthogonalCellType :=
  horizontalTripleCellTypeFromDirections
    (AxisDirection.polylineFirstDirection
      (X3CClauseOrthogonal.route set .red))
    (AxisDirection.polylineFirstDirection
      (X3CClauseOrthogonal.route set .green))
    (AxisDirection.polylineFirstDirection
      (X3CClauseOrthogonal.route set .blue))

/-- A clause constructor found at a stable triple index has exactly the
fixed-table cell type for its local clause set. -/
theorem horizontalFinalClauseTripleCellTypeComputed_eq_table
    (source : PeriodicCNF Nat)
    (tripleIndex clauseIndex : Nat) (set : X3CClauseSet)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length)
    (tripleLookup :
      (horizontalThreeDMTypedTriplesComputed source)[tripleIndex]? =
        some (.clause clauseIndex set)) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalClauseTripleCellTypeComputed set := by
  have problemIndexLt : tripleIndex <
      (horizontalThreeDMProblemComputed source).triples.length := by
    simpa only [horizontalNormalizationInputComputed_problem] using indexLt
  have tagMember (color : WireColor) :
      (⟨tripleIndex, color⟩ : PeriodicThreeDM.IncidenceTag) ∈
        (horizontalThreeDMProblemComputed source).incidenceTags :=
    PeriodicThreeDM.tripleIncidenceTag_mem_incidenceTags
      (horizontalThreeDMProblemComputed source)
      tripleIndex problemIndexLt color
  have routeTripleEq (color : WireColor) :
      horizontalAssembledRouteTriple?Computed
          (source, ⟨tripleIndex, color⟩) =
        some (.clause clauseIndex set) := by
    unfold horizontalAssembledRouteTriple?Computed
    exact tripleLookup
  rw [horizontalFinalVertexCellType_eq_incidenceDirections
    source tripleIndex indexLt]
  unfold horizontalClauseTripleCellTypeComputed
  rw [horizontalNormalizationClauseIncidenceFirstDirectionComputed
      source ⟨tripleIndex, .red⟩ clauseIndex set
      (tagMember .red) (routeTripleEq .red),
    horizontalNormalizationClauseIncidenceFirstDirectionComputed
      source ⟨tripleIndex, .green⟩ clauseIndex set
      (tagMember .green) (routeTripleEq .green),
    horizontalNormalizationClauseIncidenceFirstDirectionComputed
      source ⟨tripleIndex, .blue⟩ clauseIndex set
      (tagMember .blue) (routeTripleEq .blue)]

end PeriodicCNFStripReduction
end LeanTrominoes
