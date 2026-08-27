/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseCompactContractedRouteRasterSourceData

/-! # Canonically ordered compact blocks from incidence blocks -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicThreeDM

/-- Apply the executable degree-two/degree-three contraction table to one
colored element while retaining a compact block for every source incidence. -/
def horizontalContractedDirectionBlocksForElement
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (color : Gadget.WireColor) (atom : Nat) :
    List DirectSparseCompactContractedEdgeBlock :=
  match problem.incidences color atom with
  | [first, second] =>
      [(.through color atom first second,
        .through
          (incidenceBlock ⟨first.tripleIndex, color⟩)
          (incidenceBlock ⟨second.tripleIndex, color⟩))]
  | [first, second, third] =>
      [(.retained color atom first,
          .retained (incidenceBlock ⟨first.tripleIndex, color⟩)),
        (.retained color atom second,
          .retained (incidenceBlock ⟨second.tripleIndex, color⟩)),
        (.retained color atom third,
          .retained (incidenceBlock ⟨third.tripleIndex, color⟩))]
  | _ => []

/-- Forgetting compact direction blocks recovers the executable contracted
edges contributed by this element, in definitionally identical order. -/
@[simp] theorem map_fst_horizontalContractedDirectionBlocksForElement
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (color : Gadget.WireColor) (atom : Nat) :
    (horizontalContractedDirectionBlocksForElement
      problem incidenceBlock color atom).map Prod.fst =
      problem.contractedEdgesForElement color atom := by
  unfold horizontalContractedDirectionBlocksForElement
    PeriodicThreeDM.contractedEdgesForElement
  generalize incidencesEq : problem.incidences color atom = incidences
  rcases incidences with _ | ⟨first, incidences⟩
  · rfl
  rcases incidences with _ | ⟨second, incidences⟩
  · rfl
  rcases incidences with _ | ⟨third, incidences⟩
  · rfl
  rcases incidences with _ | ⟨fourth, incidences⟩ <;> rfl

/-- Canonical color-major, element-major compact block list. -/
def horizontalContractedDirectionBlocks
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock) :
    List DirectSparseCompactContractedEdgeBlock :=
  incidenceColors.flatMap fun color =>
    (List.range (problem.elementCount color)).flatMap fun atom =>
      horizontalContractedDirectionBlocksForElement
        problem incidenceBlock color atom

/-- The canonical compact block list projects exactly to `contractedEdges`;
there is no permutation or later index reconciliation. -/
@[simp] theorem map_fst_horizontalContractedDirectionBlocks
    (problem : PeriodicThreeDM)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock) :
    (horizontalContractedDirectionBlocks
      problem incidenceBlock).map Prod.fst = problem.contractedEdges := by
  unfold horizontalContractedDirectionBlocks
    PeriodicThreeDM.contractedEdges
    PeriodicThreeDM.contractedEdgesForColor
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro color _
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro atom _
  exact map_fst_horizontalContractedDirectionBlocksForElement
    problem incidenceBlock color atom

end PeriodicCNFStripReduction
end LeanTrominoes
