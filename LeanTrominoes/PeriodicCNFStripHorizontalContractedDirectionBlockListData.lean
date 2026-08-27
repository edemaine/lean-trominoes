/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseCompactContractedRouteRasterSourceData

/-! # Canonically ordered compact blocks from incidence blocks -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget PeriodicPlanarOneInThreeToThreeDM PeriodicThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

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

/-- A compact incidence lookup denotes every genuine assembled route selected
by the horizontal problem's stable incidence tags. -/
def HorizontalIncidenceDirectionBlocksCorrect
    (source : PeriodicCNF Nat)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock) :
    Prop :=
  ∀ tag ∈ (horizontalThreeDMProblemComputed source).incidenceTags,
    (incidenceBlock tag).directions =
    unitSubdivisionDirections
        (horizontalAssembledRouteAtTagComputed (source, tag))

private theorem horizontalAssembledRouteAtTagComputed_orthogonal
    (source : PeriodicCNF Nat) (tag : IncidenceTag) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (horizontalAssembledRouteAtTagComputed (source, tag)) := by
  have width := horizontalSemanticNormalizedRibbonSource_widthAtMostThree
    source
  have compatible := horizontalSemanticNormalizedRibbonSource_fansCompatible
    source
  rw [horizontalAssembledRouteAtTagComputed_eq_semantic
    source width compatible]
  exact assembledRouteAtTag_orthogonal
    (coordinatedSourceRibbonThreeStrandRouting
      (horizontalSemanticNormalizedRibbonReadyPresentation source)
      width compatible)
    tag

/-- Pointwise incidence correctness is preserved by one local contraction
table lookup. -/
theorem horizontalContractedDirectionBlocksForElement_directions
    (source : PeriodicCNF Nat)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (correct : HorizontalIncidenceDirectionBlocksCorrect
      source incidenceBlock)
    (color : Gadget.WireColor) (atom : Nat)
    (tagged : DirectSparseCompactContractedEdgeBlock)
    (taggedMember : tagged ∈
      horizontalContractedDirectionBlocksForElement
        (horizontalThreeDMProblemComputed source)
        incidenceBlock color atom) :
    tagged.2.directions =
      horizontalAssembledContractedDirections source tagged.1 := by
  generalize incidencesEq :
      (horizontalThreeDMProblemComputed source).incidences color atom =
        incidences at taggedMember
  unfold horizontalContractedDirectionBlocksForElement at taggedMember
  rw [incidencesEq] at taggedMember
  rcases incidences with _ | ⟨first, incidences⟩
  · simp at taggedMember
  rcases incidences with _ | ⟨second, incidences⟩
  · simp at taggedMember
  rcases incidences with _ | ⟨third, incidences⟩
  · simp only [List.mem_singleton] at taggedMember
    subst tagged
    have firstMember : first ∈
        (horizontalThreeDMProblemComputed source).incidences color atom := by
      rw [incidencesEq]
      simp
    have secondMember : second ∈
        (horizontalThreeDMProblemComputed source).incidences color atom := by
      rw [incidencesEq]
      simp
    have firstTagMember := incidenceTag_mem_of_incidence_mem
      (horizontalThreeDMProblemComputed source) color atom firstMember
    have secondTagMember := incidenceTag_mem_of_incidence_mem
      (horizontalThreeDMProblemComputed source) color atom secondMember
    have secondOrthogonal :=
      horizontalAssembledRouteAtTagComputed_orthogonal
        source ⟨second.tripleIndex, color⟩
    change
      (incidenceBlock ⟨first.tripleIndex, color⟩).directions ++
          reverseDirections
            (incidenceBlock ⟨second.tripleIndex, color⟩).directions =
        unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨first.tripleIndex, color⟩)) ++
          unitSubdivisionDirections
            (horizontalAssembledRouteAtTagComputed
              (source, ⟨second.tripleIndex, color⟩)).reverse
    rw [correct ⟨first.tripleIndex, color⟩ firstTagMember,
      correct ⟨second.tripleIndex, color⟩ secondTagMember,
      unitSubdivisionDirections_reverse _ secondOrthogonal]
  rcases incidences with _ | ⟨fourth, incidences⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at taggedMember
    rcases taggedMember with taggedEq | taggedEq | taggedEq
    · subst tagged
      have firstMember : first ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        rw [incidencesEq]
        simp
      have firstTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom firstMember
      change (incidenceBlock ⟨first.tripleIndex, color⟩).directions =
        unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨first.tripleIndex, color⟩))
      exact correct ⟨first.tripleIndex, color⟩ firstTagMember
    · subst tagged
      have secondMember : second ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        rw [incidencesEq]
        simp
      have secondTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom secondMember
      change (incidenceBlock ⟨second.tripleIndex, color⟩).directions =
        unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨second.tripleIndex, color⟩))
      exact correct ⟨second.tripleIndex, color⟩ secondTagMember
    · subst tagged
      have thirdMember : third ∈
          (horizontalThreeDMProblemComputed source).incidences color atom := by
        rw [incidencesEq]
        simp
      have thirdTagMember := incidenceTag_mem_of_incidence_mem
        (horizontalThreeDMProblemComputed source) color atom thirdMember
      change (incidenceBlock ⟨third.tripleIndex, color⟩).directions =
        unitSubdivisionDirections
          (horizontalAssembledRouteAtTagComputed
            (source, ⟨third.tripleIndex, color⟩))
      exact correct ⟨third.tripleIndex, color⟩ thirdTagMember
  · simp at taggedMember

/-- Pointwise incidence correctness therefore yields pointwise correctness of
the complete canonical contracted block list. -/
theorem horizontalContractedDirectionBlocks_directions
    (source : PeriodicCNF Nat)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (correct : HorizontalIncidenceDirectionBlocksCorrect
      source incidenceBlock)
    (tagged : DirectSparseCompactContractedEdgeBlock)
    (taggedMember : tagged ∈
      horizontalContractedDirectionBlocks
        (horizontalThreeDMProblemComputed source) incidenceBlock) :
    tagged.2.directions =
      horizontalAssembledContractedDirections source tagged.1 := by
  unfold horizontalContractedDirectionBlocks at taggedMember
  simp only [List.mem_flatMap] at taggedMember
  obtain ⟨color, _, colorMember⟩ := taggedMember
  obtain ⟨atom, _, elementMember⟩ := colorMember
  exact horizontalContractedDirectionBlocksForElement_directions
    source incidenceBlock correct color atom tagged elementMember

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance
    horizontalContractedDirectionBlockListStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- A correct compact block lookup for stable incidence tags automatically
supplies the exact direct raster-request stream after canonical contraction.
The remaining source compiler need not enumerate contracted edges itself. -/
theorem directSparseCompactContractedRouteEntries_mappedOutput_of_incidenceBlocks
    (symbols : List encoding.Γ)
    (incidenceBlock : IncidenceTag → HorizontalTypedIncidenceDirectionBlock)
    (correct : HorizontalIncidenceDirectionBlocksCorrect
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
      incidenceBlock) :
    TM2EndDelimitedBlockMap.mappedOutput
        HorizontalContractedRouteRasterSource.isEnd
        HorizontalContractedRouteRasterSource.requestOutput
        (HorizontalContractedRouteRasterSource.tokens
          (directSparseCompactContractedRouteEntries
            (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
            (directSparseAssembledRouteMetadata decider symbols)
            (horizontalContractedDirectionBlocks
              (horizontalThreeDMProblemComputed
                (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
                  decider symbols))
              incidenceBlock))) =
      GadgetSparseRouteRasterRequestTokens.tokens
        (RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols
          decider symbols) := by
  apply directSparseCompactContractedRouteEntries_mappedOutput_of_blocks
    decider symbols
  · unfold directSparseComputedNormalizationInputOfSymbols
    rw [horizontalNormalizationInputComputed_problem]
    exact map_fst_horizontalContractedDirectionBlocks
      (horizontalThreeDMProblemComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
      incidenceBlock
  · intro tagged taggedMember
    exact horizontalContractedDirectionBlocks_directions
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
      incidenceBlock correct tagged taggedMember

end PeriodicCNFStripReduction
end LeanTrominoes
