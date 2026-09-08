/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalElementCodeNumberingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceBodyHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCountedContractionPlanSemantics
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceRankedBodySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalElementDegreeHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMProblemSemanticBridge

/-! # Compiled incidence lookup selects the actual horizontal body groups -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Stable compiled lookup returns all incidence bodies at each actual
colored element, preserving the canonical order within every group. -/
theorem directSourceFinalSelectedIncidenceBodies_eq_horizontal
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.selectedBodies
        (directSourceFinalCanonicalElementCodes decider symbols)
        (directSourceFinalCanonicalElementDegrees decider symbols)
        (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
        (directSourceFinalCanonicalIncidenceBodies decider symbols) =
      CountedContractedIncidence.horizontalIncidenceDirectionBodiesByElement
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalCanonicalIncidenceDirectionBlock
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [CountedContractedIncidence.selectedBodies_eq_map_alignedBody]
  · rw [CountedContractedIncidence.incidenceBlockKeys_eq_candidateKeys,
      CountedContractedIncidence.queryKeys_map_alignedBody_eq_flatMap_idxsOf_of_perm_expanded
        _ _ _ _
        (directSourceFinalCountedContraction_elementColumns_length decider symbols)
        (directSourceFinalCountedContraction_degrees_valid decider symbols)
        (directSourceFinalCanonicalElementCodes_nodup decider symbols)
        (directSourceFinalCanonicalIncidenceElementCodes_perm_expanded decider symbols)]
    rw [directSourceFinalCanonicalElementCodes_eq_horizontal,
      directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal,
      directSourceFinalCanonicalIncidenceBodies_eq_horizontal]
    unfold CountedContractedIncidence.horizontalIncidenceDirectionBodiesByElement
      CountedContractedIncidence.horizontalIncidenceDirectionBodiesForElement
    apply incidenceFields_grouped_code_eq
    intro element member tag tagMember
    apply directSourceFinalHorizontalIncidenceCode_eq_iff decider symbols element _ tag tagMember
    simp only [CountedContractedIncidence.horizontalElementPairs,
      List.mem_flatMap, List.mem_map] at member
    obtain ⟨color, _, atom, atomMember, rfl⟩ := member
    exact List.mem_range.mp atomMember
  · unfold CountedContractedIncidence.incidenceBlockKeys
    rw [UnaryFieldStableOccurrenceKeys.keys_length,
      directSourceFinalCanonicalIncidenceBodies_length,
      directSourceFinalCanonicalIncidenceElementCodes_length]
  · exact (directSourceFinalCountedContraction_occurrenceKeyContract decider symbols).1
  · exact (directSourceFinalCountedContraction_occurrenceKeyContract decider symbols).2


/-- The actual compiled contraction produces precisely the assembler edges
of the canonical horizontal contracted blocks. -/
theorem directSourceFinalCountedContractedEdgeBlocks_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalCountedContractedEdgeBlocks decider symbols =
      (horizontalContractedDirectionBlocks
        (horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))
        (horizontalCanonicalIncidenceDirectionBlock
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))).map fun tagged =>
            HorizontalContractedRoutedRequest.ContractedBlock.assemblerEdge tagged.2 := by
  apply directSourceFinalCountedContractedEdgeBlocks_eq_horizontal_of
  · exact directSourceFinalCanonicalElementDegrees_eq_horizontal decider symbols
  · exact directSourceFinalSelectedIncidenceBodies_eq_horizontal decider symbols
  · rw [horizontalThreeDMProblemComputed_eq_problem]
    exact problem_degreeTwoOrThree _

end LeanTrominoes.PeriodicCNFStripReduction

end
