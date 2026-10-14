/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryParentRoutes
import LeanTrominoes.PeriodicCNFOrdinarySourceRouteWords

/-! # Compiled ordinary parent routes coincide with their geometric routes -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicCNF PeriodicOrthocrossing PeriodicCNF.OrdinarySourceProjection
variable {Input : Type} {encoding : _root_.LeanTrominoes.FiniteEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryRouteSemanticStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryRouteSemanticVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

private theorem source_occurrences (s : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable ordinaryRouteSemanticVariableDecidableEq) (by infer_instance) 3
      (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) :=
  PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
    (sourceFormula_occurrencesAtMostThree_canonicalBEq (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))

theorem nativeOrdinaryParentRouteDirections_eq (s : List encoding.Γ) :
    nativeOrdinaryParentRouteDirections decider s =
      (PositionedIncidenceRows.rows
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s))).map
        (fun row => Gadget.unitSubdivisionDirections
          (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) row.1.2 row.2.2)) := by
  rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
  rw [PositionedIncidenceRows.map_ordered_indices _ _ (fun ci li => Gadget.unitSubdivisionDirections
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) ci li))]
  simp only [nativeOrdinaryParentRouteDirections, directSourceFinalParentRouteBlocks, List.flatMap_map]
  apply List.flatMap_congr
  intro tagged member
  have nonempty := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
    (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_clausesNonempty _) tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have width := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
    (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_widthAtMostThree _) tagged.1.literals
    (PositionedPeriodicCNF.literals_mem_erase_of_mem_zipIdx member)
  let ordered := PositionedPeriodicCNF.orderClauseByRouteDirection
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)) tagged.2 tagged.1
  have orderedMember : (ordered, tagged.2) ∈
      (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s)).clauses.zipIdx := by
    rw [retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula,
      PositionedPeriodicCNF.orderClausesByRouteDirection, List.zipIdx_map_zipIdx]
    exact List.mem_map.mpr ⟨tagged, member, rfl⟩
  have literalMember (i : Nat) (active : i < tagged.1.literals.length) :
      ∃ literal, (literal, i) ∈ ordered.literals.zipIdx := by
    have bound : i < ordered.literals.length := by
      simpa only [ordered, PositionedPeriodicCNF.orderClauseByRouteDirection_length] using active
    exact ⟨ordered.literals[i], List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem bound)⟩
  apply selectedRouteWords_ofClause _ _ _ _ _ (List.mk_mem_zipIdx_iff_getElem?.mp member) nonempty width
  · intro i active
    obtain ⟨literal, hm⟩ := literalMember i active
    exact retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_unitSteps
      (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _)
      (source_occurrences decider s) (sourceFormula_clausesNonempty _) orderedMember hm
  · intro i active
    obtain ⟨literal, hm⟩ := literalMember i active
    exact retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_length_ge_two
      (directSourceFormula (PeriodicCNF.ProgramSource.ofDecider decider) s) (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _)
      (source_occurrences decider s) (sourceFormula_clausesNonempty _) orderedMember hm

end LeanTrominoes.PeriodicCNFStripReduction
end
