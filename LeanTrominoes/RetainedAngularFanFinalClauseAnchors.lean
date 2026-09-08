/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRoutedDescriptorBlocks
import LeanTrominoes.RetainedAngularFanFinalCoordinatedSourceClauses
import LeanTrominoes.PeriodicCNFPlanarEightOccurrenceSplitRoutes

/-! # Zero anchors of the actual retained fixed-eight parent clauses -/

namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit PeriodicEightOccurrenceSplitPositioned

private theorem coordinatedClause_anchor_zero {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom) (clause : PositionedPeriodicClause (WrappedPeriodicPlanarSATVariable Atom))
    (member : clause ∈ (finalCoordinatedSource source).clauses) :
    PeriodicCNF.clauseAnchor clause.literals = (0, 0) := by
  have literalsMember : clause.literals ∈ deduplicatedClauses source := by
    rw [← finalCoordinatedSource_clauseLiterals_eq]
    exact List.mem_map.mpr ⟨clause, member, rfl⟩
  have normalizedMember : clause.literals ∈ normalizedClauses source := by
    simpa only [deduplicatedClauses, List.mem_dedup] using literalsMember
  obtain ⟨metadata, _metadataMember, literalsEq⟩ := List.mem_map.mp normalizedMember
  rw [← literalsEq]
  exact PeriodicClause.clauseAnchor_anchorNormalize _

/-- Copied clauses preserve their normalized source anchor; local cycle
clauses have zero offsets, and geometric scaling preserves those offsets. -/
theorem retainedSplitClause_anchor_zero {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom)
    (clause : PositionedPeriodicClause (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Atom)))
    (member : clause ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses) :
    PeriodicCNF.clauseAnchor clause.literals = (0, 0) := by
  rw [finalPositionedFormula_clauses_eq_descriptorBlocks, List.mem_append] at member
  rcases member with copied | cycle
  · obtain ⟨tagged, taggedMember, rfl⟩ := List.mem_map.mp copied
    simp only [copiedOccurrenceClause, occurrenceClause_clauseAnchor]
    exact coordinatedClause_anchor_zero source tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)
  · obtain ⟨unscaled, unscaledMember, rfl⟩ := List.mem_map.mp cycle
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp unscaledMember
    change PeriodicCNF.clauseAnchor unscaled.literals = (0, 0)
    exact allCycleClauses_clauseAnchor_eq_zero (sourceScaledForFigureSeven source)
      (placementScaledForFigureSeven source) (List.mk_mem_zipIdx_iff_getElem?.mpr lookup)

/-- In the original presentation, canonical and stored clause origins coincide. -/
theorem retainedSplitClause_canonicalPosition_eq_position {Atom : Type} [DecidableEq Atom]
    (source : PeriodicCNF Atom)
    (clause : PositionedPeriodicClause (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Atom)))
    (member : clause ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses) :
    PositionedPeriodicCNF.canonicalClausePosition
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source) clause = clause.position := by
  simp only [PositionedPeriodicCNF.canonicalClausePosition, retainedSplitClause_anchor_zero source clause member]
  rcases clause.position with ⟨x, y⟩
  simp [PeriodicVariablePlacement.translation, Cell.sub, Cell.scale]

end LeanTrominoes.PeriodicOrthocrossing
