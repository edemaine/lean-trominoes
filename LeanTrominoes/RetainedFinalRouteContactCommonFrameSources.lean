/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalRouteCommonFrameSourceSelections
import LeanTrominoes.PeriodicOrthocrossingCarrierRepresentativeTranslation

/-!
# Concrete common-frame sources at arbitrary final contacts

The arbitrary terminal and crossover certificates place the direct component
in a finite carrier-contact frame.  This file proves that the corresponding
translated source formula is realized by its concrete local incidence drawing.
This is the exact presentation fact needed to invoke the finite carrier-boundary
lemmas; it does not require the translated source to remain in the retained
enumeration window.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1600000

/-- Translating an active routed-variable arm preserves the equality between
its abstract two-clause formula and its concrete incidence drawing. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_formula_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (shift : Cell)
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing formula
        (variableRouteSitePeriodTranslate site shift) arm
        (planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift)).formula =
      drawingPlanarSATRoutedVariableFormulaAt
        (planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift) := by
  have positions :=
    routedVariableLink_positions formula site linkMem
  subst arm
  have translatedPositions :
      (planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift).positions =
        routedVariableEqualityPositions formula
          (variableRouteSitePeriodTranslate site shift)
          (planarSATNodeLinkPeriodTranslate
            formula.incidenceGraph link shift).first.duplicatorArm := by
    change
      EqualityPositions.periodTranslate link.positions
          (carrierMacroPeriodTranslation formula.incidenceGraph shift) =
        routedVariableEqualityPositions formula
          (variableRouteSitePeriodTranslate site shift)
          (link.first.periodTranslate
            formula.incidenceGraph shift).duplicatorArm
    rw [PlanarSATNode.duplicatorArm_periodTranslate,
      routedVariableEqualityPositions_periodTranslate, positions]
  have translatedArm :
      (planarSATNodeLinkPeriodTranslate
          formula.incidenceGraph link shift).first.duplicatorArm =
        link.first.duplicatorArm := by
    change
      (link.first.periodTranslate
        formula.incidenceGraph shift).duplicatorArm = _
    exact PlanarSATNode.duplicatorArm_periodTranslate link.first shift
  unfold drawingPlanarSATRoutedVariableFormulaAt
  rw [translatedPositions]
  rw [translatedArm]
  simp [drawingPlanarSATRoutedVariableIncidenceDrawing,
    duplicatorArmStraightIncidenceDrawing,
    straightIncidenceDrawing, duplicatorArmFormula,
    routedVariableEqualityPositions,
    planarSATRoutedVariableMap, planarSATExternalVariableMap,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedClause.translate, EmbeddedClause.rename,
    EmbeddedClause.map, equalityInstance,
    Cell.add]

/-- A terminal contact gives the translated direct source a concrete finite
presentation of the exact common-frame route. -/
theorem FinalGaugedCarrierFrameTerminalContact.exists_commonFrameMacrocellSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {carrierClauseIndex carrierLiteralIndex
      macrocellClauseIndex macrocellLiteralIndex : Nat}
    {carrierShift macrocellShift : Cell}
    {carrier :
      FinalGaugedCarrierRouteOccurrenceWitness
        formula carrierClauseIndex carrierLiteralIndex carrierShift}
    {macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula macrocellClauseIndex macrocellLiteralIndex macrocellShift}
    (contact :
      FinalGaugedCarrierFrameTerminalContact
        formula carrier macrocell) :
    Nonempty
      (FinalGaugedCommonFrameMacrocellSource
        formula macrocell (macrocell.relativeShiftFrom carrier)) := by
  let relativeShift := macrocell.relativeShiftFrom carrier
  have originalSourceMember :
      macrocell.metadata.source.RetainedComponentMember formula :=
    (macrocell.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp macrocell.metadata_retainedValid |>.1
  rcases contact with routedClauseContact | routedVariableContact
  · obtain ⟨targetSite, occurrence, data⟩ := routedClauseContact
    have translatedSourceEq := data.1
    cases sourceEq : macrocell.metadata.source with
    | crossover crossing localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | carrier link localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | bend routeBend localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | routedClause sourceSite =>
        exact ⟨{
          source := macrocell.commonFrameSource relativeShift
          incidenceFormulaEq := by
            unfold FinalGaugedRouteOccurrenceWitness.commonFrameSource
            rw [translatedSourceEq]
            simp [DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.clauseFormula]
          sourceEq := rfl
        }⟩
    | routedVariable site armIndex arm link localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
  · obtain
        ⟨targetSite, targetArmIndex, targetArm, targetLink,
          targetLocalClauseIndex, occurrence, data⟩ :=
      routedVariableContact
    have translatedSourceEq := data.1
    cases sourceEq : macrocell.metadata.source with
    | crossover crossing localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | carrier link localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | bend routeBend localClauseIndex =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | routedClause site =>
        simp [sourceEq,
          DrawingPlanarSATClauseSource.periodTranslate] at translatedSourceEq
    | routedVariable
        sourceSite sourceArmIndex sourceArm sourceLink
          sourceLocalClauseIndex =>
        rw [sourceEq] at originalSourceMember
        change
          sourceSite ∈ drawingVariableRouteSites formula ∧
            (sourceLink, sourceArmIndex) ∈
              (routedVariableLinksAt formula sourceSite).zipIdx ∧
            sourceArm = sourceLink.first.duplicatorArm at originalSourceMember
        have formulaEq :=
          drawingPlanarSATRoutedVariableIncidenceDrawing_formula_periodTranslate
            formula sourceSite sourceArm sourceLink relativeShift
            (List.fst_mem_of_mem_zipIdx originalSourceMember.2.1)
            originalSourceMember.2.2
        exact ⟨{
          source := macrocell.commonFrameSource relativeShift
          incidenceFormulaEq := by
            simpa [FinalGaugedRouteOccurrenceWitness.commonFrameSource,
              sourceEq, DrawingPlanarSATClauseSource.periodTranslate,
              DrawingPlanarSATClauseSource.incidenceDrawing,
              DrawingPlanarSATClauseSource.clauseFormula] using formulaEq
          sourceEq := rfl
        }⟩

/-- In the normalized crossover frame, the normalized crossover itself is
a concrete presentation of the direct macrocell route. -/
theorem
    FinalGaugedRouteMacrocellOccurrenceWitness.exists_normalizedCrossoverCommonFrameSource
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    {shift : Cell}
    (macrocell :
      FinalGaugedRouteMacrocellOccurrenceWitness
        formula clauseIndex literalIndex shift)
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    (sourceEq :
      macrocell.metadata.source =
        .crossover crossing localClauseIndex) :
    Nonempty
      (FinalGaugedCommonFrameMacrocellSource
        formula macrocell
          (Cell.neg
            (crossingPeriodShift formula.incidenceGraph crossing))) := by
  let normalizedSource : DrawingPlanarSATClauseSource Variable :=
    .crossover
      (crossing.periodNormalize formula.incidenceGraph)
      localClauseIndex
  exact ⟨{
    source := normalizedSource
    incidenceFormulaEq := by
      simp [normalizedSource,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.clauseFormula]
    sourceEq := by
      simp [normalizedSource,
        FinalGaugedRouteOccurrenceWitness.commonFrameSource,
        sourceEq, DrawingPlanarSATClauseSource.periodTranslate,
        CrossingRecord.periodTranslate_neg_shift_eq_periodNormalize]
  }⟩

end PeriodicOrthocrossing
end LeanTrominoes
