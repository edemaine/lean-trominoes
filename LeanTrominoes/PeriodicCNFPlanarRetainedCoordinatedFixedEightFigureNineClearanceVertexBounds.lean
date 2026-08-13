/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedVertexBounds
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVertexPositions
import LeanTrominoes.RetainedAngularFanFinalCycleSeparation

/-!
# Vertex bounds for the retained Figure 9 clearance source

This module specializes the generic fixed-eight macrocell bounds to the
retained planar-SAT source, then transports them through the source-first,
terminal-fan, clockwise-ordering, and Figure 9 clearance refinements.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxHeartbeats 2000000

private theorem position_inSquare_scale
    {factor period : Nat} (factorPositive : 0 < factor)
    {position : Cell}
    (inside :
      0 < position.1 ∧ position.1 < period ∧
        0 < position.2 ∧ position.2 < period) :
    0 < (Cell.scale factor position).1 ∧
      (Cell.scale factor position).1 < factor * period ∧
      0 < (Cell.scale factor position).2 ∧
      (Cell.scale factor position).2 < factor * period := by
  rcases position with ⟨horizontal, vertical⟩
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  simp only [Cell.scale]
  exact
    ⟨by nlinarith, by nlinarith,
      by nlinarith, by nlinarith⟩

private theorem retainedScaledSourceVariable_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : WrappedPeriodicPlanarSATVariable Variable) :
    let sourcePlacement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).scale
        retainedAngularFanSourceClearanceFactor
    0 < (sourcePlacement.position atom).1 ∧
      (sourcePlacement.position atom).1 < sourcePlacement.period ∧
      0 < (sourcePlacement.position atom).2 ∧
      (sourcePlacement.position atom).2 < sourcePlacement.period := by
  dsimp only
  have inside :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      source atom
  simpa only [PeriodicVariablePlacement.scale_position,
    PeriodicVariablePlacement.scale_period, Nat.cast_mul] using
      position_inSquare_scale
        retainedAngularFanSourceClearanceFactor_pos inside

private theorem retainedScaledSourceClause_inSquare
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈
        ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source).scale retainedAngularFanSourceClearanceFactor).clauses) :
    let sourcePlacement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source).scale
        retainedAngularFanSourceClearanceFactor
    0 < clause.position.1 ∧
      clause.position.1 < sourcePlacement.period ∧
      0 < clause.position.2 ∧
      clause.position.2 < sourcePlacement.period := by
  dsimp only
  rw [PositionedPeriodicCNF.scale_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  let certificate :=
    retainedPlanarSATCertificate source sourceLocal sourceWidth
      sourceOccurrences sourceClausesNonempty
  have sourceInside :=
    deduplicated_storedClausePositions_inSquare
      source certificate.graphWellFormed
      certificate.graphDegreeAtMostThree certificate.graphIsLocal
      (retainedDrawingPlanarSATFormula_clausesNonempty_of_source
        source sourceClausesNonempty)
      sourceClause.position
      (List.mem_map.mpr ⟨sourceClause, sourceClauseMember, rfl⟩)
  simpa only [PositionedPeriodicClause.scale_position,
    PeriodicVariablePlacement.scale_period, Nat.cast_mul] using
      position_inSquare_scale
        retainedAngularFanSourceClearanceFactor_pos sourceInside

/-- Every occurring variable of the source-scaled fixed-eight presentation
lies strictly inside its physical fundamental square. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (atomMember :
      atom ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences) :
    0 <
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).position atom).1 ∧
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).position atom).1 <
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).period ∧
      0 <
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).position atom).2 ∧
      ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).position atom).2 <
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).period := by
  let baseFormula :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let basePlacement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let scaledFormula :=
    baseFormula.scale retainedAngularFanSourceClearanceFactor
  let scaledPlacement :=
    basePlacement.scale retainedAngularFanSourceClearanceFactor
  let ports :=
    occurrencePortsOfAngularOrder scaledFormula.erase
      (angularOccurrenceOrder scaledFormula.erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source)))
  have unscaledMember :
      atom ∈
        (formula scaledFormula scaledPlacement ports).erase.variableOccurrences := by
    simpa only [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
      retainedAngularFanSourceScaledRefinedFormula,
      retainedAngularFanRefinedFormula, PositionedPeriodicCNF.erase_scale,
      baseFormula, basePlacement, scaledFormula, scaledPlacement, ports]
      using atomMember
  have splitInside :=
    placement_position_inSquare_of_mem
      scaledFormula scaledPlacement ports
      (fun sourceAtom _sourceAtomMember => by
        simpa only [scaledPlacement, basePlacement] using
          retainedScaledSourceVariable_inSquare source sourceAtom)
      atom unscaledMember
  simpa only [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    PeriodicVariablePlacement.scale_position,
    PeriodicVariablePlacement.scale_period,
    Nat.cast_mul, basePlacement, scaledPlacement] using
      position_inSquare_scale
        (by decide : 0 < retainedTerminalFanRoutingRefinement)
        splitInside

/-- Every stored clause vertex of the source-scaled fixed-eight presentation
lies strictly inside its physical fundamental square. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitStoredClausePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (clauseMember :
      clause ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).clauses) :
    0 < clause.position.1 ∧
      clause.position.1 <
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).period ∧
      0 < clause.position.2 ∧
      clause.position.2 <
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          source).period := by
  let baseFormula :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      source
  let basePlacement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source
  let scaledFormula :=
    baseFormula.scale retainedAngularFanSourceClearanceFactor
  let scaledPlacement :=
    basePlacement.scale retainedAngularFanSourceClearanceFactor
  let ports :=
    occurrencePortsOfAngularOrder scaledFormula.erase
      (angularOccurrenceOrder scaledFormula.erase
        (PositionedPeriodicCNF.scaleIncidenceRoutes
          retainedAngularFanSourceClearanceFactor
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
            source)))
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula,
    retainedAngularFanSourceScaledRefinedFormula,
    retainedAngularFanRefinedFormula,
    PositionedPeriodicCNF.scale_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨splitClause, splitClauseMember, rfl⟩
  have splitInside :=
    storedClausePosition_inSquare_of_mem
      scaledFormula scaledPlacement ports
      (fun sourceAtom _sourceAtomMember => by
        simpa only [scaledPlacement, basePlacement] using
          retainedScaledSourceVariable_inSquare source sourceAtom)
      (fun sourceClause sourceClauseMember => by
        exact retainedScaledSourceClause_inSquare
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClause
          (by simpa only [scaledFormula, baseFormula] using sourceClauseMember))
      splitClause
      (by simpa only [scaledFormula, scaledPlacement, ports] using splitClauseMember)
  simpa only [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
    retainedAngularFanSourceScaledRefinedPlacement,
    retainedAngularFanRefinedPlacement,
    PositionedPeriodicClause.scale_position,
    PeriodicVariablePlacement.scale_period,
    Nat.cast_mul, basePlacement, scaledPlacement] using
      position_inSquare_scale
        (by decide : 0 < retainedTerminalFanRoutingRefinement)
        splitInside

/-- Every occurring variable of the twice-scaled clockwise clearance source
lies strictly inside its physical fundamental square. -/
theorem retainedFigureNineClearancePlacement_position_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (atomMember :
      atom ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences) :
    0 < ((retainedFigureNineClearancePlacement source).position atom).1 ∧
      ((retainedFigureNineClearancePlacement source).position atom).1 <
        (retainedFigureNineClearancePlacement source).period ∧
      0 < ((retainedFigureNineClearancePlacement source).position atom).2 ∧
      ((retainedFigureNineClearancePlacement source).position atom).2 <
        (retainedFigureNineClearancePlacement source).period := by
  have orderedMember :
      atom ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences := by
    simpa only [retainedFigureNineClearancePositionedFormula,
      PositionedPeriodicCNF.erase_scale] using atomMember
  have occurrencePermutation :=
    PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
  have refinedMember :
      atom ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source).erase.variableOccurrences :=
    occurrencePermutation.mem_iff.mp
      (by
        simpa only [
          retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
          using orderedMember)
  have refinedInside :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement_position_inSquare_of_mem
      source atom refinedMember
  simpa only [retainedFigureNineClearancePlacement,
    PeriodicVariablePlacement.scale_position,
    PeriodicVariablePlacement.scale_period, Nat.cast_mul] using
      position_inSquare_scale
        retainedFigureNineSourceClearanceFactor_pos refinedInside

/-- Every stored clause vertex of the twice-scaled clockwise clearance source
lies strictly inside its physical fundamental square. -/
theorem retainedFigureNineClearanceStoredClausePosition_inSquare_of_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (clauseMember :
      clause ∈
        (retainedFigureNineClearancePositionedFormula source).clauses) :
    0 < clause.position.1 ∧
      clause.position.1 <
        (retainedFigureNineClearancePlacement source).period ∧
      0 < clause.position.2 ∧
      clause.position.2 <
        (retainedFigureNineClearancePlacement source).period := by
  rw [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.scale_clauses] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨orderedClause, orderedClauseMember, rfl⟩
  rcases List.mem_iff_getElem.mp orderedClauseMember with
    ⟨clauseIndex, clauseIndexLt, clauseAt⟩
  have taggedOrderedMember :
      (orderedClause, clauseIndex) ∈
        (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨clauseIndexLt, clauseAt⟩
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source)
      (by
        simpa only [
          retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula]
          using taggedOrderedMember) with
    ⟨refinedClause, refinedClauseMember, orderedClauseEq⟩
  have refinedInside :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitStoredClausePosition_inSquare_of_mem
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      refinedClause (List.fst_mem_of_mem_zipIdx refinedClauseMember)
  have storedPositionEq : orderedClause.position = refinedClause.position := by
    rw [orderedClauseEq]
    rfl
  simp only [PositionedPeriodicClause.scale_position]
  rw [storedPositionEq]
  simpa only [retainedFigureNineClearancePlacement,
    PeriodicVariablePlacement.scale_period, Nat.cast_mul] using
      position_inSquare_scale
        retainedFigureNineSourceClearanceFactor_pos refinedInside

end PeriodicOrthocrossing
end LeanTrominoes
