/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.FiniteRetainedPlanarUniformOffsets
import LeanTrominoes.SAT.Planar.FinitePlanarVariableGauge
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedCertificate

/-! # Retained planarization preserves finite SAT -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT
set_option maxHeartbeats 300000
variable {V : Type*} [DecidableEq V] (source : PeriodicCNF V)

theorem retainedDrawingPeriodicPlanarSATFormula_finite_satisfiable_iff
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (zero : FiniteCNF.ZeroOffsets source) (occurrences : source.OccurrencesAtMost 3) :
    FiniteCNF.Satisfiable (FiniteCNF.erase (retainedDrawingPeriodicPlanarSATFormula source)) ↔
      FiniteCNF.Satisfiable (FiniteCNF.erase source) := by
  rw [FiniteCNF.satisfiable_erase_of_uniform _
    (retainedDrawingPeriodicPlanarSATFormula_uniform source wellFormed degree zero),
    retainedDrawingPeriodicPlanarSATFormula_satisfiable_iff source wellFormed degree
      (zeroOffsetGraph_isLocal _ (FiniteCNF.incidenceGraph_zero source zero)) occurrences,
    FiniteCNF.satisfiable_erase source zero]

private theorem literal_valid
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    {clause : PeriodicClause (PeriodicPlanarSATVariable V)}
    (clauseMember : clause∈(retainedDrawingPeriodicPlanarSATFormula source).clauses)
    {literal : PeriodicLiteral (PeriodicPlanarSATVariable V)} (literalMember : literal∈clause) :
    RetainedDrawingPeriodicPlanarSATVariableValid source literal.atom := by
  simp only [retainedDrawingPeriodicPlanarSATFormula,List.mem_map] at clauseMember
  obtain ⟨original,originalMember,clauseEq⟩ := clauseMember
  subst clause
  simp only [periodicizePlanarSATClause,List.mem_map] at literalMember
  obtain ⟨oldLiteral,oldMember,literalEq⟩ := literalMember
  subst literal
  apply retainedDrawingPlanarSATVariableValid_normalize source wellFormed degree isLocal
  apply retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid source wellFormed degree isLocal
  rw [EmbeddedCNFIncidenceDrawing.variableVertices,
    retainedDrawingPlanarSATLocalIncidenceDrawing_formula,List.mem_dedup]
  exact List.mem_flatMap.mpr ⟨original,originalMember,List.mem_map.mpr ⟨oldLiteral,oldMember,rfl⟩⟩

private theorem gauged_uniform
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.UniformOffsets (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula source).erase := by
  rw [retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  intro clause member
  simp only [PeriodicCNF.variableGauge,List.mem_map] at member
  obtain ⟨original,originalMember,clauseEq⟩ := member
  subst clause
  simp only [wrapPeriodicPlanarSATFormula,List.mem_map] at originalMember
  obtain ⟨raw,rawMember,wrappedEq⟩ := originalMember
  subst original
  obtain ⟨common,all⟩ := retainedDrawingPeriodicPlanarSATFormula_uniform source wellFormed degree zero raw rawMember
  refine ⟨common,?_⟩
  intro literal hl
  simp only [PeriodicClause.variableGauge,List.mem_map] at hl
  obtain ⟨wrapped,wrappedMember,literalEq⟩ := hl
  subst literal
  simp only [wrapPeriodicPlanarSATClause,List.mem_map] at wrappedMember
  obtain ⟨oldLiteral,oldMember,wrappedLiteralEq⟩ := wrappedMember
  subst wrapped
  have valid := literal_valid source wellFormed degree
    (zeroOffsetGraph_isLocal _ (FiniteCNF.incidenceGraph_zero source zero)) rawMember oldMember
  have gaugeZero := retainedVariableGauge_zero_of_source_zero source wellFormed degree zero _ valid
  have wrappedGaugeZero : retainedDrawingWrappedPeriodicPlanarSATVariableGauge source ⟨oldLiteral.atom⟩=(0,0) := by
    simp only [retainedDrawingWrappedPeriodicPlanarSATVariableGauge,
      wrappedDrawingPeriodicPlanarSATPlacement_canonicalPositionGauge_mk]
    exact gaugeZero
  simpa only [PeriodicLiteral.variableGauge,wrapPeriodicPlanarSATLiteral,
    wrappedGaugeZero,Cell.add,Int.add_zero] using all oldLiteral oldMember

theorem retainedPlanarSATFormula_zero_of_source_zero
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3) (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedPlanarSATFormula source) := by
  intro clause member literal hl
  have originalMember : clause∈
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula source).erase.clauses :=
    (PositionedPeriodicCNF.clause_mem_erase_deduplicateByLiterals_iff _ clause).mp member
  have normalizedZero : FiniteCNF.ZeroOffsets
      (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula source).erase := by
    rw [retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
      PositionedPeriodicCNF.erase_anchorNormalize]
    exact FiniteCNF.uniformOffsets_anchorNormalize _ (gauged_uniform source wellFormed degree zero)
  exact normalizedZero clause originalMember literal hl

theorem retainedPlanarSATFormula_finite_satisfiable_iff
    (zero : FiniteCNF.ZeroOffsets source) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3)
    (nonempty : ∀ clause∈source.clauses,clause≠[]) :
    FiniteCNF.Satisfiable (FiniteCNF.erase (retainedPlanarSATFormula source)) ↔
      FiniteCNF.Satisfiable (FiniteCNF.erase source) := by
  have certificate := retainedPlanarSATCertificate source (FiniteCNF.zeroOffsets_isLocal source zero)
    width occurrences nonempty
  rw [FiniteCNF.satisfiable_erase _ (retainedPlanarSATFormula_zero_of_source_zero source
    certificate.graphWellFormed certificate.graphDegreeAtMostThree zero),
    certificate.sourceSatisfiableIff,FiniteCNF.satisfiable_erase source zero]

end LeanTrominoes.PeriodicOrthocrossing
