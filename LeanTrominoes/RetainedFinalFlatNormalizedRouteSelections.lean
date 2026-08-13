/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedFinalFlatNormalizedRoutes
import LeanTrominoes.PeriodicOrthocrossingRetainedRawCarrierGeometry

/-!
# Clause and literal selections for normalized final flat routes

Carrier-boundary separation is formulated for genuine routes of finite
incidence drawings, selected by membership of a clause and literal in the
drawing's formula.  Anchor normalization preserves the local clause and
literal indices, but changes their physical variables.

This file transports the original final-route membership witnesses into the
normalized drawing and packages them together with the exact route equality.
The package applies uniformly to raw normalized carrier lenses and retained
normalized noncarrier sources.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A final flat route selected as a genuine clause/literal route of an
anchor-normalized local incidence drawing. -/
structure FinalGaugedFlatNormalizedRouteSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (taggedRoute : List Cell × Nat)
    (source : DrawingPlanarSATClauseSource Variable) where
  clause : EmbeddedClause (PlanarSATVariable Variable)
  literal : PlanarSATVariable Variable × Bool
  literalIndex : Nat
  clauseMember :
    (clause, source.localClauseIndex) ∈
      (source.incidenceDrawing formula).formula.zipIdx
  literalMember :
    (literal, literalIndex) ∈ clause.literals.zipIdx
  routeEq :
    taggedRoute.1 =
      (source.incidenceDrawing formula).routes
        source.localClauseIndex literalIndex

/-- A normalized retained noncarrier source carries the final route's
translated clause and literal at the same local indices. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.exists_routeSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell) :
    Nonempty
      (FinalGaugedFlatNormalizedRouteSelection
        formula taggedRoute normalized.source) := by
  have sourceLocalClauseMember :
      (macrocell.routeWitness.metadata.clause,
          macrocell.routeWitness.metadata.source.localClauseIndex) ∈
        (macrocell.routeWitness.metadata.source.clauseFormula
          formula).zipIdx :=
    (macrocell.routeWitness.metadata
      |>.retainedValid_iff_sourceMember_and_localClauseMember
        formula).mp
          macrocell.routeWitness.metadata_retainedValid |>.2
  rcases
      macrocell.routeWitness.metadata.source
        |>.exists_periodTranslatedClauseLiteral
          formula macrocell.routeWitness.physicalShift
          macrocell.routeWitness.metadata.clause
          sourceLocalClauseMember
          macrocell.routeWitness.literal
          macrocell.coordinates.taggedLiteral.2
          macrocell.routeWitness.literalMember with
    ⟨targetClause, targetLiteral,
      translatedClauseMember, targetLiteralMember⟩
  let translatedSource :=
    macrocell.routeWitness.metadata.source.periodTranslate
      formula macrocell.routeWitness.physicalShift
  have targetFormulaEq :
      normalized.source.clauseFormula formula =
        translatedSource.clauseFormula formula :=
    normalized.source.clauseFormula_eq_of_component_eq
      formula translatedSource normalized.componentEq
  have translatedLocalClauseIndexEq :
      translatedSource.localClauseIndex =
        macrocell.routeWitness.metadata.source.localClauseIndex :=
    DrawingPlanarSATClauseSource.localClauseIndex_periodTranslate
      formula macrocell.routeWitness.metadata.source
      macrocell.routeWitness.physicalShift
  have targetClauseMember :
      (targetClause, normalized.source.localClauseIndex) ∈
        (normalized.source.clauseFormula formula).zipIdx := by
    rw [targetFormulaEq, normalized.localClauseIndexEq,
      ← translatedLocalClauseIndexEq]
    exact translatedClauseMember
  let targetMetadata :
      DrawingPlanarSATClauseMetadata Variable :=
    ⟨targetClause, normalized.source⟩
  have targetValid : targetMetadata.RetainedValid formula := by
    apply
      (targetMetadata
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mpr
    exact ⟨normalized.sourceMember, targetClauseMember⟩
  have targetDrawingClauseMember :
      (targetClause, normalized.source.localClauseIndex) ∈
        (normalized.source.incidenceDrawing
          formula).formula.zipIdx := by
    simpa only [targetMetadata] using
      targetMetadata.retainedLocalClauseMember
        wellFormed degree isLocal targetValid
  exact ⟨{
    clause := targetClause
    literal := targetLiteral
    literalIndex := macrocell.coordinates.taggedLiteral.2
    clauseMember := targetDrawingClauseMember
    literalMember := targetLiteralMember
    routeEq := normalized.routeEq
  }⟩

/-- A raw normalized carrier lens carries the final route's translated
clause and literal at the same local indices. -/
theorem
    FinalGaugedFlatCarrierRouteWitness.exists_normalizedRouteSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    (carrier :
      FinalGaugedFlatCarrierRouteWitness
        formula taggedRoute) :
    ∃ localClauseIndex,
      Nonempty
        (FinalGaugedFlatNormalizedRouteSelection
          formula taggedRoute
            (.carrier carrier.normalizedLink localClauseIndex)) := by
  rcases
      carrier.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq
          carrier.link carrier.componentEq with
    ⟨localClauseIndex, sourceEq⟩
  have sourceLocalClauseMember :
      (carrier.routeWitness.metadata.clause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) carrier.link).zipIdx := by
    have localMember :=
      (carrier.routeWitness.metadata
        |>.retainedValid_iff_sourceMember_and_localClauseMember
          formula).mp
            carrier.routeWitness.metadata_retainedValid |>.2
    simpa [sourceEq,
      DrawingPlanarSATClauseSource.clauseFormula,
      DrawingPlanarSATClauseSource.localClauseIndex] using
        localMember
  rcases
      carrier.routeWitness.metadata.source
        |>.exists_periodTranslatedClauseLiteral
          formula carrier.routeWitness.physicalShift
          carrier.routeWitness.metadata.clause
          (by
            simpa [sourceEq,
              DrawingPlanarSATClauseSource.clauseFormula,
              DrawingPlanarSATClauseSource.localClauseIndex] using
                sourceLocalClauseMember)
          carrier.routeWitness.literal
          carrier.coordinates.taggedLiteral.2
          carrier.routeWitness.literalMember with
    ⟨targetClause, targetLiteral,
      translatedClauseMember, targetLiteralMember⟩
  have targetClauseMember :
      (targetClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) carrier.normalizedLink).zipIdx := by
    simpa [sourceEq,
      DrawingPlanarSATClauseSource.periodTranslate,
      DrawingPlanarSATClauseSource.clauseFormula,
      DrawingPlanarSATClauseSource.localClauseIndex,
      FinalGaugedFlatCarrierRouteWitness.normalizedLink] using
        translatedClauseMember
  have normalizedLinkMem :=
    carrier.normalizedLink_mem_raw
      formula wellFormed degree isLocal
  have targetDrawingClauseMember :
      (targetClause, localClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrier.normalizedLink).formula.zipIdx := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal normalizedLinkMem]
    exact targetClauseMember
  refine ⟨localClauseIndex, ⟨{
    clause := targetClause
    literal := targetLiteral
    literalIndex := carrier.coordinates.taggedLiteral.2
    clauseMember := ?_
    literalMember := targetLiteralMember
    routeEq :=
      carrier.route_eq_normalizedLink_of_source_eq sourceEq
  }⟩⟩
  simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using
      targetDrawingClauseMember

end PeriodicOrthocrossing
end LeanTrominoes
