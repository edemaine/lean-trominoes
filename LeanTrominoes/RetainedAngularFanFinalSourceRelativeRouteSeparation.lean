/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedRibbonReady
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedPeriodicContinuousPlanarity
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedTerminalDirections
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparationScaling

/-!
# Relative separation of the retained pre-split source routes

The retained gauged drawing already has global continuous planarity,
endpoint-only listed contacts, and the stronger endpoint/interior predicate
needed by its diagonal retained rays.  This module combines those drawing-
level certificates into complete route separation for every pair of periodic
incidence occurrences, in the metadata-rich relative-shift interface used by
the later fixed-eight and Figure 9 constructions.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Every two distinct periodic occurrences of retained pre-split incidence
routes satisfy complete continuous route separation. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ []) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula)
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula) := by
  let source :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let routes :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  have ribbonReady : drawing.IsRibbonReady := by
    simpa [drawing] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isRibbonReady
        formula wellFormed degree isLocal clausesNonempty
  have segmentEndpointsAvoid :
      drawing.SegmentEndpointsAvoidInteriors := by
    simpa [drawing] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_segmentEndpointsAvoidInteriors
        formula wellFormed degree isLocal clausesNonempty
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      source firstMember with
    ⟨firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember, _⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      source secondMember with
    ⟨secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember, _⟩
  have firstRouteMember :
      (routes first.1.clauseIndex first.1.literalIndex, first.2) ∈
        drawing.edgeRoutes.zipIdx := by
    change
      (routes first.1.clauseIndex first.1.literalIndex, first.2) ∈
        (PositionedPeriodicCNF.incidenceDrawing
          source placement routes).edgeRoutes.zipIdx
    exact
      PositionedPeriodicCNF.taggedRoute_mem_of_taggedIncidence
        source placement routes firstMember
  have secondRouteMember :
      (routes second.1.clauseIndex second.1.literalIndex, second.2) ∈
        drawing.edgeRoutes.zipIdx := by
    change
      (routes second.1.clauseIndex second.1.literalIndex, second.2) ∈
        (PositionedPeriodicCNF.incidenceDrawing
          source placement routes).edgeRoutes.zipIdx
    exact
      PositionedPeriodicCNF.taggedRoute_mem_of_taggedIncidence
        source placement routes secondMember
  have firstLength :
      2 ≤ (routes first.1.clauseIndex first.1.literalIndex).length := by
    simpa [source, routes] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        firstClauseMember firstLiteralMember
  have secondLength :
      2 ≤ (routes second.1.clauseIndex second.1.literalIndex).length := by
    simpa [source, routes] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_length_ge_two
        formula wellFormed degree isLocal clausesNonempty
        secondClauseMember secondLiteralMember
  have avoids :=
    PeriodicGridDrawing.routeOccurrences_avoidEachOther_of_segmentEndpointsAvoid
      ribbonReady.1 segmentEndpointsAvoid ribbonReady.2
      firstRouteMember secondRouteMember
      firstLength secondLength (0, 0) relativeTranslate
      occurrencesDifferent
  have zeroTranslate :
      (routes first.1.clauseIndex first.1.literalIndex).map
          (Cell.add (drawing.periodTranslation (0, 0))) =
        routes first.1.clauseIndex first.1.literalIndex := by
    induction routes first.1.clauseIndex first.1.literalIndex with
    | nil => rfl
    | cons point points induction =>
        simp only [List.map_cons]
        rw [induction]
        congr 1
        apply Prod.ext <;>
          simp [drawing, PeriodicGridDrawing.periodTranslation,
            Cell.add, Cell.scale]
  rw [zeroTranslate] at avoids
  have periodPositive : 0 < placement.period := by
    simpa [placement,
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
      wrappedDrawingPeriodicPlanarSATPlacement] using
      drawingPeriodicPlanarSATPlacement_period_pos formula
  have translationEqual :
      drawing.periodTranslation relativeTranslate =
        placement.translation relativeTranslate := by
    change
      (PositionedPeriodicCNF.incidenceDrawing
        source placement routes).periodTranslation relativeTranslate =
      placement.translation relativeTranslate
    simp [
      PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation,
      PositionedPeriodicCNF.incidenceDrawing_gridSize
        source placement routes periodPositive]
  rw [translationEqual] at avoids
  exact avoids

/-- Positive source-clearance scaling preserves complete separation of every
pair of retained pre-split periodic route occurrences. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_scaled_relativeAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {factor : Nat} (factorPositive : 0 < factor) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      ((retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale factor)
      ((retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).scale
        factor)
      (PositionedPeriodicCNF.scaleIncidenceRoutes factor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)) :=
  (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
    formula wellFormed degree isLocal clausesNonempty).scale factorPositive

end PeriodicOrthocrossing
end LeanTrominoes
