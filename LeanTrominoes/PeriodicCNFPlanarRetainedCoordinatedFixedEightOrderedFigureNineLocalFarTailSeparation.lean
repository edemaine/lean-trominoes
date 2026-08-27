/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalInheritedSeparation

/-!
# Local/far-tail separation for retained Figure 9 routes

The same radius-72 source-gauge argument used for complete inherited suffixes
does not require the local route to avoid the near connector.  This file
exports that strictly weaker fact so that the connector's advertised splice
endpoint may coincide with the local route endpoint.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- A normalized local route avoids the refined far tail inherited from an
incidence of the same generated clause.  Unlike separation from the complete
suffix, this remains true when the local route ends at the connector splice
point. -/
theorem
    retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_sameClauseFarTail
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clauseIndex localLiteralIndex inheritedLiteralIndex : Nat}
    (data :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex inheritedLiteralIndex)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈
        data.generatedClause.literals.zipIdx)
    (first second : Cell)
    (rest : List Cell)
    (originalRouteEq :
      retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex =
        first :: second :: rest) :
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        clauseIndex localLiteralIndex)
      (translatePolyline
        (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          (retainedFigureNineClearancePlacement source)
          data.sourceClause data.generatedClause)
        (scalePolyline
          PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (AxisDirection.unitSubdividePolyline
            (scalePolyline 2 (second :: rest))))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement clauseIndex localLiteralIndex
  have sourceClauseNonempty : data.sourceClause.literals ≠ [] := by
    exact List.ne_nil_of_mem
      (List.fst_mem_of_mem_zipIdx data.sourceLiteralMember)
  rcases exists_clockwiseClause_of_clearanceClause_mem
      data.sourceClauseMember with
    ⟨clockwiseClause, clockwiseClauseMember, sourceClauseEq⟩
  let originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes
      source data.sourceClauseIndex data.sourceLiteralIndex
  have originalOrthogonal : OrthogonalPolyline originalRoute :=
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)).2.2
  have originalSimple :
      LocalIncidenceDrawing.RouteIsSimple originalRoute :=
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitIncidenceRoutes_isSimple
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clockwiseClauseMember
      (by simpa [sourceClauseEq] using data.sourceLiteralMember)
  have clearanceRouteEq :
      retainedFigureNineClearanceIncidenceRoutes
          source data.sourceClauseIndex data.sourceLiteralIndex =
        AxisDirection.unitSubdividePolyline
          (scalePolyline 2 (first :: second :: rest)) := by
    simpa [originalRoute, originalRouteEq,
      retainedFigureNineSourceClearanceFactor] using
      retainedFigureNineClearanceIncidenceRoutes_eq_unitSubdividePolyline
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty data.sourceClauseMember
        data.sourceLiteralMember
  have clearanceHead :=
    (retainedFigureNineClearanceIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty data.sourceClauseMember
      data.sourceLiteralMember).1
  have subdividedHead :
      (AxisDirection.unitSubdividePolyline
        (scalePolyline 2 (first :: second :: rest))).head? =
          some (Cell.scale 2 first) := by
    simpa [scalePolyline] using
      AxisDirection.unitSubdividePolyline_head?
        (points := scalePolyline 2 (first :: second :: rest))
        (by simp)
  have scaledHead :
      Cell.scale 2 first =
        PositionedPeriodicCNF.canonicalClausePosition
          clearancePlacement data.sourceClause := by
    apply Option.some.inj
    exact subdividedHead.symm.trans (clearanceRouteEq ▸ clearanceHead)
  have localBounded :=
    normalizedLocalRoutes_points_within_sourceGaugeRadius72_at_metadata
      clearanceSource clearancePlacement clearanceWidth
      data.generatedClauseMember localLiteralMember
      data.metadata data.metadataLookup
  have centerEq :
      Cell.scale
          PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale
          (PlanarOneInThreeNoUnitsFigureNine.localRouteSourceGaugeCenter
            clearancePlacement data.metadata.sourceClause
            data.generatedClause) =
        Cell.add
          (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
            outputPlacement clearancePlacement data.sourceClause
            data.generatedClause)
          (Cell.scale 144 first) := by
    rw [data.metadataSourceClause,
      ← PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition_eq_scale_sourceGaugeCenter
        clearanceSource clearancePlacement data.sourceClause
        data.generatedClause]
    simp only [
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift]
    rw [← scaledHead]
    apply Prod.ext <;>
      simp [outputPlacement,
        PlanarOneInThreeNoUnitsFigureNine.composedGadgetScale,
        PlanarOneInThree.gadgetScale,
        PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        Cell.add, Cell.sub, Cell.scale] <;>
      ring
  have localBounded' :
      ∀ point ∈ localRoute,
        WithinCoordinateRadius 72
          (Cell.add
            (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
              outputPlacement clearancePlacement data.sourceClause
              data.generatedClause)
            (Cell.scale 144 first)) point := by
    intro point pointMember
    rw [← centerEq]
    exact localBounded point (by simpa [localRoute] using pointMember)
  have localOrthogonal : OrthogonalPolyline localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_orthogonal_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      data.generatedClauseMember localLiteralMember
  exact
    PlanarOneInThreeNoUnitsFigureNine.strictlyAvoids_translatedScaledDoubledSubdividedTail
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteShift
        outputPlacement clearancePlacement data.sourceClause
        data.generatedClause)
      (by simpa [originalRoute, originalRouteEq] using originalOrthogonal)
      (by simpa [originalRoute, originalRouteEq] using originalSimple)
      localOrthogonal localBounded'

end PeriodicOrthocrossing
end LeanTrominoes
