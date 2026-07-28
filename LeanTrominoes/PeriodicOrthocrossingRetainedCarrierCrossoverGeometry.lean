import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverProximity
import LeanTrominoes.PeriodicOrthocrossingContinuousParallel
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierCore
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverSeparation

/-!
# Selected retained carriers versus arbitrary crossovers

Macrocell overlap puts a selected carrier on the row or column of the
crossover center.  Its source interval then has continuously overlapping
interior with the corresponding crossing occurrence.  Continuous lane
uniqueness identifies the occurrence key, after which the matched-key
proximity theorem forces endpoint incidence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Horizontal macrocell overlap identifies the selected carrier with the
crossing's horizontal source occurrence. -/
theorem
    retainedDrawingCompleteCarrierLink_horizontal_key_eq_of_crossover_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontal : link.first.isHorizontal = true)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower crossing.point)
        (planarSATMacrocellRouteUpper crossing.point)) :
    link.first.carrierKey =
      (CarrierNode.boundary
        ⟨crossing, .left⟩).carrierKey := by
  let support := link.first.supportingSegment graph
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (retainedCarrierNode_indexed_mem graph endpoints.1)
  have storedHorizontal :
      link.first.indexed.segment.IsHorizontal :=
    (retainedCarrierNode_isHorizontal_iff
      graph endpoints.1 firstAligned).mp horizontal
  have supportHorizontal : support.IsHorizontal := by
    exact
      (GridSegment.isHorizontal_translate _ _).mpr
        storedHorizontal
  have overlapData :=
    retainedDrawingCompleteCarrierLink_horizontal_macrocell_overlap_data
      wellFormed degree isLocal linkMem horizontal
      crossing.point notSeparated
  have supportBounds :=
    retainedDrawingCompleteCarrierLink_horizontal_support_bounded
      wellFormed degree isLocal linkMem horizontal
  simp only [planarMacroScale] at overlapData supportBounds
  have pointInSupport :
      min support.start.1 support.finish.1 ≤ crossing.point.1 ∧
        crossing.point.1 ≤
          max support.start.1 support.finish.1 := by
    change
      min (link.first.supportingSegment graph).start.1
          (link.first.supportingSegment graph).finish.1 ≤
          crossing.point.1 ∧
        crossing.point.1 ≤
          max (link.first.supportingSegment graph).start.1
            (link.first.supportingSegment graph).finish.1
    constructor <;> omega
  have supportNonempty :
      min support.start.1 support.finish.1 <
        max support.start.1 support.finish.1 := by
    rcases lt_or_gt_of_ne supportHorizontal.2 with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have retainedMem :
      crossing ∈ retainedCrossings graph :=
    orientedCrossingHalo_subset_retainedCrossings
      wellFormed degree isLocal crossingMem
  have crossingSound :=
    retainedCrossings_sound graph retainedMem
  have crossingAxes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph retainedMem
  have crossingContains :
      (crossing.firstSegment graph).InteriorContains
        crossing.point :=
    crossingSound.2.2.1
  have crossingSameNormal :
      crossing.point.2 =
        (crossing.firstSegment graph).start.2 := by
    rcases crossingContains with onHorizontal | onVertical
    · exact onHorizontal.2.1
    · exact False.elim
        (crossingAxes.1.2 onVertical.1.1)
  have crossingBetween :
      GridSegment.StrictlyBetween
        (crossing.firstSegment graph).start.1
        (crossing.firstSegment graph).finish.1
        crossing.point.1 := by
    rcases crossingContains with onHorizontal | onVertical
    · exact onHorizontal.2.2
    · exact False.elim
        (crossingAxes.1.2 onVertical.1.1)
  have crossingBounds :
      min (crossing.firstSegment graph).start.1
            (crossing.firstSegment graph).finish.1 <
          crossing.point.1 ∧
        crossing.point.1 <
          max (crossing.firstSegment graph).start.1
            (crossing.firstSegment graph).finish.1 := by
    rcases crossingBetween with forward | backward
    · have ordered :
          (crossing.firstSegment graph).start.1 ≤
            (crossing.firstSegment graph).finish.1 := by
        omega
      rw [min_eq_left ordered, max_eq_right ordered]
      exact forward
    · have ordered :
          (crossing.firstSegment graph).finish.1 ≤
            (crossing.firstSegment graph).start.1 := by
        omega
      rw [min_eq_right ordered, max_eq_left ordered]
      exact backward
  have openOverlap :
      GridSegment.OpenIntervalsOverlap
        support.start.1 support.finish.1
        (crossing.firstSegment graph).start.1
        (crossing.firstSegment graph).finish.1 := by
    unfold GridSegment.OpenIntervalsOverlap
    omega
  have sameNormal :
      support.start.2 =
        (crossing.firstSegment graph).start.2 := by
    exact overlapData.1.trans crossingSameNormal
  have meet :
      GridSegment.InteriorsMeet
        support (crossing.firstSegment graph) :=
    Or.inl
      ⟨supportHorizontal, crossingAxes.1,
        sameNormal, openOverlap⟩
  have occurrenceEqual :=
    drawing_hasUniqueHorizontalContinuousInteriors
      wellFormed degree isLocal
      link.first.indexed
      (retainedCarrierNode_indexed_mem graph endpoints.1)
      crossing.first crossingSound.1
      link.first.translate crossing.firstTranslate
      (by
        simpa [support, CarrierNode.supportingSegment] using
          supportHorizontal)
      crossingAxes.1
      (by
        simpa [support, CarrierNode.supportingSegment,
          CrossingRecord.firstSegment] using meet)
  calc
    link.first.carrierKey =
        PeriodicGridDrawing.SegmentOccurrenceKey
          link.first.indexed link.first.translate :=
      CarrierNode.carrierKey_eq_indexed_translate link.first
    _ =
        PeriodicGridDrawing.SegmentOccurrenceKey
          crossing.first crossing.firstTranslate :=
      occurrenceEqual
    _ =
        (CarrierNode.boundary
          ⟨crossing, .left⟩).carrierKey := by
      rfl

/-- Vertical macrocell overlap identifies the selected carrier with the
crossing's vertical source occurrence. -/
theorem
    retainedDrawingCompleteCarrierLink_vertical_key_eq_of_crossover_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (vertical : ¬link.first.isHorizontal = true)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower crossing.point)
        (planarSATMacrocellRouteUpper crossing.point)) :
    link.first.carrierKey =
      (CarrierNode.boundary
        ⟨crossing, .top⟩).carrierKey := by
  let support := link.first.supportingSegment graph
  have endpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem graph linkMem
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (retainedCarrierNode_indexed_mem graph endpoints.1)
  have storedVertical :
      link.first.indexed.segment.IsVertical := by
    exact firstAligned.resolve_left fun storedHorizontal =>
      vertical
        ((retainedCarrierNode_isHorizontal_iff
          graph endpoints.1 firstAligned).mpr storedHorizontal)
  have supportVertical : support.IsVertical := by
    exact
      (GridSegment.isVertical_translate _ _).mpr
        storedVertical
  have overlapData :=
    retainedDrawingCompleteCarrierLink_vertical_macrocell_overlap_data
      wellFormed degree isLocal linkMem vertical
      crossing.point notSeparated
  have supportBounds :=
    retainedDrawingCompleteCarrierLink_vertical_support_bounded
      wellFormed degree isLocal linkMem vertical
  simp only [planarMacroScale] at overlapData supportBounds
  have pointInSupport :
      min support.start.2 support.finish.2 ≤ crossing.point.2 ∧
        crossing.point.2 ≤
          max support.start.2 support.finish.2 := by
    change
      min (link.first.supportingSegment graph).start.2
          (link.first.supportingSegment graph).finish.2 ≤
          crossing.point.2 ∧
        crossing.point.2 ≤
          max (link.first.supportingSegment graph).start.2
            (link.first.supportingSegment graph).finish.2
    constructor <;> omega
  have supportNonempty :
      min support.start.2 support.finish.2 <
        max support.start.2 support.finish.2 := by
    rcases lt_or_gt_of_ne supportVertical.2 with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have retainedMem :
      crossing ∈ retainedCrossings graph :=
    orientedCrossingHalo_subset_retainedCrossings
      wellFormed degree isLocal crossingMem
  have crossingSound :=
    retainedCrossings_sound graph retainedMem
  have crossingAxes :=
    retainedCrossing_firstHorizontal_secondVertical
      graph retainedMem
  have crossingContains :
      (crossing.secondSegment graph).InteriorContains
        crossing.point :=
    crossingSound.2.2.2.1
  have crossingSameNormal :
      crossing.point.1 =
        (crossing.secondSegment graph).start.1 := by
    rcases crossingContains with onHorizontal | onVertical
    · exact False.elim
        (crossingAxes.2.2 onHorizontal.1.1)
    · exact onVertical.2.1
  have crossingBetween :
      GridSegment.StrictlyBetween
        (crossing.secondSegment graph).start.2
        (crossing.secondSegment graph).finish.2
        crossing.point.2 := by
    rcases crossingContains with onHorizontal | onVertical
    · exact False.elim
        (crossingAxes.2.2 onHorizontal.1.1)
    · exact onVertical.2.2
  have crossingBounds :
      min (crossing.secondSegment graph).start.2
            (crossing.secondSegment graph).finish.2 <
          crossing.point.2 ∧
        crossing.point.2 <
          max (crossing.secondSegment graph).start.2
            (crossing.secondSegment graph).finish.2 := by
    rcases crossingBetween with forward | backward
    · have ordered :
          (crossing.secondSegment graph).start.2 ≤
            (crossing.secondSegment graph).finish.2 := by
        omega
      rw [min_eq_left ordered, max_eq_right ordered]
      exact forward
    · have ordered :
          (crossing.secondSegment graph).finish.2 ≤
            (crossing.secondSegment graph).start.2 := by
        omega
      rw [min_eq_right ordered, max_eq_left ordered]
      exact backward
  have openOverlap :
      GridSegment.OpenIntervalsOverlap
        support.start.2 support.finish.2
        (crossing.secondSegment graph).start.2
        (crossing.secondSegment graph).finish.2 := by
    unfold GridSegment.OpenIntervalsOverlap
    omega
  have sameNormal :
      support.start.1 =
        (crossing.secondSegment graph).start.1 := by
    exact overlapData.1.trans crossingSameNormal
  have meet :
      GridSegment.InteriorsMeet
        support (crossing.secondSegment graph) :=
    Or.inr
      (Or.inl
        ⟨supportVertical, crossingAxes.2,
          sameNormal, openOverlap⟩)
  have occurrenceEqual :=
    drawing_hasUniqueVerticalContinuousInteriors
      wellFormed degree isLocal
      link.first.indexed
      (retainedCarrierNode_indexed_mem graph endpoints.1)
      crossing.second crossingSound.2.1
      link.first.translate crossing.secondTranslate
      (by
        simpa [support, CarrierNode.supportingSegment] using
          supportVertical)
      crossingAxes.2
      (by
        simpa [support, CarrierNode.supportingSegment,
          CrossingRecord.secondSegment] using meet)
  calc
    link.first.carrierKey =
        PeriodicGridDrawing.SegmentOccurrenceKey
          link.first.indexed link.first.translate :=
      CarrierNode.carrierKey_eq_indexed_translate link.first
    _ =
        PeriodicGridDrawing.SegmentOccurrenceKey
          crossing.second crossing.secondTranslate :=
      occurrenceEqual
    _ =
        (CarrierNode.boundary
          ⟨crossing, .top⟩).carrierKey := by
      rfl

/-- Overlap between a selected retained carrier lens and any enumerated
crossover macrocell forces endpoint incidence. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToCrossover_of_overlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ orientedCrossingHalo graph)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower crossing.point)
        (planarSATMacrocellRouteUpper crossing.point)) :
    CarrierLinkIncidentToCrossover link crossing := by
  have retainedMem :
      crossing ∈ retainedCrossings graph :=
    orientedCrossingHalo_subset_retainedCrossings
      wellFormed degree isLocal crossingMem
  by_cases horizontal : link.first.isHorizontal = true
  · exact
      retainedDrawingCompleteCarrierLink_incidentToCrossover_of_horizontal_key_eq
        wellFormed degree isLocal linkMem horizontal retainedMem
        (retainedDrawingCompleteCarrierLink_horizontal_key_eq_of_crossover_overlap
          wellFormed degree isLocal linkMem horizontal
          crossingMem notSeparated)
        notSeparated
  · exact
      retainedDrawingCompleteCarrierLink_incidentToCrossover_of_vertical_key_eq
        wellFormed degree isLocal linkMem horizontal retainedMem
        (retainedDrawingCompleteCarrierLink_vertical_key_eq_of_crossover_overlap
          wellFormed degree isLocal linkMem horizontal
          crossingMem notSeparated)
        notSeparated

/-- Every route of a selected retained carrier lens avoids every route of
every enumerated crossover drawing.  Overlap can happen only at a genuine
carrier endpoint of that crossover; all other pairs occupy separated
rectangles. -/
theorem
    retainedDrawingPlanarSATCarrierCrossoverRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {carrierLink : EqualityLink CarrierNode}
    (carrierLinkMember :
      carrierLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {crossing : CrossingRecord}
    (crossingMember :
      crossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula))
    {carrierClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {carrierClauseIndex : Nat}
    (carrierClauseMember :
      (carrierClause, carrierClauseIndex) ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula carrierLink).formula.zipIdx)
    {carrierLiteral : PlanarSATVariable Variable × Bool}
    {carrierLiteralIndex : Nat}
    (carrierLiteralMember :
      (carrierLiteral, carrierLiteralIndex) ∈
        carrierClause.literals.zipIdx)
    {crossoverClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {crossoverClauseIndex : Nat}
    (crossoverClauseMember :
      (crossoverClause, crossoverClauseIndex) ∈
        (drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).formula.zipIdx)
    {crossoverLiteral : PlanarSATVariable Variable × Bool}
    {crossoverLiteralIndex : Nat}
    (crossoverLiteralMember :
      (crossoverLiteral, crossoverLiteralIndex) ∈
        crossoverClause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula carrierLink).routes
          carrierClauseIndex carrierLiteralIndex)
      ((drawingPlanarSATCrossoverIncidenceDrawing
        formula crossing).routes
          crossoverClauseIndex crossoverLiteralIndex) := by
  by_cases incident :
      CarrierLinkIncidentToCrossover carrierLink crossing
  · exact
      retainedDrawingPlanarSATCarrierCrossoverRoutesAvoidEachOther_of_incident
        wellFormed degree isLocal carrierLinkMember incident
        carrierClauseMember carrierLiteralMember
        crossoverClauseMember crossoverLiteralMember
  · have rectanglesSeparated :
        ClosedGridRectanglesSeparated
          (drawingCompleteCarrierLinkRectangleLower
            (PeriodicCNF.incidenceGraph formula) carrierLink)
          (drawingCompleteCarrierLinkRectangleUpper
            (PeriodicCNF.incidenceGraph formula) carrierLink)
          (planarSATMacrocellRouteLower crossing.point)
          (planarSATMacrocellRouteUpper crossing.point) := by
      by_contra notSeparated
      exact incident
        (retainedDrawingCompleteCarrierLink_incidentToCrossover_of_overlap
          wellFormed degree isLocal carrierLinkMember crossingMember
          notSeparated)
    exact
      retainedDrawingPlanarSATCarrierRoute_avoids_macrocell_of_rectanglesSeparated
        wellFormed degree isLocal carrierLinkMember
        carrierClauseMember carrierLiteralMember
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_bounded
          formula crossing)
        crossoverClauseMember crossoverLiteralMember
        rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
