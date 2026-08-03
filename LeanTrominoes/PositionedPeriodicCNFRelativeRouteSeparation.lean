import LeanTrominoes.PeriodicGridDrawingLiftedRouteSeparation
import LeanTrominoes.PositionedPeriodicCNFTaggedRouteLookup
import LeanTrominoes.OrthogonalPolylineLoopErasureTranslation
import LeanTrominoes.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.PeriodicGridDrawingLoopErasure

/-!
# Relative route separation indexed by positioned incidences

The periodic drawing interface stores only a flat list of routes.  Geometric
replacement proofs need the clause and literal metadata that selected each
route.  This module transports the relative lifted-route obligation across
the lossless positioned-incidence enumeration.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every pair of genuine positioned incidences avoids each other after one
relative semantic-lattice translation.  The flat incidence indices make the
exception exactly the same as in the drawing-level lifted predicate. -/
def RelativeIncidenceRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes) : Prop :=
  ∀ first ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
    ∀ second ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
      ∀ relativeTranslate,
        (first.2, (0, 0)) ≠
            (second.2, relativeTranslate) →
          RoutesAvoidEachOther
            (routes first.1.clauseIndex first.1.literalIndex)
            ((routes second.1.clauseIndex
                second.1.literalIndex).map
              (Cell.add
                (placement.translation relativeTranslate)))

/-- Relative incidence separation survives pointwise orthogonal loop
erasure.  Translation equivariance identifies normalization of the lifted
second route with the lift of its stored normalized representative. -/
theorem RelativeIncidenceRoutesAvoidEachOther.normalizeOrthogonalIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {routes : IncidenceRoutes}
    (separated :
      RelativeIncidenceRoutesAvoidEachOther source placement routes)
    (nonempty :
      ∀ incidence ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
        routes incidence.1.clauseIndex incidence.1.literalIndex ≠ [])
    (orthogonal :
      ∀ incidence ∈
          (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
        PeriodicOrthocrossing.OrthogonalPolyline
          (routes incidence.1.clauseIndex
            incidence.1.literalIndex)) :
    RelativeIncidenceRoutesAvoidEachOther source placement
      (normalizeOrthogonalIncidenceRoutes routes) := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  let offset := placement.translation relativeTranslate
  have firstNonempty := nonempty first firstMember
  have secondNonempty := nonempty second secondMember
  have firstOrthogonal := orthogonal first firstMember
  have secondOrthogonal := orthogonal second secondMember
  have avoids :=
    separated first firstMember second secondMember
      relativeTranslate occurrencesDifferent
  have normalizedAvoids :=
    avoids.normalizeOrthogonalPolyline
      firstNonempty
      (by simpa [offset] using secondNonempty)
      firstOrthogonal
      (secondOrthogonal.translate offset)
  rw [AxisDirection.normalizeOrthogonalPolyline_map_add
      secondNonempty secondOrthogonal offset] at normalizedAvoids
  change
    RoutesAvoidEachOther
      (AxisDirection.normalizeOrthogonalPolyline
        (routes first.1.clauseIndex first.1.literalIndex))
      ((AxisDirection.normalizeOrthogonalPolyline
        (routes second.1.clauseIndex
          second.1.literalIndex)).map (Cell.add offset))
  exact normalizedAvoids

/-- Incidence-indexed relative separation supplies the anonymous flat-route
predicate used by the generic ribbon-readiness bridge. -/
theorem incidenceDrawing_relativeLiftedRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (periodPositive : 0 < placement.period)
    (separated :
      RelativeIncidenceRoutesAvoidEachOther source placement routes) :
    PeriodicGridDrawing.RelativeLiftedRoutesAvoidEachOther
      (incidenceDrawing source placement routes) := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  rcases exists_incidenceCoordinates_of_taggedRoute
      source placement routes first firstMember with
    ⟨firstIncidence, firstIncidenceMember,
      firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember,
      firstRouteEq, firstIndexEq⟩
  rcases exists_incidenceCoordinates_of_taggedRoute
      source placement routes second secondMember with
    ⟨secondIncidence, secondIncidenceMember,
      secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember,
      secondRouteEq, secondIndexEq⟩
  have incidenceOccurrencesDifferent :
      (firstIncidence.2, (0, 0)) ≠
        (secondIncidence.2, relativeTranslate) := by
    intro equal
    apply occurrencesDifferent
    have indexEqual : first.2 = second.2 := by
      calc
        first.2 = firstIncidence.2 := firstIndexEq.symm
        _ = secondIncidence.2 :=
          congrArg
            (fun occurrence : Nat × Cell => occurrence.1) equal
        _ = second.2 := secondIndexEq
    have relativeEqual : (0, 0) = relativeTranslate :=
      congrArg
        (fun occurrence : Nat × Cell => occurrence.2) equal
    apply Prod.ext
    · exact indexEqual
    · exact relativeEqual
  have avoids :=
    separated firstIncidence firstIncidenceMember
      secondIncidence secondIncidenceMember
      relativeTranslate incidenceOccurrencesDifferent
  have translationEqual :
      (incidenceDrawing source placement routes).periodTranslation
          relativeTranslate =
        placement.translation relativeTranslate := by
    simp [PeriodicGridDrawing.periodTranslation,
      PeriodicVariablePlacement.translation,
      incidenceDrawing_gridSize source placement routes periodPositive]
  rw [firstRouteEq, secondRouteEq, translationEqual]
  exact avoids

end PositionedPeriodicCNF
end LeanTrominoes
