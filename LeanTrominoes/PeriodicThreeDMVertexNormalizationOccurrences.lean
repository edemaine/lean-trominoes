import LeanTrominoes.PeriodicThreeDMVertexNormalizationStageDrawings
import LeanTrominoes.PeriodicThreeDMContractionEndpointContacts
import LeanTrominoes.RetainedRayRasterizationTranslation

/-!
# Lifted occurrences of vertex-normalized routes

Local endpoint replacement is most naturally proved on complete periodic
route occurrences.  This module records the translation-equivariance of
the magnification, trimming, and template-splicing operations, then gives
an exact occurrence formula for the first normalization round.
-/

namespace LeanTrominoes

open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Normalizing positions commutes with translating the old position, up
to the corresponding twelvefold translation of the new position. -/
theorem normalizeVertexPosition_add_left
    (shift position : Cell) :
    normalizeVertexPosition (Cell.add shift position) =
      Cell.add (Cell.scale vertexNormalizationScale shift)
        (normalizeVertexPosition position) := by
  rcases shift with ⟨shiftX, shiftY⟩
  rcases position with ⟨positionX, positionY⟩
  simp [normalizeVertexPosition, vertexNormalizationScale,
    DegreeThreeVertexNormalization.center, Cell.add, Cell.scale]
  constructor <;> ring

/-- Anchored local templates commute with a translation of their old
vertex position. -/
theorem normalizationTemplateAt_add_left
    (shift position : Cell) (template : List Cell) :
    normalizationTemplateAt (Cell.add shift position) template =
      translatePolyline (Cell.scale vertexNormalizationScale shift)
        (normalizationTemplateAt position template) := by
  unfold normalizationTemplateAt
    PeriodicOrthocrossing.translatePolyline
  rw [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  rcases shift with ⟨shiftX, shiftY⟩
  rcases position with ⟨positionX, positionY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [vertexNormalizationScale, Cell.add, Cell.scale]
  constructor <;> ring

/-- Magnification and ordered unit subdivision commute with translating
the old route. -/
theorem magnifiedUnitRoute_translatePolyline
    (shift : Cell) (points : List Cell) :
    magnifiedUnitRoute (translatePolyline shift points) =
      translatePolyline (Cell.scale vertexNormalizationScale shift)
        (magnifiedUnitRoute points) := by
  unfold magnifiedUnitRoute
    PeriodicOrthocrossing.translatePolyline
  have normalizedMap :
      (points.map (Cell.add shift)).map normalizeVertexPosition =
        (points.map normalizeVertexPosition).map
          (Cell.add (Cell.scale vertexNormalizationScale shift)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro point pointMember
    exact normalizeVertexPosition_add_left shift point
  rw [normalizedMap]
  exact AxisDirection.unitSubdividePolyline_map_add
    (Cell.scale vertexNormalizationScale shift)
    (points.map normalizeVertexPosition)

/-- The symmetric endpoint trim is translation-equivariant as well. -/
theorem trimmedMagnifiedRoute_translatePolyline
    (shift : Cell) (points : List Cell) :
    trimmedMagnifiedRoute (translatePolyline shift points) =
      translatePolyline (Cell.scale vertexNormalizationScale shift)
        (trimmedMagnifiedRoute points) := by
  unfold trimmedMagnifiedRoute
  rw [magnifiedUnitRoute_translatePolyline]
  unfold PeriodicOrthocrossing.translatePolyline
  simp only [List.length_map]
  rw [← List.map_drop, ← List.map_take]

/-- A complete local replacement commutes with translating the old route
and both old endpoint positions. -/
theorem normalizeRouteWithTemplates_translatePolyline
    (shift sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell) :
    normalizeRouteWithTemplates
        (Cell.add shift sourcePosition)
        (Cell.add shift targetPosition)
        sourceTemplate targetTemplate
        (translatePolyline shift oldRoute) =
      translatePolyline (Cell.scale vertexNormalizationScale shift)
        (normalizeRouteWithTemplates
          sourcePosition targetPosition
          sourceTemplate targetTemplate oldRoute) := by
  unfold normalizeRouteWithTemplates
  rw [translatePolyline_joinAtEndpoint,
    translatePolyline_joinAtEndpoint,
    ← normalizationTemplateAt_add_left,
    ← trimmedMagnifiedRoute_translatePolyline,
    show
      translatePolyline (Cell.scale vertexNormalizationScale shift)
          (normalizationTemplateAt targetPosition targetTemplate).reverse =
        (normalizationTemplateAt
          (Cell.add shift targetPosition) targetTemplate).reverse by
        rw [show
          translatePolyline (Cell.scale vertexNormalizationScale shift)
              (normalizationTemplateAt targetPosition targetTemplate).reverse =
            (translatePolyline
              (Cell.scale vertexNormalizationScale shift)
              (normalizationTemplateAt
                targetPosition targetTemplate)).reverse by
              simp [translatePolyline]]
        rw [← normalizationTemplateAt_add_left]]

/-- The first normalized route realized at an arbitrary lattice translate. -/
def PlanarPresentation.normalizationRouteOccurrence1
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (translate : Cell) : List Cell :=
  translatePolyline
    (presentation.normalizationGridDrawing1.periodTranslation translate)
    (presentation.normalizationRoute1 edge)

/-- One first-stage period translation is the twelvefold image of the old
contracted-drawing period translation. -/
theorem PlanarPresentation.normalizationGridDrawing1_periodTranslation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) (translate : Cell) :
    presentation.normalizationGridDrawing1.periodTranslation translate =
      Cell.scale vertexNormalizationScale
        (presentation.contractedDrawing.periodTranslation translate) := by
  rcases translate with ⟨translateX, translateY⟩
  simp [PeriodicGridDrawing.periodTranslation,
    vertexNormalizationScale, Cell.scale]
  constructor <;> ring

/-- A lifted first-round route is literally the same local splice applied
to the corresponding lifted contracted route and lifted old endpoints. -/
theorem PlanarPresentation.normalizationRouteOccurrence1_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) (translate : Cell) :
    presentation.normalizationRouteOccurrence1 edge translate =
      normalizeRouteWithTemplates
        (Cell.add
          (presentation.contractedDrawing.periodTranslation translate)
          (presentation.normalizationPosition0
            edge.toPeriodicEdge.source))
        (Cell.add
          (presentation.contractedDrawing.periodTranslation translate)
          (presentation.normalizationTarget0 edge))
        ((ContractedEndpoint.source edge).firstNormalizationTemplate
          presentation)
        ((ContractedEndpoint.target edge).firstNormalizationTemplate
          presentation)
        (presentation.contractedEdgeRouteOccurrence edge translate) := by
  unfold PlanarPresentation.normalizationRouteOccurrence1
    PlanarPresentation.normalizationRoute1
  rw [presentation.normalizationGridDrawing1_periodTranslation]
  rw [← normalizeRouteWithTemplates_translatePolyline]
  unfold PlanarPresentation.contractedEdgeRouteOccurrence
  rfl

end PeriodicThreeDM
end LeanTrominoes
