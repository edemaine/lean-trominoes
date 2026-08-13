/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceTranslation
import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.PeriodicOrthocrossingCarrierTranslationGeometry

/-!
# Route geometry under planar-SAT source translation

The source action defined in the preceding module is geometric: selecting a
route from a translated local gadget gives the pointwise physical-period
translate of the same route in the original gadget.  This file proves that
operational statement, first for the template-positioned gadget families and
then uniformly for clause sources.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Scaling distributes over addition of drawing cells. -/
theorem cell_scale_add
    (factor : Int) (first second : Cell) :
    Cell.scale factor (Cell.add first second) =
      Cell.add (Cell.scale factor first)
        (Cell.scale factor second) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [Cell.add, Cell.scale]
  constructor <;> ring

/-- Reassociate two common point translations in the order produced by
successive `List.map`s. -/
theorem cell_add_add_swap
    (origin offset point : Cell) :
    Cell.add (Cell.add origin offset) point =
      Cell.add offset (Cell.add origin point) := by
  rcases origin with ⟨originX, originY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]
  constructor <;> ring

/-- A common point translation preserves the directed axis between two
points. -/
@[simp]
theorem AxisDirection.between_add
    (first second offset : Cell) :
    AxisDirection.between
        (Cell.add first offset) (Cell.add second offset) =
      AxisDirection.between first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [AxisDirection.between, Cell.add]

/-- A common point translation preserves axis span. -/
@[simp]
theorem AxisDirection.axisSpan_add
    (first second offset : Cell) :
    AxisDirection.axisSpan
        (Cell.add first offset) (Cell.add second offset) =
      AxisDirection.axisSpan first second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [AxisDirection.axisSpan, Cell.add]

/-- Composing two pointwise polyline translations adds their offsets. -/
theorem translatePolyline_add
    (first second : Cell) (points : List Cell) :
    translatePolyline second (translatePolyline first points) =
      translatePolyline (Cell.add first second) points := by
  unfold translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases point with ⟨pointX, pointY⟩
  simp [Cell.add]
  constructor <;> ring

/-- Translating one nonempty polyline by two offsets gives equal routes only
when the offsets themselves are equal. -/
theorem translatePolyline_offsets_eq_of_nonempty
    (first second : Cell)
    (points : List Cell)
    (nonempty : points ≠ [])
    (routesEqual :
      translatePolyline first points =
        translatePolyline second points) :
    first = second := by
  cases points with
  | nil =>
      contradiction
  | cons head tail =>
      have headsEqual :=
        congrArg List.head? routesEqual
      rcases first with ⟨firstX, firstY⟩
      rcases second with ⟨secondX, secondY⟩
      rcases head with ⟨headX, headY⟩
      simp only [translatePolyline, List.map_cons,
        List.head?_cons, Option.some.injEq, Cell.add,
        Prod.mk.injEq] at headsEqual
      apply Prod.ext
      · simp only
        omega
      · simp only
        omega

/-- A translated crossing macrocell origin adds the refined macro-period
offset. -/
@[simp]
theorem crossingMacroOrigin_periodTranslate
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (crossing : CrossingRecord) (shift : Cell) :
    crossingMacroOrigin (crossing.periodTranslate graph shift) =
      Cell.add (crossingMacroOrigin crossing)
        (carrierMacroPeriodTranslation graph shift) := by
  unfold crossingMacroOrigin
  rw [CrossingRecord.periodTranslate,
    carrierMacroPeriodTranslation_eq_scale_periodTranslation]
  exact cell_scale_add planarMacroScale crossing.point
    ((drawing graph).periodTranslation shift)

@[simp]
theorem RouteBend.incomingPort_periodTranslate
    (routeBend : RouteBend) (shift : Cell) :
    (routeBend.periodTranslate shift).incomingPort =
      routeBend.incomingPort := by
  rfl

@[simp]
theorem RouteBend.outgoingPort_periodTranslate
    (routeBend : RouteBend) (shift : Cell) :
    (routeBend.periodTranslate shift).outgoingPort =
      routeBend.outgoingPort := by
  rfl

/-- Translate a metadata-rich CNF route occurrence without changing its
logical incidence or flattened edge index. -/
def CNFRouteOccurrence.periodTranslate
    {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) (shift : Cell) :
    CNFRouteOccurrence Variable where
  incidence := occurrence.incidence
  edgeIndex := occurrence.edgeIndex
  translate := Cell.add occurrence.translate shift

@[simp]
theorem sourceOccurrenceArm_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (shift : Cell) :
    sourceOccurrenceArm formula
        (occurrence.periodTranslate shift) =
      sourceOccurrenceArm formula occurrence := by
  rfl

/-- Translating a routed clause site translates each of its logical
incidence occurrences in place and preserves their presentation order. -/
theorem clauseRouteOccurrencesAt_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) (shift : Cell) :
    clauseRouteOccurrencesAt formula
        (clauseRouteSitePeriodTranslate site shift) =
      (clauseRouteOccurrencesAt formula site).map
        (fun occurrence => occurrence.periodTranslate shift) := by
  unfold clauseRouteOccurrencesAt clauseRouteSitePeriodTranslate
  rw [List.map_map]
  apply List.map_congr_left
  intro taggedIncidence taggedIncidenceMember
  rfl

/-- The local arm and polarity list of a routed source clause is invariant
under physical period translation. -/
@[simp]
theorem routedClausePortLiterals_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) (shift : Cell) :
    routedClausePortLiterals formula
        (clauseRouteSitePeriodTranslate site shift) =
      routedClausePortLiterals formula site := by
  rw [routedClausePortLiterals,
    clauseRouteOccurrencesAt_periodTranslate,
    List.map_map]
  apply List.map_congr_left
  intro occurrence occurrenceMember
  apply Prod.ext
  · exact sourceOccurrenceArm_periodTranslate
      formula occurrence shift
  · rfl

/-- Every selected crossover route is equivariant under physical period
translation. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    (drawingPlanarSATCrossoverIncidenceDrawing formula
        (crossing.periodTranslate
          (PeriodicCNF.incidenceGraph formula) shift)).routes
          clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).routes clauseIndex literalIndex) := by
  simp only [drawingPlanarSATCrossoverIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    crossingMacroOrigin_periodTranslate,
    translatePolyline]
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  exact cell_add_add_swap
    (crossingMacroOrigin crossing)
    (carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) shift)
    point

/-- Every selected route-bend route is equivariant under physical period
translation. -/
theorem drawingPlanarSATBendCornerIncidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend) (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    (drawingPlanarSATBendCornerIncidenceDrawing formula
        (routeBend.periodTranslate shift)).routes
          clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).routes clauseIndex literalIndex) := by
  simp only [drawingPlanarSATBendCornerIncidenceDrawing,
    RouteBend.cornerDrawing,
    placedCornerEqualityDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    RouteBend.incomingPort_periodTranslate,
    RouteBend.outgoingPort_periodTranslate,
    RouteBend.drawingPoint_periodTranslate,
    translatePolyline]
  rw [cell_scale_add,
    ← carrierMacroPeriodTranslation_eq_scale_periodTranslation]
  rw [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  exact cell_add_add_swap
    (Cell.scale planarMacroScale
      (routeBend.drawingPoint
        (PeriodicCNF.incidenceGraph formula)))
    (carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) shift)
    point

/-- Every selected routed-variable arm route is equivariant under physical
period translation. -/
theorem
    drawingPlanarSATRoutedVariableIncidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing formula
        (variableRouteSitePeriodTranslate site shift) arm
        (planarSATNodeLinkPeriodTranslate
          (PeriodicCNF.incidenceGraph formula) link shift)).routes
          clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site arm link).routes clauseIndex literalIndex) := by
  simp only [drawingPlanarSATRoutedVariableIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    routedVariableOrigin_periodTranslate,
    translatePolyline]
  rw [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  exact cell_add_add_swap
    (routedVariableOrigin formula site)
    (carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) shift)
    point

/-- Every selected routed source-clause ray is equivariant under physical
period translation. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing formula
        (clauseRouteSitePeriodTranslate site shift)).routes
          clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((drawingPlanarSATRoutedClauseIncidenceDrawing
          formula site).routes clauseIndex literalIndex) := by
  simp only [drawingPlanarSATRoutedClauseIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.translate,
    routedClausePortLiterals_periodTranslate,
    routedClauseOrigin_periodTranslate,
    translatePolyline]
  rw [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  exact cell_add_add_swap
    (routedClauseOrigin formula site)
    (carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) shift)
    point

/-- Every selected straight-carrier lens route is equivariant under physical
period translation. -/
theorem drawingPlanarSATCarrierLensIncidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    (drawingPlanarSATCarrierLensIncidenceDrawing formula
        (carrierLinkPeriodTranslate
          (PeriodicCNF.incidenceGraph formula) link shift)).routes
          clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes clauseIndex literalIndex) := by
  simp only [drawingPlanarSATCarrierLensIncidenceDrawing,
    EqualityLink.lensDrawing,
    placedEqualityLensDrawing,
    axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    EmbeddedCNFIncidenceDrawing.translate,
    carrierLinkPeriodTranslate_first,
    carrierLinkPeriodTranslate_second,
    CarrierNode.position_periodTranslate,
    AxisDirection.between_add,
    AxisDirection.axisSpan_add,
    translatePolyline]
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  exact cell_add_add_swap
    (link.first.position
      (PeriodicCNF.incidenceGraph formula))
    (carrierMacroPeriodTranslation
      (PeriodicCNF.incidenceGraph formula) shift)
    ((AxisDirection.between
      (link.first.position (PeriodicCNF.incidenceGraph formula))
      (link.second.position
        (PeriodicCNF.incidenceGraph formula))).orientPoint point)

namespace DrawingPlanarSATClauseSource

/-- Uniform route equivariance for all five local planar-SAT source
families.  The source's local clause index and the selected literal index are
preserved syntactically. -/
theorem incidenceDrawing_routes_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (shift : Cell)
    (clauseIndex literalIndex : Nat) :
    ((source.periodTranslate formula shift).incidenceDrawing formula).routes
        clauseIndex literalIndex =
      translatePolyline
        (carrierMacroPeriodTranslation
          (PeriodicCNF.incidenceGraph formula) shift)
        ((source.incidenceDrawing formula).routes
          clauseIndex literalIndex) := by
  cases source with
  | crossover crossing localClauseIndex =>
      exact
        drawingPlanarSATCrossoverIncidenceDrawing_routes_periodTranslate
          formula crossing shift clauseIndex literalIndex
  | carrier link localClauseIndex =>
      exact
        drawingPlanarSATCarrierLensIncidenceDrawing_routes_periodTranslate
          formula link shift clauseIndex literalIndex
  | bend routeBend localClauseIndex =>
      exact
        drawingPlanarSATBendCornerIncidenceDrawing_routes_periodTranslate
          formula routeBend shift clauseIndex literalIndex
  | routedClause site =>
      exact
        drawingPlanarSATRoutedClauseIncidenceDrawing_routes_periodTranslate
          formula site shift clauseIndex literalIndex
  | routedVariable site armIndex arm link localClauseIndex =>
      exact
        drawingPlanarSATRoutedVariableIncidenceDrawing_routes_periodTranslate
          formula site arm link shift clauseIndex literalIndex

end DrawingPlanarSATClauseSource

end PeriodicOrthocrossing
end LeanTrominoes
