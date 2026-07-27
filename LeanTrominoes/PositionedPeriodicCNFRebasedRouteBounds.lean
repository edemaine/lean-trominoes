import LeanTrominoes.PeriodicGridDrawingPointBounds
import LeanTrominoes.PeriodicPlanarThreeDMIncidenceRouting
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-!
# Halo bounds for rebased periodic CNF incidence routes

The planar 3DM construction traverses every source incidence in the reverse
direction and rebases it at its variable prototype.  Bounds on the stored
clause-to-variable route do not directly state bounds on this rebased route,
especially when the incidence crosses a fundamental-square boundary.

This file records the exact pointwise halo hypothesis needed by the 3DM
assembly.  It also proves that the hypothesis is invariant under clause-anchor
normalization: normalization changes the incidence metadata, but it leaves
both the physical drawing and every rebased route unchanged.
-/

namespace LeanTrominoes

namespace CNFIncidence

/-- Normalize the clause and literal metadata of one syntactic incidence. -/
def anchorNormalize
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    CNFIncidence Variable :=
  ⟨incidence.clauseIndex, incidence.clause.anchorNormalize,
    incidence.literalIndex,
    incidence.literal.anchorNormalize
      (PeriodicCNF.clauseAnchor incidence.clause)⟩

@[simp]
theorem anchorNormalize_clauseIndex
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    incidence.anchorNormalize.clauseIndex = incidence.clauseIndex := by
  rfl

@[simp]
theorem anchorNormalize_clause
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    incidence.anchorNormalize.clause =
      incidence.clause.anchorNormalize := by
  rfl

@[simp]
theorem anchorNormalize_literalIndex
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    incidence.anchorNormalize.literalIndex =
      incidence.literalIndex := by
  rfl

@[simp]
theorem anchorNormalize_literal
    {Variable : Type*} (incidence : CNFIncidence Variable) :
    incidence.anchorNormalize.literal =
      incidence.literal.anchorNormalize
        (PeriodicCNF.clauseAnchor incidence.clause) := by
  rfl

end CNFIncidence

namespace PeriodicCNF

/-- Anchor normalization maps the metadata-rich incidence list pointwise,
without changing its clause-major, literal-minor order. -/
theorem incidencesWithMetadata_anchorNormalize
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    incidencesWithMetadata formula.anchorNormalize =
      (incidencesWithMetadata formula).map
        CNFIncidence.anchorNormalize := by
  unfold incidencesWithMetadata PeriodicCNF.anchorNormalize
  rw [List.zipIdx_map]
  simp only [List.flatMap_map, Prod.map, id_eq]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro taggedClause taggedClauseMember
  rcases taggedClause with ⟨clause, clauseIndex⟩
  simp [PeriodicClause.anchorNormalize, List.zipIdx_map,
    List.map_map, CNFIncidence.anchorNormalize,
    Function.comp_def]

end PeriodicCNF

namespace PositionedPeriodicCNF

/-- Every point of every genuine variable-to-clause route lies in the open
one-cell halo around the source drawing's fundamental square. -/
def PlanarIncidencePresentation.RebasedRoutePointsInExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) : Prop :=
  ∀ tagged ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
    ∀ point ∈ presentation.variableToClauseRoute tagged.1,
      (incidenceDrawing source placement presentation.routes)
        |>.PositionInExpandedSquare point

/-- Stronger rebased-route bound with one unit of room below both upper
halo boundaries.  This is the margin consumed by a closed refined ribbon
macrocell. -/
def PlanarIncidencePresentation.RebasedRoutePointsInExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) : Prop :=
  ∀ tagged ∈
      (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx,
    ∀ point ∈ presentation.variableToClauseRoute tagged.1,
      (incidenceDrawing source placement presentation.routes)
        |>.PositionInExpandedSquareWithUpperMargin point

/-- Forgetting the extra unit of upper room recovers the ordinary
rebased-route halo bound. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_of_upperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {presentation : PlanarIncidencePresentation source placement}
    (bounds :
      presentation.RebasedRoutePointsInExpandedSquareWithUpperMargin) :
    presentation.RebasedRoutePointsInExpandedSquare := by
  intro tagged taggedMember point pointMember
  exact
    PeriodicGridDrawing.positionInExpandedSquare_of_upperMargin
      (bounds tagged taggedMember point pointMember)

/-- Anchor normalization leaves each reversed-and-rebased incidence route
literally unchanged. -/
theorem PlanarIncidencePresentation.variableToClauseRoute_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (incidence : CNFIncidence Variable) :
    (presentation.anchorNormalize.variableToClauseRoute
        incidence.anchorNormalize) =
      presentation.variableToClauseRoute incidence := by
  unfold PlanarIncidencePresentation.variableToClauseRoute
    CNFIncidence.anchorNormalize
  congr 1
  rcases incidence with
    ⟨clauseIndex, clause, literalIndex,
      ⟨atom, ⟨literalX, literalY⟩, value⟩⟩
  rcases PeriodicCNF.clauseAnchor clause with
    ⟨anchorX, anchorY⟩
  apply Prod.ext <;>
    simp [PeriodicVariablePlacement.translation,
      Cell.scale, Cell.sub]

/-- Pointwise rebased-route halo bounds survive anchor normalization. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (bounds : presentation.RebasedRoutePointsInExpandedSquare) :
    presentation.anchorNormalize
      |>.RebasedRoutePointsInExpandedSquare := by
  intro normalizedTagged normalizedTaggedMember point pointMember
  rw [PositionedPeriodicCNF.erase_anchorNormalize,
    PeriodicCNF.incidencesWithMetadata_anchorNormalize,
    List.zipIdx_map] at normalizedTaggedMember
  rcases List.mem_map.mp normalizedTaggedMember with
    ⟨tagged, taggedMember, taggedEqual⟩
  subst normalizedTagged
  have pointMember' :
      point ∈
        presentation.anchorNormalize.variableToClauseRoute
          tagged.1.anchorNormalize := by
    simpa using pointMember
  rw [variableToClauseRoute_anchorNormalize] at pointMember'
  rw [incidenceDrawing_anchorNormalize]
  exact bounds tagged taggedMember point pointMember'

/-- The stronger one-unit upper halo margin likewise survives anchor
normalization. -/
theorem PlanarIncidencePresentation.rebasedRoutePointsInExpandedSquareWithUpperMargin_anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement)
    (bounds :
      presentation.RebasedRoutePointsInExpandedSquareWithUpperMargin) :
    presentation.anchorNormalize
      |>.RebasedRoutePointsInExpandedSquareWithUpperMargin := by
  intro normalizedTagged normalizedTaggedMember point pointMember
  rw [PositionedPeriodicCNF.erase_anchorNormalize,
    PeriodicCNF.incidencesWithMetadata_anchorNormalize,
    List.zipIdx_map] at normalizedTaggedMember
  rcases List.mem_map.mp normalizedTaggedMember with
    ⟨tagged, taggedMember, taggedEqual⟩
  subst normalizedTagged
  have pointMember' :
      point ∈
        presentation.anchorNormalize.variableToClauseRoute
          tagged.1.anchorNormalize := by
    simpa using pointMember
  rw [variableToClauseRoute_anchorNormalize] at pointMember'
  rw [incidenceDrawing_anchorNormalize]
  exact bounds tagged taggedMember point pointMember'

/-- A continuously planar source presentation equipped with precisely the
rebased-route coordinate bound consumed by the planar 3DM assembly. -/
structure HaloBoundedContinuousPlanarIncidencePresentation
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    extends ContinuousPlanarIncidencePresentation source placement where
  rebasedRoutePointsInside :
    toPlanarIncidencePresentation
      |>.RebasedRoutePointsInExpandedSquare

namespace HaloBoundedContinuousPlanarIncidencePresentation

/-- Anchor normalization preserves the complete continuously planar,
halo-bounded source interface. -/
def anchorNormalize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      HaloBoundedContinuousPlanarIncidencePresentation source placement) :
    HaloBoundedContinuousPlanarIncidencePresentation
      (source.anchorNormalize placement) placement where
  toContinuousPlanarIncidencePresentation :=
    presentation.toContinuousPlanarIncidencePresentation.anchorNormalize
  rebasedRoutePointsInside :=
    presentation.toPlanarIncidencePresentation
      |>.rebasedRoutePointsInExpandedSquare_anchorNormalize
        presentation.rebasedRoutePointsInside

end HaloBoundedContinuousPlanarIncidencePresentation

end PositionedPeriodicCNF

end LeanTrominoes
