import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.OrthogonalPolylineBoundingBox

/-!
# Macrocell bounds for planar-SAT local incidence routes

Crossovers, route bends, routed source clauses, and routed variable arms all
live in the `20 × 20` macrocell attached to one point of the source drawing.
Every listed route point in their fixed templates has both local coordinates
between zero and thirteen.  Consequently components attached to distinct
integer drawing points occupy strictly separated closed rectangles.

Straight carrier lenses are intentionally excluded: they connect two such
macrocells along a source segment and require the separate corridor argument.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The closed local rectangle containing every non-carrier planarizer
template. -/
def InStandardPlanarSATMacrocell (point : Cell) : Prop :=
  InClosedGridRectangle (0, 0) (13, 13) point

instance (point : Cell) :
    Decidable (InStandardPlanarSATMacrocell point) := by
  unfold InStandardPlanarSATMacrocell
  infer_instance

/-- Lower corner of the route-containing rectangle at one drawing-grid
point. -/
def planarSATMacrocellRouteLower (center : Cell) : Cell :=
  Cell.scale planarMacroScale center

/-- Upper corner of the route-containing rectangle at one drawing-grid
point. -/
def planarSATMacrocellRouteUpper (center : Cell) : Cell :=
  Cell.add (Cell.scale planarMacroScale center) (13, 13)

/-- A route point lies in the closed route-containing part of the planar-SAT
macrocell at `center`. -/
def InPlanarSATMacrocell (center point : Cell) : Prop :=
  InClosedGridRectangle
    (planarSATMacrocellRouteLower center)
    (planarSATMacrocellRouteUpper center)
    point

instance (center point : Cell) :
    Decidable (InPlanarSATMacrocell center point) := by
  unfold InPlanarSATMacrocell
  infer_instance

/-- Translating a standard local point by a scaled drawing-grid center puts
it in that center's global macrocell. -/
theorem inPlanarSATMacrocell_add_origin
    {center localPoint : Cell}
    (bounded : InStandardPlanarSATMacrocell localPoint) :
    InPlanarSATMacrocell center
      (Cell.add (Cell.scale planarMacroScale center) localPoint) := by
  rcases center with ⟨centerX, centerY⟩
  rcases localPoint with ⟨localX, localY⟩
  simp only [InStandardPlanarSATMacrocell,
    InClosedGridRectangle] at bounded
  simp only [InPlanarSATMacrocell,
    planarSATMacrocellRouteLower,
    planarSATMacrocellRouteUpper,
    planarMacroScale, InClosedGridRectangle,
    Cell.add, Cell.scale]
  omega

/-- The route rectangles of two distinct integer drawing-grid points are
strictly separated: the unused margin is at least seven refined cells. -/
theorem planarSATMacrocellRouteRectangles_separated
    {firstCenter secondCenter : Cell}
    (different : firstCenter ≠ secondCenter) :
    ClosedGridRectanglesSeparated
      (planarSATMacrocellRouteLower firstCenter)
      (planarSATMacrocellRouteUpper firstCenter)
      (planarSATMacrocellRouteLower secondCenter)
      (planarSATMacrocellRouteUpper secondCenter) := by
  rcases firstCenter with ⟨firstX, firstY⟩
  rcases secondCenter with ⟨secondX, secondY⟩
  have differentCoordinates : firstX ≠ secondX ∨ firstY ≠ secondY := by
    by_cases differentX : firstX ≠ secondX
    · exact Or.inl differentX
    · exact Or.inr fun equalY =>
        different (Prod.ext (not_ne_iff.mp differentX) equalY)
  simp only [ClosedGridRectanglesSeparated,
    planarSATMacrocellRouteLower,
    planarSATMacrocellRouteUpper,
    planarMacroScale, Cell.add, Cell.scale]
  rcases differentCoordinates with differentX | differentY
  · rcases lt_or_gt_of_ne differentX with less | greater
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
  · rcases lt_or_gt_of_ne differentY with less | greater
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

/-- Routes contained in macrocells at distinct drawing-grid points have no
continuous or listed-point contact. -/
theorem routesStrictlyAvoidEachOther_of_inPlanarSATMacrocells
    {firstCenter secondCenter : Cell}
    {first second : List Cell}
    (firstBounded :
      ∀ point ∈ first, InPlanarSATMacrocell firstCenter point)
    (secondBounded :
      ∀ point ∈ second, InPlanarSATMacrocell secondCenter point)
    (different : firstCenter ≠ secondCenter) :
    EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther
      first second := by
  exact
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      firstBounded secondBounded
      (planarSATMacrocellRouteRectangles_separated different)

/-- Every genuine route of the fixed crossover template lies in the common
local planarizer rectangle. -/
theorem crossoverStraightIncidenceDrawing_routePoints_bounded :
    crossoverStraightIncidenceDrawing.RoutePointsSatisfy
      InStandardPlanarSATMacrocell := by
  native_decide

/-- Every genuine route in any fixed corner template lies in the common
local planarizer rectangle. -/
theorem cornerEqualityDrawing_routePoints_bounded
    (first second : CornerPort) :
    (cornerEqualityDrawing first second).RoutePointsSatisfy
      InStandardPlanarSATMacrocell := by
  cases first <;> cases second <;> native_decide

/-- Every genuine direct route of one active duplicator arm lies in the
common local planarizer rectangle. -/
theorem duplicatorArmStraightIncidenceDrawing_routePoints_bounded
    (arm : DuplicatorArm) :
    (duplicatorArmStraightIncidenceDrawing arm).RoutePointsSatisfy
      InStandardPlanarSATMacrocell := by
  cases arm <;> native_decide

/-- Every genuine direct source-clause ray lies in the common local
planarizer rectangle, for any presented signed arm list. -/
theorem routedClausePortStraightIncidenceDrawing_routePoints_bounded
    (literals : List (DuplicatorArm × Bool)) :
    (routedClausePortStraightIncidenceDrawing literals).RoutePointsSatisfy
      InStandardPlanarSATMacrocell := by
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.straightIncidenceDrawing_routePointsSatisfy
  · intro clause clauseMember
    simp only [routedClausePortFormula, List.mem_singleton] at clauseMember
    subst clause
    norm_num [InStandardPlanarSATMacrocell,
      InClosedGridRectangle]
  · intro clause clauseMember literal literalMember
    simp only [routedClausePortFormula, List.mem_singleton] at clauseMember
    subst clause
    rcases literal with ⟨arm, polarity⟩
    cases arm <;>
      norm_num [InStandardPlanarSATMacrocell,
        InClosedGridRectangle, DuplicatorArm.portPosition]

/-- Translating any standard-bounded drawing to a scaled source point gives
the corresponding global macrocell bound. -/
theorem routePointsSatisfy_inPlanarSATMacrocell_translate
    {Variable : Type*}
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (bounded :
      drawing.RoutePointsSatisfy InStandardPlanarSATMacrocell)
    (center : Cell) :
    (drawing.translate
      (Cell.scale planarMacroScale center)).RoutePointsSatisfy
        (InPlanarSATMacrocell center) := by
  exact bounded.translate
    (Cell.scale planarMacroScale center)
    (fun point pointBounded =>
      inPlanarSATMacrocell_add_origin pointBounded)

/-- Every route of a placed crossover is bounded by its crossing
macrocell. -/
theorem drawingPlanarSATCrossoverIncidenceDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (crossing : CrossingRecord) :
    (drawingPlanarSATCrossoverIncidenceDrawing
      formula crossing).RoutePointsSatisfy
        (InPlanarSATMacrocell crossing.point) := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing
    crossingMacroOrigin
  exact
    (routePointsSatisfy_inPlanarSATMacrocell_translate
      crossoverStraightIncidenceDrawing_routePoints_bounded
      crossing.point).rename
        (planarSATCrossoverVariableMap crossing)
        (drawingPlanarSATVariablePosition formula)

/-- Every route of a placed bend corner is bounded by the macrocell at the
bend's drawing point. -/
theorem drawingPlanarSATBendCornerIncidenceDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing
      formula routeBend).RoutePointsSatisfy
        (InPlanarSATMacrocell
          (routeBend.drawingPoint
            (PeriodicCNF.incidenceGraph formula))) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing
    RouteBend.cornerDrawing placedCornerEqualityDrawing
    EmbeddedCNFIncidenceDrawing.renameToImage
  exact
    ((routePointsSatisfy_inPlanarSATMacrocell_translate
      (cornerEqualityDrawing_routePoints_bounded
        routeBend.incomingPort routeBend.outgoingPort)
      (routeBend.drawingPoint
        (PeriodicCNF.incidenceGraph formula))).rename
          (equalityLensVariableMap
            (CarrierNode.terminal routeBend.incomingTerminal)
            (CarrierNode.terminal routeBend.outgoingTerminal))
          (EmbeddedCNFIncidenceDrawing.imageVariablePosition
            ((cornerEqualityDrawing
              routeBend.incomingPort
              routeBend.outgoingPort).translate
                (Cell.scale planarMacroScale
                  (routeBend.drawingPoint
                    (PeriodicCNF.incidenceGraph formula))))
            (equalityLensVariableMap
              (CarrierNode.terminal routeBend.incomingTerminal)
              (CarrierNode.terminal routeBend.outgoingTerminal)))).rename
        planarSATCarrierVariableMap
        (drawingPlanarSATVariablePosition formula)

/-- Every route of a placed active routed-variable arm is bounded by its
lifted variable macrocell. -/
theorem drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable)) :
    (drawingPlanarSATRoutedVariableIncidenceDrawing
      formula site arm link).RoutePointsSatisfy
        (InPlanarSATMacrocell
          (liftedIncidenceVertexPosition
            formula (.variable site.1) site.2)) := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing
    routedVariableOrigin
    liftedIncidenceVertexMacroOrigin
  exact
    (routePointsSatisfy_inPlanarSATMacrocell_translate
      (duplicatorArmStraightIncidenceDrawing_routePoints_bounded arm)
      (liftedIncidenceVertexPosition
        formula (.variable site.1) site.2)).rename
          (planarSATRoutedVariableMap link)
          (drawingPlanarSATVariablePosition formula)

/-- Every route of a placed routed source clause is bounded by its lifted
clause macrocell. -/
theorem drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_bounded
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite) :
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      formula site).RoutePointsSatisfy
        (InPlanarSATMacrocell
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2)) := by
  let source :=
    drawingPlanarSATRoutedClauseIncidenceDrawing formula site
  let variableMap :=
    @planarSATRoutedClauseArm Variable
  let targetPosition :=
    routedClauseArmPosition formula site
  have translatedBounded :
      ((routedClausePortStraightIncidenceDrawing
          (routedClausePortLiterals formula site)).translate
        (routedClauseOrigin formula site)).RoutePointsSatisfy
          (InPlanarSATMacrocell
            (liftedIncidenceVertexPosition
              formula (.clause site.1) site.2)) := by
    unfold routedClauseOrigin
      liftedIncidenceVertexMacroOrigin
    exact
      routePointsSatisfy_inPlanarSATMacrocell_translate
        (routedClausePortStraightIncidenceDrawing_routePoints_bounded
          (routedClausePortLiterals formula site))
        (liftedIncidenceVertexPosition
          formula (.clause site.1) site.2)
  have renamedBounded :
      (source.rename variableMap targetPosition).RoutePointsSatisfy
        (InPlanarSATMacrocell
          (liftedIncidenceVertexPosition
            formula (.clause site.1) site.2)) := by
    rw [show source.rename variableMap targetPosition =
        (routedClausePortStraightIncidenceDrawing
          (routedClausePortLiterals formula site)).translate
            (routedClauseOrigin formula site) by
      exact drawingPlanarSATRoutedClauseIncidenceDrawing_rename
        formula site]
    exact translatedBounded
  exact renamedBounded.of_rename variableMap targetPosition

namespace DrawingPlanarSATComponent

/-- Drawing-grid center of a macrocell component.  A carrier lens instead
occupies the corridor between two macrocells and therefore has no single
macrocell center. -/
def macrocellCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATComponent Variable → Option Cell
  | .crossover crossing => some crossing.point
  | .carrier _ => none
  | .bend routeBend =>
      some
        (routeBend.drawingPoint
          (PeriodicCNF.incidenceGraph formula))
  | .routedClause site =>
      some
        (liftedIncidenceVertexPosition
          formula (.clause site.1) site.2)
  | .routedVariable site _ _ =>
      some
        (liftedIncidenceVertexPosition
          formula (.variable site.1) site.2)

end DrawingPlanarSATComponent

namespace DrawingPlanarSATClauseMetadata

/-- Every genuine selected route of a non-carrier metadata component lies
in the macrocell named by that component. -/
theorem localRoutePoints_inPlanarSATMacrocell
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.Valid formula)
    (center : Cell)
    (centerEqual :
      metadata.source.component.macrocellCenter formula =
        some center)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    {point : Cell}
    (pointMember :
      point ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex) :
    InPlanarSATMacrocell center point := by
  have clauseMember :=
    metadata.localClauseMember
      wellFormed degree isLocal valid
  rcases metadata with ⟨clause, source⟩
  cases source with
  | crossover crossing localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEqual
      subst center
      exact
        (drawingPlanarSATCrossoverIncidenceDrawing_routePoints_bounded
          formula crossing).of_members
            clauseMember literalMember pointMember
  | carrier link localClauseIndex =>
      simp [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter] at centerEqual
  | bend routeBend localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEqual
      subst center
      exact
        (drawingPlanarSATBendCornerIncidenceDrawing_routePoints_bounded
          formula routeBend).of_members
            clauseMember literalMember pointMember
  | routedClause site =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEqual
      subst center
      exact
        (drawingPlanarSATRoutedClauseIncidenceDrawing_routePoints_bounded
          formula site).of_members
            clauseMember literalMember pointMember
  | routedVariable site armIndex arm link localClauseIndex =>
      simp only [DrawingPlanarSATClauseSource.component,
        DrawingPlanarSATComponent.macrocellCenter,
        Option.some.injEq] at centerEqual
      subst center
      exact
        (drawingPlanarSATRoutedVariableIncidenceDrawing_routePoints_bounded
          formula site arm link).of_members
            clauseMember literalMember pointMember

/-- Selected routes from two non-carrier components at distinct drawing-grid
centers satisfy the complete cross-component separation predicate. -/
theorem localRoutes_avoidEachOther_of_macrocellCenters_ne
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable)
    (firstValid : firstMetadata.Valid formula)
    (secondValid : secondMetadata.Valid formula)
    (firstCenter secondCenter : Cell)
    (firstCenterEqual :
      firstMetadata.source.component.macrocellCenter formula =
        some firstCenter)
    (secondCenterEqual :
      secondMetadata.source.component.macrocellCenter formula =
        some secondCenter)
    {firstLiteral secondLiteral :
        PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstMetadata.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondMetadata.clause.literals.zipIdx)
    (centersDifferent : firstCenter ≠ secondCenter) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((firstMetadata.source.incidenceDrawing formula).routes
        firstMetadata.source.localClauseIndex firstLiteralIndex)
      ((secondMetadata.source.incidenceDrawing formula).routes
        secondMetadata.source.localClauseIndex secondLiteralIndex) := by
  apply
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesStrictlyAvoidEachOther.toRoutesAvoidEachOther
  apply routesStrictlyAvoidEachOther_of_inPlanarSATMacrocells
  · intro point pointMember
    exact firstMetadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal firstValid
      firstCenter firstCenterEqual firstLiteralMember pointMember
  · intro point pointMember
    exact secondMetadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal secondValid
      secondCenter secondCenterEqual secondLiteralMember pointMember
  · exact centersDifferent

end DrawingPlanarSATClauseMetadata

end PeriodicOrthocrossing
end LeanTrominoes
