import LeanTrominoes.PeriodicCNFPlanarSATClauseIndex
import LeanTrominoes.PeriodicCNFPlanarSATGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingBendCornerDrawingFamily
import LeanTrominoes.EmbeddedCNFIncidenceDrawingRenaming
import LeanTrominoes.PlanarThreeSATEqualityLensCarrierInterface

/-!
# Wire incidence drawings in the finite planar-SAT block

The complete route core has two kinds of equality links: lenses along
straight carriers and corner drawings at route bends.  This module embeds
both certified local drawings into the final `PlanarSATVariable` type through
one common carrier-node map.  Their exact formulas, variable positions,
orthogonality, and continuous planarity are all preserved.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Embed a route carrier node into the external summand of the combined
planar-SAT variable type. -/
def planarSATCarrierVariableMap
    {Variable : Type*} (node : CarrierNode) :
    PlanarSATVariable Variable :=
  .inl (.carrier node)

/-- The carrier-node embedding is injective. -/
theorem planarSATCarrierVariableMap_injective
    {Variable : Type*} :
    Function.Injective (@planarSATCarrierVariableMap Variable) := by
  intro first second equal
  cases equal
  rfl

/-- The combined planar-SAT placement agrees definitionally with the
underlying carrier-node placement. -/
@[simp] theorem planarSATCarrierVariableMap_position
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : CarrierNode) :
    drawingPlanarSATVariablePosition formula
        (planarSATCarrierVariableMap node) =
      node.position (PeriodicCNF.incidenceGraph formula) := by
  rfl

/-- A certified straight-carrier lens renamed into the combined planar-SAT
variable type. -/
def drawingPlanarSATCarrierLensIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) :=
  (EqualityLink.lensDrawing
      (CarrierNode.position
        (PeriodicCNF.incidenceGraph formula))
      link).rename
    planarSATCarrierVariableMap
    (drawingPlanarSATVariablePosition formula)

/-- A represented carrier lens draws exactly the local clause block recorded
by the global clause index. -/
@[simp] theorem drawingPlanarSATCarrierLensIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing formula link).formula =
      drawingPlanarSATCarrierFormulaAt
        (Variable := Variable) link := by
  rw [drawingPlanarSATCarrierLensIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    drawingCompleteCarrierLink_lensDrawing_formula
      wellFormed degree isLocal linkMember]
  simp [drawingPlanarSATCarrierFormulaAt,
    planarSATCarrierVariableMap, EmbeddedClause.rename,
    EmbeddedClause.map, List.map_map, Function.comp_def,
    planarSATCoreVariableMap]

/-- A represented carrier lens retains exact endpoints, orthogonality, and
continuous finite planarity after the final variable embedding. -/
theorem drawingPlanarSATCarrierLensIncidenceDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing formula link).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro first firstMember second secondMember equal
    exact planarSATCarrierVariableMap_injective equal
  · intro node nodeMember
    have nodeCases :
        node = link.first ∨ node = link.second := by
      rw [EmbeddedCNFIncidenceDrawing.variableVertices,
        drawingCompleteCarrierLink_lensDrawing_formula
          wellFormed degree isLocal linkMember] at nodeMember
      simpa [equalityInstance] using nodeMember
    rcases nodeCases with rfl | rfl
    · rw [planarSATCarrierVariableMap_position,
        drawingCompleteCarrierLink_lensDrawing_firstPosition
          wellFormed degree isLocal linkMember]
    · rw [planarSATCarrierVariableMap_position,
        drawingCompleteCarrierLink_lensDrawing_secondPosition
          wellFormed degree isLocal linkMember]
  · exact drawingCompleteCarrierLink_lensDrawing_isValid
      wellFormed degree isLocal linkMember

/-- The final-variable carrier drawing retains the first endpoint's
external macrocell bound. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        ((EqualityLink.firstCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula))
          link).OutsideCarrierBoundaryAt
            (EqualityLink.firstCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routePoints_outsideFirstCarrierBoundary
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- The final-variable carrier drawing retains the second endpoint's
external macrocell bound. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RoutePointsSatisfy
        ((EqualityLink.secondCarrierPort
          (CarrierNode.position
            (PeriodicCNF.incidenceGraph formula))
          link).OutsideCarrierBoundaryAt
            (EqualityLink.secondCarrierMacroOrigin
              (CarrierNode.position
                (PeriodicCNF.incidenceGraph formula))
              link)) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routePoints_outsideSecondCarrierBoundary
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- The final-variable carrier drawing retains endpoint-only contact at its
first carrier port. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RouteContactsAtEndpoint
        (Cell.add
          (EqualityLink.firstCarrierMacroOrigin
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            link)
          (EqualityLink.firstCarrierPort
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            link).position) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routeContactsAt_firstCarrierPort
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- The final-variable carrier drawing retains endpoint-only contact at its
second carrier port. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMember :
      link ∈ drawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing
      formula link).RouteContactsAtEndpoint
        (Cell.add
          (EqualityLink.secondCarrierMacroOrigin
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            link)
          (EqualityLink.secondCarrierPort
            (CarrierNode.position
              (PeriodicCNF.incidenceGraph formula))
            link).position) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing
  exact
    (EqualityLink.lensDrawing_routeContactsAt_secondCarrierPort
      (drawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- A certified route-bend corner drawing renamed into the combined
planar-SAT variable type. -/
def drawingPlanarSATBendCornerIncidenceDrawing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    EmbeddedCNFIncidenceDrawing (PlanarSATVariable Variable) :=
  (routeBend.cornerDrawing
      (PeriodicCNF.incidenceGraph formula)).rename
    planarSATCarrierVariableMap
    (drawingPlanarSATVariablePosition formula)

/-- A represented bend corner draws exactly the local clause block recorded
by the global clause index. -/
@[simp] theorem drawingPlanarSATBendCornerIncidenceDrawing_formula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing formula routeBend).formula =
      drawingPlanarSATBendFormulaAt
        (Variable := Variable)
        (PeriodicCNF.incidenceGraph formula)
        routeBend := by
  rw [drawingPlanarSATBendCornerIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    RouteBend.cornerDrawing_formula
      (PeriodicCNF.incidenceGraph formula) routeBend]
  simp [drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt,
    planarSATCarrierVariableMap, EmbeddedClause.rename,
    EmbeddedClause.map, List.map_map, Function.comp_def,
    planarSATCoreVariableMap]

/-- A represented bend corner retains exact endpoints, orthogonality, and
continuous finite planarity after the final variable embedding. -/
theorem drawingPlanarSATBendCornerIncidenceDrawing_isValid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {routeBend : RouteBend}
    (routeBendMember :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup) :
    (drawingPlanarSATBendCornerIncidenceDrawing formula routeBend).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro first firstMember second secondMember equal
    exact planarSATCarrierVariableMap_injective equal
  · intro node nodeMember
    have nodeCases :
        node =
            (routeBend.equalityLink
              (PeriodicCNF.incidenceGraph formula)).first ∨
          node =
            (routeBend.equalityLink
              (PeriodicCNF.incidenceGraph formula)).second := by
      rw [EmbeddedCNFIncidenceDrawing.variableVertices,
        RouteBend.cornerDrawing_formula
          (PeriodicCNF.incidenceGraph formula) routeBend]
        at nodeMember
      simpa [equalityInstance] using nodeMember
    rcases nodeCases with rfl | rfl
    · rw [planarSATCarrierVariableMap_position,
        drawingRouteBend_cornerDrawing_firstPosition
          wellFormed degree isLocal routeBendMember]
    · rw [planarSATCarrierVariableMap_position,
        drawingRouteBend_cornerDrawing_secondPosition
          wellFormed degree isLocal routeBendMember]
  · exact drawingRouteBend_cornerDrawing_isValid
      wellFormed degree isLocal routeBendMember

/-- The final-variable bend drawing stays inside its incoming carrier
boundary. -/
theorem
    drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideIncoming
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing
      formula routeBend).RoutePointsSatisfy
        (routeBend.incomingPort.InsideCarrierBoundaryAt
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula)))) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing
  exact
    (routeBend.cornerDrawing_routePoints_insideIncomingCarrierBoundary
      (PeriodicCNF.incidenceGraph formula)).rename _ _

/-- The final-variable bend drawing stays inside its outgoing carrier
boundary. -/
theorem
    drawingPlanarSATBendCornerIncidenceDrawing_routePoints_insideOutgoing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing
      formula routeBend).RoutePointsSatisfy
        (routeBend.outgoingPort.InsideCarrierBoundaryAt
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula)))) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing
  exact
    (routeBend.cornerDrawing_routePoints_insideOutgoingCarrierBoundary
      (PeriodicCNF.incidenceGraph formula)).rename _ _

/-- The final-variable bend drawing has endpoint-only contact with its
incoming physical carrier port. -/
theorem
    drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_incoming
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing
      formula routeBend).RouteContactsAtEndpoint
        (Cell.add
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula)))
          routeBend.incomingPort.position) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing
  exact
    (routeBend.cornerDrawing_routeContactsAt_incomingCarrierPort
      (PeriodicCNF.incidenceGraph formula)).rename _ _

/-- The final-variable bend drawing has endpoint-only contact with its
outgoing physical carrier port. -/
theorem
    drawingPlanarSATBendCornerIncidenceDrawing_routeContactsAt_outgoing
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (routeBend : RouteBend) :
    (drawingPlanarSATBendCornerIncidenceDrawing
      formula routeBend).RouteContactsAtEndpoint
        (Cell.add
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint
              (PeriodicCNF.incidenceGraph formula)))
          routeBend.outgoingPort.position) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing
  exact
    (routeBend.cornerDrawing_routeContactsAt_outgoingCarrierPort
      (PeriodicCNF.incidenceGraph formula)).rename _ _

end PeriodicOrthocrossing
end LeanTrominoes
