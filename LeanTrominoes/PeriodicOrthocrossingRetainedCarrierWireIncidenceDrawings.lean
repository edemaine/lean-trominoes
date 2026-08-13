/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingWireIncidenceDrawings

/-!
# Selected retained carrier incidence drawings

The final planar-SAT carrier-lens drawing is independent of how its source
link was enumerated.  This file instantiates its formula, validity, and
carrier-boundary certificates for the selected zero-shift retained family.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A selected retained carrier lens draws its indexed planar-SAT clause
block. -/
@[simp] theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula
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
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing formula link).formula =
      drawingPlanarSATCarrierFormulaAt
        (Variable := Variable) link := by
  rw [drawingPlanarSATCarrierLensIncidenceDrawing,
    EmbeddedCNFIncidenceDrawing.rename,
    retainedDrawingCompleteCarrierLink_lensDrawing_formula
      wellFormed degree isLocal linkMember]
  simp [drawingPlanarSATCarrierFormulaAt,
    planarSATCarrierVariableMap, EmbeddedClause.rename,
    EmbeddedClause.map, List.map_map, Function.comp_def,
    planarSATCoreVariableMap]

/-- A selected retained carrier lens retains exact endpoints, orthogonality,
and continuous finite planarity after the final variable embedding. -/
theorem retainedDrawingPlanarSATCarrierLensIncidenceDrawing_isValid
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
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula)) :
    (drawingPlanarSATCarrierLensIncidenceDrawing formula link).IsValid := by
  apply EmbeddedCNFIncidenceDrawing.isValid_rename
  · intro first firstMember second secondMember equal
    exact planarSATCarrierVariableMap_injective equal
  · intro node nodeMember
    have nodeCases :
        node = link.first ∨ node = link.second := by
      rw [EmbeddedCNFIncidenceDrawing.variableVertices,
        retainedDrawingCompleteCarrierLink_lensDrawing_formula
          wellFormed degree isLocal linkMember] at nodeMember
      simpa [equalityInstance] using nodeMember
    rcases nodeCases with rfl | rfl
    · rw [planarSATCarrierVariableMap_position,
        retainedDrawingCompleteCarrierLink_lensDrawing_firstPosition
          wellFormed degree isLocal linkMember]
    · rw [planarSATCarrierVariableMap_position,
        retainedDrawingCompleteCarrierLink_lensDrawing_secondPosition
          wellFormed degree isLocal linkMember]
  · exact retainedDrawingCompleteCarrierLink_lensDrawing_isValid
      wellFormed degree isLocal linkMember

/-- A selected retained carrier drawing lies outside its first endpoint's
carrier boundary. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideFirst
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- A selected retained carrier drawing lies outside its second endpoint's
carrier boundary. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routePoints_outsideSecond
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- A selected retained carrier drawing contacts its first port only at route
endpoints. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_first
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

/-- A selected retained carrier drawing contacts its second port only at
route endpoints. -/
theorem
    retainedDrawingPlanarSATCarrierLensIncidenceDrawing_routeContactsAt_second
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
      link ∈ retainedDrawingCompleteCarrierLinks
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
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember)).rename _ _

end PeriodicOrthocrossing
end LeanTrominoes
