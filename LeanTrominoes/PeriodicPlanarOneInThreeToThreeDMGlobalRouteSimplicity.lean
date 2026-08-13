/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes
import LeanTrominoes.EmbeddedCNFIncidenceDrawingTranslation

/-!
# Simplicity of finite assembled route pieces

The checked variable-site and clause drawings already include simple-route
certificates.  This file exposes those certificates for the typed local
routes used by the global assembly and transports them through the assembly
translations.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing

/-- Every route selected from an instantiated finite variable-site drawing
is geometrically simple. -/
theorem typedVariableSiteRoute_simple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : Variable) (atomMember : atom ∈ occurringVariables source)
    (slot : OccurrenceSlot) (slotMember : slot ∈ usedSlots source atom)
    (triple : Triple Variable)
    (tripleMember : triple ∈ occurrenceTriples source atom slot)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (typedVariableSiteRoute source atom atomMember slot slotMember
        triple tripleMember color) := by
  exact
    (sourceVariableSiteDrawing_isValid source atom atomMember).2.2.1
      (activeVariableSiteTriple source atom atomMember slot slotMember
        triple tripleMember, color)

/-- Every polarity-oriented finite incidence route remains geometrically
simple. -/
theorem orientedIncidenceLocalRoute_simple
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (triple : Triple Variable)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (orientedIncidenceLocalRoute source triple color) := by
  cases triple with
  | ordinary atom slot variant localTriple =>
      exact
        (VariableOccurrence.orientedBoundaryDrawing_isValid
          variant (occurrencePolarity source atom slot)).2.2.1
            (localTriple, color)
  | fixedRed atom slot localTriple =>
      exact
        (FixedRedConnector.boundaryDrawing_isValid
          (occurrencePolarity source atom slot)).2.2.1
            (localTriple, color)
  | clause clauseIndex set =>
      exact X3CClauseOrthogonal.drawing_isValid.2.2.1 (set, color)

/-- Every translated ordinary variable-site prefix is simple. -/
theorem assembledOrdinaryPrefix_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (member :
      Triple.ordinary atom slot variant localTriple ∈ triples source)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledOrdinaryPrefix routing atom slot variant localTriple
        member color) := by
  let location :=
    ordinaryTriple_location source atom slot variant localTriple member
  have localSimple :=
    typedVariableSiteRoute_simple source atom location.1 slot
      location.2.1 (.ordinary atom slot variant localTriple)
      location.2.2 color
  simpa [assembledOrdinaryPrefix, translatePolyline] using
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      localSimple (routing.variableOrigin atom)

/-- Every translated fixed-red variable-site prefix is simple. -/
theorem assembledFixedRedPrefix_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (atom : Variable) (slot : OccurrenceSlot)
    (localTriple : FixedRedConnectorTriple)
    (member :
      Triple.fixedRed atom slot localTriple ∈ triples source)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledFixedRedPrefix routing atom slot localTriple
        member color) := by
  let location :=
    fixedRedTriple_location source atom slot localTriple member
  have localSimple :=
    typedVariableSiteRoute_simple source atom location.1 slot
      location.2.1 (.fixedRed atom slot localTriple)
      location.2.2 color
  simpa [assembledFixedRedPrefix, translatePolyline] using
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      localSimple (routing.variableOrigin atom)

/-- Every translated clause-core incidence route is simple. -/
theorem assembledClauseRoute_simple
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (clauseIndex : Nat) (set : X3CClauseSet)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (assembledClauseRoute routing clauseIndex set color) := by
  have localSimple :=
    orientedIncidenceLocalRoute_simple source
      (.clause clauseIndex set) color
  simpa [assembledClauseRoute, translatePolyline] using
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.routeIsSimple_translate
      localSimple (routing.clauseOrigin clauseIndex)

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
