/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSplice
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRoutes

/-!
# Routed variable prefixes in the global assembly

The global route constructor spells its routed variable prefix separately
for ordinary and fixed-red typed triples.  This file exposes their common
source-level route and identifies both branches with it.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The common routed variable-site prefix before the global constructor
case-splits on the routed triple's connector kind. -/
def assembledRoutedVariablePrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) : List Cell :=
  translatePolyline (routing.variableOrigin entry.1.1)
    (typedVariableSiteRoute source entry.1.1 entry.atom_mem
      entry.1.2 entry.slot_mem
      (routedOccurrenceTriple source entry.1.1 entry.1.2 color)
      (routedOccurrenceTriple_mem_occurrenceTriples
        source entry.1.1 entry.1.2 color)
      color)

/-- A routing with the constructed variable origins uses exactly the
source-coordinate prefix from the finite-to-source splice theorem. -/
theorem assembledRoutedVariablePrefix_eq_constructed
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (routing : ThreeStrandRouting source.erase)
    (variableOriginEq :
      routing.variableOrigin =
        constructedVariableOrigin placement standardThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    assembledRoutedVariablePrefix routing entry color =
      constructedRoutedVariablePrefix placement entry color := by
  simp [assembledRoutedVariablePrefix, constructedRoutedVariablePrefix,
    variableOriginEq]

/-- The ordinary global prefix branch is the common routed prefix whenever
the selected occurrence triple is ordinary. -/
theorem assembledOrdinaryPrefix_eq_assembledRoutedVariablePrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor)
    (variant : VariableOccurrenceVariant)
    (localTriple : VariableOccurrenceTriple)
    (tripleEq :
      routedOccurrenceTriple source entry.1.1 entry.1.2 color =
        .ordinary entry.1.1 entry.1.2 variant localTriple) :
    assembledOrdinaryPrefix routing entry.1.1 entry.1.2
        variant localTriple
        (tripleEq ▸
          routedOccurrenceTriple_mem_triples
            source entry.1.1 entry.1.2
            entry.atom_mem entry.slot_mem color)
        color =
      assembledRoutedVariablePrefix routing entry color := by
  unfold assembledOrdinaryPrefix assembledRoutedVariablePrefix
  apply congrArg (translatePolyline (routing.variableOrigin entry.1.1))
  unfold typedVariableSiteRoute
  congr 2
  exact tripleEq.symm

/-- The fixed-red global prefix branch is the same common routed prefix
whenever the selected occurrence triple is fixed red. -/
theorem assembledFixedRedPrefix_eq_assembledRoutedVariablePrefix
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor)
    (localTriple : FixedRedConnectorTriple)
    (tripleEq :
      routedOccurrenceTriple source entry.1.1 entry.1.2 color =
        .fixedRed entry.1.1 entry.1.2 localTriple) :
    assembledFixedRedPrefix routing entry.1.1 entry.1.2
        localTriple
        (tripleEq ▸
          routedOccurrenceTriple_mem_triples
            source entry.1.1 entry.1.2
            entry.atom_mem entry.slot_mem color)
        color =
      assembledRoutedVariablePrefix routing entry color := by
  unfold assembledFixedRedPrefix assembledRoutedVariablePrefix
  apply congrArg (translatePolyline (routing.variableOrigin entry.1.1))
  unfold typedVariableSiteRoute
  congr 2
  exact tripleEq.symm

/-- The routed typed-incidence branch of the global constructor is exactly
the common variable prefix joined to the routing's occurrence route. -/
theorem assembledRoutedTypedIncidenceRoute_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (routing : ThreeStrandRouting source)
    (entry : ActiveOccurrenceEntry source)
    (color : WireColor) :
    assembledTypedIncidenceRoute routing
        ⟨routedOccurrenceTriple source entry.1.1 entry.1.2 color,
          routedOccurrenceTriple_mem_triples
            source entry.1.1 entry.1.2
            entry.atom_mem entry.slot_mem color⟩
        color =
      joinAtEndpoint
        (assembledRoutedVariablePrefix routing entry color)
        (routing.route entry color) := by
  cases kindEq : occurrenceConnectorKind
      source entry.1.1 entry.1.2 <;>
    cases color <;>
    simp only [routedOccurrenceTriple, kindEq] <;>
    simp [assembledTypedIncidenceRoute, routedOccurrenceTriple,
      kindEq, assembledRoutedVariablePrefix,
      assembledOrdinaryPrefix, assembledFixedRedPrefix]

/-- In an assembly with the standard constructed variable origins, its
unified routed prefix inherits the source-level coordinated-stub avoidance
certificate. -/
theorem assembledRoutedVariablePrefix_avoids_coordinatedVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (routing : ThreeStrandRouting source.erase)
    (variableOriginEq :
      routing.variableOrigin =
        constructedVariableOrigin placement standardThreeStrandLayout)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    RoutesAvoidEachOther
      (assembledRoutedVariablePrefix routing entry color)
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color) := by
  rw [assembledRoutedVariablePrefix_eq_constructed
    routing variableOriginEq entry color]
  exact constructedRoutedVariablePrefix_avoids_coordinatedVariableStub
    presentation compatible entry color

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
