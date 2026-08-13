/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoreClauseSeparation

/-!
# Coordinated source endpoint-fan separation

The five source-level separation theorems assemble directly into the generic
`RibbonEndpointFanSystem.Separation` interface.  The only extra geometric
hypothesis is that every source route has an interior lattice point, used by
the mixed variable/clause theorem.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 800000 in
/-- The coordinated endpoint fans of a width-three ribbon-ready source form a
separated fan system whenever every active source route has length at least
three. -/
noncomputable def coordinatedSourceRibbonEndpointFanSystemSeparation
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (lengthGeThree :
      ∀ entry : ActiveOccurrenceEntry source.erase,
        3 ≤
          (occurrenceUnitSourceRoute
            presentation.toPlanarIncidencePresentation entry).length) :
    RibbonEndpointFanSystem.Separation presentation
      (coordinatedSourceRibbonEndpointFanSystem
        presentation.toPlanarIncidencePresentation width compatible) where
  variableVariable _ _ _ _ different :=
    occurrenceCoordinatedRibbonVariableStubs_strictlyAvoidEachOther
      presentation compatible different
  variableCore _ _ _ _ different :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceRibbonCorridorCore
      presentation compatible different
  variableClause first firstColor second secondColor _ :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub_of_length_ge_three
      presentation compatible first second firstColor secondColor
      (lengthGeThree first)
  coreClause _ _ _ _ different :=
    occurrenceRibbonCorridorCore_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub
      presentation width compatible different
  clauseClause _ _ _ _ different :=
    occurrenceCoordinatedRibbonClauseStubs_strictlyAvoidEachOther
      presentation width compatible different

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
