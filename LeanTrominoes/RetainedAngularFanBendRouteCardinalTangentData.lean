/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalData
import LeanTrominoes.RetainedAngularFanFallbackCardinalGateTangentData
import LeanTrominoes.RetainedAngularFanFallbackRouteDecomposition
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation

/-! # Cardinal tangent data for retained bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- Cardinal tangent parameters of one bend route: its terminal port,
factor-four terminal length, and fully refined penultimate-segment length.
The route table determines separately on which side of the fan gate the
tangent lies. -/
structure BendRouteCardinalTangentData where
  port : Port
  scaledLength : Nat
  distance : Nat

/-- Cardinal port of a retained terminal, with an irrelevant east fallback
for the routed-clause cases that do not occur in the corner table. -/
def retainedTerminalCompassPort : RetainedTerminalDirection → Port
  | .compass port => port
  | .routedClause _ => .east

/-- Length of the segment immediately before the deleted variable segment. -/
def bendRoutePenultimateLength
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : Nat :=
  match (gridPolylineSegments
      (cornerEqualityRoutes firstPort secondPort
        localClauseIndex literalIndex).dropLast).getLast? with
  | some segment =>
      AxisDirection.segmentLength segment.start segment.finish
  | none => 0

/-- Computed cardinal tangent parameters of one route in the finite bend
table. -/
def bendRouteCardinalTangentData
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) :
    BendRouteCardinalTangentData :=
  let terminal := bendRouteTerminalData firstPort secondPort
    localClauseIndex literalIndex
  { port := retainedTerminalCompassPort terminal.1
    scaledLength := retainedAngularFanSourceClearanceFactor * terminal.2
    distance := retainedTerminalFanTotalRefinement *
      retainedAngularFanSourceClearanceFactor *
      bendRoutePenultimateLength firstPort secondPort
        localClauseIndex literalIndex }

end PeriodicEightOccurrenceSplit
end LeanTrominoes
