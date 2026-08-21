/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorData

/-! # Numeric CNF route and segment enumerations -/

namespace LeanTrominoes
namespace PeriodicCNF

/-- One compact numeric route descriptor per metadata incidence, in exact
edge-presentation order. -/
def numericRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  (incidencesWithMetadata formula).zipIdx.map fun tagged =>
    tagged.1.numericRouteDescriptor formula tagged.2

/-- Routes reconstructed pointwise from the compact numeric descriptors. -/
def numericEdgeRoutes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List (List Cell) :=
  (numericRouteDescriptors formula).map
    PeriodicOrthocrossing.RouteDescriptor.route

/-- Complete indexed-segment enumeration reconstructed from the compact
numeric route stream. -/
def numericIndexedSegments
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List IndexedGridSegment :=
  (numericEdgeRoutes formula).zipIdx.flatMap fun taggedRoute =>
    (gridPolylineSegments taggedRoute.1).zipIdx.map fun taggedSegment =>
      ⟨taggedRoute.2, taggedSegment.2, taggedSegment.1⟩

end PeriodicCNF
end LeanTrominoes
