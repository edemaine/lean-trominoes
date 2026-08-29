/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BinaryRouteTailRecordBatchFormatterData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendRoutePrefixDirectionStreamSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalColumnData
import LeanTrominoes.RetainedAngularFanFallbackJoinedDirectionSemantics

/-! # Semantic four-route record blocks for retained bends -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace BendFallbackRouteTailRecords

open PlanarThreeSAT
open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

/-- The finite corner-port data of one untranslated retained bend. -/
structure Geometry where
  firstPort : CornerPort
  secondPort : CornerPort

/-- Untranslated bends in numeric-route and within-route presentation order. -/
def selectedGeometries (descriptors : List RouteDescriptor) :
    List Geometry :=
  descriptors.flatMap fun descriptor =>
    (routeBends descriptor.edgeIndex (0, 0) descriptor.route).map
      fun routeBend =>
        { firstPort := routeBend.incomingPort
          secondPort := routeBend.outgoingPort }

def Geometry.prefixWords (geometry : Geometry) :
    List (List AxisDirection) :=
  [Gadget.repeatDirections 1152
      (bendRoutePrefixDirections
        geometry.firstPort geometry.secondPort 0 0),
    Gadget.repeatDirections 1152
      (bendRoutePrefixDirections
        geometry.firstPort geometry.secondPort 0 1),
    Gadget.repeatDirections 1152
      (bendRoutePrefixDirections
        geometry.firstPort geometry.secondPort 1 0),
    Gadget.repeatDirections 1152
      (bendRoutePrefixDirections
        geometry.firstPort geometry.secondPort 1 1)]

/-- Exact ordinary-policy terminal query belonging to one bend route. -/
def routeQuery (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) :
    FallbackSuffixDirectionCompiler.Batch.Query :=
  let terminal := bendRouteTerminalData
    geometry.firstPort geometry.secondPort localClauseIndex literalIndex
  { kind := .ordinary
    direction := terminal.1
    rawLength := terminal.2
    slot := slot }

def routeDirections (geometry : Geometry)
    (localClauseIndex literalIndex : Nat)
    (slot : RetainedTerminalSlot) : List AxisDirection :=
  Gadget.repeatDirections 1152
      (bendRoutePrefixDirections geometry.firstPort geometry.secondPort
        localClauseIndex literalIndex) ++
    (routeQuery geometry localClauseIndex literalIndex slot).geometricSuffixDirections

def queryBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  [routeQuery geometry 0 0 first,
    routeQuery geometry 0 1 second,
    routeQuery geometry 1 0 third,
    routeQuery geometry 1 1 fourth]

def routeDirectionBlock (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    List (List AxisDirection) :=
  [routeDirections geometry 0 0 first,
    routeDirections geometry 0 1 second,
    routeDirections geometry 1 0 third,
    routeDirections geometry 1 1 fourth]

/-- One retained bend contributes two binary profiles and four complete
routes in clause-major incidence order. -/
def block (geometry : Geometry)
    (first second third fourth : RetainedTerminalSlot) :
    BinaryRouteTailRecordBatchFormatter.Block where
  firstProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (bendClauseDescriptor geometry.firstPort geometry.secondPort false true)
  secondProfile := BinaryRouteTailRecordFormatter.descriptorProfile
    (bendClauseDescriptor geometry.firstPort geometry.secondPort false false)
  first := routeDirections geometry 0 0 first
  second := routeDirections geometry 0 1 second
  third := routeDirections geometry 1 0 third
  fourth := routeDirections geometry 1 1 fourth

def blocks : List Geometry → List RetainedTerminalSlot →
    List BinaryRouteTailRecordBatchFormatter.Block
  | geometry :: geometries, first :: second :: third :: fourth :: slots =>
      block geometry first second third fourth :: blocks geometries slots
  | _, _ => []

end BendFallbackRouteTailRecords
end PeriodicOrthocrossing
end LeanTrominoes
