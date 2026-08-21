/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Explicit complete descriptor stream for occurrence splitting -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Explicit cycle-suffix route records in local suffix order. -/
def cycleLinkRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  (cycleLinkIncidences source).zipIdx.map fun tagged =>
    cycleLinkRouteDescriptor source tagged.1 tagged.2

/-- The full explicit occurrence-split route stream. -/
def splitRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    List PeriodicOrthocrossing.RouteDescriptor :=
  occurrenceRouteDescriptors source ++ cycleLinkRouteDescriptors source

@[simp] theorem cycleLinkRouteDescriptors_length
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (cycleLinkRouteDescriptors source).length =
      2 * PeriodicCNF.presentationLiteralCount source := by
  simp [cycleLinkRouteDescriptors]

@[simp] theorem splitRouteDescriptors_length
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    (splitRouteDescriptors source).length =
      3 * PeriodicCNF.presentationLiteralCount source := by
  simp [splitRouteDescriptors]
  omega

end PeriodicThreeSATThree
end LeanTrominoes
