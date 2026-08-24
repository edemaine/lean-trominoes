/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceData
import LeanTrominoes.PeriodicGraph
import LeanTrominoes.PeriodicOrthocrossingConstruction
import LeanTrominoes.PeriodicOrthocrossingPlanarTerminals

/-! # Terminal data for routed periodic-CNF incidences -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A translated incidence route's finite occurrence key. -/
def CNFRouteOccurrence.routeKey {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) :
    Nat × Cell :=
  (occurrence.edgeIndex, occurrence.translate)

/-- Tagged geometric segments of one metadata-rich route occurrence. -/
def CNFRouteOccurrence.taggedSegments
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) :
    List (GridSegment × Nat) :=
  (gridPolylineSegments
    (constructedEdgeRoute
      (PeriodicCNF.incidenceGraph formula)
      occurrence.edge occurrence.edgeIndex)).zipIdx

/-- Harmless total default for selecting from a route segment list. -/
def defaultTaggedGridSegment : GridSegment × Nat :=
  (⟨(0, 0), (0, 0)⟩, 0)

/-- Canonical terminal at the clause/source end of a routed incidence. -/
def CNFRouteOccurrence.sourceTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) : SegmentTerminal :=
  let first :=
    (occurrence.taggedSegments formula).getD
      0 defaultTaggedGridSegment
  ⟨⟨occurrence.edgeIndex, first.2, first.1⟩,
    occurrence.translate, .start⟩

/-- Canonical terminal at the variable/target end of a routed incidence. -/
def CNFRouteOccurrence.targetTerminal
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable) : SegmentTerminal :=
  let last :=
    (occurrence.taggedSegments formula).getLastD
      defaultTaggedGridSegment
  ⟨⟨occurrence.edgeIndex, last.2, last.1⟩,
    occurrence.translate, .finish⟩

end LeanTrominoes.PeriodicOrthocrossing
