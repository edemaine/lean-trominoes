/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRouteOccurrenceData
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort

/-! # Routed-variable occurrences by site -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- A lifted variable vertex is named by its atom and cell. -/
abbrev VariableRouteSite (Variable : Type*) := Variable × Cell

/-- Lifted variable sites appearing in the neighboring routed-occurrence
block, in last-occurrence deduplication order. -/
def drawingVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (VariableRouteSite Variable) :=
  ((drawingCNFRouteOccurrences formula).map
    CNFRouteOccurrence.variableOccurrence).dedup

/-- Routed occurrences at one lifted variable site, in global edge order. -/
def variableRouteOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (CNFRouteOccurrence Variable) :=
  ((drawingCNFRouteOccurrences formula).filter fun occurrence =>
    occurrence.variableOccurrence = site).insertionSort fun first second =>
      first.edgeIndex ≤ second.edgeIndex

end LeanTrominoes.PeriodicOrthocrossing
