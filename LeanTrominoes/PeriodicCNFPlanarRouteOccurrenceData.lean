/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataData
import LeanTrominoes.PeriodicOrthocrossingNeighborTranslationsData

/-! # Translated periodic-CNF route occurrences -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- One translated routed occurrence of a syntactic CNF incidence. -/
structure CNFRouteOccurrence (Variable : Type*) where
  incidence : CNFIncidence Variable
  edgeIndex : Nat
  translate : Cell
  deriving DecidableEq, Repr

/-- The protoedge routed by a CNF occurrence. -/
def CNFRouteOccurrence.edge {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) :
    PeriodicEdge (CNFVertex Variable) :=
  occurrence.incidence.edge

/-- The lifted clause vertex at the source of the route. -/
def CNFRouteOccurrence.clauseOccurrence {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) : Nat × Cell :=
  (occurrence.incidence.clauseIndex, occurrence.translate)

/-- The lifted variable vertex at the target of the route. -/
def CNFRouteOccurrence.variableOccurrence {Variable : Type*}
    (occurrence : CNFRouteOccurrence Variable) : Variable × Cell :=
  (occurrence.incidence.literal.atom,
    Cell.add occurrence.translate occurrence.edge.offset)

/-- Every neighboring translated occurrence of every metadata-rich
incidence edge. -/
def drawingCNFRouteOccurrences
    {Variable : Type*} (formula : PeriodicCNF Variable) :
    List (CNFRouteOccurrence Variable) :=
  (PeriodicCNF.incidencesWithMetadata formula).zipIdx.flatMap
    fun taggedIncidence =>
      neighborTranslations.map fun translate =>
        ⟨taggedIncidence.1, taggedIncidence.2, translate⟩

end LeanTrominoes.PeriodicOrthocrossing
