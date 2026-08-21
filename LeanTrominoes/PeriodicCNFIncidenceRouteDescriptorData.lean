/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceMetadataOccurrences
import LeanTrominoes.PeriodicCNFIncidenceVertexIndices
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Numeric route descriptors for CNF incidences -/

namespace LeanTrominoes
namespace CNFIncidence

/-- Compact numeric route data read from a formula and one indexed metadata
incidence.  No graph endpoint, local-port, or geometric route query remains. -/
def numericRouteDescriptor
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (incidence : CNFIncidence Variable) (edgeIndex : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount :=
    formula.variableOccurrences.dedup.length + formula.clauses.length
  edgeCount := (PeriodicCNF.incidencesWithMetadata formula).length
  edgeIndex := edgeIndex
  sourceVertexIndex :=
    formula.variableOccurrences.dedup.length + incidence.clauseIndex
  targetVertexIndex :=
    formula.variableOccurrences.dedup.idxOf incidence.literal.atom
  sourcePortRank :=
    (((PeriodicCNF.incidencesWithMetadata formula).take edgeIndex).map
      CNFIncidence.clauseIndex).count incidence.clauseIndex
  targetPortRank :=
    (formula.variableOccurrences.take edgeIndex).count incidence.literal.atom
  offset := incidence.edge.offset

end CNFIncidence
end LeanTrominoes
