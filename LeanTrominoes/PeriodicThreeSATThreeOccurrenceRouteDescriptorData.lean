/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceData
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration

/-! # Explicit route descriptors for copied occurrence incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The complete numeric route record for one copied source incidence.  Every
field is expressed directly in source presentation data. -/
def occurrenceRouteDescriptor
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence Variable) (edgeIndex : Nat) :
    PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := source.clauses.length +
    2 * PeriodicCNF.presentationLiteralCount source
  edgeCount := 3 * PeriodicCNF.presentationLiteralCount source
  edgeIndex := edgeIndex
  sourceVertexIndex := PeriodicCNF.presentationLiteralCount source +
    incidence.clauseIndex
  targetVertexIndex :=
    (rotatedOccurrenceVariables source).idxOf
      (incidence.literal.atom, incidence.clauseIndex,
        incidence.literalIndex)
  sourcePortRank := incidence.literalIndex
  targetPortRank := 0
  offset := Cell.sub incidence.literal.offset
    (PeriodicCNF.clauseAnchor incidence.clause)

end PeriodicThreeSATThree
end LeanTrominoes
