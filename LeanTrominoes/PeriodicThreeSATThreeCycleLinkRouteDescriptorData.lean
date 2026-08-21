/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkIncidenceData
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptors

/-! # Explicit route descriptors for cycle-link incidences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The complete numeric route record for one local cycle-suffix incidence. -/
def cycleLinkRouteDescriptor
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (incidence : CNFIncidence (ThreeOccurrenceVariable Variable))
    (localIndex : Nat) : PeriodicOrthocrossing.RouteDescriptor where
  vertexCount := source.clauses.length +
    2 * PeriodicCNF.presentationLiteralCount source
  edgeCount := 3 * PeriodicCNF.presentationLiteralCount source
  edgeIndex := PeriodicCNF.presentationLiteralCount source + localIndex
  sourceVertexIndex := PeriodicCNF.presentationLiteralCount source +
    incidence.clauseIndex
  targetVertexIndex :=
    @List.idxOf (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq incidence.literal.atom
      (rotatedOccurrenceVariables source)
  sourcePortRank := incidence.literalIndex
  targetPortRank :=
    1 + @List.count (ThreeOccurrenceVariable Variable)
      instBEqOfDecidableEq incidence.literal.atom
      (((cycleLinkIncidences source).map
        (fun item => item.literal.atom)).take localIndex)
  offset := incidence.edge.offset

end PeriodicThreeSATThree
end LeanTrominoes
