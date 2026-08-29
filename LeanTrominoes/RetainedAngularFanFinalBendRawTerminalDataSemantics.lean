/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBaseBendRepresentativeMetadata
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRepresentativeTerminalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalDataSemantics
import LeanTrominoes.RetainedAngularFanFinalBendLookupSemantics

/-! # Raw representative terminal data of final retained bends -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

local instance finalBendRawTerminalThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Terminal vector of the raw first metadata representative selected by one
final bend clause index. -/
def finalBendRawRepresentativeTerminalVectorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  routeTerminalVector
    (rawRepresentativeRoute
      (PeriodicThreeSATThree.formula source) clauseIndex literalIndex)

/-- Semantic corner-table terminal datum of one canonical bend implication. -/
def finalBendSemanticTerminalDataAt
    {Variable : Type} [DecidableEq Variable]
    (_source : PeriodicCNF Variable)
    (taggedBend : RouteBend × Bool)
    (literalIndex : Nat) : RetainedTerminalData :=
  bendRouteTerminalData
    taggedBend.1.incomingPort taggedBend.1.outgoingPort
    (if taggedBend.2 then 0 else 1) literalIndex

/-- The raw first representative of an indexed canonical bend clause has the
exact corner-table terminal datum of that bend and implication. -/
theorem finalBendRawTerminalData_eq_semantic
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedBend : RouteBend × Bool)
    (clauseIndex : Nat)
    (taggedBendIndexed :
      finalBendTaggedBendIndexed source taggedBend clauseIndex)
    (literalIndex : Nat) :
    classifiedRetainedTerminalData
        (finalBendRawRepresentativeTerminalVectorAt
          source clauseIndex literalIndex) =
      finalBendSemanticTerminalDataAt
        source taggedBend literalIndex := by
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedBendClauseAt retained taggedBend
  have taggedBendIndexed' := taggedBendIndexed
  unfold finalBendTaggedBendIndexed at taggedBendIndexed'
  have taggedBendMember : taggedBend ∈
      (baseRouteBends retained).product [true, false] :=
    List.fst_mem_of_mem_zipIdx taggedBendIndexed'
  have clauseLookup :
      (deduplicatedClauses retained)[clauseIndex]? = some clause := by
    simpa only [retained, clause] using
      finalBendClause_lookup source sourceLocal sourceWidth
        sourceClausesNonempty positiveOffsets taggedBend clauseIndex
          taggedBendIndexed
  rcases exists_baseBendRepresentativeMetadata
      retained
      (formula_incidenceGraph_isWellFormed source)
      (formula_incidenceGraph_degreeAtMostThree sourceWidth)
      (formula_incidenceGraph_isLocal sourceLocal)
      taggedBend taggedBendMember with
    ⟨selectedBend, metadataLookup, incomingEq, outgoingEq⟩
  have vectorEq :=
    rawRepresentativeRoute_routeTerminalVector_eq_metadata
      retained clauseIndex literalIndex clause
        (bendClauseMetadataAt
          (Variable := ThreeOccurrenceVariable Variable)
          retained.incidenceGraph selectedBend taggedBend.2)
        clauseLookup metadataLookup
  unfold finalBendRawRepresentativeTerminalVectorAt
    finalBendSemanticTerminalDataAt
  calc
    classifiedRetainedTerminalData
          (routeTerminalVector
            (rawRepresentativeRoute retained clauseIndex literalIndex)) =
        classifiedRetainedTerminalData
          (routeTerminalVector
            (((DrawingPlanarSATClauseSource.bend selectedBend
                (if taggedBend.2 then 0 else 1)).incidenceDrawing
              retained).routes
                (if taggedBend.2 then 0 else 1) literalIndex)) :=
      congrArg classifiedRetainedTerminalData (by
        simpa only [bendClauseMetadataAt,
          DrawingPlanarSATClauseSource.localClauseIndex] using vectorEq)
    _ = bendRouteTerminalData selectedBend.incomingPort
          selectedBend.outgoingPort
          (if taggedBend.2 then 0 else 1) literalIndex :=
      bend_routeTerminalData_eq retained selectedBend
        (if taggedBend.2 then 0 else 1) literalIndex
    _ = bendRouteTerminalData taggedBend.1.incomingPort
          taggedBend.1.outgoingPort
          (if taggedBend.2 then 0 else 1) literalIndex := by
      rw [incomingEq, outgoingEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
