/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBaseBendRepresentativeMetadata
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRawRepresentativeRouteSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRepresentativeRouteLength
import LeanTrominoes.RetainedAngularFanFallbackPrefixLengths
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence

/-! # Fallback policy of final retained-bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

private theorem FinalBendIndexedOccurrence.clauseLookupForKind
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    (deduplicatedClauses occurrence.retained)[occurrence.clauseIndex]? =
      some (normalizedBendClauseAt occurrence.retained
        occurrence.taggedBend) := by
  exact finalBendClause_lookup occurrence.source
    occurrence.sourceLocal occurrence.sourceWidth
    occurrence.sourceClausesNonempty occurrence.positiveOffsets
    occurrence.taggedBend occurrence.clauseIndex
    occurrence.taggedBendIndexed

private theorem FinalBendIndexedOccurrence.baseTaggedBendMemberForKind
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    occurrence.taggedBend ∈
      (baseRouteBends occurrence.retained).product [true, false] := by
  have indexed := occurrence.taggedBendIndexed
  unfold finalBendTaggedBendIndexed at indexed
  exact List.fst_mem_of_mem_zipIdx indexed

/-- Deleting the variable endpoint from an indexed final bend route never
leaves a singleton prefix. -/
theorem FinalBendIndexedOccurrence.sourcePrefix_length_ne_one
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    (finalCoordinatedSourceRoutes occurrence.retained
      occurrence.clauseIndex occurrence.literalIndex).dropLast.length ≠ 1 := by
  let retained := occurrence.retained
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed occurrence.source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree occurrence.sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal occurrence.sourceLocal
  rcases exists_baseBendRepresentativeMetadata
      retained retainedWellFormed retainedDegree retainedLocal
      occurrence.taggedBend occurrence.baseTaggedBendMemberForKind with
    ⟨selectedBend, metadataLookup, _incomingEq, _outgoingEq⟩
  have rawRouteEq := rawRepresentativeRoute_eq_bendClauseMetadataAt
    retained occurrence.taggedBend selectedBend occurrence.clauseIndex
      occurrence.literalIndex occurrence.clauseLookupForKind metadataLookup
  let localClauseIndex : Nat := if occurrence.taggedBend.2 then 0 else 1
  let localRoute :=
    (((DrawingPlanarSATClauseSource.bend selectedBend
        localClauseIndex).incidenceDrawing retained).routes
      localClauseIndex occurrence.literalIndex)
  have routeLengthEq :
      (finalCoordinatedSourceRoutes retained occurrence.clauseIndex
          occurrence.literalIndex).length =
        localRoute.length := by
    calc
      _ = (rawRepresentativeRoute retained occurrence.clauseIndex
            occurrence.literalIndex).length :=
        incidenceRoutes_length_eq_rawRepresentativeRoute
          retained occurrence.clauseIndex occurrence.literalIndex
      _ = _ := congrArg List.length (by
        simpa only [localRoute, localClauseIndex] using rawRouteEq)
  have localPrefixNe : localRoute.dropLast.length ≠ 1 := by
    have finite := bendCornerIncidenceRoute_prefix_length_ne_one
      retained selectedBend localClauseIndex occurrence.literalIndex
    simpa only [localRoute,
      DrawingPlanarSATClauseSource.incidenceDrawing] using finite
  intro singleton
  apply localPrefixNe
  calc
    localRoute.dropLast.length =
        (finalCoordinatedSourceRoutes retained occurrence.clauseIndex
          occurrence.literalIndex).dropLast.length := by
      simp only [List.length_dropLast]
      omega
    _ = 1 := singleton

/-- Therefore every indexed final retained bend selects the ordinary fallback
fan rather than the delayed-lane escaped fan. -/
theorem FinalBendIndexedOccurrence.fallbackKind_eq_ordinary
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    (if (finalCoordinatedSourceRoutes occurrence.retained
          occurrence.clauseIndex occurrence.literalIndex).dropLast.length = 1
      then RetainedFallbackFanKind.escaped
      else RetainedFallbackFanKind.ordinary) =
      RetainedFallbackFanKind.ordinary := by
  rw [if_neg occurrence.sourcePrefix_length_ne_one]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
