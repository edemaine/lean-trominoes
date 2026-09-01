/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBaseBendRepresentativeMetadata
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRawRepresentativeRouteSemantics
import LeanTrominoes.RetainedAngularFanFinalBendIndexedOccurrence
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRawRoutePrefixDirections

/-! # Raw prefix words of final retained-bend routes -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT
open PeriodicThreeSATThree

attribute [local instance]
  finalBendIndexedOccurrenceThreeOccurrenceDecidableEq

private theorem FinalBendIndexedOccurrence.clauseLookup
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

private theorem FinalBendIndexedOccurrence.baseTaggedBendMember
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    occurrence.taggedBend ∈
      (baseRouteBends occurrence.retained).product [true, false] := by
  have indexed := occurrence.taggedBendIndexed
  unfold finalBendTaggedBendIndexed at indexed
  exact List.fst_mem_of_mem_zipIdx indexed

private theorem FinalBendIndexedOccurrence.rawRepresentativePrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    Gadget.unitSubdivisionDirections
        (rawRepresentativeRoute occurrence.retained
          occurrence.clauseIndex occurrence.literalIndex).dropLast =
      bendRoutePrefixDirections
        occurrence.taggedBend.1.incomingPort
        occurrence.taggedBend.1.outgoingPort
        occurrence.localClauseIndex occurrence.literalIndex := by
  let retained := occurrence.retained
  have retainedWellFormed : retained.incidenceGraph.IsWellFormed :=
    formula_incidenceGraph_isWellFormed occurrence.source
  have retainedDegree : retained.incidenceGraph.DegreeAtMost 3 :=
    formula_incidenceGraph_degreeAtMostThree occurrence.sourceWidth
  have retainedLocal : retained.incidenceGraph.IsLocal :=
    formula_incidenceGraph_isLocal occurrence.sourceLocal
  rcases exists_baseBendRepresentativeMetadata
      retained retainedWellFormed retainedDegree retainedLocal
      occurrence.taggedBend occurrence.baseTaggedBendMember with
    ⟨selectedBend, metadataLookup, incomingEq, outgoingEq⟩
  have rawPrefix := rawRepresentativeRoute_bend_prefixDirections_eq
    retained occurrence.taggedBend selectedBend occurrence.clauseIndex
      occurrence.literalIndex occurrence.clauseLookup metadataLookup
  calc
    Gadget.unitSubdivisionDirections
          (rawRepresentativeRoute retained occurrence.clauseIndex
            occurrence.literalIndex).dropLast =
        bendRoutePrefixDirections selectedBend.incomingPort
          selectedBend.outgoingPort occurrence.localClauseIndex
          occurrence.literalIndex := by
      cases h : occurrence.taggedBend.2 <;>
        simpa [FinalBendIndexedOccurrence.localClauseIndex, h] using rawPrefix
    _ = _ := by rw [incomingEq, outgoingEq]

/-- Deleting the old variable endpoint from an indexed final bend route
exposes the finite corner-table prefix word of its untranslated bend. -/
theorem FinalBendIndexedOccurrence.rawRoutePrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    Gadget.unitSubdivisionDirections
        (finalCoordinatedSourceRoutes occurrence.retained
          occurrence.clauseIndex occurrence.literalIndex).dropLast =
      bendRoutePrefixDirections
        occurrence.taggedBend.1.incomingPort
        occurrence.taggedBend.1.outgoingPort
        occurrence.localClauseIndex occurrence.literalIndex := by
  calc
    Gadget.unitSubdivisionDirections
          (finalCoordinatedSourceRoutes occurrence.retained
            occurrence.clauseIndex occurrence.literalIndex).dropLast =
        Gadget.unitSubdivisionDirections
          (rawRepresentativeRoute occurrence.retained occurrence.clauseIndex
            occurrence.literalIndex).dropLast :=
      finalCoordinatedSourceRoutes_prefixDirections_eq_rawRepresentativeRoute
        occurrence.retained occurrence.clauseIndex occurrence.literalIndex
    _ = _ := occurrence.rawRepresentativePrefixDirections

/-- Scaling by the construction's two fixed refinements repeats that finite
prefix word exactly 1152 times. -/
theorem FinalBendIndexedOccurrence.fallbackSourcePrefixDirections
    {Variable : Type} [DecidableEq Variable]
    (occurrence : FinalBendIndexedOccurrence Variable) :
    Gadget.unitSubdivisionDirections
        (retainedFallbackSourcePrefix occurrence.scaledRoute) =
      Gadget.repeatDirections 1152
        (bendRoutePrefixDirections
          occurrence.taggedBend.1.incomingPort
          occurrence.taggedBend.1.outgoingPort
          occurrence.localClauseIndex occurrence.literalIndex) := by
  rw [retainedFallbackSourcePrefix_sourceClearanceScaled_directions,
    occurrence.rawRoutePrefixDirections]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
