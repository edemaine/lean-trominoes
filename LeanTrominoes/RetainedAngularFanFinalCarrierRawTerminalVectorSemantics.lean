/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRepresentativeTerminalSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics

/-! # Raw representative terminal vectors of retained carrier clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

local instance finalCarrierRawVectorThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Terminal vector of the raw first metadata representative selected by one
final clause index. -/
def finalCarrierRawRepresentativeTerminalVectorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) : Cell :=
  routeTerminalVector
    (rawRepresentativeRoute
      (PeriodicThreeSATThree.formula source) clauseIndex literalIndex)

/-- Raw local carrier-lens terminal vector at one tagged implication. -/
def finalCarrierLocalTerminalVectorAt
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (taggedLink : EqualityLink CarrierNode × Bool)
    (literalIndex : Nat) : Cell :=
  let retained := PeriodicThreeSATThree.formula source
  let localClauseIndex := if taggedLink.2 then 0 else 1
  routeTerminalVector
    (((DrawingPlanarSATClauseSource.carrier
        taggedLink.1 localClauseIndex).incidenceDrawing retained).routes
      localClauseIndex literalIndex)

/-- Exact carrier clause and metadata lookup identify the raw representative
terminal vector with its local carrier-lens route. -/
theorem finalCarrierRawTerminalVector_eq_local
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedLink : EqualityLink CarrierNode × Bool)
    (clauseIndex : Nat)
    (taggedLinkIndexed :
      finalCarrierTaggedLinkIndexed source taggedLink clauseIndex)
    (literalIndex : Nat) :
    finalCarrierRawRepresentativeTerminalVectorAt
        source clauseIndex literalIndex =
      finalCarrierLocalTerminalVectorAt
        source taggedLink literalIndex := by
  unfold finalCarrierRawRepresentativeTerminalVectorAt
    finalCarrierLocalTerminalVectorAt
  dsimp only
  let retained := PeriodicThreeSATThree.formula source
  let clause := normalizedCarrierClauseAt retained taggedLink
  let metadata := carrierClauseMetadataAt
    (Variable := ThreeOccurrenceVariable Variable)
      taggedLink.1 taggedLink.2
  have lookups := finalCarrierClause_metadata_lookups
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
      taggedLink clauseIndex taggedLinkIndexed
  have vectorEq :=
    rawRepresentativeRoute_routeTerminalVector_eq_metadata
      retained clauseIndex literalIndex clause metadata
        lookups.1 lookups.2
  simpa only [retained, metadata, carrierClauseMetadataAt,
    DrawingPlanarSATClauseSource.localClauseIndex] using vectorEq

end PeriodicEightOccurrenceSplit
end LeanTrominoes
