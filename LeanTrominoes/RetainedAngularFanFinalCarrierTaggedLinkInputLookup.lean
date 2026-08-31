/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCarrierLookupSemantics
import LeanTrominoes.RetainedAngularFanFinalCarrierTaggedLiteralInputData

/-! # Clause lookup from packaged final retained-carrier input -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing
open PlanarThreeSAT

/-- The packaged index and source hypotheses for a tagged final carrier imply
its exact lookup in the duplicate-free retained clause presentation. -/
theorem FinalCarrierTaggedLinkInput.clauseLookup
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedLink : EqualityLink CarrierNode × Bool}
    {clauseIndex : Nat}
    (input : FinalCarrierTaggedLinkInput
      source taggedLink clauseIndex) :
    (deduplicatedClauses (PeriodicThreeSATThree.formula source))[
        clauseIndex]? =
      some (normalizedCarrierClauseAt
        (PeriodicThreeSATThree.formula source) taggedLink) := by
  have lookups := finalCarrierClause_metadata_lookups
    source
    input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
    input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
    input.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty
    input.sourceInput.sourceFacts.positiveOffsets
    taggedLink clauseIndex input.taggedLinkIndexed
  exact lookups.1

end PeriodicEightOccurrenceSplit
end LeanTrominoes
