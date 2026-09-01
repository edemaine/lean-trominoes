/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalBendTaggedLiteralInputData

/-! # Clause lookup from packaged final retained-bend input -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- The packaged index and source hypotheses for a tagged final bend imply
its exact lookup in the duplicate-free retained clause presentation. -/
theorem FinalBendTaggedBendInput.clauseLookup
    {Variable : Type} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    {taggedBend : RouteBend × Bool}
    {clauseIndex : Nat}
    (input : FinalBendTaggedBendInput
      source taggedBend clauseIndex) :
    (deduplicatedClauses (PeriodicThreeSATThree.formula source))[
        clauseIndex]? =
      some (normalizedBendClauseAt
        (PeriodicThreeSATThree.formula source) taggedBend) := by
  exact finalBendClause_lookup source
    input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.localFacts.sourceLocal
    input.sourceInput.sourceFacts.nonemptyFacts.widthFacts.sourceWidth
    input.sourceInput.sourceFacts.nonemptyFacts.sourceClausesNonempty
    input.sourceInput.sourceFacts.positiveOffsets
    taggedBend clauseIndex input.taggedBendIndexed

end PeriodicEightOccurrenceSplit
end LeanTrominoes
