/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenClauseSemantics

/-! # Exact flat-formula parsing for occurrence tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Turing

/-- Consecutive promised clauses concatenate their exact occurrence-token
blocks while returning the parser to the arity state. -/
theorem scan_clauseList (clauses : List (PeriodicClause Nat))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3) :
    FiniteStateTransducer.scan transition (.arity .start)
        (PartrecToTM2.trList
          (clauses.flatMap PeriodicCNFFlatEncoding.clauseFields)) =
      (.arity .start, clauses.flatMap clauseTokens) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses induction =>
      have clauseWidth : clause.length ≤ 3 := width clause (by simp)
      have tailWidth : ∀ member ∈ clauses, member.length ≤ 3 := by
        intro member membership
        exact width member (by simp [membership])
      simp only [List.flatMap_cons]
      rw [trList_append, FiniteStateTransducer.scan_append,
        scan_clauseFields clause clauseWidth]
      simp only
      rw [induction tailWidth]

/-- Parsing the complete native field word of a promised width-three formula
emits exactly its semantic occurrence stream. -/
theorem scan_formulaFields (formula : PeriodicCNF Nat)
    (width : formula.WidthAtMost 3) :
    FiniteStateTransducer.scan transition initial
        (PartrecToTM2.trList
          (PeriodicCNFFlatEncoding.formulaFields formula)) =
      (.arity .start, formulaTokens formula) := by
  rcases formula with ⟨clauses⟩
  simp only [PeriodicCNFFlatEncoding.formulaFields, initial]
  rw [show PartrecToTM2.trList
        (clauses.length ::
          clauses.flatMap PeriodicCNFFlatEncoding.clauseFields) =
      (PartrecToTM2.trNat clauses.length ++ [.cons]) ++
        PartrecToTM2.trList
          (clauses.flatMap PeriodicCNFFlatEncoding.clauseFields) by
        simp [PartrecToTM2.trList, List.append_assoc]]
  rw [FiniteStateTransducer.scan_append,
    scan_clauseCountField clauses.length]
  simp only
  rw [scan_clauseList clauses width]
  rfl

/-- The physical flat formula encoding parses to the exact semantic
occurrence stream. -/
theorem parse_finEncoding_encode (formula : PeriodicCNF Nat)
    (width : formula.WidthAtMost 3) :
    parse (PeriodicCNFFlatEncoding.finEncoding.encode formula) =
      formulaTokens formula := by
  change parse
      (PeriodicCNFFlatEncoding.encodeNatFields
        (PeriodicCNFFlatEncoding.formulaFields formula)) = _
  rw [PeriodicCNFFlatEncoding.encodeNatFields_eq_trList]
  unfold parse FiniteStateTransducer.output
  rw [scan_formulaFields formula width]
  simp [finish]

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes
