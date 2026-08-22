/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenAtomSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenOffsetOneSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenOffsetZeroSemantics
import LeanTrominoes.PeriodicCNFSourceForwardOffsetData

/-! # Semantics of finite source-occurrence route tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceRouteTokens

/-- Intended finite route block for one source literal. -/
def literalTokens (index : Nat) (literal : PeriodicLiteral Nat) :
    List Token :=
  [.literal (SourceOccurrenceTokens.literalIndex index),
    .offsetNext (SourceForwardOffset.isNext literal), .literalEnd]

/-- Intended finite route block for one source clause. -/
def clauseTokens (clause : PeriodicClause Nat) : List Token :=
  .clause (SourceOccurrenceTokens.clauseArity clause.length) ::
    (clause.zipIdx.flatMap fun tagged =>
      literalTokens tagged.2 tagged.1)

/-- Intended finite route stream for a complete source formula. -/
def formulaTokens (formula : PeriodicCNF Nat) : List Token :=
  formula.clauses.flatMap clauseTokens

/-- A canonical forward-local literal block loses only its unused atom bits
and records its offset as the exact finite current/next bit. -/
theorem scan_literalTokens (index : Nat) (literal : PeriodicLiteral Nat)
    (forward : literal.IsForwardLocal) :
    FiniteStateTransducer.scan transition false
      (SourceOccurrenceTokens.literalTokens index literal) =
      (false, literalTokens index literal) := by
  rcases literal with ⟨atom, offset, value⟩
  change offset = (0, 0) ∨ offset = (1, 0) at forward
  rcases forward with current | next
  · subst offset
    change FiniteStateTransducer.scan transition false
        ([SourceOccurrenceTokens.Token.literal
            (SourceOccurrenceTokens.literalIndex index)] ++
          SourceOccurrenceTokens.atomTokens atom ++
          [SourceOccurrenceTokens.Token.atomEnd] ++
          SourceOccurrenceTokens.offsetTokens 0 ++
          [SourceOccurrenceTokens.Token.offsetEnd,
            SourceOccurrenceTokens.Token.literalEnd]) = _
    simp only [FiniteStateTransducer.scan_append, scan_atomTokens,
      scan_offsetTokens_zero, FiniteStateTransducer.scan, transition,
      List.nil_append, List.append_assoc]
    simp [literalTokens, SourceForwardOffset.isNext]
  · subst offset
    change FiniteStateTransducer.scan transition false
        ([SourceOccurrenceTokens.Token.literal
            (SourceOccurrenceTokens.literalIndex index)] ++
          SourceOccurrenceTokens.atomTokens atom ++
          [SourceOccurrenceTokens.Token.atomEnd] ++
          SourceOccurrenceTokens.offsetTokens 1 ++
          [SourceOccurrenceTokens.Token.offsetEnd,
            SourceOccurrenceTokens.Token.literalEnd]) = _
    simp only [FiniteStateTransducer.scan_append, scan_atomTokens,
      scan_offsetTokens_one, FiniteStateTransducer.scan, transition,
      List.nil_append, List.append_assoc]
    simp [literalTokens, SourceForwardOffset.isNext]

end SourceOccurrenceRouteTokens
end PeriodicCNF
end LeanTrominoes
