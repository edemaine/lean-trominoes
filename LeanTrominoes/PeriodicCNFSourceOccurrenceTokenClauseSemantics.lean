/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenFieldSemantics

/-! # Exact flat-clause parsing for occurrence tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTokens

open Turing

/-- The native list-of-naturals word respects concatenation of field lists. -/
theorem trList_append (first second : List Nat) :
    PartrecToTM2.trList (first ++ second) =
      PartrecToTM2.trList first ++ PartrecToTM2.trList second := by
  induction first with
  | nil => rfl
  | cons field first induction =>
      simp only [List.cons_append, PartrecToTM2.trList]
      rw [induction]
      simp [List.append_assoc]

/-- Parsing one promised width-three clause emits exactly its clause and
indexed literal blocks, and returns to the arity state. -/
theorem scan_clauseFields (clause : PeriodicClause Nat)
    (width : clause.length ≤ 3) :
    FiniteStateTransducer.scan transition (.arity .start)
        (PartrecToTM2.trList
          (PeriodicCNFFlatEncoding.clauseFields clause)) =
      (.arity .start, clauseTokens clause) := by
  rcases clause with _ | ⟨first, rest⟩
  · rfl
  · cases rest with
    | nil =>
        simp only [PeriodicCNFFlatEncoding.clauseFields,
          List.length_cons, List.length_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        rw [show PartrecToTM2.trList
              (1 :: PeriodicCNFFlatEncoding.literalFields first) =
            (PartrecToTM2.trNat 1 ++ [.cons]) ++
              PartrecToTM2.trList
                (PeriodicCNFFlatEncoding.literalFields first) by rfl]
        rw [FiniteStateTransducer.scan_append,
          scan_arityField 1 (by omega)]
        simp [beginClause, clauseArity]
        rw [scan_literalFields]
        simp [nextLiteral, clauseTokens, literalTokens, literalIndex,
          clauseArity]
    | cons second rest =>
        cases rest with
        | nil =>
            simp only [PeriodicCNFFlatEncoding.clauseFields,
              List.length_cons, List.length_nil, List.flatMap_cons,
              List.flatMap_nil, List.append_nil]
            rw [show PartrecToTM2.trList
                  (2 :: (PeriodicCNFFlatEncoding.literalFields first ++
                    PeriodicCNFFlatEncoding.literalFields second)) =
                (PartrecToTM2.trNat 2 ++ [.cons]) ++
                  (PartrecToTM2.trList
                      (PeriodicCNFFlatEncoding.literalFields first) ++
                    PartrecToTM2.trList
                      (PeriodicCNFFlatEncoding.literalFields second)) by
              simp [trList_append, List.append_assoc]]
            rw [FiniteStateTransducer.scan_append,
              scan_arityField 2 (by omega)]
            simp [beginClause, clauseArity]
            rw [FiniteStateTransducer.scan_append, scan_literalFields]
            simp [nextLiteral]
            rw [scan_literalFields]
            simp [nextLiteral, clauseTokens, literalTokens, literalIndex,
              clauseArity, List.append_assoc]
            rfl
        | cons third rest =>
            cases rest with
            | nil =>
                simp only [PeriodicCNFFlatEncoding.clauseFields,
                  List.length_cons, List.length_nil, List.flatMap_cons,
                  List.flatMap_nil, List.append_nil]
                rw [show PartrecToTM2.trList
                      ((0 + 1 + 1 + 1) ::
                        (PeriodicCNFFlatEncoding.literalFields first ++
                          (PeriodicCNFFlatEncoding.literalFields second ++
                            PeriodicCNFFlatEncoding.literalFields third))) =
                    (PartrecToTM2.trNat 3 ++ [.cons]) ++
                      (PartrecToTM2.trList
                          (PeriodicCNFFlatEncoding.literalFields first) ++
                        (PartrecToTM2.trList
                            (PeriodicCNFFlatEncoding.literalFields second) ++
                          PartrecToTM2.trList
                            (PeriodicCNFFlatEncoding.literalFields third))) by
                  simp [trList_append, List.append_assoc]]
                rw [FiniteStateTransducer.scan_append,
                  scan_arityField 3 (by omega)]
                simp [beginClause, clauseArity]
                rw [FiniteStateTransducer.scan_append, scan_literalFields]
                simp [nextLiteral]
                rw [FiniteStateTransducer.scan_append, scan_literalFields]
                simp [nextLiteral]
                rw [scan_literalFields]
                simp [nextLiteral, clauseTokens, literalTokens,
                  literalIndex, clauseArity, List.append_assoc]
                rfl
            | cons fourth rest =>
                simp only [List.length_cons] at width
                omega

end SourceOccurrenceTokens
end PeriodicCNF
end LeanTrominoes
