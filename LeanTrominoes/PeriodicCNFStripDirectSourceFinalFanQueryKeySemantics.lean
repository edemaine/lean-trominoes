/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanQueryRankKeyCoverage
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceKeySemantics

/-! # Semantic coverage of compiled final variable-fan query keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Repeated query identity bases have their direct semantic block form. -/
theorem directSourceFinalFanQueryIdentityBases_eq
    (symbols : List encoding.Γ) :
    directSourceFinalFanQueryIdentityBases decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).flatMap fun code =>
        List.replicate 3 (code * 3) := by
  unfold directSourceFinalFanQueryIdentityBases
    directSourceFinalScaledAtomIdentityCodes
  generalize directSourceFinalAtomIdentityCodes decider symbols = codes
  simp [UnaryFieldFixedCopies.values, UnaryFieldConstantScale.values,
    List.flatMap_map]

/-- Repeated finite query ranks have their direct semantic block form. -/
theorem directSourceFinalFanQueryRanks_eq
    (symbols : List encoding.Γ) :
    directSourceFinalFanQueryRanks decider symbols =
      (directSourceFinalAtomIdentityCodes decider symbols).flatMap fun code =>
        (FinalFanQueryRanks.block
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            ((directSourceFinalAtomIdentityCodes decider symbols).count
              code))).map Fin.val := by
  unfold directSourceFinalFanQueryRanks FinalFanQueryRanks.ranks
    FinalFanQueryRanks.finiteRanks
  rw [directSourceFinalOccurrenceCountPreds_eq_identityCodes]
  generalize directSourceFinalAtomIdentityCodes decider symbols = codes
  rw [List.map_flatMap, List.flatMap_map]

private theorem zipWith_fan_query_blocks_aux
    (countPred : Nat → Fin 3) (values : List Nat) :
    List.zipWith (fun first second => first + second)
        (values.flatMap fun value => List.replicate 3 (value * 3))
        (values.flatMap fun value =>
          (FinalFanQueryRanks.block (countPred value)).map Fin.val) =
      values.flatMap fun value =>
        (FinalFanQueryRanks.block (countPred value)).map fun rank =>
          value * 3 + rank.val := by
  have blockZip (value : Nat) :
      List.zipWith (fun first second => first + second)
          (List.replicate 3 (value * 3))
          ((FinalFanQueryRanks.block (countPred value)).map Fin.val) =
        (FinalFanQueryRanks.block (countPred value)).map fun rank =>
          value * 3 + rank.val := by
    simp [FinalFanQueryRanks.block, List.replicate_succ]
  induction values with
  | nil => rfl
  | cons value tail induction =>
      simp only [List.flatMap_cons]
      rw [List.zipWith_append (by simp), blockZip, induction]

private theorem zipWith_fan_query_blocks
    (values : List Nat) :
    List.zipWith (fun first second => first + second)
        (values.flatMap fun value => List.replicate 3 (value * 3))
        (values.flatMap fun value =>
          (FinalFanQueryRanks.block
            (BoundedPositiveCountPreds.boundedPositiveCountPred
              (values.count value))).map Fin.val) =
      FinalFanQueryRanks.keyedBlocks values := by
  unfold FinalFanQueryRanks.keyedBlocks
  exact zipWith_fan_query_blocks_aux
    (fun value => BoundedPositiveCountPreds.boundedPositiveCountPred
      (values.count value)) values

/-- The compiled final fan queries are exactly the three semantic
active-or-fallback rank keys per presented identity. -/
theorem directSourceFinalFanQueryKeys_eq_keyedBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalFanQueryKeys decider symbols =
      FinalFanQueryRanks.keyedBlocks
        (directSourceFinalAtomIdentityCodes decider symbols) := by
  rw [directSourceFinalFanQueryKeys_eq_zipWith,
    directSourceFinalFanQueryIdentityBases_eq,
    directSourceFinalFanQueryRanks_eq]
  exact zipWith_fan_query_blocks
    (directSourceFinalAtomIdentityCodes decider symbols)

/-- Every compiled final fan query has a matching compiled occurrence
candidate key. -/
theorem directSourceFinalFanQueryKey_mem_candidateKeys
    (symbols : List encoding.Γ) (query : Nat)
    (queryMember : query ∈ directSourceFinalFanQueryKeys decider symbols) :
    query ∈ directSourceFinalOccurrenceCandidateKeys decider symbols := by
  rw [directSourceFinalFanQueryKeys_eq_keyedBlocks] at queryMember
  rw [directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  exact FinalFanQueryRanks.keyedBlocks_subset_candidateKeys
    (directSourceFinalAtomIdentityCodes decider symbols) queryMember

end LeanTrominoes.PeriodicCNFStripReduction
