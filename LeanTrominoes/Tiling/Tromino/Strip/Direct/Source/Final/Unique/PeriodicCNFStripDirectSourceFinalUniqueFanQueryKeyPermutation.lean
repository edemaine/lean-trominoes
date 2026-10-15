/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Graphs.Drawings.Grid.FinalFanQueryRankKeyPermutation
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Atom.PeriodicCNFStripDirectSourceFinalAtomIdentityOccurrenceBound
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Unique.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Exact grouped occurrence-key coverage -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- The stable variable-major fan keys are a permutation of the complete
clause-major occurrence-key column.  Thus regrouping neither loses nor
duplicates any genuine final occurrence. -/
theorem directSourceFinalUniqueFanQueryKeys_perm_candidateKeys
    (symbols : List encoding.Γ) :
    (directSourceFinalUniqueFanQueryKeys decider symbols).Perm
      (directSourceFinalOccurrenceCandidateKeys decider symbols) := by
  rw [directSourceFinalUniqueFanQueryKeys_eq,
    directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
  apply FinalFanQueryRanks.dedup_keyedBlocks_perm_candidateKeys
  intro value _valueMember
  exact directSourceFinalAtomIdentityCodes_count_le_three
    decider symbols value

end LeanTrominoes.PeriodicCNFStripReduction
