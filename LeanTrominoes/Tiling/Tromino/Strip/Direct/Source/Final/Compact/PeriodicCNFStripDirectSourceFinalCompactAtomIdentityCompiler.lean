/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Computation.Encoding.Delimited.DelimitedBinaryWordLastIndexIdentityCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Compact.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Copied.PeriodicCNFStripDirectSourceFinalCopiedClauseDescriptorArity
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Copied.PeriodicCNFStripDirectSourceFinalCopiedScopedAtomWordData
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Numeric identities of direct compact final-source atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- For each pre-Figure9 final-source occurrence, the last presentation
index carrying the same compact atom word. -/
def directSourceFinalCompactOccurrenceAtomIdentityIndices
    (symbols : List encoding.Γ) : List Nat :=
  DelimitedBinaryWordLastIndexIdentity.identityIndices
    (directSourceFinalCompactOccurrenceAtomWords decider symbols)

/-- The identity column remains aligned with the complete pre-Figure9 atom
word column and hence with copied descriptor arity. -/
theorem directSourceFinalCompactOccurrenceAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomIdentityIndices
      decider symbols).length =
      ((directRetainedFigureNineCopiedClauseDescriptors decider symbols).map
        retainedFinalCopiedDescriptorArity).sum := by
  rw [directSourceFinalCompactOccurrenceAtomIdentityIndices,
    DelimitedBinaryWordLastIndexIdentity.identityIndices_length,
    directSourceFinalCopiedScopedAtomWords_sourceLength]

/-- Direct compact source-atom identities are polynomial-time computable as
unary fields. -/
noncomputable def
    directSourceFinalCompactOccurrenceAtomIdentityIndicesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalCompactOccurrenceAtomIdentityIndices decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ :=
      ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalCompactOccurrenceAtomIdentityIndices
    exact DelimitedBinaryWordLastIndexIdentity.computableInPolyTime
      id (directSourceFinalCompactOccurrenceAtomWords decider)
      (directSourceFinalCompactOccurrenceAtomWordsComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ :=
      ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

end LeanTrominoes.PeriodicCNFStripReduction

end
