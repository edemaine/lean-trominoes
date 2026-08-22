/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceClauseCountFieldCompiler
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteEmitterData
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeSemantics
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time source cycle-link route-emitter inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

open Computability Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

abbrev PairSymbol := SeparatedProductEncoding.Token
  UnaryFieldEncoderMachine.Symbol UnaryFieldEncoderMachine.Symbol

def mergeBlock : PairSymbol → List UnaryFieldEncoderMachine.Symbol
  | .left symbol => [symbol]
  | .separator => []
  | .right symbol => [symbol]

def merge (tokens : List PairSymbol) :
    List UnaryFieldEncoderMachine.Symbol :=
  tokens.flatMap mergeBlock

def pairOutput
    (pair : List UnaryFieldEncoderMachine.Symbol × List Nat) :
    List UnaryFieldEncoderMachine.Symbol :=
  pair.1 ++ UnaryFieldEncoderMachine.unaryFields pair.2

@[simp] theorem merge_separated
    (first : List UnaryFieldEncoderMachine.Symbol) (second : List Nat) :
    merge (SeparatedProductEncoding.encode id
      UnaryFieldEncoderMachine.unaryFields (first, second)) =
        pairOutput (first, second) := by
  simp [merge, mergeBlock, pairOutput,
    SeparatedProductEncoding.encode, List.flatMap_map]

noncomputable def mergeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List UnaryFieldEncoderMachine.Symbol × List Nat)
      (List UnaryFieldEncoderMachine.Symbol)
      PairSymbol UnaryFieldEncoderMachine.Symbol
      (SeparatedProductEncoding.encode id
        UnaryFieldEncoderMachine.unaryFields)
      id pairOutput := by
  let compiler := FiniteBlockTransducer.computableInPolyTime mergeBlock
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  rintro ⟨first, second⟩
  rw [← merge_separated first second]
  exact compiler.outputsFun
    (SeparatedProductEncoding.encode id
      UnaryFieldEncoderMachine.unaryFields (first, second))

theorem compiledGroupSizes_eq_sourceInput (source :
    SourceSplitRouteDescriptorTokens.Source) :
    PeriodicCNF.SourceOccurrenceAtomGroupSizes.sizes source =
      (sourceInput source).groupSizes := by
  rw [PeriodicCNF.SourceOccurrenceAtomGroupSizes.sizes_eq_sourceVariableCounts]
  unfold sourceInput
  apply List.map_congr_left
  intro atom atomMember
  exact (PeriodicThreeSATThree.occurrenceVariables_length_eq_count
    source.formula atom).symm

/-- The source clause count and last-occurrence-ordered atom-group sizes can
be prepared together in the emitter's unary encoding in polynomial time. -/
noncomputable def sourceInputComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode encode sourceInput := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceClauseCountField.computableInPolyTime
    PeriodicCNF.SourceOccurrenceAtomGroupSizes.unaryFieldsComputableInPolyTime
  let merged := TM2CompositionMachine.computableInPolyTime paired
    mergeComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq merged
    fun source => by
      rw [pairOutput, SourceClauseCountField.sourceField_eq,
        compiledGroupSizes_eq_sourceInput]
      rfl

end LeanTrominoes.PeriodicCNF.SourceCycleLinkRouteEmitter

end
