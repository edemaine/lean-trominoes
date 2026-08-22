/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkRouteDescriptorTokenCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteDescriptorTokenCompiler
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time complete occurrence-split descriptor tokens -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceSplitRouteDescriptorTokens

open Computability Turing

abbrev PairSymbol := SeparatedProductEncoding.Token
  UnaryProgramTokens.Token UnaryProgramTokens.Token

def mergeBlock : PairSymbol → List UnaryProgramTokens.Token
  | .left token => [token]
  | .separator => []
  | .right token => [token]

def merge (tokens : List PairSymbol) : List UnaryProgramTokens.Token :=
  tokens.flatMap mergeBlock

def pairOutput
    (pair : List UnaryProgramTokens.Token ×
      List UnaryProgramTokens.Token) :
    List UnaryProgramTokens.Token :=
  pair.1 ++ pair.2

@[simp] theorem merge_separated
    (first second : List UnaryProgramTokens.Token) :
    merge (SeparatedProductEncoding.encode id id (first, second)) =
      pairOutput (first, second) := by
  simp [merge, mergeBlock, pairOutput,
    SeparatedProductEncoding.encode, List.flatMap_map]

noncomputable def mergeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List UnaryProgramTokens.Token × List UnaryProgramTokens.Token)
      (List UnaryProgramTokens.Token)
      PairSymbol UnaryProgramTokens.Token
      (SeparatedProductEncoding.encode id id) id pairOutput := by
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
    (SeparatedProductEncoding.encode id id (first, second))

theorem pairOutput_eq_tokens (source : Source) :
    pairOutput
        (PeriodicOrthocrossing.routeDescriptorTokens
          (PeriodicThreeSATThree.occurrenceRouteDescriptors source.formula),
        PeriodicOrthocrossing.routeDescriptorTokens
          (PeriodicThreeSATThree.cycleLinkRouteDescriptors source.formula)) =
      tokens source := by
  unfold pairOutput tokens PeriodicThreeSATThree.splitRouteDescriptors
  exact (SourceCycleLinkRouteEmitter.routeDescriptorTokens_append _ _).symm

/-- The occurrence-prefix compiler and cycle-link compiler concatenate to the
complete route-descriptor token stream of occurrence splitting. -/
noncomputable def compiler : Compiler := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceRouteEmitter.occurrenceRouteDescriptorTokensComputableInPolyTime
    SourceCycleLinkRouteEmitter.cycleLinkRouteDescriptorTokensComputableInPolyTime
  let merged := TM2CompositionMachine.computableInPolyTime paired
    mergeComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq merged
    pairOutput_eq_tokens

end SourceSplitRouteDescriptorTokens
end PeriodicCNF
end LeanTrominoes

end
