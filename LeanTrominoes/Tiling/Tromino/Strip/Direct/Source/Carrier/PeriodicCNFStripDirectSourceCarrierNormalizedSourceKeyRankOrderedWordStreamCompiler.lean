/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedWordStreamData
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Source.PeriodicOrthocrossingCarrierSourcePairFieldFormatterCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine
import LeanTrominoes.Computation.TM2.TM2PolyTimeInputEncodingTransport

/-! # Compiler for direct-source normalized rank-ordered carrier words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Direct source symbols compile to one guarded normalized source-pair word
per global carrier rank in polynomial time. -/
noncomputable def
    directSourceCarrierNormalizedSourceKeyRankOrderedWordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens decider) := by
  let formatter : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun values => CarrierSourcePairFieldFormatter.output
        (UnaryFieldEncoderMachine.unaryFields values)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields
      CarrierSourcePairFieldFormatter.computableInPolyTime
      (fun _ => rfl) (fun _ => rfl)
  change TM2ComputableInPolyTime id id
    (fun symbols => CarrierSourcePairFieldFormatter.output
      (UnaryFieldEncoderMachine.unaryFields
        (directSourceCarrierNormalizedSourceKeyRankOrderedFields
          decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (A := List encoding.Γ) (B := List Nat)
    (C := List DelimitedBinaryWords.Token)
    (encodeA := id)
    (encodeB := UnaryFieldEncoderMachine.unaryFields)
    (encodeC := id)
    (f := directSourceCarrierNormalizedSourceKeyRankOrderedFields decider)
    (g := fun values => CarrierSourcePairFieldFormatter.output
      (UnaryFieldEncoderMachine.unaryFields values))
    (directSourceCarrierNormalizedSourceKeyRankOrderedFieldsComputableInPolyTime
      decider)
    formatter

end PeriodicCNFStripReduction
end LeanTrominoes

end
