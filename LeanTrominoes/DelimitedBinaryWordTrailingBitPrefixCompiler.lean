/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrailingBitPrefixData
import LeanTrominoes.FiniteReverseBlockTransducer
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for moving trailing word bits behind a fixed prefix -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix

open Computability Turing

@[simp] theorem reverse_flatMap_singleton
    (source : List DelimitedBinaryWords.Token) :
    (source.flatMap fun token => [token]).reverse = source.reverse := by
  induction source with
  | nil => rfl
  | cons token source induction =>
      simp [List.reverse_cons]

noncomputable def reverseComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (List.reverse : List DelimitedBinaryWords.Token →
        List DelimitedBinaryWords.Token) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (FiniteReverseBlockTransducer.computableInPolyTime
      (fun token : DelimitedBinaryWords.Token => [token]))
    reverse_flatMap_singleton

noncomputable def reversePassComputableInPolyTime :
    TM2ComputableInPolyTime id id reversePass :=
  FiniteStateTransducer.computableInPolyTime
    (.between : Control) reverseTransition finish

/-- Two linear reversals around one linear finite-state pass compute the
prefix transformation in polynomial time. -/
noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens := by
  let first := TM2CompositionMachine.computableInPolyTime
    reverseComputableInPolyTime reversePassComputableInPolyTime
  let second := TM2CompositionMachine.computableInPolyTime
    first reverseComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => (reversePass input.reverse).reverse)
  exact second

end LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix

end
