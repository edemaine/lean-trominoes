/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedUnaryListClosure
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSpanData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for signed order-coordinate spans of carrier pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing
open CarrierRankDatumCompiledFields

noncomputable def orderExcessesComputableInPolyTime
    (field : Field) (keepFirst : Bool) :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (orderExcesses field keepFirst) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    (Field.rankOrderedValuesComputableInPolyTime field)
    UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompilerRaw := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let pairCompiler : TM2ComputableInPolyTime InputEncoding
      DelimitedBinaryWordPairs.finEncoding.encode (orderWordPairs field) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      pairCompilerRaw (fun _ => rfl)
  let excessCompilerRaw := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime keepFirst)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    excessCompilerRaw (fun _ => rfl)

/-- The row-major nonnegative signed carrier-coordinate differences are
polynomial-time computable from numeric route descriptors. -/
noncomputable def orderSpansComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields orderSpans :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding
    (orderExcesses .orderPositive false)
    (orderExcesses .orderNegative true)
    (fun descriptors => by simp)
    (orderExcessesComputableInPolyTime .orderPositive false)
    (orderExcessesComputableInPolyTime .orderNegative true)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
