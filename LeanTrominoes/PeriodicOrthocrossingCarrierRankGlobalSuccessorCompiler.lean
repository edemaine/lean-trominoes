/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSuccessorData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for global carrier-rank successor bits -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobalSuccessor

open Computability Turing

/-- The complete row-major global-rank successor square is polynomial-time
computable from route descriptors. -/
opaque successorBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id successorBits := by
  unfold successorBits
  let wordCompiler : TM2ComputableInPolyTime InputEncoding
      DelimitedBinaryWords.finEncoding.encode
      (fun descriptors => UnaryFieldBinaryWords.words
        (CarrierRankGlobal.ranks descriptors)) :=
    TM2CompositionMachine.computableInPolyTime
    CarrierRankGlobal.ranksComputableInPolyTime
    UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompilerRaw := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let pairCompiler : TM2ComputableInPolyTime InputEncoding
      DelimitedBinaryWordPairs.finEncoding.encode rankWordPairs :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      pairCompilerRaw (fun _ => rfl)
  let excessCompilerRaw := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime false)
  let excessCompiler : TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields rankExcesses :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      excessCompilerRaw (fun _ => rfl)
  exact TM2CompositionMachine.computableInPolyTime
    excessCompiler UnaryExactOneBooleans.bitsComputableInPolyTime

/-- Conjoining the successor square with the existing aggregate-key equality
square computes exactly the same-carrier adjacent-pair predicate. -/
opaque bitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id bits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    CarrierRankKeyEquality.bits successorBits
    (fun descriptors => by simp)
    CarrierRankKeyEquality.bitsComputableInPolyTime
    successorBitsComputableInPolyTime

end CarrierRankGlobalSuccessor
end LeanTrominoes.PeriodicOrthocrossing

end
