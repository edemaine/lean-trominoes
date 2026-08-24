/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsTime
import LeanTrominoes.DelimitedBinaryWordEqualitySquareData
import LeanTrominoes.DelimitedBinaryWordPairEqualityTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time square equality rows of binary-word compilers -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordEqualitySquare

open Computability Turing

/-- Any polynomial-time delimited-word emitter can be followed by the ordered
pair product and word comparator to produce its flat equality square. -/
noncomputable def equalityBitsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (wordInput : Input → DelimitedBinaryWords.Input)
    (wordCompiler :
      @TM2ComputableInPolyTime
        Input DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeInput DelimitedBinaryWords.finEncoding.encode wordInput) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool
      encodeInput id (fun input => equalityBits (wordInput input)) := by
  let paired := TM2CompositionMachine.computableInPolyTime
    wordCompiler
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let compared := TM2CompositionMachine.computableInPolyTime paired
    DelimitedBinaryWordPairEqualityMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compared
    (fun _input => rfl)

/-- Reinterpret the flat equality output at its promised-square type without
changing the physical Boolean tape. -/
noncomputable def squareInputComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (wordInput : Input → DelimitedBinaryWords.Input)
    (wordCompiler :
      @TM2ComputableInPolyTime
        Input DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeInput DelimitedBinaryWords.finEncoding.encode wordInput) :
    @TM2ComputableInPolyTime
      Input BoolSquareRows.Input InputSymbol Bool
      encodeInput BoolSquareRows.finEncoding.encode
      (fun input => squareInput (wordInput input)) := by
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (equalityBitsComputableInPolyTime encodeInput wordInput wordCompiler)
    (fun _input => rfl)

/-- Ordered equality rows of any polynomial-time delimited-word emitter are
themselves computable in polynomial time. -/
noncomputable def rowsComputableInPolyTime
    {Input InputSymbol : Type}
    (encodeInput : Input → List InputSymbol)
    (wordInput : Input → DelimitedBinaryWords.Input)
    (wordCompiler :
      @TM2ComputableInPolyTime
        Input DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeInput DelimitedBinaryWords.finEncoding.encode wordInput) :
    @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input InputSymbol
      DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => rows (wordInput input)) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (squareInputComputableInPolyTime encodeInput wordInput wordCompiler)
    BoolSquareRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _input => rfl)

end LeanTrominoes.DelimitedBinaryWordEqualitySquare

end
