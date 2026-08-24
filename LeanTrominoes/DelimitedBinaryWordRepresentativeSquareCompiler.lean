/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareData
import LeanTrominoes.LastRepresentativeEqualityRowsTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Polynomial-time last representatives of binary-word squares -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordRepresentativeSquare

open Computability Turing

/-- Last-occurrence representative equality rows of any polynomial-time
delimited-word emitter are computable in polynomial time. -/
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
    (DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
      encodeInput wordInput wordCompiler)
    LastRepresentativeEqualityRowsMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _input => rfl)

end LeanTrominoes.DelimitedBinaryWordRepresentativeSquare

end
