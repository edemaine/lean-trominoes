/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastRepresentativeEqualityRowsTime
import LeanTrominoes.SupportedLastRepresentativeEqualityRows
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler boundary for support-guarded representative rows -/

noncomputable section

namespace LeanTrominoes.SupportedLastRepresentativeEqualityRows

open Computability Turing

/-- Any polynomial-time guarded-row emitter composes with the existing
last-representative selector to compute the supported representatives. -/
noncomputable def selectedRowsComputableInPolyTime
    {Input InputSymbol Value : Type} [DecidableEq Value]
    (encodeInput : Input → List InputSymbol)
    (base candidates : Input → List Value)
    (rowCompiler :
      @TM2ComputableInPolyTime
        Input DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token
        encodeInput DelimitedBinaryWords.finEncoding.encode
        (fun input => rows (base input) (candidates input))) :
    @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input
      InputSymbol DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => selectedRows (base input) (candidates input)) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    rowCompiler LastRepresentativeEqualityRowsMachine.computableInPolyTime
  exact composed

end LeanTrominoes.SupportedLastRepresentativeEqualityRows

end
