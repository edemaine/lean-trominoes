/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler closure under Boolean filtering of binary-word pairs -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

open Computability Turing

/-- Boolean controls and delimited pair streams compiled from one input can
be paired positionally and filtered in polynomial time. -/
noncomputable def filteredPairsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (controls : Source → List Bool)
    (pairs : Source → DelimitedBinaryWordPairs.Input)
    (controlCompiler : TM2ComputableInPolyTime
      encodeSource id controls)
    (pairCompiler : TM2ComputableInPolyTime
      encodeSource DelimitedBinaryWordPairs.encode pairs) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWordPairs.encode
      (fun source =>
        ⟨selectedPairs (controls source) (pairs source).pairs⟩) := by
  let forked := TM2ForkMachine.computableInPolyTime
    controlCompiler pairCompiler
  let prepared : TM2ComputableInPolyTime encodeSource encodeInput
      (fun source : Source =>
        { controls := controls source
          pairs := (pairs source).pairs }) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      forked (fun _ => rfl)
  let filtered := TM2CompositionMachine.computableInPolyTime
    prepared
    DelimitedBinaryWordPairBooleanFilterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    filtered (fun _ => rfl)

end LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

end
