/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseContractedRouteRasterSourceData
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteRasterRequestCompiler
import LeanTrominoes.PeriodicThreeDMContractedRouteRasterSourceCompiler

/-! # Direct compiler boundary for framed contracted raster requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseContractedRouteSourceCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The remaining source-side route obligation after factoring out retained/
through assembly and raster-request framing. -/
abbrev DirectSparseContractedRouteSourceTokenCompiler :=
  TM2ComputableInPolyTime id id fun symbols : List encoding.Γ =>
    directSparseContractedRouteSourceTokens decider symbols

/-- A polynomial-time emitter for the framed source tokens composes with the
fixed bridge to emit the exact canonical compact raster-request stream. -/
noncomputable def directSparseRouteRasterRequestTokenCompilerOfContractedSource
    (source : DirectSparseContractedRouteSourceTokenCompiler decider) :
    DirectSparseRouteRasterRequestTokenCompiler decider := by
  let compiled := TM2CompositionMachine.computableInPolyTime source
    PeriodicThreeDM.ContractedRouteRasterSource.outputComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun symbols => by
      simpa only [id_eq] using
        directSparseContractedRouteSourceTokens_output decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
