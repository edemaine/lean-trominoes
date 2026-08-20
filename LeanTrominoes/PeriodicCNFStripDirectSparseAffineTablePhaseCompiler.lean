/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTablePhaseGeneratedCompiler
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTablePhaseSemantics

/-! # Complete compact vertex compiler from four indexed table phases -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open GadgetSparseAffineIndexedEmitter

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTablePhaseCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Four verified indexed families over the uniform unary program stream
compile a certified opaque name for the exact canonical compact
vertex-request word in polynomial time. -/
noncomputable def directSparseAffineVertexRequestsComputableInPolyTimeOfTablePhases
    (phases : DirectSparseAffineTablePhaseFamilies decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List GadgetSparseAffineVertexTokens.Token)
      encoding.Γ GadgetSparseAffineVertexTokens.Token id id
      (directSparseAffineVertexRequestOutput decider) := by
  exact @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (List encoding.Γ)
    (List GadgetSparseAffineVertexTokens.Token)
    (List GadgetSparseAffineVertexTokens.Token)
    encoding.Γ GadgetSparseAffineVertexTokens.Token
    id id id
    (DirectSparseAffineTablePhaseFamilies.output decider phases)
    (directSparseAffineVertexRequestOutput decider)
    (@directSparseAffineTablePhaseOutputComputableInPolyTime
      Input encoding language decider phases)
    (@DirectSparseAffineTablePhaseFamilies.emitted_eq_output
      Input encoding language decider phases)

end PeriodicCNFStripReduction
end LeanTrominoes
