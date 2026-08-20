/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTablePhaseData

/-! # Canonical semantics of the four affine table phases -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open GadgetSparseAffineIndexedEmitter

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseAffineTablePhaseSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The four phase specifications jointly identify their output with the
canonical compact vertex-request stream. -/
theorem DirectSparseAffineTablePhaseFamilies.emitted_eq_vertexRequests
    (phases : DirectSparseAffineTablePhaseFamilies decider)
    (symbols : List encoding.Γ) :
    DirectSparseAffineTablePhaseFamilies.output decider phases symbols =
      directSparseComputedAffineVertexRequestsOfSymbols decider symbols := by
  rw [DirectSparseAffineTablePhaseFamilies.emitted_eq_table decider phases,
    ← directSparseComputedAffineVertexRequestsOfSymbols_eq_table]

/-- Opaque machine-facing name for the canonical compact vertex-request
function.  Its subtype certificate retains exact pointwise semantics while
preventing machine records from unfolding the full geometry construction. -/
opaque directSparseAffineVertexRequestOutputSpec :
    { output : List encoding.Γ →
        List GadgetSparseAffineVertexTokens.Token //
      ∀ symbols,
        output symbols =
          directSparseComputedAffineVertexRequestsOfSymbols
            decider symbols } :=
  ⟨directSparseComputedAffineVertexRequestsOfSymbols decider,
    fun _ => rfl⟩

def directSparseAffineVertexRequestOutput
    (symbols : List encoding.Γ) :
    List GadgetSparseAffineVertexTokens.Token :=
  (directSparseAffineVertexRequestOutputSpec decider).1 symbols

theorem directSparseAffineVertexRequestOutput_eq
    (symbols : List encoding.Γ) :
    directSparseAffineVertexRequestOutput decider symbols =
      directSparseComputedAffineVertexRequestsOfSymbols
        decider symbols :=
  (directSparseAffineVertexRequestOutputSpec decider).2 symbols

/-- The phase pipeline equals the opaque machine-facing output without
unfolding the canonical geometry function. -/
theorem DirectSparseAffineTablePhaseFamilies.emitted_eq_output
    (phases : DirectSparseAffineTablePhaseFamilies decider)
    (symbols : List encoding.Γ) :
    DirectSparseAffineTablePhaseFamilies.output decider phases symbols =
      directSparseAffineVertexRequestOutput decider symbols :=
  (DirectSparseAffineTablePhaseFamilies.emitted_eq_vertexRequests
      decider phases symbols).trans
    (directSparseAffineVertexRequestOutput_eq decider symbols).symm

end PeriodicCNFStripReduction
end LeanTrominoes
