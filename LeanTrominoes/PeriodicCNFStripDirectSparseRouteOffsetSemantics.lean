/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteOffsetData

/-! # Opaque machine-facing semantics for exact-offset route records -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteOffsetSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Opaque machine target carrying both its simple offset definition and its
exact canonical route-record semantics. -/
opaque directSparseRouteOffsetOutputSpec :
    { output : List encoding.Γ →
        List GadgetSparseAssignmentTokens.Token //
      (∀ symbols,
        output symbols =
          directSparseComputedRouteOffsetRecordsOfSymbols decider symbols) ∧
      ∀ symbols,
        output symbols =
          directSparseComputedRouteRecordsOfSymbols decider symbols } :=
  ⟨directSparseComputedRouteOffsetRecordsOfSymbols decider,
    fun _ => rfl,
    fun symbols =>
      (directSparseComputedRouteOffsetRecordsOfSymbols_eq
        decider symbols).trans
        (directSparseComputedRouteRecordsOfSymbols_eq_tripleRecords
          decider symbols).symm⟩

def directSparseRouteOffsetOutput (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  (directSparseRouteOffsetOutputSpec decider).1 symbols

theorem directSparseRouteOffsetOutput_eq_offsets
    (symbols : List encoding.Γ) :
    directSparseRouteOffsetOutput decider symbols =
      directSparseComputedRouteOffsetRecordsOfSymbols decider symbols :=
  (directSparseRouteOffsetOutputSpec decider).2.1 symbols

theorem directSparseRouteOffsetOutput_eq_routeRecords
    (symbols : List encoding.Γ) :
    directSparseRouteOffsetOutput decider symbols =
      directSparseComputedRouteRecordsOfSymbols decider symbols :=
  (directSparseRouteOffsetOutputSpec decider).2.2 symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
