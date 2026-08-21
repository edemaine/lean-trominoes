/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorTokenData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorTokensSemantics

/-! # Exact semantics of direct-source route-descriptor tokens -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorTokenSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceRouteDescriptorTokenSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Parsing every emitted eleven-field block recovers the exact numeric
descriptor list of the direct source formula. -/
@[simp] theorem directSourceRouteDescriptorFieldBlocks_decode
    (symbols : List encoding.Γ) :
    (routeDescriptorFieldBlocks
      (numericRouteDescriptors
        (directSourceFormula decider symbols))).map
        RouteDescriptor.ofUnaryFields? =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).map some := by
  simp

/-- The counted record marker total is exactly the source incidence count. -/
@[simp] theorem directSourceRouteDescriptorTokens_selectedCount
    (symbols : List encoding.Γ) :
    UnaryPolynomialPaddingMachine.selectedCount
        PeriodicCNF.UnaryProgramTokens.isClauseMarker
        (directSourceRouteDescriptorTokens decider symbols) =
      (numericRouteDescriptors
        (directSourceFormula decider symbols)).length := by
  unfold directSourceRouteDescriptorTokens
  simp

end LeanTrominoes.PeriodicCNFStripReduction
