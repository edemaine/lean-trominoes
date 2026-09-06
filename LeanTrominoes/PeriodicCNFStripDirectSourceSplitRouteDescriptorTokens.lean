/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorTokenData
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors

/-! # Explicit route-descriptor tokens for direct strip sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceSplitRouteDescriptorTokensStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceSplitRouteDescriptorTokensVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The exact direct-source unary token stream encodes the explicit
copied-plus-cycle route records. -/
theorem directSourceRouteDescriptorTokens_eq_splitRouteDescriptors
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorTokens decider symbols =
      routeDescriptorTokens
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PeriodicThreeCNF.formula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))) := by
  exact congrArg routeDescriptorTokens
    (directSource_numericRouteDescriptors_eq_splitRouteDescriptors decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction
