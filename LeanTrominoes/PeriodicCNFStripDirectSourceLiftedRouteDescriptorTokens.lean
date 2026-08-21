/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptorTokens
import LeanTrominoes.PeriodicThreeCNFWidthThreeIdentity

/-! # Direct route tokens over the compiled source presentation -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceLiftedRouteTokensStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Since the generated source already has width at most three, its route
records can be emitted directly from the original compiled clauses: the
intermediate 3CNF pass only injects each atom into `Sum.inl`. -/
theorem directSourceRouteDescriptorTokens_eq_liftedSource
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorTokens decider symbols =
      routeDescriptorTokens
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PeriodicThreeCNF.liftFormula
            (PolySpaceCompiler.formulaOfSymbols decider symbols))) := by
  rw [directSourceRouteDescriptorTokens_eq_splitRouteDescriptors]
  rw [PeriodicThreeCNF.formula_eq_liftFormula_of_widthAtMostThree
    _ (formulaOfSymbols_widthAtMostThree decider symbols)]

end LeanTrominoes.PeriodicCNFStripReduction
