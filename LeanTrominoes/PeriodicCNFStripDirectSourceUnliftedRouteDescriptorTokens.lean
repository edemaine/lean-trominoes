/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceLiftedRouteDescriptorTokens
import LeanTrominoes.PeriodicThreeCNFLiftRenaming
import LeanTrominoes.PeriodicThreeSATThreeFormulaRenaming

/-! # Direct route tokens over the original flat CNF -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceUnliftedRouteTokensStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The exact direct-source route records can be emitted from the original
flat natural-variable CNF, with neither 3CNF auxiliaries nor atom lifts. -/
theorem directSourceRouteDescriptorTokens_eq_sourceSplitDescriptors
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorTokens decider symbols =
      routeDescriptorTokens
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PolySpaceCompiler.formulaOfSymbols decider symbols)) := by
  rw [directSourceRouteDescriptorTokens_eq_liftedSource]
  rw [PeriodicThreeCNF.liftFormula_eq_rename]
  rw [PeriodicThreeSATThree.splitRouteDescriptors_rename_of_injective
    (Sum.inl : Nat → ThreeCNFVariable Nat)
    Sum.inl_injective]

end LeanTrominoes.PeriodicCNFStripReduction
