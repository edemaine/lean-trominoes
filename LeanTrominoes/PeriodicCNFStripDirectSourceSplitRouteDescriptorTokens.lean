/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorTokenData
import LeanTrominoes.PeriodicCNFStripDirectSourceSplitRouteDescriptors

/-! # Explicit route-descriptor tokens for direct strip sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The exact direct-source unary token stream encodes the explicit
copied-plus-cycle route records. -/
theorem directSourceRouteDescriptorTokens_eq_splitRouteDescriptors
    (symbols : List encoding.Γ) :
    directSourceRouteDescriptorTokens decider symbols =
      routeDescriptorTokens
        (PeriodicThreeSATThree.splitRouteDescriptors
          (PeriodicThreeCNF.formula
            (ProgramSource.formulaOfSymbols decider symbols))) := by
  exact congrArg routeDescriptorTokens
    ((directSource_numericRouteDescriptors_eq_splitRouteDescriptors decider symbols).trans
      (directSource_splitRouteDescriptors_eq_structural decider symbols))

end LeanTrominoes.PeriodicCNFStripReduction
