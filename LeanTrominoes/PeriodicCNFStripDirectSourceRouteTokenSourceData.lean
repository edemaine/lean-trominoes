/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaFacts

/-! # Promised route-emitter sources from direct PSPACE inputs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteTokenSourceDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Package the generated flat source formula with the exact syntactic and
geometric promises required by the generic route emitter. -/
def directSourceRouteTokenSource (symbols : List encoding.Γ) :
    PeriodicCNF.SourceSplitRouteDescriptorTokens.Source where
  formula := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols
  oneDimensional :=
    (formulaOfSymbols_sourceAdmissible decider symbols).1
  isLocal :=
    (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  widthAtMostThree :=
    formulaOfSymbols_widthAtMostThree decider symbols

@[simp] theorem directSourceRouteTokenSource_formula
    (symbols : List encoding.Γ) :
    (directSourceRouteTokenSource decider symbols).formula =
      PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols := by
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
