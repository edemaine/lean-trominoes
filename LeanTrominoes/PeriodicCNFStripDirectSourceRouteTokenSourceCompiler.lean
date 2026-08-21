/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceHardness
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteTokenSourceData

/-! # Polynomial-time promised direct route sources -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteTokenSourceCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Reinterpret the existing flat-formula compiler at the promised-source
codomain; the physical word is unchanged. -/
noncomputable def directSourceRouteTokenSourceComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      PeriodicCNF.SourceSplitRouteDescriptorTokens.Source
      encoding.Γ PeriodicCNFFlatEncoding.Symbol
      id PeriodicCNF.SourceSplitRouteDescriptorTokens.finEncoding.encode
      (directSourceRouteTokenSource decider) := by
  let formulaCompiler :=
    PeriodicCNF.PolySpaceHardness.directSourceFormulaComputableInPolyTime
      decider
  refine
    { tm := formulaCompiler.tm
      inputAlphabet := formulaCompiler.inputAlphabet
      outputAlphabet := formulaCompiler.outputAlphabet
      time := formulaCompiler.time
      outputsFun := ?_ }
  intro symbols
  rw [PeriodicCNF.SourceSplitRouteDescriptorTokens.finEncoding_encode,
    directSourceRouteTokenSource_formula]
  exact formulaCompiler.outputsFun symbols

end LeanTrominoes.PeriodicCNFStripReduction
