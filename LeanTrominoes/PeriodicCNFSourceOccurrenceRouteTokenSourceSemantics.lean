/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceRouteTokenFormulaSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceTokenCompilerSemantics

/-! # Promised-source semantics of finite occurrence route tokens -/

namespace LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens

/-- The compiled finite stream is the exact clause/literal index and
current/next offset stream of the promised source formula. -/
theorem sourceTokens_eq_formulaTokens
    (source : SourceSplitRouteDescriptorTokens.Source) :
    sourceTokens source = formulaTokens source.formula := by
  unfold sourceTokens
  rw [SourceOccurrenceTokens.parsedSource_eq_formulaTokens]
  exact normalize_formulaTokens source.formula source.isForwardLocal

end LeanTrominoes.PeriodicCNF.SourceOccurrenceRouteTokens
