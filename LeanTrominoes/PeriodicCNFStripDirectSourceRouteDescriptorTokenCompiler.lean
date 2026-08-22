/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceSplitRouteDescriptorTokenCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceRouteDescriptorTokenCompilerBridge

/-! # Concrete direct source route-descriptor token compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceRouteDescriptorCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The guarded source-formula compiler followed by the complete
occurrence-split emitter computes all direct route descriptors in polynomial
time. -/
noncomputable def directSourceRouteDescriptorTokenCompiler :
    DirectSourceRouteDescriptorTokenCompiler decider :=
  directSourceRouteDescriptorTokenCompilerOfSourceSplit decider
    PeriodicCNF.SourceSplitRouteDescriptorTokens.compiler

end PeriodicCNFStripReduction
end LeanTrominoes

end
