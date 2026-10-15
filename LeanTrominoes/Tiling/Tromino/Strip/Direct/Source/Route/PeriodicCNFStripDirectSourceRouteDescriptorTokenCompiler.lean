/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.Source.PeriodicCNFSourceSplitRouteDescriptorTokenCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Route.PeriodicCNFStripDirectSourceRouteDescriptorTokenCompilerBridge

/-! # Concrete direct source route-descriptor token compiler -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
