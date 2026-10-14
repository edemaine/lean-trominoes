/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler

/-! # Opaque direct numeric route-descriptor compiler boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directNumericDescriptorOpaqueCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Opaque spelling of the existing compiler prevents downstream composition
from normalizing its large proof term. -/
opaque directSourceNumericRouteDescriptorsOpaqueComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List RouteDescriptor)
      encoding.Γ DelimitedBinaryWords.Token id
      CarrierRankOrderedPairs.InputEncoding
      (fun symbols =>
        numericRouteDescriptors (directSourceFormula decider symbols)) :=
  directSourceNumericRouteDescriptorsComputableInPolyTime decider

end PeriodicCNFStripReduction
end LeanTrominoes

end
