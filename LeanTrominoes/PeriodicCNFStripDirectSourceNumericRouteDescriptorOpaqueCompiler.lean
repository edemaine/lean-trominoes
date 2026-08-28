/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler

/-! # Opaque direct numeric route-descriptor compiler boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directNumericDescriptorOpaqueCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
