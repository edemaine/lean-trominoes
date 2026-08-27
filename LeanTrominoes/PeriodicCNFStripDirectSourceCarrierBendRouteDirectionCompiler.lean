/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendRouteDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBaseBendRouteDirectionStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Direct retained carrier-and-bend route-direction streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierBendDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceCarrierBendDirectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Complete retained carrier blocks followed by complete untranslated bend
blocks, compiled through their shared numeric descriptor representation. -/
def directSourceCarrierBendRouteDirectionBlocks
    (symbols : List encoding.Γ) :
    List CarrierSpanRouteDirections.Token :=
  CarrierBaseBendRouteDirections.stream
    (numericRouteDescriptors (directSourceFormula decider symbols))

/-- The combined stream is exactly the concatenation of the independently
specified direct carrier and bend streams. -/
theorem directSourceCarrierBendRouteDirectionBlocks_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierBendRouteDirectionBlocks decider symbols =
      directSourceCarrierRouteDirectionBlocks decider symbols ++
        directSourceBaseBendRouteDirectionBlocks decider symbols := by
  rfl

/-- Direct PSPACE source symbols compile to the complete retained
carrier-and-bend direction stream in polynomial time. -/
noncomputable def
    directSourceCarrierBendRouteDirectionBlocksComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierBendRouteDirectionBlocks decider) := by
  change TM2ComputableInPolyTime id id
    (fun symbols =>
      CarrierBaseBendRouteDirections.stream
        (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierBaseBendRouteDirections.streamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
