/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalRadialCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Physical direct retained-carrier terminal-radial stream -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierTerminalRadialStreamStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceCarrierTerminalRadialStreamVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical composition through numeric descriptors and packed spans. -/
opaque
    directSourceCarrierTerminalRadialStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierTerminalRadialStream decider) := by
  change TM2ComputableInPolyTime id id
    (fun symbols : List encoding.Γ =>
      CarrierPackedSpanTerminalColumns.radialLengthStream
        (CarrierRankOrderedPairs.packedSpanStream
          (numericRouteDescriptors
            (directSourceFormula decider symbols))))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
      CarrierRankOrderedPairs.packedSpanStreamComputableInPolyTime)
    CarrierPackedSpanTerminalColumns.radialLengthStreamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
