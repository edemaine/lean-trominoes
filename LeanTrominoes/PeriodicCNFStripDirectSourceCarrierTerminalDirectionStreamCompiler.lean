/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceNumericRouteDescriptorCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalColumnData
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanTerminalDirectionCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanStreamCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Physical direct retained-carrier terminal-direction stream -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directSourceCarrierTerminalDirectionStreamVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Physical composition through numeric descriptors and packed spans. -/
opaque
    directSourceCarrierTerminalDirectionStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierTerminalDirectionStream decider) := by
  change TM2ComputableInPolyTime id id
    (fun symbols : List encoding.Γ =>
      CarrierPackedSpanTerminalColumns.directionRankStream
        (CarrierRankOrderedPairs.packedSpanStream
          (numericRouteDescriptors
            (directSourceFormula decider symbols))))
  exact TM2CompositionMachine.computableInPolyTime
    (TM2CompositionMachine.computableInPolyTime
      (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
      CarrierRankOrderedPairs.packedSpanStreamComputableInPolyTime)
    CarrierPackedSpanTerminalColumns.directionRankStreamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
