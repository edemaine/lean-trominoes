/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairBlockMapSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Terminal.PeriodicOrthocrossingTerminalCarrierKeyAxisValueCompiler
import LeanTrominoes.Computation.TM2.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for padded terminal carrier-key axes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalCarrierKeyAxisStream

open Computability Turing

def emittedFields (tokens : List RouteDescriptorPairFieldTags.Token) :
    List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    RouteDescriptorPairAffine.terminalCarrierKeyAxisCompiledFields tokens

noncomputable def emittedFieldsComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedFields := by
  exact TM2EndDelimitedBlockMap.computableInPolyTime
    RouteDescriptorPairAffine.terminalCarrierKeyAxisCompiledFieldsComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalCarrierKeyAxisStream
end LeanTrominoes.PeriodicOrthocrossing

end
