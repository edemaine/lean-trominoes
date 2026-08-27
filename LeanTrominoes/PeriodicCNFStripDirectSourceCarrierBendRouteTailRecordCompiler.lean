/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendRouteTailRecordCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierRouteTailRecordCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierBaseBendRouteTailRecordStreamCompiler

/-! # Direct retained carrier-and-bend Figure 9 record streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierBendTailRecordStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directSourceCarrierBendTailRecordVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

def directSourceCarrierBendRouteTailRecordTokens
    (symbols : List encoding.Γ) :
    List HorizontalRoutedRouteTailRecord.Token :=
  CarrierBaseBendRouteTailRecords.stream
    (numericRouteDescriptors (directSourceFormula decider symbols))

theorem directSourceCarrierBendRouteTailRecordTokens_eq
    (symbols : List encoding.Γ) :
    directSourceCarrierBendRouteTailRecordTokens decider symbols =
      directSourceCarrierRouteTailRecordTokens decider symbols ++
        directSourceBaseBendRouteTailRecordTokens decider symbols := by
  rfl

noncomputable def
    directSourceCarrierBendRouteTailRecordTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceCarrierBendRouteTailRecordTokens decider) := by
  change TM2ComputableInPolyTime id id (fun symbols =>
    CarrierBaseBendRouteTailRecords.stream
      (numericRouteDescriptors (directSourceFormula decider symbols)))
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceNumericRouteDescriptorsComputableInPolyTime decider)
    CarrierBaseBendRouteTailRecords.streamComputableInPolyTime

end PeriodicCNFStripReduction
end LeanTrominoes

end
