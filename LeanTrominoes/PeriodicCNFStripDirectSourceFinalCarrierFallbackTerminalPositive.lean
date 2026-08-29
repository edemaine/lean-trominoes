/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackTerminalDataPresentation
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryData

/-! # Positivity of direct-source carrier fallback terminal lengths -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackTerminalPositiveStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackTerminalPositiveVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierFallbackTerminalData_lengthPositive
    (symbols : List encoding.Γ) :
    ∀ terminal ∈
        directSourceFinalCarrierFallbackTerminalData decider symbols,
      0 < terminal.2 := by
  intro terminal terminalMember
  unfold directSourceFinalCarrierFallbackTerminalData at terminalMember
  rcases List.mem_flatMap.mp terminalMember with
    ⟨block, blockMember, terminalMember⟩
  have largeNat :=
    directSourceFinalCarrierFallbackPrefixBlocks_spanLarge
      decider symbols block blockMember
  have largeInt : (6 : Int) < block.2 := by
    exact_mod_cast largeNat
  exact FallbackSuffixQueries.carrierLensRouteTerminalDataBlock_lengthPositive
    block.1 block.2 largeInt terminal terminalMember

end LeanTrominoes.PeriodicCNFStripReduction

end
