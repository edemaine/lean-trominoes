/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedIncidenceHeaderBlocks
import LeanTrominoes.PeriodicCNFStripNativeClauseArities
import LeanTrominoes.PeriodicCNFStripNativeOffsetColumns

/-! # Native clause headers aligned with the literal field blocks -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PositionedIncidenceRows
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeHeaderStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance nativeHeaderVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

/-- Emit a clause-length field at its first literal and an empty prefix at
its other literals, with one explicit block boundary per occurrence. -/
noncomputable def nativeClauseHeaderBlocksCompiler :
    BlocksCompiler (nativeIncidenceRows decider) (fun _ row => header row) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime (fun token =>
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((HorizontalRoutedRouteHeaderClauseFrame.tokenBlocks token).flatMap
          (fun block => headerBlocks block.length))))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  change _ = FiniteAlphabetDelimitedBlockJoin.blocks
    ((rows (horizontalRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))).map header)
  rw [headers_eq_lengths, ← nativeClauseArities_eq decider s]
  simp only [FiniteAlphabetDelimitedBlockJoin.blocks,
    HorizontalRoutedRouteHeaderClauseFrame.outputBlocks, List.flatMap_map, List.flatMap_assoc]

end LeanTrominoes.PeriodicCNFStripReduction
end
