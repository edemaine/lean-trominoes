/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementBridge
import LeanTrominoes.PeriodicCNFStripHorizontalPeriodSize
import LeanTrominoes.PeriodicCNFStripDirectGridUnitEmitter
import LeanTrominoes.UnaryColumnSignedEncoding

/-! # Native compilation of the actual routed drawing period -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing UnaryColumn PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
set_option maxHeartbeats 2000000

/-- Routing adds exactly the threefold polarity refinement to the retained period. -/
theorem nativeRoutedPeriod_eq (source : PeriodicCNF Nat) :
    (horizontalRoutedPlacementComputed source).period =
      (3 * horizontalPlacementPeriodFactor) * sourceOrthocrossingGridSize source := by
  rw [horizontalRoutedPlacementComputed_eq_semantic]
  change 3 * (horizontalPlacement source).period = _
  rw [horizontalPlacement_period_eq]
  exact (Nat.mul_assoc _ _ _).symm

theorem nativeRoutedPeriod_positive (source : PeriodicCNF Nat) :
    0 < (horizontalRoutedPlacementComputed source).period := by
  rw [nativeRoutedPeriod_eq]
  exact Nat.mul_pos (by decide) (drawingGridSize_pos _)

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativePeriodStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable def nativeRoutedPeriodCompiler :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => [(horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).period]) := by
  let base : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun s => [(directGridUnitsOfSymbols decider s).length]) :=
    TM2CompositionMachine.computableInPolyTime
    (directGridUnitsOfSymbolsComputableInPolyTime decider)
    UnaryFieldUnitLengthBroadcast.singletonComputableInPolyTime
  let result := TM2CompositionMachine.computableInPolyTime base
    (UnaryFieldConstantScale.computableInPolyTime (3 * horizontalPlacementPeriodFactor))
  simpa only [UnaryFieldConstantScale.values, List.map_cons, List.map_nil,
    directGridUnitsOfSymbols_length, nativeRoutedPeriod_eq, Nat.mul_comm] using result

end LeanTrominoes.PeriodicCNFStripReduction
end
