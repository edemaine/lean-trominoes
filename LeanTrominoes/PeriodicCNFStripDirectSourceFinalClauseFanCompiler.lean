/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Actual final-clause fan enumeration -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

noncomputable local instance : Inhabited ClauseRibbonFanData :=
  ⟨⟨false, fun _ => .north⟩⟩

/-- Select one common finite fan at the top frame that starts each actual
final clause.  Left and right occurrence frames contribute no new clause. -/
def finalClauseFanFrameBlock
    (frame : HorizontalRoutedRouteHeaderClauseFrame.Data) :
    List ClauseRibbonFanData :=
  HorizontalRoutedRouteHeaderClauseFrame.fanFrameBlock frame

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One fan per actual final polarity-normalized Figure 9 clause, in clause
presentation order.  This is deliberately finer than the parent-descriptor
stream: one descriptor can generate many final clauses. -/
def directSourceFinalClauseFans
    (symbols : List encoding.Γ) : List ClauseRibbonFanData :=
  HorizontalRoutedRouteHeaderClauseFrame.outputClauseFans
    (directSourceFinalClauseDescriptors decider symbols)

/-- The canonical list is definitionally the fan projection of the retained
actual-clause blocks. -/
theorem directSourceFinalClauseFans_eq_blockFans
    (symbols : List encoding.Γ) :
    directSourceFinalClauseFans decider symbols =
      (HorizontalRoutedRouteHeaderClauseFrame.outputBlocks
        (directSourceFinalClauseDescriptors decider symbols)).map
          HorizontalRoutedRouteHeaderClauseFrame.blockFan := by
  rfl

/-- Expose the descriptor-level normal form without unfolding the direct
compiler in downstream semantic proofs. -/
theorem directSourceFinalClauseFans_eq_output
    (symbols : List encoding.Γ) :
    directSourceFinalClauseFans decider symbols =
      (HorizontalRoutedRouteHeaderClauseFrame.output
        (directSourceFinalClauseDescriptors decider symbols)).flatMap
          finalClauseFanFrameBlock := by
  exact
    (HorizontalRoutedRouteHeaderClauseFrame.output_flatMap_fanFrameBlock_eq_outputClauseFans
      _).symm

/-- The actual final-clause fan stream is polynomial-time computable. -/
noncomputable def directSourceFinalClauseFansComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseFans decider) := by
  let selected := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFramesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      finalClauseFanFrameBlock)
  apply Turing.TM2ComputableInPolyTime.of_eq selected
  intro symbols
  exact
    HorizontalRoutedRouteHeaderClauseFrame.output_flatMap_fanFrameBlock_eq_outputClauseFans
      (directSourceFinalClauseDescriptors decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
