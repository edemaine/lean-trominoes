/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Actual final-clause fan enumeration -/

noncomputable section

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
  if frame.group = .top then [frame.clauseFan] else []

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- One fan per actual final polarity-normalized Figure 9 clause, in clause
presentation order.  This is deliberately finer than the parent-descriptor
stream: one descriptor can generate many final clauses. -/
def directSourceFinalClauseFans
    (symbols : List encoding.Γ) : List ClauseRibbonFanData :=
  (directSourceFinalClauseFrames decider symbols).flatMap
    finalClauseFanFrameBlock

/-- The actual final-clause fan stream is polynomial-time computable. -/
noncomputable def directSourceFinalClauseFansComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseFans decider) := by
  unfold directSourceFinalClauseFans
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFramesComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      finalClauseFanFrameBlock)

end LeanTrominoes.PeriodicCNFStripReduction

end
