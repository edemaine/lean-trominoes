/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRecordAppenderCompiler

/-! # Uniform direct sparse record-appender packaging -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Uniform split contract for the two remaining geometry passes. -/
def DirectSparseSplitRecordAppenders : Prop :=
  ∀ {Input : Type}
      (encoding : _root_.Computability.FinEncoding Input)
      (language : Input → Prop)
      (decider : Complexity.DeciderInPolySpace encoding language),
    Nonempty (DirectSparseVertexRecordAppender decider) ∧
      Nonempty (DirectSparseRouteRecordAppender decider)

/-- Split retained-input appenders discharge the existing complete record
emitter contract. -/
theorem directSparseAssignmentRecordEmitters_of_splitAppenders
    (appenders : DirectSparseSplitRecordAppenders) :
    DirectSparseAssignmentRecordEmitters := by
  intro Input encoding language decider
  obtain ⟨⟨vertices⟩, ⟨routes⟩⟩ :=
    appenders encoding language decider
  exact ⟨directSparseRecordEmitterOfAppenders decider vertices routes⟩

end PeriodicCNFStripReduction
end LeanTrominoes
