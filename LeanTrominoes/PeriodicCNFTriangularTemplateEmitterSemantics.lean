/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterCleanup

/-!
# Whole-machine semantics of the triangular emitter

All verified phases are composed from `initList` to a genuinely halted
configuration.  The accumulated frame prefix, final base, and unwind suffix
are identified with the semantic triangular recursion, yielding exact
`TM2OutputsInTime` behavior for arbitrary fixed recipes and token blocks.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

theorem repeatTokens_succ_right (tokens : List Token) (count : Nat) :
    repeatTokens tokens (count + 1) = repeatTokens tokens count ++ tokens := by
  induction count with
  | zero => simp [repeatTokens]
  | succ count induction =>
      change tokens ++ repeatTokens tokens (count + 1) =
        (tokens ++ repeatTokens tokens count) ++ tokens
      rw [induction]
      simp [List.append_assoc]

/-- The iterative machine order is exactly the recursive semantic contract. -/
theorem frameRangeTokens_append_final {Data : Type}
    (parameters : Parameters Data) (first position count : Nat) :
    frameRangeTokens parameters first position count ++
        parameters.finalBase ++
        repeatTokens parameters.finalCloser count =
      emittedAux parameters.outerFirst parameters.inner
        parameters.outerSecond parameters.innerBase parameters.innerCloser
        parameters.frameCloser parameters.finalBase parameters.finalCloser
        first position count := by
  induction count generalizing position with
  | zero => simp [frameRangeTokens, emittedAux, repeatTokens]
  | succ count induction =>
      calc
        frameRangeTokens parameters first position (count + 1) ++
              parameters.finalBase ++
              repeatTokens parameters.finalCloser (count + 1) =
            frameTokens parameters.outerFirst parameters.inner
                parameters.outerSecond parameters.innerBase
                parameters.innerCloser parameters.frameCloser first position
                count ++
              ((frameRangeTokens parameters first (position + 1) count ++
                  parameters.finalBase ++
                  repeatTokens parameters.finalCloser count) ++
                parameters.finalCloser) := by
          rw [frameRangeTokens, repeatTokens_succ_right]
          simp [List.append_assoc]
        _ = frameTokens parameters.outerFirst parameters.inner
                parameters.outerSecond parameters.innerBase
                parameters.innerCloser parameters.frameCloser first position
                count ++
              (emittedAux parameters.outerFirst parameters.inner
                  parameters.outerSecond parameters.innerBase
                  parameters.innerCloser parameters.frameCloser
                  parameters.finalBase parameters.finalCloser first
                  (position + 1) count ++ parameters.finalCloser) := by
          rw [induction]
        _ = emittedAux parameters.outerFirst parameters.inner
              parameters.outerSecond parameters.innerBase
              parameters.innerCloser parameters.frameCloser
              parameters.finalBase parameters.finalCloser first position
              (count + 1) := by
          rw [emittedAux]
          simp [List.append_assoc]

/-- Exact whole-machine runtime before later polynomial bounding. -/
def totalTime {Data : Type} (parameters : Parameters Data)
    (workspace : List (Workspace Data)) : Nat :=
  let first := selectedCount parameters.firstSelected workspace
  let count := selectedCount parameters.secondSelected workspace
  workspace.length + 1 +
    outerFrameRangeTime parameters first 0 count +
    (count + 2) +
    (first + 1) +
    (appendedOutput parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser workspace).length + 1

theorem initList_eq_scanCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    initList
        (machine Data parameters.firstSelected parameters.secondSelected
          parameters.outerFirst parameters.inner parameters.outerSecond
          parameters.innerBase parameters.innerCloser parameters.frameCloser
          parameters.finalBase parameters.finalCloser) workspace =
      parameters.scanCfg
        ⟨workspace, [], [], [], [], [], [], [], [], []⟩ := by
  unfold initList machine Parameters.scanCfg
    TriangularTemplateEmitterMachine.scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (parameters : Parameters Data) (output : List (Workspace Data)) :
    haltList
        (machine Data parameters.firstSelected parameters.secondSelected
          parameters.outerFirst parameters.inner parameters.outerSecond
          parameters.innerBase parameters.innerCloser parameters.frameCloser
          parameters.finalBase parameters.finalCloser) output =
      haltCfg (outerFirst := parameters.outerFirst) (inner := parameters.inner)
        (outerSecond := parameters.outerSecond) output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem haltDataCfg_empty_eq_haltCfg {Data : Type}
    (parameters : Parameters Data) (output : List (Workspace Data)) :
    parameters.haltDataCfg
        ⟨[], [], [], [], [], [], [], [], [], output⟩ =
      haltCfg (outerFirst := parameters.outerFirst) (inner := parameters.inner)
        (outerSecond := parameters.outerSecond) output :=
  rfl

/-- The finite triangular machine emits exactly its semantic contract. -/
def machine_outputsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (parameters : Parameters Data) (workspace : List (Workspace Data)) :
    TM2OutputsInTime
      (machine Data parameters.firstSelected parameters.secondSelected
        parameters.outerFirst parameters.inner parameters.outerSecond
        parameters.innerBase parameters.innerCloser parameters.frameCloser
        parameters.finalBase parameters.finalCloser)
      workspace
      (some (appendedOutput parameters.firstSelected parameters.secondSelected
        parameters.outerFirst parameters.inner parameters.outerSecond
        parameters.innerBase parameters.innerCloser parameters.frameCloser
        parameters.finalBase parameters.finalCloser workspace))
      (totalTime parameters workspace) := by
  let first := selectedCount parameters.firstSelected workspace
  let count := selectedCount parameters.secondSelected workspace
  let emitted := TriangularTemplateEmitter.emitted parameters.outerFirst
    parameters.inner parameters.outerSecond parameters.innerBase
    parameters.innerCloser parameters.frameCloser parameters.finalBase
    parameters.finalCloser first count
  let initial : TapeData Data :=
    ⟨workspace, [], [], [], [], [], [], [], [], []⟩
  let scanned : TapeData Data :=
    ⟨[], List.replicate first (), List.replicate count (), [], [], [], [], [],
      workspace.reverse, []⟩
  let framed : TapeData Data :=
    ⟨[], List.replicate first (), [], [], List.replicate count (), [], [], [],
      ((frameRangeTokens parameters first 0 count).map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse, []⟩
  let ended : TapeData Data :=
    ⟨[], List.replicate first (), [], [], [], [], [], [],
      ((parameters.finalBase ++
          repeatTokens parameters.finalCloser count).map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++
          ((frameRangeTokens parameters first 0 count).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse,
      []⟩
  let cleared : TapeData Data := { ended with first := [] }
  have scanRun := scan_evalsInTime parameters workspace initial rfl
  have framesRun := outerFrames_evalsInTime parameters first 0 count scanned
    rfl rfl rfl rfl rfl rfl rfl
  have firstTwo := EvalsToInTime.trans parameters.transition
    (workspace.length + 1)
    (outerFrameRangeTime parameters first 0 count)
    (parameters.scanCfg initial) (parameters.beginOuterCfg scanned)
    (some (parameters.beginOuterCfg framed))
    (by simpa [initial, scanned, first, count] using scanRun)
    (by simpa [scanned, framed] using framesRun)
  have finalRun := finishOuterRange_evalsInTime parameters count framed rfl rfl
  have firstThree := EvalsToInTime.trans parameters.transition
    (outerFrameRangeTime parameters first 0 count +
      (workspace.length + 1))
    (count + 2)
    (parameters.scanCfg initial) (parameters.beginOuterCfg framed)
    (some (parameters.clearFirstCfg ended)) firstTwo (by
      simpa [ended, framed, List.append_assoc] using finalRun)
  have clearRun := clearFirst_evalsInTime parameters
    (List.replicate first ()) ended rfl
  have firstFour := EvalsToInTime.trans parameters.transition
    (count + 2 +
      (outerFrameRangeTime parameters first 0 count +
        (workspace.length + 1)))
    (first + 1)
    (parameters.scanCfg initial) (parameters.clearFirstCfg ended)
    (some (parameters.reverseOutputCfg cleared)) firstThree (by
      simpa [cleared] using clearRun)
  have emittedEq :
      frameRangeTokens parameters first 0 count ++ parameters.finalBase ++
          repeatTokens parameters.finalCloser count = emitted := by
    simpa [emitted, TriangularTemplateEmitter.emitted] using
      frameRangeTokens_append_final parameters first 0 count
  have emissionReverseEq :
      ((parameters.finalBase ++
          repeatTokens parameters.finalCloser count).map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++
          ((frameRangeTokens parameters first 0 count).map fun token =>
            (Sum.inr token : Workspace Data)).reverse =
        (emitted.map fun token =>
          (Sum.inr token : Workspace Data)).reverse := by
    rw [← List.reverse_append, ← List.map_append]
    congr 2
    simpa [List.append_assoc] using emittedEq
  have endedEq : ended.outputReverse =
      (appendedOutput parameters.firstSelected parameters.secondSelected
        parameters.outerFirst parameters.inner parameters.outerSecond
        parameters.innerBase parameters.innerCloser parameters.frameCloser
        parameters.finalBase parameters.finalCloser workspace).reverse := by
    change
      ((parameters.finalBase ++
          repeatTokens parameters.finalCloser count).map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++
          ((frameRangeTokens parameters first 0 count).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse =
        (workspace ++ emitted.map fun token =>
          (Sum.inr token : Workspace Data)).reverse
    rw [List.reverse_append, emissionReverseEq]
  have reverseRun := reverseOutput_evalsInTime parameters
    (appendedOutput parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser workspace).reverse
    cleared (by simpa [cleared] using endedEq)
  have whole := EvalsToInTime.trans parameters.transition
    (first + 1 +
      (count + 2 +
        (outerFrameRangeTime parameters first 0 count +
          (workspace.length + 1))))
    ((appendedOutput parameters.firstSelected parameters.secondSelected
      parameters.outerFirst parameters.inner parameters.outerSecond
      parameters.innerBase parameters.innerCloser parameters.frameCloser
      parameters.finalBase parameters.finalCloser workspace).length + 1)
    (parameters.scanCfg initial) (parameters.reverseOutputCfg cleared)
    (some (haltCfg (outerFirst := parameters.outerFirst)
      (inner := parameters.inner) (outerSecond := parameters.outerSecond)
      (appendedOutput parameters.firstSelected parameters.secondSelected
        parameters.outerFirst parameters.inner parameters.outerSecond
        parameters.innerBase parameters.innerCloser parameters.frameCloser
        parameters.finalBase parameters.finalCloser workspace)))
    firstFour (by
      simpa [cleared, ended, framed, scanned, initial] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind parameters.transition)^[whole.steps]
        (some (initList
          (machine Data parameters.firstSelected parameters.secondSelected
            parameters.outerFirst parameters.inner parameters.outerSecond
            parameters.innerBase parameters.innerCloser parameters.frameCloser
            parameters.finalBase parameters.finalCloser) workspace)) =
        some (haltList
          (machine Data parameters.firstSelected parameters.secondSelected
            parameters.outerFirst parameters.inner parameters.outerSecond
            parameters.innerBase parameters.innerCloser parameters.frameCloser
            parameters.finalBase parameters.finalCloser)
          (appendedOutput parameters.firstSelected parameters.secondSelected
            parameters.outerFirst parameters.inner parameters.outerSecond
            parameters.innerBase parameters.innerCloser parameters.frameCloser
            parameters.finalBase parameters.finalCloser workspace))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime, first, count]
      omega)

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
