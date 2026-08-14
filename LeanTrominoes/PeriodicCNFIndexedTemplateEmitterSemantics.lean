/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIndexedTemplateEmitterCleanup

/-!
# Whole-machine semantics for indexed template emission

Compose the complete input scan, counter cleanup, token reversal, and retained
input reversal from `initList` to a genuinely halted `haltList` output.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open IndexedTemplateEmitter

def totalTime {Data : Type} (family : Family Data) (data : List Data) : Nat :=
  scanTime family 0 data +
    (IndexedTemplateEmitter.selectedCount family data + 1) +
    (IndexedTemplateEmitter.emitted family data).length + 1 +
    data.length + 1

@[simp]
theorem initList_eq_scanCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (family : Family Data) (data : List Data) :
    initList (machine Data family) data =
      scanCfg
        ⟨data, [], [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem haltList_eq_haltCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (family : Family Data) (output : List (Data ⊕ UnaryProgramTokens.Token)) :
    haltList (machine Data family) output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem haltDataCfg_empty_eq_haltCfg {Data : Type} {family : Family Data}
    (output : List (Data ⊕ UnaryProgramTokens.Token)) :
    haltDataCfg (family := family) ⟨[], [], [], [], [], output⟩ =
      haltCfg output :=
  rfl

def machine_evalsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (family : Family Data) (input : List Data) :
    EvalsToInTime (TM2.step (program family))
      (scanCfg ⟨input, [], [], [], [], []⟩)
      (some (haltCfg (appendedOutput family input)))
      (totalTime family input) := by
  let initial : TapeData Data := ⟨input, [], [], [], [], []⟩
  have scanned := scan_evalsInTime family 0 input initial rfl rfl rfl
  let scannedData : TapeData Data :=
    { initial with
      input := []
      inputReverse := input.reverse
      processed := List.replicate
        (IndexedTemplateEmitter.selectedCount family input) ()
      scratch := []
      tokenReverse :=
        (IndexedTemplateEmitter.emitted family input).reverse }
  have scanned' : EvalsToInTime (TM2.step (program family))
      (scanCfg initial) (some (clearProcessedCfg scannedData))
      (scanTime family 0 input) := by
    simpa [scannedData, initial, IndexedTemplateEmitter.emitted] using scanned
  have cleared := clearProcessed_evalsInTime family
    (List.replicate (IndexedTemplateEmitter.selectedCount family input) ())
    scannedData rfl
  let clearedData : TapeData Data :=
    { scannedData with processed := [] }
  have firstTwo := EvalsToInTime.trans
    (TM2.step (program family))
    (scanTime family 0 input)
    (IndexedTemplateEmitter.selectedCount family input + 1)
    (scanCfg initial) (clearProcessedCfg scannedData)
    (some (reverseTokensCfg clearedData)) scanned' (by
      simpa [clearedData] using cleared)
  have tokens := reverseTokens_evalsInTime family
    (IndexedTemplateEmitter.emitted family input).reverse clearedData rfl
  let tokenData : TapeData Data :=
    { clearedData with
      tokenReverse := []
      output :=
        (IndexedTemplateEmitter.emitted family input).map Sum.inr }
  have firstThree := EvalsToInTime.trans
    (TM2.step (program family))
    (IndexedTemplateEmitter.selectedCount family input + 1 +
      scanTime family 0 input)
    ((IndexedTemplateEmitter.emitted family input).length + 1)
    (scanCfg initial) (reverseTokensCfg clearedData)
    (some (reverseInputCfg tokenData)) (by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using firstTwo) (by
      simpa [tokenData, clearedData, scannedData, initial] using tokens)
  have retained := reverseInput_evalsInTime family input.reverse tokenData rfl
  have whole := EvalsToInTime.trans
    (TM2.step (program family))
    ((IndexedTemplateEmitter.emitted family input).length + 1 +
      (IndexedTemplateEmitter.selectedCount family input + 1 +
        scanTime family 0 input))
    (input.length + 1)
    (scanCfg initial) (reverseInputCfg tokenData)
    (some (haltCfg (appendedOutput family input))) (by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using firstThree) (by
      convert retained using 1
      · simp [tokenData, clearedData, scannedData, haltDataCfg,
          haltCfg, appendedOutput]
      · simp)
  convert whole using 1
  unfold totalTime
  omega

/-- Exact genuinely halted execution on every finite input. -/
def machine_outputsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (family : Family Data) (input : List Data) :
    TM2OutputsInTime (machine Data family) input
      (some (appendedOutput family input)) (totalTime family input) := by
  unfold TM2OutputsInTime
  change EvalsToInTime (TM2.step (program family))
    (initList (machine Data family) input)
    (some (haltList (machine Data family) (appendedOutput family input)))
    (totalTime family input)
  rw [initList_eq_scanCfg, haltList_eq_haltCfg]
  exact machine_evalsInTime family input

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
