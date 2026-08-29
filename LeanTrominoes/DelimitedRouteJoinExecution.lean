/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinCleanupExecution
import LeanTrominoes.DelimitedRouteJoinJoinExecution
import LeanTrominoes.DelimitedRouteJoinParsing
import LeanTrominoes.DelimitedRouteJoinReverseExecution

/-! # Complete execution of delimited-route joining -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open Computability StateTransition Turing

def totalTime (prefixes suffixes : List Token) : Nat :=
  let result := resultAux .prefix prefixes suffixes
  parseTime prefixes suffixes +
    joinTime .prefix prefixes suffixes +
    (result.remainingPrefixes.length + 1) +
    (result.remainingSuffixes.length + 1) +
    (2 * result.output.length + 1)

theorem initList_eq_scanLeftCfg (input : List Token × List Token) :
    initList machine (encode input) =
      scanLeftCfg ⟨encode input, [], [], [], [], [], []⟩ := by
  unfold initList machine scanLeftCfg emptyCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg (output : List Token) :
    haltList machine output = haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def execution (prefixes suffixes : List Token) :
    EvalsToInTime machine.step
      (scanLeftCfg
        ⟨encode (prefixes, suffixes), [], [], [], [], [], []⟩)
      (some (haltCfg (joined prefixes suffixes)))
      (totalTime prefixes suffixes) := by
  let result := resultAux .prefix prefixes suffixes
  let parsedData : TapeData :=
    ⟨[], [], prefixes, [], suffixes, [], []⟩
  let joinedData : TapeData :=
    ⟨[], [], result.remainingPrefixes, [],
      result.remainingSuffixes, result.output.reverse, []⟩
  let prefixesCleaned : TapeData :=
    { joinedData with prefixes := [] }
  let cleanedData : TapeData :=
    { prefixesCleaned with suffixes := [] }
  have parsed := parsing_evalsInTime prefixes suffixes
  have parsed' : EvalsToInTime machine.step
      (scanLeftCfg
        ⟨encode (prefixes, suffixes), [], [], [], [], [], []⟩)
      (some (scanPrefixCfg parsedData))
      (parseTime prefixes suffixes) := by
    simpa [encode, SeparatedProductEncoding.encode, parsedData]
      using parsed
  have joinedRun := joining_evalsInTime .prefix prefixes suffixes
    parsedData rfl rfl
  have joinedRun' : EvalsToInTime machine.step
      (scanPrefixCfg parsedData)
      (some (cleanupPrefixesCfg joinedData))
      (joinTime .prefix prefixes suffixes) := by
    simpa [phaseCfg, result, parsedData, joinedData] using joinedRun
  have prefixesRun := cleanupPrefixes_evalsInTime
    result.remainingPrefixes joinedData rfl
  have prefixesRun' : EvalsToInTime machine.step
      (cleanupPrefixesCfg joinedData)
      (some (cleanupSuffixesCfg prefixesCleaned))
      (result.remainingPrefixes.length + 1) := by
    simpa [prefixesCleaned] using prefixesRun
  have suffixesRun := cleanupSuffixes_evalsInTime
    result.remainingSuffixes prefixesCleaned rfl
  have suffixesRun' : EvalsToInTime machine.step
      (cleanupSuffixesCfg prefixesCleaned)
      (some (reverseOutputCfg cleanedData))
      (result.remainingSuffixes.length + 1) := by
    simpa [cleanedData] using suffixesRun
  have reversed := reverseOutput_evalsInTime
    result.output.reverse cleanedData rfl
  have reversed' : EvalsToInTime machine.step
      (reverseOutputCfg cleanedData)
      (some (haltCfg result.output))
      (2 * result.output.length + 1) := by
    simpa [cleanedData, prefixesCleaned, joinedData, haltCfg]
      using reversed
  have throughJoin := EvalsToInTime.trans machine.step
    (parseTime prefixes suffixes)
    (joinTime .prefix prefixes suffixes)
    _ _ _ parsed' joinedRun'
  have throughPrefixes := EvalsToInTime.trans machine.step
    (joinTime .prefix prefixes suffixes + parseTime prefixes suffixes)
    (result.remainingPrefixes.length + 1)
    _ _ _ throughJoin prefixesRun'
  have throughSuffixes := EvalsToInTime.trans machine.step
    (result.remainingPrefixes.length + 1 +
      (joinTime .prefix prefixes suffixes + parseTime prefixes suffixes))
    (result.remainingSuffixes.length + 1)
    _ _ _ throughPrefixes suffixesRun'
  have whole := EvalsToInTime.trans machine.step
    (result.remainingSuffixes.length + 1 +
      (result.remainingPrefixes.length + 1 +
        (joinTime .prefix prefixes suffixes + parseTime prefixes suffixes)))
    (2 * result.output.length + 1)
    _ _ _ throughSuffixes reversed'
  simpa [totalTime, joined, joinedAux, result,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using whole

/-- The fixed finite machine joins corresponding delimiter-terminated route
prefixes and suffixes.  Its behavior is total even on malformed streams. -/
def machine_outputsInTime (input : List Token × List Token) :
    TM2OutputsInTime machine (encode input)
      (some (joined input.1 input.2))
      (totalTime input.1 input.2) := by
  have run := execution input.1 input.2
  refine
    { steps := run.steps
      evals_in_steps := ?_
      steps_le_m := run.steps_le_m }
  change (flip bind machine.step)^[run.steps]
      (some (initList machine (encode input))) =
        some (haltList machine (joined input.1 input.2))
  rw [initList_eq_scanLeftCfg, haltList_eq_haltCfg]
  exact run.evals_in_steps

end LeanTrominoes.DelimitedRouteJoin

end
