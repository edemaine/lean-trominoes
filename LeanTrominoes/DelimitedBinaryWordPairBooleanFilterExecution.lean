/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterConfigurations

/-! # Execution of Boolean filtering for binary-word pairs -/

noncomputable section

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordPairBooleanFilterMachine

open DelimitedBinaryWordPairBooleanFilter

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration}
    (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    change (some first).bind transition = some last
    simpa using step
  steps_le_m := Nat.le_refl 1

def widenTime {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first : Configuration} {last : Option Configuration}
    {smaller larger : Nat}
    (run : EvalsToInTime transition first last smaller)
    (bound : smaller ≤ larger) :
    EvalsToInTime transition first last larger where
  steps := run.steps
  evals_in_steps := run.evals_in_steps
  steps_le_m := run.steps_le_m.trans bound

/-- Scan the left control prefix through its separator. -/
def scanControls_evalsInTime
    (controls : List Bool) (input : List InputToken)
    (controlReverse : List Bool) :
    EvalsToInTime (TM2.step program)
      (scanControlsCfg
        (controls.map .left ++ .separator :: input) controlReverse)
      (some (restoreControlsCfg input
        (controls.reverse ++ controlReverse) []))
      (controls.length + 1) := by
  induction controls generalizing controlReverse with
  | nil =>
      simpa using oneStep
        (step_scanControls_separator input controlReverse)
  | cons control controls induction =>
      have first := oneStep (step_scanControls_left control
        (controls.map .left ++ .separator :: input) controlReverse)
      have rest := induction (control :: controlReverse)
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (controls.length + 1)
        (scanControlsCfg
          (.left control :: controls.map .left ++ .separator :: input)
          controlReverse)
        (scanControlsCfg
          (controls.map .left ++ .separator :: input)
          (control :: controlReverse))
        (some (restoreControlsCfg input
          (controls.reverse ++ control :: controlReverse) []))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using complete

/-- Restore the collected controls to their original order. -/
def restoreControls_evalsInTime
    (input : List InputToken) (controlReverse controls : List Bool) :
    EvalsToInTime (TM2.step program)
      (restoreControlsCfg input controlReverse controls)
      (some (scanPairsCfg input
        (controlReverse.reverse ++ controls) []))
      (controlReverse.length + 1) := by
  induction controlReverse generalizing controls with
  | nil =>
      simpa using oneStep (step_restoreControls_nil input controls)
  | cons control controlReverse induction =>
      have first := oneStep
        (step_restoreControls_cons input control controlReverse controls)
      have rest := induction (control :: controls)
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (controlReverse.length + 1)
        (restoreControlsCfg input (control :: controlReverse) controls)
        (restoreControlsCfg input controlReverse (control :: controls))
        (some (scanPairsCfg input
          (controlReverse.reverse ++ control :: controls) []))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using complete

private def pairBody
    (pair : List Bool × List Bool) : List PairToken :=
  pair.1.map .firstBit ++ .middle :: pair.2.map .secondBit

private theorem pairTokens_eq (pair : List Bool × List Bool) :
    DelimitedBinaryWordPairs.pairTokens pair =
      .pairStart :: pairBody pair ++ [.pairEnd] := by
  simp [DelimitedBinaryWordPairs.pairTokens, pairBody,
    List.append_assoc]

private theorem pairBody_ne_end
    (pair : List Bool × List Bool) (token : PairToken)
    (member : token ∈ pairBody pair) : token ≠ .pairEnd := by
  rcases pair with ⟨first, second⟩
  simp only [pairBody, List.mem_append, List.mem_map,
    List.mem_cons] at member
  rcases member with ⟨bit, _bitMember, rfl⟩ |
      rfl | ⟨bit, _bitMember, rfl⟩ <;> simp

/-- Scan the body and final delimiter of one pair. -/
def scanPair_evalsInTime
    (body : List PairToken)
    (noEnd : ∀ token ∈ body, token ≠ .pairEnd)
    (input : List InputToken) (controls : List Bool)
    (active : Option Bool) (outputReverse : List PairToken) :
    EvalsToInTime (TM2.step program)
      (scanPairCfg
        (body.map .right ++ [.right .pairEnd] ++ input)
        controls active outputReverse)
      (some (scanPairsCfg input controls
        (if active.getD false then
          (.pairEnd :: body.reverse) ++ outputReverse
        else outputReverse)))
      (body.length + 1) := by
  induction body generalizing outputReverse with
  | nil =>
      simpa using oneStep
        (step_scanPair_end input controls active outputReverse)
  | cons token body induction =>
      have tokenNotEnd : token ≠ .pairEnd := noEnd token (by simp)
      have tailNoEnd : ∀ current ∈ body, current ≠ .pairEnd := by
        intro current currentMember
        exact noEnd current (by simp [currentMember])
      let nextOutput :=
        if active.getD false then token :: outputReverse
        else outputReverse
      have first := oneStep (step_scanPair_token
        (body.map .right ++ [.right .pairEnd] ++ input)
        controls active token tokenNotEnd outputReverse)
      have rest := induction tailNoEnd nextOutput
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (body.length + 1)
        (scanPairCfg
          (.right token :: body.map .right ++
            [.right .pairEnd] ++ input)
          controls active outputReverse)
        (scanPairCfg
          (body.map .right ++ [.right .pairEnd] ++ input)
          controls active nextOutput)
        (some (scanPairsCfg input controls
          (if active.getD false then
            (.pairEnd :: body.reverse) ++ nextOutput
          else nextOutput)))
        first rest
      cases active with
      | none => simpa [nextOutput] using complete
      | some active =>
          cases active <;>
            simpa [nextOutput, List.reverse_cons,
              List.append_assoc] using complete

/-- Empty any unmatched suffix of the control stream. -/
def clearControls_evalsInTime
    (controls : List Bool) (outputReverse : List PairToken) :
    EvalsToInTime (TM2.step program)
      (clearControlsCfg controls outputReverse)
      (some (reverseOutputCfg outputReverse []))
      (controls.length + 1) := by
  induction controls with
  | nil =>
      simpa using oneStep (step_clearControls_nil outputReverse)
  | cons control controls induction =>
      have first := oneStep
        (step_clearControls_cons control controls outputReverse)
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (controls.length + 1)
        (clearControlsCfg (control :: controls) outputReverse)
        (clearControlsCfg controls outputReverse)
        (some (reverseOutputCfg outputReverse []))
        first induction
      simpa using complete

/-- Consume all encoded pairs, accumulating precisely the selected output
in reverse. Unmatched controls are cleared and unmatched pairs are scanned
without being copied. -/
def scanPairs_evalsInTime
    (controls : List Bool)
    (pairs : List (List Bool × List Bool))
    (outputReverse : List PairToken) :
    EvalsToInTime (TM2.step program)
      (scanPairsCfg
        ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
        controls outputReverse)
      (some (reverseOutputCfg
        ((DelimitedBinaryWordPairs.encode
          ⟨selectedPairs controls pairs⟩).reverse ++ outputReverse) []))
      ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).length +
        pairs.length + controls.length + 2) := by
  induction pairs generalizing controls outputReverse with
  | nil =>
      have first := oneStep (step_scanPairs_nil controls outputReverse)
      have cleared := clearControls_evalsInTime controls outputReverse
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (controls.length + 1)
        (scanPairsCfg [] controls outputReverse)
        (clearControlsCfg controls outputReverse)
        (some (reverseOutputCfg outputReverse []))
        first cleared
      simpa [DelimitedBinaryWordPairs.encode, selectedPairs] using complete
  | cons pair pairs induction =>
      cases controls with
      | nil =>
          have start := oneStep (step_scanPairs_start
            (((pairBody pair ++
                [DelimitedBinaryWordPairs.Token.pairEnd]) ++
              DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            [] outputReverse)
          have control := oneStep (step_readControl_nil
            (((pairBody pair ++
                [DelimitedBinaryWordPairs.Token.pairEnd]) ++
              DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            outputReverse)
          have pairRun := scanPair_evalsInTime
            (pairBody pair) (pairBody_ne_end pair)
            ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            [] none outputReverse
          have pairRun' : EvalsToInTime (TM2.step program)
              (scanPairCfg
                (((pairBody pair ++
                    [DelimitedBinaryWordPairs.Token.pairEnd]) ++
                  DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                [] none outputReverse)
              (some (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                [] outputReverse))
              ((pairBody pair).length + 1) := by
            simpa [List.map_append, List.append_assoc] using pairRun
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 _ _ _ start control
          have throughPairRaw := EvalsToInTime.trans (TM2.step program)
            2 ((pairBody pair).length + 1) _ _ _ firstTwo pairRun'
          have throughPair : EvalsToInTime (TM2.step program)
              (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode
                  ⟨pair :: pairs⟩).map .right)
                [] outputReverse)
              (some (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                [] outputReverse))
              ((DelimitedBinaryWordPairs.pairTokens pair).length + 1) := by
            simpa [pairTokens_eq, List.map_append, List.append_assoc,
              DelimitedBinaryWordPairs.encode] using throughPairRaw
          have rest := induction [] outputReverse
          have complete := EvalsToInTime.trans (TM2.step program)
            ((DelimitedBinaryWordPairs.pairTokens pair).length + 1)
            ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).length +
              pairs.length + 2)
            _ _ _ throughPair rest
          convert complete using 1 <;>
            simp [DelimitedBinaryWordPairs.encode, selectedPairs] <;>
            omega
      | cons active controls =>
          let pairOutput :=
            if active then
              (DelimitedBinaryWordPairs.pairTokens pair).reverse ++
                outputReverse
            else outputReverse
          have start := oneStep (step_scanPairs_start
            (((pairBody pair ++
                [DelimitedBinaryWordPairs.Token.pairEnd]) ++
              DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            (active :: controls) outputReverse)
          have control := oneStep (step_readControl_cons
            (((pairBody pair ++
                [DelimitedBinaryWordPairs.Token.pairEnd]) ++
              DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            active controls outputReverse)
          have pairRun := scanPair_evalsInTime
            (pairBody pair) (pairBody_ne_end pair)
            ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
            controls (some active)
            (if active then .pairStart :: outputReverse
              else outputReverse)
          have pairRun' : EvalsToInTime (TM2.step program)
              (scanPairCfg
                (((pairBody pair ++
                    [DelimitedBinaryWordPairs.Token.pairEnd]) ++
                  DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                controls (some active)
                (if active then .pairStart :: outputReverse
                  else outputReverse))
              (some (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                controls
                (if (some active).getD false then
                  (.pairEnd :: (pairBody pair).reverse) ++
                    (if active then .pairStart :: outputReverse
                      else outputReverse)
                else if active then .pairStart :: outputReverse
                  else outputReverse)))
              ((pairBody pair).length + 1) := by
            simpa [List.map_append, List.append_assoc] using pairRun
          have firstTwo := EvalsToInTime.trans (TM2.step program)
            1 1 _ _ _ start control
          have throughPairRaw := EvalsToInTime.trans (TM2.step program)
            2 ((pairBody pair).length + 1) _ _ _ firstTwo pairRun'
          have throughPair : EvalsToInTime (TM2.step program)
              (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode
                  ⟨pair :: pairs⟩).map .right)
                (active :: controls) outputReverse)
              (some (scanPairsCfg
                ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
                controls pairOutput))
              ((DelimitedBinaryWordPairs.pairTokens pair).length + 1) := by
            cases active <;>
              simpa [pairOutput, pairTokens_eq, List.map_append,
                List.reverse_append, List.append_assoc,
                DelimitedBinaryWordPairs.encode] using throughPairRaw
          have rest := induction controls pairOutput
          have complete := EvalsToInTime.trans (TM2.step program)
            ((DelimitedBinaryWordPairs.pairTokens pair).length + 1)
            ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).length +
              pairs.length + controls.length + 2)
            _ _ _ throughPair rest
          have complete' := widenTime
            (larger :=
              (DelimitedBinaryWordPairs.encode ⟨pair :: pairs⟩).length +
                (pair :: pairs).length +
                (active :: controls).length + 2)
            complete (by
              simp [DelimitedBinaryWordPairs.encode]
              omega)
          cases active <;>
            convert complete' using 1 <;>
              simp [pairOutput, DelimitedBinaryWordPairs.encode,
                selectedPairs, List.reverse_append,
                List.append_assoc]

/-- Reverse the selected token accumulation onto the physical output. -/
def reverseOutput_evalsInTime
    (outputReverse output : List PairToken) :
    EvalsToInTime (TM2.step program)
      (reverseOutputCfg outputReverse output)
      (some (haltCfg (outputReverse.reverse ++ output)))
      (outputReverse.length + 1) := by
  induction outputReverse generalizing output with
  | nil =>
      simpa using oneStep (step_reverseOutput_nil output)
  | cons token outputReverse induction =>
      have first := oneStep
        (step_reverseOutput_cons token outputReverse output)
      have rest := induction (token :: output)
      have complete := EvalsToInTime.trans (TM2.step program)
        1 (outputReverse.length + 1)
        (reverseOutputCfg (token :: outputReverse) output)
        (reverseOutputCfg outputReverse (token :: output))
        (some (haltCfg (outputReverse.reverse ++ token :: output)))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using complete

theorem initList_eq_scanControlsCfg (tokens : List InputToken) :
    initList machine tokens = scanControlsCfg tokens [] := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some Label.scanControls) initialState stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg (tokens : List PairToken) :
    haltList machine tokens = haltCfg tokens := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk none initialState stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

/-- Exact execution before replacing its structural size expression by a
linear input-length envelope. -/
def machine_outputsInTime
    (input : DelimitedBinaryWordPairBooleanFilter.Input) :
    TM2OutputsInTime machine
      (encodeInput input)
      (some (DelimitedBinaryWordPairs.encode
        ⟨selectedPairs input.controls input.pairs⟩))
      (3 * input.controls.length +
        (DelimitedBinaryWordPairs.encode ⟨input.pairs⟩).length +
        input.pairs.length +
        (DelimitedBinaryWordPairs.encode
          ⟨selectedPairs input.controls input.pairs⟩).length + 5) := by
  rcases input with ⟨controls, pairs⟩
  dsimp only
  let pairInput : List InputToken :=
    (DelimitedBinaryWordPairs.encode ⟨pairs⟩).map
      SeparatedProductEncoding.Token.right
  have scanned := scanControls_evalsInTime controls pairInput []
  have restored := restoreControls_evalsInTime
    pairInput controls.reverse []
  have setup := EvalsToInTime.trans (TM2.step program)
    (controls.length + 1) (controls.length + 1)
    _ _ _ scanned (by simpa using restored)
  have setup' : EvalsToInTime (TM2.step program)
      (scanControlsCfg
        (controls.map .left ++ .separator ::
          (DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right) [])
      (some (scanPairsCfg
        ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).map .right)
        controls []))
      (2 * controls.length + 2) := by
    convert setup using 1 <;> (try simp [pairInput]) <;> omega
  have pairsRun := scanPairs_evalsInTime controls pairs []
  have throughPairs := EvalsToInTime.trans (TM2.step program)
    (2 * controls.length + 2)
    ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).length +
      pairs.length + controls.length + 2)
    _ _ _ setup' (by simpa [pairInput] using pairsRun)
  have reversed := reverseOutput_evalsInTime
    (DelimitedBinaryWordPairs.encode
      ⟨selectedPairs controls pairs⟩).reverse []
  have complete := EvalsToInTime.trans (TM2.step program)
    ((DelimitedBinaryWordPairs.encode ⟨pairs⟩).length +
      pairs.length + controls.length + 2 +
        (2 * controls.length + 2))
    ((DelimitedBinaryWordPairs.encode
      ⟨selectedPairs controls pairs⟩).length + 1)
    _ _ _ throughPairs (by simpa using reversed)
  change EvalsToInTime (TM2.step program)
    (initList machine (encodeInput ⟨controls, pairs⟩))
    (some (haltList machine
      (DelimitedBinaryWordPairs.encode
        ⟨selectedPairs controls pairs⟩))) _
  rw [initList_eq_scanControlsCfg, haltList_eq_haltCfg]
  convert complete using 1 <;>
    (try simp [encodeInput, SeparatedProductEncoding.encode,
      List.map_append, List.append_assoc]) <;> omega

end DelimitedBinaryWordPairBooleanFilterMachine
end LeanTrominoes

end
