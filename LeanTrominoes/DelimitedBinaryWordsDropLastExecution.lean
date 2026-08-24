/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsDropLastMachine

/-! # Execution of final delimited-binary-word removal -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordsDropLastMachine

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

/-- The collection pass reverses every remaining input token. -/
def collect_evalsInTime
    (input reverse : List Token) :
    EvalsToInTime (TM2.step program)
      (collectCfg input reverse)
      (some (discardLastCfg (input.reverse ++ reverse)))
      (input.length + 1) := by
  induction input generalizing reverse with
  | nil =>
      simpa using oneStep (step_collect_nil reverse)
  | cons token input induction =>
      have first := oneStep (step_collect_cons token input reverse)
      have rest := induction (token :: reverse)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (input.length + 1)
        (collectCfg (token :: input) reverse)
        (collectCfg input (token :: reverse))
        (some (discardLastCfg (input.reverse ++ token :: reverse)))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

/-- Discard a start-free reversed suffix and its following `wordStart`. -/
def discardThroughStart_evalsInTime
    (tokens reverse : List Token)
    (noStart : ∀ token ∈ tokens, token ≠ .wordStart) :
    EvalsToInTime (TM2.step program)
      (discardLastCfg (tokens ++ .wordStart :: reverse))
      (some (restorePrefixCfg reverse []))
      (tokens.length + 1) := by
  induction tokens generalizing reverse with
  | nil =>
      simpa using oneStep (step_discardLast_wordStart reverse)
  | cons token tokens induction =>
      have tokenNotStart : token ≠ .wordStart :=
        noStart token (by simp)
      have tailNoStart :
          ∀ tailToken ∈ tokens, tailToken ≠ .wordStart := by
        intro tailToken tailMember
        exact noStart tailToken (by simp [tailMember])
      have first := oneStep
        (step_discardLast_nonstart token
          (tokens ++ .wordStart :: reverse) tokenNotStart)
      have rest := induction reverse tailNoStart
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (tokens.length + 1)
        (discardLastCfg (token :: tokens ++ .wordStart :: reverse))
        (discardLastCfg (tokens ++ .wordStart :: reverse))
        (some (restorePrefixCfg reverse [])) first rest
      simpa using composed

/-- One complete reversed delimited word is discarded exactly. -/
def discardWord_evalsInTime
    (word : List Bool) (reverse : List Token) :
    EvalsToInTime (TM2.step program)
      (discardLastCfg
        ((DelimitedBinaryWords.wordTokens word).reverse ++ reverse))
      (some (restorePrefixCfg reverse []))
      (DelimitedBinaryWords.wordTokens word).length := by
  let suffix : List Token :=
    .wordEnd :: (word.map .bit).reverse
  have noStart : ∀ token ∈ suffix, token ≠ .wordStart := by
    intro token tokenMember
    simp only [suffix, List.mem_cons, List.mem_reverse,
      List.mem_map] at tokenMember
    rcases tokenMember with tokenEnd | ⟨bit, _bitMember, tokenBit⟩
    · subst token
      simp
    · subst token
      simp
  have run := discardThroughStart_evalsInTime suffix reverse noStart
  convert run using 1 <;>
    simp [suffix, DelimitedBinaryWords.wordTokens,
      List.reverse_append, List.append_assoc]

/-- The remaining reversed prefix is restored in forward order. -/
def restorePrefix_evalsInTime
    (reverse output : List Token) :
    EvalsToInTime (TM2.step program)
      (restorePrefixCfg reverse output)
      (some (haltCfg (reverse.reverse ++ output)))
      (reverse.length + 1) := by
  induction reverse generalizing output with
  | nil =>
      simpa using oneStep (step_restorePrefix_nil output)
  | cons token reverse induction =>
      have first := oneStep
        (step_restorePrefix_cons token reverse output)
      have rest := induction (token :: output)
      have composed := EvalsToInTime.trans (TM2.step program)
        1 (reverse.length + 1)
        (restorePrefixCfg (token :: reverse) output)
        (restorePrefixCfg reverse (token :: output))
        (some (haltCfg (reverse.reverse ++ token :: output)))
        first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

theorem initList_eq_collectCfg (tokens : List Token) :
    initList machine tokens = collectCfg tokens [] := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk (some Label.collect) none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

theorem haltList_eq_haltCfg (tokens : List Token) :
    haltList machine tokens = haltCfg tokens := by
  apply congrArg (fun stackValues =>
    TM2.Cfg.mk none none stackValues)
  funext stack
  cases stack <;> simp [machine, tapes]

/-- The machine removes exactly the final encoded word in `2n + 2` steps. -/
def machine_outputsInTime (input : DelimitedBinaryWords.Input) :
    TM2OutputsInTime machine
      (DelimitedBinaryWords.encode input)
      (some (DelimitedBinaryWords.encode
        ⟨input.words.dropLast⟩))
      (2 * (DelimitedBinaryWords.encode input).length + 2) := by
  rcases input with ⟨words⟩
  change EvalsToInTime (TM2.step program)
    (initList machine
      (DelimitedBinaryWords.encode
        (DelimitedBinaryWords.Input.mk words)))
    (some (haltList machine
      (DelimitedBinaryWords.encode
        (DelimitedBinaryWords.Input.mk words.dropLast))))
    (2 * (DelimitedBinaryWords.encode
      (DelimitedBinaryWords.Input.mk words)).length + 2)
  by_cases wordsEmpty : words = []
  · subst words
    have first := collect_evalsInTime ([] : List Token) []
    have second := oneStep step_discardLast_nil
    have composed := EvalsToInTime.trans (TM2.step program)
      1 1 (collectCfg [] []) (discardLastCfg [])
      (some (haltCfg [])) first second
    rw [initList_eq_collectCfg, haltList_eq_haltCfg]
    simpa [DelimitedBinaryWords.encode] using composed
  · let leadingWords := words.dropLast
    let last := words.getLast wordsEmpty
    have wordsEq : leadingWords ++ [last] = words := by
      exact List.dropLast_append_getLast wordsEmpty
    let leadingTokens := DelimitedBinaryWords.encode
      (DelimitedBinaryWords.Input.mk leadingWords)
    have encodedEq :
        DelimitedBinaryWords.encode
            (DelimitedBinaryWords.Input.mk words) =
          leadingTokens ++ DelimitedBinaryWords.wordTokens last := by
      rw [← wordsEq]
      simp [DelimitedBinaryWords.encode, leadingTokens]
    have collected := collect_evalsInTime
      (DelimitedBinaryWords.encode
        (DelimitedBinaryWords.Input.mk words)) []
    have collected' : EvalsToInTime (TM2.step program)
        (collectCfg
          (DelimitedBinaryWords.encode
            (DelimitedBinaryWords.Input.mk words)) [])
        (some (discardLastCfg
          ((DelimitedBinaryWords.wordTokens last).reverse ++
            leadingTokens.reverse)))
        ((DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words)).length + 1) := by
      simpa [encodedEq, List.reverse_append] using collected
    have discarded := discardWord_evalsInTime last leadingTokens.reverse
    have firstTwo := EvalsToInTime.trans (TM2.step program)
      ((DelimitedBinaryWords.encode
        (DelimitedBinaryWords.Input.mk words)).length + 1)
      (DelimitedBinaryWords.wordTokens last).length
      (collectCfg
        (DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words)) [])
      (discardLastCfg
        ((DelimitedBinaryWords.wordTokens last).reverse ++
          leadingTokens.reverse))
      (some (restorePrefixCfg leadingTokens.reverse []))
      collected' discarded
    have restored := restorePrefix_evalsInTime leadingTokens.reverse []
    have complete := EvalsToInTime.trans (TM2.step program)
      ((DelimitedBinaryWords.wordTokens last).length +
        ((DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words)).length + 1))
      (leadingTokens.reverse.length + 1)
      (collectCfg
        (DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words)) [])
      (restorePrefixCfg leadingTokens.reverse [])
      (some (haltCfg leadingTokens)) firstTwo (by simpa using restored)
    rw [initList_eq_collectCfg, haltList_eq_haltCfg]
    change EvalsToInTime (TM2.step program)
      (collectCfg
        (DelimitedBinaryWords.encode
          (DelimitedBinaryWords.Input.mk words)) [])
      (some (haltCfg leadingTokens))
      (2 * (DelimitedBinaryWords.encode
        (DelimitedBinaryWords.Input.mk words)).length + 2)
    convert complete using 1
    simp only [List.length_reverse]
    rw [encodedEq, List.length_append]
    omega

end DelimitedBinaryWordsDropLastMachine
end LeanTrominoes
