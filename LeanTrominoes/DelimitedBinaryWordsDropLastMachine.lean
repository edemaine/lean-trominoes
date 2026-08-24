/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords

/-! # Machine dropping the final delimited binary word -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace DelimitedBinaryWordsDropLastMachine

abbrev Token := DelimitedBinaryWords.Token

inductive Stack
  | input
  | reverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | collect
  | discardLast
  | restorePrefix
  deriving Fintype

abbrev State := Option Token

abbrev Alphabet : Stack → Type
  | .input | .reverse | .output => Token

def initialState : State := none

instance : Inhabited State := ⟨initialState⟩

def setToken (_state : State) (token : Option Token) : State := token

def clearToken (_state : State) : State := none

def tokenIsNone (state : State) : Bool := state.isNone

def tokenIsWordStart : State → Bool
  | some .wordStart => true
  | _ => false

def tokenFromState (state : State) : Token :=
  state.getD .wordStart

/-- Reverse the input, discard through the first reversed `wordStart`, then
restore the remaining prefix directly onto the output stack. -/
def program : Label → TM2.Stmt Alphabet Label State
  | .collect =>
      .pop .input setToken
        (.branch tokenIsNone
          (.load clearToken (.goto fun _ => .discardLast))
          (.push .reverse tokenFromState
            (.load clearToken (.goto fun _ => .collect))))
  | .discardLast =>
      .pop .reverse setToken
        (.branch tokenIsNone
          (.load clearToken .halt)
          (.branch tokenIsWordStart
            (.load clearToken (.goto fun _ => .restorePrefix))
            (.load clearToken (.goto fun _ => .discardLast))))
  | .restorePrefix =>
      .pop .reverse setToken
        (.branch tokenIsNone
          (.load clearToken .halt)
          (.push .output tokenFromState
            (.load clearToken (.goto fun _ => .restorePrefix))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .collect
  σ := State
  initialState := initialState
  m := program

def tapes (input reverse output : List Token) :
    ∀ stack, List (Alphabet stack)
  | .input => input
  | .reverse => reverse
  | .output => output

def collectCfg (input reverse : List Token) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .collect, none, tapes input reverse []⟩

def discardLastCfg (reverse : List Token) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .discardLast, none, tapes [] reverse []⟩

def restorePrefixCfg (reverse output : List Token) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .restorePrefix, none, tapes [] reverse output⟩

def haltCfg (output : List Token) : TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes [] [] output⟩

@[simp] theorem update_tapes_input
    (head : Token) (input reverse output : List Token) :
    Function.update (tapes (head :: input) reverse output)
        Stack.input input =
      tapes input reverse output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_reverse
    (input : List Token) (head : Token)
    (reverse output : List Token) :
    Function.update (tapes input reverse output)
        Stack.reverse (head :: reverse) =
      tapes input (head :: reverse) output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_reverse
    (input : List Token) (head : Token)
    (reverse output : List Token) :
    Function.update (tapes input (head :: reverse) output)
        Stack.reverse reverse =
      tapes input reverse output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_output
    (input reverse : List Token) (head : Token)
    (output : List Token) :
    Function.update (tapes input reverse output)
        Stack.output (head :: output) =
      tapes input reverse (head :: output) := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_collect_cons (token : Token) (input reverse : List Token) :
    TM2.step program (collectCfg (token :: input) reverse) =
      some (collectCfg input (token :: reverse)) := by
  simp [TM2.step, program, collectCfg, tapes,
    setToken, clearToken, tokenIsNone, tokenFromState]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_collect_nil (reverse : List Token) :
    TM2.step program (collectCfg [] reverse) =
      some (discardLastCfg reverse) := by
  simp [TM2.step, program, collectCfg, discardLastCfg, tapes,
    setToken, clearToken, tokenIsNone, tokenFromState]

theorem step_discardLast_nil :
    TM2.step program (discardLastCfg []) = some (haltCfg []) := by
  simp [TM2.step, program, discardLastCfg, haltCfg, tapes,
    setToken, clearToken, tokenIsNone, tokenIsWordStart]

theorem step_discardLast_wordStart (reverse : List Token) :
    TM2.step program
        (discardLastCfg (.wordStart :: reverse)) =
      some (restorePrefixCfg reverse []) := by
  simp [TM2.step, program, discardLastCfg, restorePrefixCfg, tapes,
    setToken, clearToken, tokenIsNone, tokenIsWordStart]

theorem step_discardLast_nonstart
    (token : Token) (reverse : List Token)
    (notStart : token ≠ .wordStart) :
    TM2.step program (discardLastCfg (token :: reverse)) =
      some (discardLastCfg reverse) := by
  cases token <;>
    simp_all [TM2.step, program, discardLastCfg, tapes,
      setToken, clearToken, tokenIsNone, tokenIsWordStart]

theorem step_restorePrefix_cons
    (token : Token) (reverse output : List Token) :
    TM2.step program
        (restorePrefixCfg (token :: reverse) output) =
      some (restorePrefixCfg reverse (token :: output)) := by
  simp [TM2.step, program, restorePrefixCfg, tapes,
    setToken, clearToken, tokenIsNone, tokenFromState]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_restorePrefix_nil (output : List Token) :
    TM2.step program (restorePrefixCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, restorePrefixCfg, haltCfg, tapes,
    setToken, clearToken, tokenIsNone]

end DelimitedBinaryWordsDropLastMachine
end LeanTrominoes
