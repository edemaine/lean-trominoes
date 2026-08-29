/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Complexity
import LeanTrominoes.DelimitedRouteJoinData

/-! # Machine for joining aligned route-delimited streams -/

noncomputable section

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

inductive Stack
  | input
  | prefixReverse
  | prefixes
  | suffixReverse
  | suffixes
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | scanLeft
  | pushPrefixReverse
  | scanRight
  | pushSuffixReverse
  | restorePrefixes
  | pushPrefix
  | restoreSuffixes
  | pushSuffix
  | scanPrefix
  | pushPrefixToken
  | scanSuffix
  | pushSuffixToken
  | cleanupPrefixes
  | cleanupSuffixes
  | reverseOutput
  | pushOutput
  deriving Fintype

inductive State
  | empty
  | input (symbol : Option InputSymbol)
  | token (symbol : Option Token)
  deriving Fintype

abbrev Alphabet : Stack → Type
  | .input => InputSymbol
  | .prefixReverse | .prefixes | .suffixReverse | .suffixes |
      .outputReverse | .output => Token

def inputSymbol : State → Option InputSymbol
  | .input symbol => symbol
  | _ => none

def tokenSymbol : State → Option Token
  | .token symbol => symbol
  | _ => none

def inputIsNone (state : State) : Bool :=
  (inputSymbol state).isNone

def inputIsLeft : State → Bool
  | .input (some (.left _)) => true
  | _ => false

def inputIsSeparator : State → Bool
  | .input (some .separator) => true
  | _ => false

def inputIsRight : State → Bool
  | .input (some (.right _)) => true
  | _ => false

def tokenIsNone (state : State) : Bool :=
  (tokenSymbol state).isNone

def tokenIsRouteEnd : State → Bool
  | .token (some .routeEnd) => true
  | _ => false

def leftToken : State → Token
  | .input (some (.left token)) => token
  | _ => .routeEnd

def rightToken : State → Token
  | .input (some (.right token)) => token
  | _ => .routeEnd

def storedToken : State → Token
  | .token (some token) => token
  | _ => .routeEnd

def clear : State → State := fun _ => .empty

def program : Label → TM2.Stmt Alphabet Label State
  | .scanLeft =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restorePrefixes))
          (.branch inputIsLeft
            (.goto fun _ => .pushPrefixReverse)
            (.branch inputIsSeparator
              (.load clear (.goto fun _ => .scanRight))
              (.load clear (.goto fun _ => .scanLeft)))))
  | .pushPrefixReverse =>
      .push .prefixReverse leftToken
        (.load clear (.goto fun _ => .scanLeft))
  | .scanRight =>
      .pop .input (fun _ symbol => .input symbol)
        (.branch inputIsNone
          (.load clear (.goto fun _ => .restorePrefixes))
          (.branch inputIsRight
            (.goto fun _ => .pushSuffixReverse)
            (.load clear (.goto fun _ => .scanRight))))
  | .pushSuffixReverse =>
      .push .suffixReverse rightToken
        (.load clear (.goto fun _ => .scanRight))
  | .restorePrefixes =>
      .pop .prefixReverse (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .restoreSuffixes))
          (.goto fun _ => .pushPrefix))
  | .pushPrefix =>
      .push .prefixes storedToken
        (.load clear (.goto fun _ => .restorePrefixes))
  | .restoreSuffixes =>
      .pop .suffixReverse (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .scanPrefix))
          (.goto fun _ => .pushSuffix))
  | .pushSuffix =>
      .push .suffixes storedToken
        (.load clear (.goto fun _ => .restoreSuffixes))
  | .scanPrefix =>
      .pop .prefixes (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .cleanupPrefixes))
          (.branch tokenIsRouteEnd
            (.load clear (.goto fun _ => .scanSuffix))
            (.goto fun _ => .pushPrefixToken)))
  | .pushPrefixToken =>
      .push .outputReverse storedToken
        (.load clear (.goto fun _ => .scanPrefix))
  | .scanSuffix =>
      .pop .suffixes (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .cleanupPrefixes))
          (.goto fun _ => .pushSuffixToken))
  | .pushSuffixToken =>
      .push .outputReverse storedToken
        (.branch tokenIsRouteEnd
          (.load clear (.goto fun _ => .scanPrefix))
          (.load clear (.goto fun _ => .scanSuffix)))
  | .cleanupPrefixes =>
      .pop .prefixes (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .cleanupSuffixes))
          (.load clear (.goto fun _ => .cleanupPrefixes)))
  | .cleanupSuffixes =>
      .pop .suffixes (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear (.goto fun _ => .reverseOutput))
          (.load clear (.goto fun _ => .cleanupSuffixes)))
  | .reverseOutput =>
      .pop .outputReverse (fun _ symbol => .token symbol)
        (.branch tokenIsNone
          (.load clear .halt)
          (.goto fun _ => .pushOutput))
  | .pushOutput =>
      .push .output storedToken
        (.load clear (.goto fun _ => .reverseOutput))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scanLeft
  σ := State
  initialState := .empty
  m := program

end LeanTrominoes.DelimitedRouteJoin

end
