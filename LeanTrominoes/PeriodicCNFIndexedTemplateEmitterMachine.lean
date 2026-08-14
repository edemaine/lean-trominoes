/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPolySpaceInitialSourceTemplates

/-!
# Finite machine for data-indexed affine template emission

The machine scans input items from left to right.  Every item is retained on a
reverse stack.  A selected item immediately executes its data-dependent affine
recipe at the unary length of the processed-position stack.  Generated tokens
use a separate reverse stack.  Cleanup reverses tokens first and retained data
second, yielding the retained input followed by the emitted token word.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace IndexedTemplateEmitterMachine

open AffineTemplateEmitterMachine
open IndexedTemplateEmitter
open UnaryProgramTokens

def recipesFor {Data : Type} (family : Family Data) (data : Data) :
    List Recipe :=
  (family data).getD []

/-- Semantic whole-machine output. -/
def appendedOutput {Data : Type} (family : Family Data)
    (data : List Data) : List (Data ⊕ Token) :=
  data.map Sum.inl ++ (emitted family data).map Sum.inr

inductive Stack
  | input
  | inputReverse
  | processed
  | scratch
  | tokenReverse
  | output
  deriving DecidableEq, Fintype

inductive Label (Data : Type) (family : Family Data)
  | scan
  | beginItem (data : Data)
  | execute (data : Data) (index : Fin (recipesFor family data).length)
  | scanPosition (data : Data)
      (index : Fin (recipesFor family data).length)
  | restorePosition (data : Data)
      (index : Fin (recipesFor family data).length)
  | clearProcessed
  | reverseTokens
  | reverseInput
  deriving Fintype

abbrev State (Data : Type) := Option (Data ⊕ (Unit ⊕ Token))

abbrev Alphabet (Data : Type) : Stack → Type
  | .input | .inputReverse => Data
  | .processed | .scratch => Unit
  | .tokenReverse => Token
  | .output => Data ⊕ Token

def dataFromState {Data : Type} [Inhabited Data] : State Data → Data
  | some (.inl data) => data
  | _ => default

def tokenFromState {Data : Type} : State Data → Token
  | some (.inr (.inr token)) => token
  | _ => default

def pushTokens {Data : Type} {family : Family Data}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data) (Label Data family) (State Data)) :
    TM2.Stmt (Alphabet Data) (Label Data family) (State Data) :=
  tokens.foldr
    (fun token continuation =>
      .push .tokenReverse (fun _ => token) continuation)
    next

def pushAtomUnits {Data : Type} {family : Family Data} (count : Nat)
    (next : TM2.Stmt (Alphabet Data) (Label Data family) (State Data)) :
    TM2.Stmt (Alphabet Data) (Label Data family) (State Data) :=
  pushTokens (List.replicate count .atomUnit) next

def afterRecipe {Data : Type} (family : Family Data) (data : Data)
    (index : Fin (recipesFor family data).length) :
    TM2.Stmt (Alphabet Data) (Label Data family) (State Data) :=
  if nextExists : index.val + 1 < (recipesFor family data).length then
    .load (fun _ => none)
      (.goto fun _ => .execute data ⟨index.val + 1, nextExists⟩)
  else
    .push .processed (fun _ => ())
      (.load (fun _ => none) (.goto fun _ => .scan))

def program {Data : Type} [Inhabited Data] (family : Family Data) :
    Label Data family →
      TM2.Stmt (Alphabet Data) (Label Data family) (State Data)
  | .scan =>
      .pop .input (fun _ data => data.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .clearProcessed)
          (.push .inputReverse dataFromState
            (.goto fun state =>
              match state with
              | some (.inl data) => .beginItem data
              | _ => .scan)))
  | .beginItem data =>
      match value : family data with
      | none =>
          .load (fun _ => none) (.goto fun _ => .scan)
      | some recipes =>
          if nonempty : 0 < recipes.length then
            have indexedNonempty : 0 < (recipesFor family data).length := by
              simpa [recipesFor, value] using nonempty
            .load (fun _ => none)
              (.goto fun _ => .execute data ⟨0, indexedNonempty⟩)
          else
            .push .processed (fun _ => ())
              (.load (fun _ => none) (.goto fun _ => .scan))
  | .execute data index =>
      match (recipesFor family data).get index with
      | .fixed token =>
          .push .tokenReverse (fun _ => token)
            (afterRecipe family data index)
      | .atom base _stride =>
          pushAtomUnits base
            (.load (fun _ => none)
              (.goto fun _ => .scanPosition data index))
  | .scanPosition data index =>
      .pop .processed (fun _ unit => unit.map fun _ => Sum.inr (.inl ()))
        (.branch Option.isNone
          (.goto fun _ => .restorePosition data index)
          (.push .scratch (fun _ => ())
            (match (recipesFor family data).get index with
            | .fixed _ =>
                .load (fun _ => none)
                  (.goto fun _ => .scanPosition data index)
            | .atom _ stride =>
                pushAtomUnits stride
                  (.load (fun _ => none)
                    (.goto fun _ => .scanPosition data index)))))
  | .restorePosition data index =>
      .pop .scratch (fun _ unit => unit.map fun _ => Sum.inr (.inl ()))
        (.branch Option.isNone
          (afterRecipe family data index)
          (.push .processed (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restorePosition data index))))
  | .clearProcessed =>
      .pop .processed (fun _ unit => unit.map fun _ => Sum.inr (.inl ()))
        (.branch Option.isNone
          (.goto fun _ => .reverseTokens)
          (.load (fun _ => none) (.goto fun _ => .clearProcessed)))
  | .reverseTokens =>
      .pop .tokenReverse (fun _ token => token.map fun token =>
          Sum.inr (.inr token))
        (.branch Option.isNone
          (.goto fun _ => .reverseInput)
          (.push .output (fun state => .inr (tokenFromState state))
            (.load (fun _ => none) (.goto fun _ => .reverseTokens))))
  | .reverseInput =>
      .pop .inputReverse (fun _ data => data.map Sum.inl)
        (.branch Option.isNone
          .halt
          (.push .output (fun state => .inl (dataFromState state))
            (.load (fun _ => none) (.goto fun _ => .reverseInput))))

abbrev machine (Data : Type) [Fintype Data] [Inhabited Data]
    (family : Family Data) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Data
  Λ := Label Data family
  main := .scan
  σ := State Data
  initialState := none
  m := program family

end IndexedTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
