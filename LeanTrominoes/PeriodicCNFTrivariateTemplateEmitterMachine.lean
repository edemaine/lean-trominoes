/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTrivariateTemplateEmitterData

/-! # Finite trivariate affine template-emitter machine -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TrivariateTemplateEmitterMachine

open UnaryProgramTokens
open TrivariateTemplateEmitter

abbrev Recipe := TrivariateTemplateEmitter.Recipe
abbrev Workspace (Data : Type) := Data ⊕ Token

instance workspaceInhabited {Data : Type} [Inhabited Data] :
    Inhabited (Workspace Data) :=
  ⟨.inl default⟩

def dataSelected {Data : Type} (selected : Data → Bool) :
    Workspace Data → Bool
  | .inl data => selected data
  | .inr _ => false

def selectedCount {Data : Type} (selected : Data → Bool)
    (workspace : List (Workspace Data)) : Nat :=
  UnaryPolynomialPaddingMachine.selectedCount (dataSelected selected)
    workspace

inductive Stack
  | input
  | first
  | second
  | remaining
  | processed
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label (recipeCount : Nat)
  | scan
  | beginPosition
  | execute (index : Fin recipeCount)
  | scanFirst (index : Fin recipeCount)
  | restoreFirst (index : Fin recipeCount)
  | scanSecond (index : Fin recipeCount)
  | restoreSecond (index : Fin recipeCount)
  | scanPosition (index : Fin recipeCount)
  | restorePosition (index : Fin recipeCount)
  | emitEnding
  | clearFirst
  | clearSecond
  | clearProcessed
  | reverseOutput
  deriving Fintype

abbrev State (Data : Type) := Option (Workspace Data ⊕ Unit)

abbrev Alphabet (Data : Type) : Stack → Type
  | .input | .outputReverse | .output => Workspace Data
  | .first | .second | .remaining | .processed | .scratch => Unit

def workspaceFromState {Data : Type} [Inhabited Data] :
    State Data → Workspace Data
  | some (.inl workspace) => workspace
  | _ => default

def stateSelected {Data : Type} (selected : Data → Bool) :
    State Data → Bool
  | some (.inl workspace) => dataSelected selected workspace
  | _ => false

def pushTokens {Data : Type} {recipeCount : Nat}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data)) :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  tokens.foldr
    (fun token continuation =>
      .push .outputReverse (fun _ => (Sum.inr token : Workspace Data))
        continuation)
    next

def pushAtomUnits {Data : Type} {recipeCount : Nat} (count : Nat)
    (next : TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data)) :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  pushTokens (List.replicate count .atomUnit) next

def continueScan {Data : Type} {recipeCount : Nat} :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  .load (fun _ => none) (.goto fun _ => .scan)

def countPosition {Data : Type} {recipeCount : Nat}
    (positionSelected : Data → Bool) :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  .branch (stateSelected positionSelected)
    (.push .remaining (fun _ => ()) continueScan)
    continueScan

def countSecondAndPosition {Data : Type} {recipeCount : Nat}
    (secondSelected positionSelected : Data → Bool) :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  .branch (stateSelected secondSelected)
    (.push .second (fun _ => ()) (countPosition positionSelected))
    (countPosition positionSelected)

def countAll {Data : Type} {recipeCount : Nat}
    (firstSelected secondSelected positionSelected : Data → Bool) :
    TM2.Stmt (Alphabet Data) (Label recipeCount) (State Data) :=
  .branch (stateSelected firstSelected)
    (.push .first (fun _ => ())
      (countSecondAndPosition secondSelected positionSelected))
    (countSecondAndPosition secondSelected positionSelected)

def beginTemplate {Data : Type} (recipes : List Recipe) :
    TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data) :=
  if nonempty : 0 < recipes.length then
    .load (fun _ => none)
      (.goto fun _ => .execute ⟨0, nonempty⟩)
  else
    .push .processed (fun _ => ())
      (.load (fun _ => none) (.goto fun _ => .beginPosition))

def afterRecipe {Data : Type} (recipes : List Recipe)
    (index : Fin recipes.length) :
    TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data) :=
  if nextExists : index.val + 1 < recipes.length then
    .load (fun _ => none)
      (.goto fun _ => .execute ⟨index.val + 1, nextExists⟩)
  else
    .push .processed (fun _ => ())
      (.load (fun _ => none) (.goto fun _ => .beginPosition))

/-- The finite program counts two persistent global dimensions and one
position range, then emits each trivariate recipe in left-to-right order. -/
def program {Data : Type} [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token) :
    Label recipes.length →
      TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data)
  | .scan =>
      .pop .input (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .beginPosition)
          (.push .outputReverse workspaceFromState
            (countAll firstSelected secondSelected positionSelected)))
  | .beginPosition =>
      .pop .remaining (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .emitEnding)
          (beginTemplate recipes))
  | .execute index =>
      match recipes.get index with
      | .fixed token =>
          .push .outputReverse
            (fun _ => (Sum.inr token : Workspace Data))
            (afterRecipe recipes index)
      | .atom base _ _ _ =>
          pushAtomUnits base
            (.load (fun _ => none) (.goto fun _ => .scanFirst index))
  | .scanFirst index =>
      .pop .first (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restoreFirst index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none) (.goto fun _ => .scanFirst index)
            | .atom _ firstStride _ _ =>
                pushAtomUnits firstStride
                  (.load (fun _ => none)
                    (.goto fun _ => .scanFirst index)))))
  | .restoreFirst index =>
      .pop .scratch (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .scanSecond index)
          (.push .first (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restoreFirst index))))
  | .scanSecond index =>
      .pop .second (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restoreSecond index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none) (.goto fun _ => .scanSecond index)
            | .atom _ _ secondStride _ =>
                pushAtomUnits secondStride
                  (.load (fun _ => none)
                    (.goto fun _ => .scanSecond index)))))
  | .restoreSecond index =>
      .pop .scratch (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .scanPosition index)
          (.push .second (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restoreSecond index))))
  | .scanPosition index =>
      .pop .processed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restorePosition index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none) (.goto fun _ => .scanPosition index)
            | .atom _ _ _ positionStride =>
                pushAtomUnits positionStride
                  (.load (fun _ => none)
                    (.goto fun _ => .scanPosition index)))))
  | .restorePosition index =>
      .pop .scratch (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (afterRecipe recipes index)
          (.push .processed (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restorePosition index))))
  | .emitEnding =>
      pushTokens ending
        (.load (fun _ => none) (.goto fun _ => .clearFirst))
  | .clearFirst =>
      .pop .first (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .clearSecond)
          (.load (fun _ => none) (.goto fun _ => .clearFirst)))
  | .clearSecond =>
      .pop .second (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .clearProcessed)
          (.load (fun _ => none) (.goto fun _ => .clearSecond)))
  | .clearProcessed =>
      .pop .processed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.load (fun _ => none) (.goto fun _ => .clearProcessed)))
  | .reverseOutput =>
      .pop .outputReverse (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone
          .halt
          (.push .output workspaceFromState
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

abbrev machine (Data : Type) [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected positionSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Data
  Λ := Label recipes.length
  main := .scan
  σ := State Data
  initialState := none
  m := program firstSelected secondSelected positionSelected recipes ending

end TrivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
