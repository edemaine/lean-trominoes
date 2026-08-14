/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFTriangularTemplateEmitterSpec

/-!
# Finite triangular template-emitter machine

This file contains only the finite machine core.  It retains the input while
counting a persistent first class and an outer-position class.  Each outer
iteration holds one marker aside, emits its first template, moves all strictly
higher markers through an inner loop, restores them while emitting fold
closers, emits its second template, and finally unwinds one fixed block per
outer position.  Execution and runtime proofs are intentionally split into
later modules to keep individual Lean jobs small.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace TriangularTemplateEmitterMachine

open UnaryProgramTokens
open TriangularTemplateEmitter

abbrev Recipe := BivariateProgramTemplates.Recipe

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

/-- Semantic output realized by the machine. -/
def appendedOutput {Data : Type}
    (firstSelected secondSelected : Data → Bool)
    (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser finalBase finalCloser : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  workspace ++
    (TriangularTemplateEmitter.emitted outerFirst inner outerSecond
      innerBase innerCloser frameCloser finalBase finalCloser
      (selectedCount firstSelected workspace)
      (selectedCount secondSelected workspace)).map Sum.inr

/-- The three recipe blocks executed within one outer frame. -/
inductive Stage
  | outerFirst
  | inner
  | outerSecond
  deriving DecidableEq, Fintype

def stageRecipes (outerFirst inner outerSecond : List Recipe) :
    Stage → List Recipe
  | .outerFirst => outerFirst
  | .inner => inner
  | .outerSecond => outerSecond

@[simp]
def Stage.isInner : Stage → Bool
  | .inner => true
  | _ => false

inductive Stack
  | input
  | first
  | remaining
  | current
  | processed
  | innerProcessed
  | firstScratch
  | positionScratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

/-- Finite control.  Recipe indices are bounded by the three fixed recipe
lists, so this remains finite independently of the runtime counters. -/
inductive Label (outerFirstCount innerCount outerSecondCount : Nat)
  | scan
  | beginOuter
  | beginInner
  | executeOuterFirst (index : Fin outerFirstCount)
  | executeInner (index : Fin innerCount)
  | executeOuterSecond (index : Fin outerSecondCount)
  | scanFirstOuterFirst (index : Fin outerFirstCount)
  | scanFirstInner (index : Fin innerCount)
  | scanFirstOuterSecond (index : Fin outerSecondCount)
  | restoreFirstOuterFirst (index : Fin outerFirstCount)
  | restoreFirstInner (index : Fin innerCount)
  | restoreFirstOuterSecond (index : Fin outerSecondCount)
  | scanPositionOuterFirst (index : Fin outerFirstCount)
  | scanPositionInner (index : Fin innerCount)
  | scanPositionOuterSecond (index : Fin outerSecondCount)
  | restorePositionOuterFirst (index : Fin outerFirstCount)
  | restorePositionInner (index : Fin innerCount)
  | restorePositionOuterSecond (index : Fin outerSecondCount)
  | scanInner (index : Fin innerCount)
  | restoreInner (index : Fin innerCount)
  | finishInnerPosition
  | restoreInnerRange
  | finishOuter
  | unwind
  | clearFirst
  | reverseOutput
  deriving Fintype

abbrev State (Data : Type) := Option (Workspace Data ⊕ Unit)

abbrev Alphabet (Data : Type) : Stack → Type
  | .input | .outputReverse | .output => Workspace Data
  | .first | .remaining | .current | .processed | .innerProcessed |
      .firstScratch | .positionScratch => Unit

def workspaceFromState {Data : Type} [Inhabited Data] :
    State Data → Workspace Data
  | some (.inl workspace) => workspace
  | _ => default

def stateSelected {Data : Type} (selected : Data → Bool) :
    State Data → Bool
  | some (.inl workspace) => dataSelected selected workspace
  | _ => false

def stageCount (outerFirst inner outerSecond : List Recipe) : Stage → Nat
  | .outerFirst => outerFirst.length
  | .inner => inner.length
  | .outerSecond => outerSecond.length

def stageLabel
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    Label outerFirst.length inner.length outerSecond.length :=
  match stage with
  | .outerFirst => .executeOuterFirst index
  | .inner => .executeInner index
  | .outerSecond => .executeOuterSecond index

def scanFirstLabel
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    Label outerFirst.length inner.length outerSecond.length :=
  match stage with
  | .outerFirst => .scanFirstOuterFirst index
  | .inner => .scanFirstInner index
  | .outerSecond => .scanFirstOuterSecond index

def restoreFirstLabel
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    Label outerFirst.length inner.length outerSecond.length :=
  match stage with
  | .outerFirst => .restoreFirstOuterFirst index
  | .inner => .restoreFirstInner index
  | .outerSecond => .restoreFirstOuterSecond index

def scanPositionLabel
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    Label outerFirst.length inner.length outerSecond.length :=
  match stage with
  | .outerFirst => .scanPositionOuterFirst index
  | .inner => .scanPositionInner index
  | .outerSecond => .scanPositionOuterSecond index

def restorePositionLabel
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    Label outerFirst.length inner.length outerSecond.length :=
  match stage with
  | .outerFirst => .restorePositionOuterFirst index
  | .inner => .restorePositionInner index
  | .outerSecond => .restorePositionOuterSecond index

def recipeAt
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) : Recipe :=
  (stageRecipes outerFirst inner outerSecond stage).get
    ⟨index.val, by cases stage <;> exact index.isLt⟩

def afterStage
    (outerFirst inner outerSecond : List Recipe) :
    Stage → Label outerFirst.length inner.length outerSecond.length
  | .outerFirst => .beginInner
  | .inner => .finishInnerPosition
  | .outerSecond => .finishOuter

def pushTokens {Data : Type}
    {outerFirstCount innerCount outerSecondCount : Nat}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data) :=
  tokens.foldr
    (fun token continuation =>
      .push .outputReverse (fun _ => (Sum.inr token : Workspace Data))
        continuation)
    next

def pushAtomUnits {Data : Type}
    {outerFirstCount innerCount outerSecondCount : Nat}
    (count : Nat)
    (next : TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirstCount innerCount outerSecondCount) (State Data) :=
  pushTokens (List.replicate count .atomUnit) next

def beginTemplate {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (stage : Stage) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  if nonempty : 0 < stageCount outerFirst inner outerSecond stage then
    .load (fun _ => none)
      (.goto fun _ => stageLabel outerFirst inner outerSecond stage
        ⟨0, nonempty⟩)
  else
    .load (fun _ => none)
      (.goto fun _ => afterStage outerFirst inner outerSecond stage)

def afterRecipe {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  if nextExists : index.val + 1 <
      stageCount outerFirst inner outerSecond stage then
    .load (fun _ => none)
      (.goto fun _ => stageLabel outerFirst inner outerSecond stage
        ⟨index.val + 1, nextExists⟩)
  else
    .load (fun _ => none)
      (.goto fun _ => afterStage outerFirst inner outerSecond stage)

def executeRecipe {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  match recipeAt outerFirst inner outerSecond stage index with
  | .fixed token =>
      pushTokens [token] (afterRecipe outerFirst inner outerSecond stage index)
  | .atom base _ _ =>
      pushAtomUnits base
        (.goto fun _ => scanFirstLabel outerFirst inner outerSecond stage index)

def scanFirst {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .first (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (.goto fun _ => restoreFirstLabel outerFirst inner outerSecond stage index)
      (.push .firstScratch (fun _ => ())
        (pushAtomUnits
          (match recipeAt outerFirst inner outerSecond stage index with
            | .fixed _ => 0
            | .atom _ firstStride _ => firstStride)
          (.load (fun _ => none)
            (.goto fun _ => scanFirstLabel outerFirst inner outerSecond
              stage index)))))

def restoreFirst {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .firstScratch (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (if stage.isInner then
        pushAtomUnits
          (match recipeAt outerFirst inner outerSecond stage index with
            | .fixed _ => 0
            | .atom _ _ secondStride => secondStride)
          (.goto fun _ => scanPositionLabel outerFirst inner outerSecond
            stage index)
       else
        .goto fun _ => scanPositionLabel outerFirst inner outerSecond
          stage index)
      (.push .first (fun _ => ())
        (.load (fun _ => none)
          (.goto fun _ => restoreFirstLabel outerFirst inner outerSecond
            stage index))))

def scanPosition {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .processed (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (.goto fun _ => restorePositionLabel outerFirst inner outerSecond
        stage index)
      (.push .positionScratch (fun _ => ())
        (pushAtomUnits
          (match recipeAt outerFirst inner outerSecond stage index with
            | .fixed _ => 0
            | .atom _ _ secondStride => secondStride)
          (.load (fun _ => none)
            (.goto fun _ => scanPositionLabel outerFirst inner outerSecond
              stage index)))))

def restorePosition {Data : Type}
    (outerFirst inner outerSecond : List Recipe)
    (stage : Stage)
    (index : Fin (stageCount outerFirst inner outerSecond stage)) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .positionScratch (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (match stage with
       | .outerFirst =>
          afterRecipe outerFirst inner outerSecond .outerFirst index
       | .inner => .goto fun _ => .scanInner index
       | .outerSecond =>
          afterRecipe outerFirst inner outerSecond .outerSecond index)
      (.push .processed (fun _ => ())
        (.load (fun _ => none)
          (.goto fun _ => restorePositionLabel outerFirst inner outerSecond
            stage index))))

def scanInner {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (index : Fin inner.length) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .innerProcessed (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (.goto fun _ => .restoreInner index)
      (.push .positionScratch (fun _ => ())
        (pushAtomUnits
          (match inner.get index with
            | .fixed _ => 0
            | .atom _ _ secondStride => secondStride)
          (.load (fun _ => none) (.goto fun _ => .scanInner index)))))

def restoreInner {Data : Type}
    (outerFirst inner outerSecond : List Recipe) (index : Fin inner.length) :
    TM2.Stmt (Alphabet Data)
      (Label outerFirst.length inner.length outerSecond.length) (State Data) :=
  .pop .positionScratch (fun _ unit => unit.map Sum.inr)
    (.branch Option.isNone
      (afterRecipe outerFirst inner outerSecond .inner index)
      (.push .innerProcessed (fun _ => ())
        (.load (fun _ => none) (.goto fun _ => .restoreInner index))))

/-- Complete finite transition program. -/
def program {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser finalBase finalCloser : List Token) :
    Label outerFirst.length inner.length outerSecond.length →
      TM2.Stmt (Alphabet Data)
        (Label outerFirst.length inner.length outerSecond.length) (State Data)
  | .scan =>
      .pop .input (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .beginOuter)
          (.push .outputReverse workspaceFromState
            (.branch (stateSelected firstSelected)
              (.push .first (fun _ => ())
                (.branch (stateSelected secondSelected)
                  (.push .remaining (fun _ => ())
                    (.load (fun _ => none) (.goto fun _ => .scan)))
                  (.load (fun _ => none) (.goto fun _ => .scan))))
              (.branch (stateSelected secondSelected)
                (.push .remaining (fun _ => ())
                  (.load (fun _ => none) (.goto fun _ => .scan)))
                (.load (fun _ => none) (.goto fun _ => .scan))))))
  | .beginOuter =>
      .pop .remaining (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (pushTokens finalBase (.goto fun _ => .unwind))
          (.push .current (fun _ => ())
            (beginTemplate outerFirst inner outerSecond .outerFirst)))
  | .beginInner =>
      .pop .remaining (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (pushTokens innerBase (.goto fun _ => .restoreInnerRange))
          (beginTemplate outerFirst inner outerSecond .inner))
  | .executeOuterFirst index =>
      executeRecipe outerFirst inner outerSecond .outerFirst index
  | .executeInner index =>
      executeRecipe outerFirst inner outerSecond .inner index
  | .executeOuterSecond index =>
      executeRecipe outerFirst inner outerSecond .outerSecond index
  | .scanFirstOuterFirst index =>
      scanFirst outerFirst inner outerSecond .outerFirst index
  | .scanFirstInner index =>
      scanFirst outerFirst inner outerSecond .inner index
  | .scanFirstOuterSecond index =>
      scanFirst outerFirst inner outerSecond .outerSecond index
  | .restoreFirstOuterFirst index =>
      restoreFirst outerFirst inner outerSecond .outerFirst index
  | .restoreFirstInner index =>
      restoreFirst outerFirst inner outerSecond .inner index
  | .restoreFirstOuterSecond index =>
      restoreFirst outerFirst inner outerSecond .outerSecond index
  | .scanPositionOuterFirst index =>
      scanPosition outerFirst inner outerSecond .outerFirst index
  | .scanPositionInner index =>
      scanPosition outerFirst inner outerSecond .inner index
  | .scanPositionOuterSecond index =>
      scanPosition outerFirst inner outerSecond .outerSecond index
  | .restorePositionOuterFirst index =>
      restorePosition outerFirst inner outerSecond .outerFirst index
  | .restorePositionInner index =>
      restorePosition outerFirst inner outerSecond .inner index
  | .restorePositionOuterSecond index =>
      restorePosition outerFirst inner outerSecond .outerSecond index
  | .scanInner index => scanInner outerFirst inner outerSecond index
  | .restoreInner index => restoreInner outerFirst inner outerSecond index
  | .finishInnerPosition =>
      .push .innerProcessed (fun _ => ())
        (.load (fun _ => none) (.goto fun _ => .beginInner))
  | .restoreInnerRange =>
      .pop .innerProcessed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (pushTokens frameCloser
            (beginTemplate outerFirst inner outerSecond .outerSecond))
          (.push .remaining (fun _ => ())
            (pushTokens innerCloser
              (.load (fun _ => none) (.goto fun _ => .restoreInnerRange)))))
  | .finishOuter =>
      .pop .current (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .beginOuter)
          (.push .processed (fun _ => ())
            (.load (fun _ => none) (.goto fun _ => .beginOuter))))
  | .unwind =>
      .pop .processed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .clearFirst)
          (pushTokens finalCloser
            (.load (fun _ => none) (.goto fun _ => .unwind))))
  | .clearFirst =>
      .pop .first (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .reverseOutput)
          (.load (fun _ => none) (.goto fun _ => .clearFirst)))
  | .reverseOutput =>
      .pop .outputReverse (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone .halt
          (.push .output workspaceFromState
            (.load (fun _ => none) (.goto fun _ => .reverseOutput))))

/-- Finite machine underlying triangular template emission. -/
def machine (Data : Type) [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (outerFirst inner outerSecond : List Recipe)
    (innerBase innerCloser frameCloser finalBase finalCloser : List Token) :
    FinTM2 where
  K := Stack
  kDecidableEq := inferInstance
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Data
  Γk₀Fin := inferInstance
  Λ := Label outerFirst.length inner.length outerSecond.length
  main := .scan
  σ := State Data
  initialState := none
  m := program firstSelected secondSelected outerFirst inner outerSecond
    innerBase innerCloser frameCloser finalBase finalCloser

end TriangularTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
