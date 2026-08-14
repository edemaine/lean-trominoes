/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramTokens

/-!
# Affine-position template emitter

Many dynamic pieces of the normalized bounded-machine program iterate over a
unary width.  Within one iteration every runtime atom has the affine form
`base + stride * position`, while all instruction and clause tokens are fixed.

This file defines one reusable finite machine for that pattern.  It retains
an arbitrary finite workspace, counts selected data symbols into a unary loop,
and appends a fixed recipe at every position.  Atom recipes rescan the unary
processed-position stack, so arbitrary fixed bases and strides require no
unbounded control state.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace AffineTemplateEmitterMachine

open UnaryProgramTokens

/-- One fixed entry of a position-dependent token template. -/
inductive Recipe
  | fixed (token : Token)
  | atom (base stride : Nat)
  deriving DecidableEq

namespace Recipe

/-- Tokens contributed by one recipe at a zero-based runtime position. -/
def tokens (position : Nat) : Recipe → List Token
  | .fixed token => [token]
  | .atom base stride =>
      List.replicate (base + stride * position) .atomUnit

end Recipe

def positionTokens (recipes : List Recipe) (position : Nat) : List Token :=
  recipes.flatMap (Recipe.tokens position)

/-- Token fragment contributed by consecutive positions beginning at
`firstPosition`. -/
def positionRangeTokens (recipes : List Recipe)
    (firstPosition : Nat) : Nat → List Token
  | 0 => []
  | count + 1 =>
      positionTokens recipes firstPosition ++
        positionRangeTokens recipes (firstPosition + 1) count

@[simp]
theorem positionRangeTokens_zero (recipes : List Recipe)
    (firstPosition : Nat) :
    positionRangeTokens recipes firstPosition 0 = [] :=
  rfl

theorem positionRangeTokens_succ (recipes : List Recipe)
    (firstPosition count : Nat) :
    positionRangeTokens recipes firstPosition (count + 1) =
      positionTokens recipes firstPosition ++
        positionRangeTokens recipes (firstPosition + 1) count :=
  rfl

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

/-- Semantic stage output: retain the complete workspace and append every
affine-position template followed by a fixed ending word. -/
def appendedOutput {Data : Type} (selected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  workspace ++
    (positionRangeTokens recipes 0 (selectedCount selected workspace) ++
      ending).map Sum.inr

inductive Stack
  | input
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
  | scanPosition (index : Fin recipeCount)
  | restorePosition (index : Fin recipeCount)
  | emitEnding
  | clearProcessed
  | reverseOutput
  deriving Fintype

abbrev State (Data : Type) := Option (Workspace Data ⊕ Unit)

abbrev Alphabet (Data : Type) : Stack → Type
  | .input | .outputReverse | .output => Workspace Data
  | .remaining | .processed | .scratch => Unit

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

def program {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token) :
    Label recipes.length →
      TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data)
  | .scan =>
      .pop .input (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .beginPosition)
          (.push .outputReverse workspaceFromState
            (.branch (stateSelected selected)
              (.push .remaining (fun _ => ())
                (.load (fun _ => none) (.goto fun _ => .scan)))
              (.load (fun _ => none) (.goto fun _ => .scan)))))
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
      | .atom base _stride =>
          pushAtomUnits base
            (.load (fun _ => none)
              (.goto fun _ => .scanPosition index))
  | .scanPosition index =>
      .pop .processed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restorePosition index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none)
                  (.goto fun _ => .scanPosition index)
            | .atom _ stride =>
                pushAtomUnits stride
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
        (.load (fun _ => none) (.goto fun _ => .clearProcessed))
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
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token) :
    FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Data
  Λ := Label recipes.length
  main := .scan
  σ := State Data
  initialState := none
  m := program selected recipes ending

structure TapeData (Data : Type) where
  input : List (Workspace Data)
  remaining : List Unit
  processed : List Unit
  scratch : List Unit
  outputReverse : List (Workspace Data)
  output : List (Workspace Data)

def tapes {Data : Type} (data : TapeData Data) :
    ∀ stack, List (Alphabet Data stack)
  | .input => data.input
  | .remaining => data.remaining
  | .processed => data.processed
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg {Data : Type} {recipes : List Recipe}
    (label : Label recipes.length) (state : State Data)
    (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨some label, state, tapes data⟩

def scanCfg {Data : Type} {recipes : List Recipe} (data : TapeData Data) :=
  cfg (recipes := recipes) .scan none data

def beginPositionCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .beginPosition none data

def executeCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.execute index) none data

def scanPositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanPosition index) none data

def restorePositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restorePosition index) none data

def emitEndingCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .emitEnding none data

def clearProcessedCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearProcessed none data

def reverseOutputCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .reverseOutput none data

def haltCfg {Data : Type} {recipes : List Recipe}
    (output : List (Workspace Data)) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨none, none, tapes ⟨[], [], [], [], [], output⟩⟩

def haltDataCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨none, none, tapes data⟩

def afterRecipeCfg {Data : Type} (recipes : List Recipe)
    (index : Fin recipes.length) (data : TapeData Data) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  if nextExists : index.val + 1 < recipes.length then
    executeCfg ⟨index.val + 1, nextExists⟩ data
  else
    beginPositionCfg (recipes := recipes)
      { data with processed := () :: data.processed }

@[simp]
theorem update_tapes_input {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_remaining {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.remaining value =
      tapes { data with remaining := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_processed {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.processed value =
      tapes { data with processed := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_scratch {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_outputReverse {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp]
theorem update_tapes_output {Data : Type} (data : TapeData Data)
    (value : List (Workspace Data)) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem stepAux_pushTokens {Data : Type} {recipes : List Recipe}
    (tokens : List Token)
    (next : TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushTokens tokens next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse :=
            (tokens.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  induction tokens generalizing data with
  | nil => simp [pushTokens]
  | cons token tokens induction =>
      simp only [pushTokens, List.foldr_cons, TM2.stepAux]
      rw [update_tapes_outputReverse]
      change TM2.stepAux (pushTokens tokens next) state
          (tapes { data with
            outputReverse :=
              (Sum.inr token : Workspace Data) :: data.outputReverse }) = _
      rw [induction]
      simp [List.reverse_cons, List.append_assoc]

theorem stepAux_pushAtomUnits {Data : Type} {recipes : List Recipe}
    (count : Nat)
    (next : TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data))
    (state : State Data) (data : TapeData Data) :
    TM2.stepAux (pushAtomUnits count next) state (tapes data) =
      TM2.stepAux next state
        (tapes { data with
          outputReverse :=
            List.replicate count
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rw [pushAtomUnits, stepAux_pushTokens]
  simp

theorem step_scan_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (inputEq : data.input = []) :
    TM2.step (program selected recipes ending) (scanCfg data) =
      some (beginPositionCfg { data with input := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, beginPositionCfg, cfg, tapes]

theorem step_scan_selected {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (selectedEq : dataSelected selected workspace = true) :
    TM2.step (program selected recipes ending) (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          remaining := () :: data.remaining
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at selectedEq

theorem step_scan_unselected {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (selectedEq : dataSelected selected workspace = false) :
    TM2.step (program selected recipes ending) (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]

theorem step_beginPosition_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (remainingEq : data.remaining = []) :
    TM2.step (program selected recipes ending) (beginPositionCfg data) =
      some (emitEndingCfg { data with remaining := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change remaining = [] at remainingEq
  subst remaining
  simp [TM2.step, program, beginPositionCfg, emitEndingCfg, cfg, tapes]

theorem step_beginPosition_cons_nonempty {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (nonempty : 0 < recipes.length) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step (program selected recipes ending) (beginPositionCfg data) =
      some (executeCfg ⟨0, nonempty⟩
        { data with remaining := tail }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, nonempty,
    beginPositionCfg, executeCfg, cfg, tapes]

theorem step_beginPosition_cons_empty {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (empty : recipes = []) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step (program selected recipes ending) (beginPositionCfg data) =
      some (beginPositionCfg
        { data with
          remaining := tail
          processed := () :: data.processed }) := by
  subst recipes
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, beginPositionCfg, cfg, tapes]

theorem step_execute_fixed {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (token : Token) (data : TapeData Data)
    (recipeEq : recipes.get index = .fixed token) :
    TM2.step (program selected recipes ending) (executeCfg index data) =
      some (afterRecipeCfg recipes index
        { data with
          outputReverse :=
            (Sum.inr token : Workspace Data) :: data.outputReverse }) := by
  simp only [TM2.step, program, executeCfg, cfg]
  rw [recipeEq]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [afterRecipe, afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [afterRecipe, afterRecipeCfg, nextExists, beginPositionCfg, cfg,
      tapes]

theorem step_execute_atom {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base stride : Nat) (data : TapeData Data)
    (recipeEq : recipes.get index = .atom base stride) :
    TM2.step (program selected recipes ending) (executeCfg index data) =
      some (scanPositionCfg index
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  simp only [TM2.step, program, executeCfg, scanPositionCfg, cfg]
  rw [recipeEq, stepAux_pushAtomUnits]
  rfl

theorem step_scanPosition_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (processedEq : data.processed = []) :
    TM2.step (program selected recipes ending)
      (scanPositionCfg index data) =
      some (restorePositionCfg index { data with processed := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, scanPositionCfg, restorePositionCfg, cfg, tapes]

theorem step_scanPosition_cons_atom {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base stride : Nat) (data : TapeData Data)
    (tail : List Unit) (processedEq : data.processed = () :: tail)
    (recipeEq : recipes.get index = .atom base stride) :
    TM2.step (program selected recipes ending)
      (scanPositionCfg index data) =
      some (scanPositionCfg index
        { data with
          processed := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate stride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp only [TM2.step, program, scanPositionCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_processed, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restorePosition_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step (program selected recipes ending)
      (restorePositionCfg index data) =
      some (afterRecipeCfg recipes index { data with scratch := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, beginPositionCfg, cfg, tapes]

theorem step_restorePosition_cons {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step (program selected recipes ending)
      (restorePositionCfg index data) =
      some (restorePositionCfg index
        { data with
          processed := () :: data.processed
          scratch := tail }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restorePositionCfg, cfg, tapes]

theorem step_emitEnding {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) :
    TM2.step (program selected recipes ending) (emitEndingCfg data) =
      some (clearProcessedCfg
        { data with
          outputReverse :=
            (ending.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  simp only [TM2.step, program, emitEndingCfg, clearProcessedCfg, cfg]
  rw [stepAux_pushTokens]
  rfl

theorem step_clearProcessed_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (processedEq : data.processed = []) :
    TM2.step (program selected recipes ending) (clearProcessedCfg data) =
      some (reverseOutputCfg { data with processed := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, reverseOutputCfg, cfg, tapes]

theorem step_clearProcessed_cons {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail) :
    TM2.step (program selected recipes ending) (clearProcessedCfg data) =
      some (clearProcessedCfg { data with processed := tail }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, cfg, tapes]

theorem step_reverseOutput_nil {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (outputReverseEq : data.outputReverse = []) :
    TM2.step (program selected recipes ending) (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (outputReverseEq : data.outputReverse = workspace :: tail) :
    TM2.step (program selected recipes ending) (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := workspace :: data.output }) := by
  rcases data with
    ⟨input, remaining, processed, scratch, outputReverse, output⟩
  change outputReverse = workspace :: tail at outputReverseEq
  subst outputReverse
  rcases workspace with dataValue | token <;>
    simp [TM2.step, program, reverseOutputCfg, cfg, tapes,
      workspaceFromState]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 :=
  FiniteBlockTransducer.oneStep step

@[simp]
theorem selectedCount_cons {Data : Type} (selected : Data → Bool)
    (workspace : Workspace Data) (workspaces : List (Workspace Data)) :
    selectedCount selected (workspace :: workspaces) =
      (if dataSelected selected workspace then 1 else 0) +
        selectedCount selected workspaces :=
  rfl

theorem replicate_unit_add_one_right (count : Nat) :
    List.replicate (count + 1) () =
      List.replicate count () ++ [()] := by
  rw [List.replicate_add]
  rfl

def scan_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspaces : List (Workspace Data)) (data : TapeData Data)
    (inputEq : data.input = workspaces) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (scanCfg data)
      (some (beginPositionCfg
        { data with
          input := []
          remaining :=
            List.replicate (selectedCount selected workspaces) () ++
              data.remaining
          outputReverse := workspaces.reverse ++ data.outputReverse }))
      (workspaces.length + 1) := by
  induction workspaces generalizing data with
  | nil =>
      have step := oneStep
        (step_scan_nil selected recipes ending data inputEq)
      convert step using 1 <;>
        simp [selectedCount,
          UnaryPolynomialPaddingMachine.selectedCount]
  | cons workspace workspaces induction =>
      by_cases selectedEq : dataSelected selected workspace = true
      · let nextData : TapeData Data :=
          { data with
            input := workspaces
            remaining := () :: data.remaining
            outputReverse := workspace :: data.outputReverse }
        have first := oneStep
          (step_scan_selected selected recipes ending data workspace
            workspaces inputEq selectedEq)
        have rest := induction nextData rfl
        have composed := EvalsToInTime.trans
          (TM2.step (program selected recipes ending))
          1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
          (some (beginPositionCfg
            { nextData with
              input := []
              remaining :=
                List.replicate (selectedCount selected workspaces) () ++
                  nextData.remaining
              outputReverse :=
                workspaces.reverse ++ nextData.outputReverse }))
          first rest
        convert composed using 1
        · simp only [selectedCount_cons, selectedEq, if_true]
          rw [show 1 + selectedCount selected workspaces =
              selectedCount selected workspaces + 1 by omega,
            replicate_unit_add_one_right]
          simp [nextData, List.reverse_cons, List.append_assoc]
        · simp
      · have selectedFalse :
            dataSelected selected workspace = false := by
          exact Bool.eq_false_of_not_eq_true selectedEq
        let nextData : TapeData Data :=
          { data with
            input := workspaces
            outputReverse := workspace :: data.outputReverse }
        have first := oneStep
          (step_scan_unselected selected recipes ending data workspace
            workspaces inputEq selectedFalse)
        have rest := induction nextData rfl
        have composed := EvalsToInTime.trans
          (TM2.step (program selected recipes ending))
          1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
          (some (beginPositionCfg
            { nextData with
              input := []
              remaining :=
                List.replicate (selectedCount selected workspaces) () ++
                  nextData.remaining
              outputReverse :=
                workspaces.reverse ++ nextData.outputReverse }))
          first rest
        convert composed using 1
        · simp [nextData, selectedCount_cons, selectedFalse,
            List.reverse_cons, List.append_assoc]
        · simp

def scanPosition_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base stride : Nat)
    (recipeEq : recipes.get index = .atom base stride)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (scanPositionCfg index data)
      (some (restorePositionCfg index
        { data with
          processed := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (stride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanPosition_nil selected recipes ending index data
          processedEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate stride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have first := oneStep
        (step_scanPosition_cons_atom selected recipes ending index
          base stride data word processedEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        1 (word.length + 1) (scanPositionCfg index data)
        (scanPositionCfg index nextData)
        (some (restorePositionCfg index
          { nextData with
            processed := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (stride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show stride * (word.length + 1) =
            stride * word.length + stride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restorePosition_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (restorePositionCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          processed := word.reverse ++ data.processed
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restorePosition_nil selected recipes ending index data
          scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := () :: data.processed
          scratch := word }
      have first := oneStep
        (step_restorePosition_cons selected recipes ending index data word
          scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        1 (word.length + 1) (restorePositionCfg index data)
        (restorePositionCfg index nextData)
        (some (afterRecipeCfg recipes index
          { nextData with
            processed := word.reverse ++ nextData.processed
            scratch := [] }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def recipeTime (position : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ => 2 * position + 3

def executeRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (position : Nat) (data : TapeData Data)
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (executeCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          processed := List.replicate position ()
          scratch := []
          outputReverse :=
            ((Recipe.tokens position (recipes.get index)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeTime position (recipes.get index)) := by
  cases recipeEq : recipes.get index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed selected recipes ending index token data recipeEq)
      convert step using 1 <;>
        simp [Recipe.tokens, recipeTime, processedEq, scratchEq]
  | atom base stride =>
      let emittedData : TapeData Data :=
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have first := oneStep
        (step_execute_atom selected recipes ending index base stride data
          recipeEq)
      have scanned := scanPosition_evalsInTime selected recipes ending index
        base stride recipeEq (List.replicate position ()) emittedData (by
          simpa [emittedData] using processedEq)
      let scannedData : TapeData Data :=
        { emittedData with
          processed := []
          scratch := (List.replicate position ()).reverse
          outputReverse :=
            List.replicate (stride * position)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              emittedData.outputReverse }
      have firstTwo := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        1 (position + 1) (executeCfg index data)
        (scanPositionCfg index emittedData)
        (some (restorePositionCfg index scannedData)) first (by
          simpa [scannedData, emittedData, scratchEq] using scanned)
      have restored := restorePosition_evalsInTime selected recipes ending
        index (List.replicate position ()).reverse scannedData rfl
      have whole := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        (position + 2) (position + 1) (executeCfg index data)
        (restorePositionCfg index scannedData)
        (some (afterRecipeCfg recipes index
          { data with
            processed := List.replicate position ()
            scratch := []
            outputReverse :=
              List.replicate (base + stride * position)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                data.outputReverse }))
        firstTwo (by
          have outputEq :
              List.replicate (base + stride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  data.outputReverse =
                List.replicate (stride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  (List.replicate base
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                    data.outputReverse) := by
            rw [← List.append_assoc, ← List.replicate_add]
            congr 2
            ring
          convert restored using 1
          · simp [scannedData, emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [Recipe.tokens]
      · simp [recipeTime]
        ring

def recipeSuffixTokens (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) : List Token :=
  (recipes.drop index.val).flatMap (Recipe.tokens position)

theorem recipeSuffixTokens_eq (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTokens recipes position index =
      Recipe.tokens position (recipes.get index) ++
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTokens recipes position
            ⟨index.val + 1, nextExists⟩
        else [] := by
  unfold recipeSuffixTokens
  rw [← List.cons_get_drop_succ (l := recipes) (n := index)]
  simp only [List.flatMap_cons]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le beyond]
    simp [nextExists]

def recipeSuffixTime (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) : Nat :=
  ((recipes.drop index.val).map (recipeTime position)).sum

theorem recipeSuffixTime_eq (recipes : List Recipe) (position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTime recipes position index =
      recipeTime position (recipes.get index) +
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTime recipes position
            ⟨index.val + 1, nextExists⟩
        else 0 := by
  unfold recipeSuffixTime
  rw [← List.cons_get_drop_succ (l := recipes) (n := index)]
  simp only [List.map_cons, List.sum_cons]
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [nextExists]
  · have beyond : recipes.length ≤ index.val + 1 := by omega
    rw [List.drop_eq_nil_of_le beyond]
    simp [nextExists]

def executeRecipes_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (position : Nat) (data : TapeData Data)
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (executeCfg index data)
      (some (beginPositionCfg
        { data with
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes position index).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeSuffixTime recipes position index) := by
  have first := executeRecipe_evalsInTime selected recipes ending index
    position data processedEq scratchEq
  by_cases nextExists : index.val + 1 < recipes.length
  · let nextIndex : Fin recipes.length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        processed := List.replicate position ()
        scratch := []
        outputReverse :=
          ((Recipe.tokens position (recipes.get index)).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              data.outputReverse }
    have first' : EvalsToInTime
        (TM2.step (program selected recipes ending))
        (executeCfg index data) (some (executeCfg nextIndex currentData))
        (recipeTime position (recipes.get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := executeRecipes_evalsInTime selected recipes ending nextIndex
      position currentData rfl rfl
    have composed := EvalsToInTime.trans
      (TM2.step (program selected recipes ending))
      (recipeTime position (recipes.get index))
      (recipeSuffixTime recipes position nextIndex)
      (executeCfg index data) (executeCfg nextIndex currentData)
      (some (beginPositionCfg
        { currentData with
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes position nextIndex).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                currentData.outputReverse }))
      first' rest
    convert composed using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists, nextIndex, currentData, List.map_append,
        List.reverse_append, List.append_assoc]
    · rw [recipeSuffixTime_eq]
      simp [nextExists, nextIndex]
      omega
  · have first' : EvalsToInTime
        (TM2.step (program selected recipes ending))
        (executeCfg index data)
        (some (beginPositionCfg
          { data with
            processed := () :: List.replicate position ()
            scratch := []
            outputReverse :=
              ((Recipe.tokens position (recipes.get index)).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  data.outputReverse }))
        (recipeTime position (recipes.get index)) := by
      convert first using 1
      simp [afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [recipeSuffixTime_eq]
      simp [nextExists]
termination_by recipes.length - index.val
decreasing_by omega

def templateTime (recipes : List Recipe) (position : Nat) : Nat :=
  (recipes.map (recipeTime position)).sum

@[simp]
theorem recipeSuffixTokens_zero (recipes : List Recipe) (position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTokens recipes position ⟨0, nonempty⟩ =
      positionTokens recipes position := by
  simp [recipeSuffixTokens, positionTokens]

@[simp]
theorem recipeSuffixTime_zero (recipes : List Recipe) (position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTime recipes position ⟨0, nonempty⟩ =
      templateTime recipes position := by
  simp [recipeSuffixTime, templateTime]

def positionRangeTime (recipes : List Recipe) (firstPosition : Nat) :
    Nat → Nat
  | 0 => 1
  | count + 1 =>
      1 + templateTime recipes firstPosition +
        positionRangeTime recipes (firstPosition + 1) count

def positions_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (firstPosition count : Nat) (data : TapeData Data)
    (remainingEq : data.remaining = List.replicate count ())
    (processedEq : data.processed = List.replicate firstPosition ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (beginPositionCfg data)
      (some (emitEndingCfg
        { data with
          remaining := []
          processed := List.replicate (firstPosition + count) ()
          scratch := []
          outputReverse :=
            ((positionRangeTokens recipes firstPosition count).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (positionRangeTime recipes firstPosition count) := by
  induction count generalizing firstPosition data with
  | zero =>
      have step := oneStep
        (step_beginPosition_nil selected recipes ending data (by
          simpa using remainingEq))
      convert step using 1 <;>
        simp [positionRangeTime, processedEq, scratchEq]
  | succ count induction =>
      by_cases recipesEmpty : recipes = []
      · have first := oneStep
          (step_beginPosition_cons_empty selected recipes ending recipesEmpty
            data (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        let nextData : TapeData Data :=
          { data with
            remaining := List.replicate count ()
            processed := () :: data.processed }
        have rest := induction (firstPosition + 1) nextData rfl (by
          simpa [nextData, List.replicate_succ] using processedEq) (by
          simpa [nextData] using scratchEq)
        have composed := EvalsToInTime.trans
          (TM2.step (program selected recipes ending))
          1 (positionRangeTime recipes (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg nextData)
          (some (emitEndingCfg
            { nextData with
              remaining := []
              processed :=
                List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes (firstPosition + 1) count).map
                  fun token =>
                    (Sum.inr token : Workspace Data)).reverse ++
                      nextData.outputReverse }))
          first rest
        convert composed using 1
        · subst recipes
          simp [nextData, positionRangeTokens, positionTokens]
          congr 3
          omega
        · subst recipes
          simp [positionRangeTime, templateTime]
          omega
      · have recipesNonempty : 0 < recipes.length := by
          cases recipes with
          | nil => exact False.elim (recipesEmpty rfl)
          | cons recipe recipes => simp
        let selectedData : TapeData Data :=
          { data with remaining := List.replicate count () }
        have first := oneStep
          (step_beginPosition_cons_nonempty selected recipes ending
            recipesNonempty data (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        have templateRun := executeRecipes_evalsInTime selected recipes ending
          ⟨0, recipesNonempty⟩ firstPosition selectedData (by
            simpa [selectedData] using processedEq) (by
            simpa [selectedData] using scratchEq)
        let emittedData : TapeData Data :=
          { selectedData with
            processed := () :: List.replicate firstPosition ()
            scratch := []
            outputReverse :=
              ((positionTokens recipes firstPosition).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  selectedData.outputReverse }
        have firstTwo := EvalsToInTime.trans
          (TM2.step (program selected recipes ending))
          1 (templateTime recipes firstPosition)
          (beginPositionCfg data) (executeCfg ⟨0, recipesNonempty⟩ selectedData)
          (some (beginPositionCfg emittedData)) first (by
            simpa [emittedData] using templateRun)
        have rest := induction (firstPosition + 1) emittedData rfl (by
          simp [emittedData, List.replicate_succ]) rfl
        have composed := EvalsToInTime.trans
          (TM2.step (program selected recipes ending))
          (templateTime recipes firstPosition + 1)
          (positionRangeTime recipes (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg emittedData)
          (some (emitEndingCfg
            { emittedData with
              remaining := []
              processed :=
                List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes (firstPosition + 1) count).map
                  fun token =>
                    (Sum.inr token : Workspace Data)).reverse ++
                      emittedData.outputReverse }))
          firstTwo rest
        convert composed using 1
        · simp [emittedData, selectedData, positionRangeTokens_succ,
            List.map_append, List.reverse_append, List.append_assoc]
          congr 3
          omega
        · simp [positionRangeTime]
          omega

def reverseOutput_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (word : List (Workspace Data)) (data : TapeData Data)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil selected recipes ending data
          outputReverseEq)
      convert step using 1 <;> simp
  | cons workspace word induction =>
      let nextData : TapeData Data :=
        { data with
          outputReverse := word
          output := workspace :: data.output }
      have first := oneStep
        (step_reverseOutput_cons selected recipes ending data workspace word
          outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        1 (word.length + 1) (reverseOutputCfg data)
        (reverseOutputCfg nextData)
        (some (haltDataCfg
          { nextData with
            outputReverse := []
            output := word.reverse ++ nextData.output }))
        first rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def clearProcessed_evalsInTime {Data : Type} [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime (TM2.step (program selected recipes ending))
      (clearProcessedCfg data)
      (some (reverseOutputCfg { data with processed := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearProcessed_nil selected recipes ending data processedEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with processed := word }
      have first := oneStep
        (step_clearProcessed_cons selected recipes ending data word
          processedEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program selected recipes ending))
        1 (word.length + 1) (clearProcessedCfg data)
        (clearProcessedCfg nextData)
        (some (reverseOutputCfg { nextData with processed := [] }))
        first rest
      simpa using composed

def totalTime {Data : Type} (selected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : Nat :=
  workspace.length + 1 +
    positionRangeTime recipes 0 (selectedCount selected workspace) +
    1 + (selectedCount selected workspace + 1) +
    (appendedOutput selected recipes ending workspace).length + 1

theorem initList_eq_scanCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    initList (machine Data selected recipes ending) workspace =
      scanCfg ⟨workspace, [], [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (output : List (Workspace Data)) :
    haltList (machine Data selected recipes ending) output =
      haltCfg (recipes := recipes) output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem haltDataCfg_empty_eq_haltCfg {Data : Type}
    {recipes : List Recipe} (output : List (Workspace Data)) :
    haltDataCfg (recipes := recipes) ⟨[], [], [], [], [], output⟩ =
      haltCfg (recipes := recipes) output :=
  rfl

def machine_outputsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (selected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    TM2OutputsInTime (machine Data selected recipes ending) workspace
      (some (appendedOutput selected recipes ending workspace))
      (totalTime selected recipes ending workspace) := by
  let count := selectedCount selected workspace
  let emitted := positionRangeTokens recipes 0 count
  let initial : TapeData Data := ⟨workspace, [], [], [], [], []⟩
  let scanned : TapeData Data :=
    ⟨[], List.replicate count (), [], [], workspace.reverse, []⟩
  let positioned : TapeData Data :=
    ⟨[], [], List.replicate count (), [],
      (emitted.map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse,
      []⟩
  let ended : TapeData Data :=
    ⟨[], [], List.replicate count (), [],
      (ending.map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++
        (emitted.map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse,
      []⟩
  let cleared : TapeData Data := { ended with processed := [] }
  have scanRun := scan_evalsInTime selected recipes ending workspace initial rfl
  have positionsRun := positions_evalsInTime selected recipes ending 0 count
    scanned rfl rfl rfl
  have firstTwo := EvalsToInTime.trans
    (TM2.step (program selected recipes ending))
    (workspace.length + 1) (positionRangeTime recipes 0 count)
    (scanCfg initial) (beginPositionCfg scanned)
    (some (emitEndingCfg positioned))
    (by simpa [initial, scanned, count] using scanRun)
    (by simpa [scanned, positioned, emitted, count] using positionsRun)
  have endingRun := oneStep (step_emitEnding selected recipes ending positioned)
  have firstThree := EvalsToInTime.trans
    (TM2.step (program selected recipes ending))
    (positionRangeTime recipes 0 count + (workspace.length + 1)) 1
    (scanCfg initial) (emitEndingCfg positioned)
    (some (clearProcessedCfg ended)) firstTwo (by
      simpa [ended, positioned, List.append_assoc] using endingRun)
  have clearRun := clearProcessed_evalsInTime selected recipes ending
    (List.replicate count ()) ended rfl
  have firstFour := EvalsToInTime.trans
    (TM2.step (program selected recipes ending))
    (1 + (positionRangeTime recipes 0 count + (workspace.length + 1)))
    (count + 1)
    (scanCfg initial) (clearProcessedCfg ended)
    (some (reverseOutputCfg cleared)) firstThree (by
      simpa [cleared] using clearRun)
  have endedEq : ended.outputReverse =
      (appendedOutput selected recipes ending workspace).reverse := by
    simp [ended, emitted, count, appendedOutput, List.map_append,
      List.reverse_append, List.append_assoc]
  have reverseRun := reverseOutput_evalsInTime selected recipes ending
    (appendedOutput selected recipes ending workspace).reverse cleared (by
      simpa [cleared] using endedEq)
  have whole := EvalsToInTime.trans
    (TM2.step (program selected recipes ending))
    (count + 1 +
      (1 + (positionRangeTime recipes 0 count + (workspace.length + 1))))
    ((appendedOutput selected recipes ending workspace).length + 1)
    (scanCfg initial) (reverseOutputCfg cleared)
    (some (haltDataCfg
      ⟨[], [], [], [], [],
        appendedOutput selected recipes ending workspace⟩))
    firstFour (by
      simpa [cleared, ended] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program selected recipes ending)))^[whole.steps]
        (some (initList (machine Data selected recipes ending) workspace)) =
          some (haltList (machine Data selected recipes ending)
            (appendedOutput selected recipes ending workspace))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg,
      ← haltDataCfg_empty_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime, count]
      omega)

end AffineTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
