/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFBivariateProgramTemplates

/-!
# Bivariate affine-position template emitter

This machine realizes `BivariateProgramTemplates.Recipe`.  It counts one
selected class into a persistent unary first counter and a second class into
the position loop.  Every affine atom rescans both counters, emitting exactly
`base + firstStride × first + secondStride × position` units while
restoring both counters.  The complete input is retained and the emitted token
stream is appended in order.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace PeriodicCNF
namespace BivariateTemplateEmitterMachine

open UnaryProgramTokens
open BivariateProgramTemplates

abbrev Recipe := BivariateProgramTemplates.Recipe

def positionTokens (recipes : List Recipe) (first position : Nat) :
    List Token :=
  BivariateProgramTemplates.positionTokens recipes first position

/-- Token fragment contributed by consecutive positions beginning at
`firstPosition`. -/
def positionRangeTokens (recipes : List Recipe)
    (first firstPosition : Nat) : Nat → List Token
  | 0 => []
  | count + 1 =>
      positionTokens recipes first firstPosition ++
        positionRangeTokens recipes first (firstPosition + 1) count

@[simp]
theorem positionRangeTokens_zero (recipes : List Recipe)
    (first firstPosition : Nat) :
    positionRangeTokens recipes first firstPosition 0 = [] :=
  rfl

theorem positionRangeTokens_succ (recipes : List Recipe)
    (first firstPosition count : Nat) :
    positionRangeTokens recipes first firstPosition (count + 1) =
      positionTokens recipes first firstPosition ++
        positionRangeTokens recipes first (firstPosition + 1) count :=
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
def appendedOutput {Data : Type} (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : List (Workspace Data) :=
  workspace ++
    (positionRangeTokens recipes (selectedCount firstSelected workspace) 0
        (selectedCount secondSelected workspace) ++
      ending).map Sum.inr

inductive Stack
  | input
  | first
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
  | scanPosition (index : Fin recipeCount)
  | restorePosition (index : Fin recipeCount)
  | emitEnding
  | clearFirst
  | clearProcessed
  | reverseOutput
  deriving Fintype

abbrev State (Data : Type) := Option (Workspace Data ⊕ Unit)

abbrev Alphabet (Data : Type) : Stack → Type
  | .input | .outputReverse | .output => Workspace Data
  | .first | .remaining | .processed | .scratch => Unit

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
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token) :
    Label recipes.length →
      TM2.Stmt (Alphabet Data) (Label recipes.length) (State Data)
  | .scan =>
      .pop .input (fun _ workspace => workspace.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .beginPosition)
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
      | .atom base _firstStride _secondStride =>
          pushAtomUnits base
            (.load (fun _ => none)
              (.goto fun _ => .scanFirst index))
  | .scanFirst index =>
      .pop .first (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restoreFirst index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none)
                  (.goto fun _ => .scanFirst index)
            | .atom _ firstStride _ =>
                pushAtomUnits firstStride
                  (.load (fun _ => none)
                    (.goto fun _ => .scanFirst index)))))
  | .restoreFirst index =>
      .pop .scratch (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .scanPosition index)
          (.push .first (fun _ => ())
            (.load (fun _ => none)
              (.goto fun _ => .restoreFirst index))))
  | .scanPosition index =>
      .pop .processed (fun _ unit => unit.map Sum.inr)
        (.branch Option.isNone
          (.goto fun _ => .restorePosition index)
          (.push .scratch (fun _ => ())
            (match recipes.get index with
            | .fixed _ =>
                .load (fun _ => none)
                  (.goto fun _ => .scanPosition index)
            | .atom _ _ secondStride =>
                pushAtomUnits secondStride
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
          (.goto fun _ => .clearProcessed)
          (.load (fun _ => none) (.goto fun _ => .clearFirst)))
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
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token) :
    FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet Data
  Λ := Label recipes.length
  main := .scan
  σ := State Data
  initialState := none
  m := program firstSelected secondSelected recipes ending

structure TapeData (Data : Type) where
  input : List (Workspace Data)
  first : List Unit
  remaining : List Unit
  processed : List Unit
  scratch : List Unit
  outputReverse : List (Workspace Data)
  output : List (Workspace Data)

def tapes {Data : Type} (data : TapeData Data) :
    ∀ stack, List (Alphabet Data stack)
  | .input => data.input
  | .first => data.first
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

def scanFirstCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanFirst index) none data

def restoreFirstCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restoreFirst index) none data

def scanPositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.scanPosition index) none data

def restorePositionCfg {Data : Type} {recipes : List Recipe}
    (index : Fin recipes.length) (data : TapeData Data) :=
  cfg (.restorePosition index) none data

def emitEndingCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .emitEnding none data

def clearFirstCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearFirst none data

def clearProcessedCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .clearProcessed none data

def reverseOutputCfg {Data : Type} {recipes : List Recipe}
    (data : TapeData Data) :=
  cfg (recipes := recipes) .reverseOutput none data

def haltCfg {Data : Type} {recipes : List Recipe}
    (output : List (Workspace Data)) :
    TM2.Cfg (Alphabet Data) (Label recipes.length) (State Data) :=
  ⟨none, none, tapes ⟨[], [], [], [], [], [], output⟩⟩

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
theorem update_tapes_first {Data : Type} (data : TapeData Data)
    (value : List Unit) :
    Function.update (tapes data) Stack.first value =
      tapes { data with first := value } := by
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
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (inputEq : data.input = []) :
    TM2.step (program firstSelected secondSelected recipes ending) (scanCfg data) =
      some (beginPositionCfg { data with input := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change input = [] at inputEq
  subst input
  simp [TM2.step, program, scanCfg, beginPositionCfg, cfg, tapes]

theorem step_scan_both {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected firstSelected workspace = true)
    (secondEq : dataSelected secondSelected workspace = true) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          first := () :: data.first
          remaining := () :: data.remaining
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at firstEq

theorem step_scan_first {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected firstSelected workspace = true)
    (secondEq : dataSelected secondSelected workspace = false) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          first := () :: data.first
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at firstEq

theorem step_scan_second {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected firstSelected workspace = false)
    (secondEq : dataSelected secondSelected workspace = true) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          remaining := () :: data.remaining
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [dataSelected] at secondEq

theorem step_scan_neither {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (inputEq : data.input = workspace :: tail)
    (firstEq : dataSelected firstSelected workspace = false)
    (secondEq : dataSelected secondSelected workspace = false) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (scanCfg data) =
      some (scanCfg
        { data with
          input := tail
          outputReverse := workspace :: data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change input = workspace :: tail at inputEq
  subst input
  rcases workspace with dataValue | token
  · simp_all [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]
  · simp [TM2.step, program, scanCfg, cfg, tapes,
      workspaceFromState, stateSelected, dataSelected]

theorem step_beginPosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (remainingEq : data.remaining = []) :
    TM2.step (program firstSelected secondSelected recipes ending) (beginPositionCfg data) =
      some (emitEndingCfg { data with remaining := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change remaining = [] at remainingEq
  subst remaining
  simp [TM2.step, program, beginPositionCfg, emitEndingCfg, cfg, tapes]

theorem step_beginPosition_cons_nonempty {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (nonempty : 0 < recipes.length) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending) (beginPositionCfg data) =
      some (executeCfg ⟨0, nonempty⟩
        { data with remaining := tail }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, nonempty,
    beginPositionCfg, executeCfg, cfg, tapes]

theorem step_beginPosition_cons_empty {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (empty : recipes = []) (data : TapeData Data)
    (tail : List Unit) (remainingEq : data.remaining = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending) (beginPositionCfg data) =
      some (beginPositionCfg
        { data with
          remaining := tail
          processed := () :: data.processed }) := by
  subst recipes
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change remaining = () :: tail at remainingEq
  subst remaining
  simp [TM2.step, program, beginTemplate, beginPositionCfg, cfg, tapes]

theorem step_execute_fixed {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (token : Token) (data : TapeData Data)
    (recipeEq : recipes.get index = .fixed token) :
    TM2.step (program firstSelected secondSelected recipes ending) (executeCfg index data) =
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
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base firstStride secondStride : Nat)
    (data : TapeData Data)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride) :
    TM2.step (program firstSelected secondSelected recipes ending) (executeCfg index data) =
      some (scanFirstCfg index
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  simp only [TM2.step, program, executeCfg, scanFirstCfg, cfg]
  rw [recipeEq, stepAux_pushAtomUnits]
  rfl

theorem step_scanFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (firstEq : data.first = []) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (scanFirstCfg index data) =
      some (restoreFirstCfg index { data with first := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, scanFirstCfg, restoreFirstCfg, cfg, tapes]

theorem step_scanFirst_cons_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base firstStride secondStride : Nat)
    (data : TapeData Data) (tail : List Unit)
    (firstEq : data.first = () :: tail)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (scanFirstCfg index data) =
      some (scanFirstCfg index
        { data with
          first := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change first = () :: tail at firstEq
  subst first
  simp only [TM2.step, program, scanFirstCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_first, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restoreFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (restoreFirstCfg index data) =
      some (scanPositionCfg index { data with scratch := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  simp [TM2.step, program, restoreFirstCfg, scanPositionCfg, cfg, tapes]

theorem step_restoreFirst_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (restoreFirstCfg index data) =
      some (restoreFirstCfg index
        { data with
          first := () :: data.first
          scratch := tail }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restoreFirstCfg, cfg, tapes]

theorem step_scanPosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (processedEq : data.processed = []) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (scanPositionCfg index data) =
      some (restorePositionCfg index { data with processed := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, scanPositionCfg, restorePositionCfg, cfg, tapes]

theorem step_scanPosition_cons_atom {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base firstStride secondStride : Nat)
    (data : TapeData Data)
    (tail : List Unit) (processedEq : data.processed = () :: tail)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (scanPositionCfg index data) =
      some (scanPositionCfg index
        { data with
          processed := tail
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp only [TM2.step, program, scanPositionCfg, cfg]
  rw [recipeEq]
  simp only [TM2.stepAux, update_tapes_processed, update_tapes_scratch]
  rw [stepAux_pushAtomUnits]
  rfl

theorem step_restorePosition_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data)
    (scratchEq : data.scratch = []) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (restorePositionCfg index data) =
      some (afterRecipeCfg recipes index { data with scratch := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change scratch = [] at scratchEq
  subst scratch
  by_cases nextExists : index.val + 1 < recipes.length
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, executeCfg, cfg, tapes]
  · simp [TM2.step, program, restorePositionCfg, afterRecipe,
      afterRecipeCfg, nextExists, beginPositionCfg, cfg, tapes]

theorem step_restorePosition_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (data : TapeData Data) (tail : List Unit)
    (scratchEq : data.scratch = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending)
      (restorePositionCfg index data) =
      some (restorePositionCfg index
        { data with
          processed := () :: data.processed
          scratch := tail }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change scratch = () :: tail at scratchEq
  subst scratch
  simp [TM2.step, program, restorePositionCfg, cfg, tapes]

theorem step_emitEnding {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) :
    TM2.step (program firstSelected secondSelected recipes ending) (emitEndingCfg data) =
      some (clearFirstCfg
        { data with
          outputReverse :=
            (ending.map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }) := by
  simp only [TM2.step, program, emitEndingCfg, clearFirstCfg, cfg]
  rw [stepAux_pushTokens]
  rfl

theorem step_clearFirst_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (firstEq : data.first = []) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (clearFirstCfg data) =
      some (clearProcessedCfg { data with first := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change first = [] at firstEq
  subst first
  simp [TM2.step, program, clearFirstCfg, clearProcessedCfg, cfg, tapes]

theorem step_clearFirst_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (firstEq : data.first = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending)
        (clearFirstCfg data) =
      some (clearFirstCfg { data with first := tail }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change first = () :: tail at firstEq
  subst first
  simp [TM2.step, program, clearFirstCfg, cfg, tapes]

theorem step_clearProcessed_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (processedEq : data.processed = []) :
    TM2.step (program firstSelected secondSelected recipes ending) (clearProcessedCfg data) =
      some (reverseOutputCfg { data with processed := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change processed = [] at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, reverseOutputCfg, cfg, tapes]

theorem step_clearProcessed_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (tail : List Unit)
    (processedEq : data.processed = () :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending) (clearProcessedCfg data) =
      some (clearProcessedCfg { data with processed := tail }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change processed = () :: tail at processedEq
  subst processed
  simp [TM2.step, program, clearProcessedCfg, cfg, tapes]

theorem step_reverseOutput_nil {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (outputReverseEq : data.outputReverse = []) :
    TM2.step (program firstSelected secondSelected recipes ending) (reverseOutputCfg data) =
      some (haltDataCfg { data with outputReverse := [] }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
  change outputReverse = [] at outputReverseEq
  subst outputReverse
  simp [TM2.step, program, reverseOutputCfg, haltDataCfg, cfg, tapes]

theorem step_reverseOutput_cons {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (data : TapeData Data) (workspace : Workspace Data)
    (tail : List (Workspace Data))
    (outputReverseEq : data.outputReverse = workspace :: tail) :
    TM2.step (program firstSelected secondSelected recipes ending) (reverseOutputCfg data) =
      some (reverseOutputCfg
        { data with
          outputReverse := tail
          output := workspace :: data.output }) := by
  rcases data with
    ⟨input, first, remaining, processed, scratch, outputReverse, output⟩
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
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspaces : List (Workspace Data)) (data : TapeData Data)
    (inputEq : data.input = workspaces) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (scanCfg data)
      (some (beginPositionCfg
        { data with
          input := []
          first :=
            List.replicate (selectedCount firstSelected workspaces) () ++
              data.first
          remaining :=
            List.replicate (selectedCount secondSelected workspaces) () ++
              data.remaining
          outputReverse := workspaces.reverse ++ data.outputReverse }))
      (workspaces.length + 1) := by
  induction workspaces generalizing data with
  | nil =>
      have step := oneStep
        (step_scan_nil firstSelected secondSelected recipes ending data
          inputEq)
      convert step using 1 <;>
        simp [selectedCount,
          UnaryPolynomialPaddingMachine.selectedCount]
  | cons workspace workspaces induction =>
      by_cases firstEq : dataSelected firstSelected workspace = true
      · by_cases secondEq : dataSelected secondSelected workspace = true
        · let nextData : TapeData Data :=
            { data with
              input := workspaces
              first := () :: data.first
              remaining := () :: data.remaining
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_both firstSelected secondSelected recipes ending data
              workspace workspaces inputEq firstEq secondEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans
            (TM2.step
              (program firstSelected secondSelected recipes ending))
            1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
            (some (beginPositionCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstEq, secondEq, if_true]
            rw [show 1 + selectedCount firstSelected workspaces =
                  selectedCount firstSelected workspaces + 1 by omega,
              show 1 + selectedCount secondSelected workspaces =
                  selectedCount secondSelected workspaces + 1 by omega,
              replicate_unit_add_one_right,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
        · have secondFalse :
              dataSelected secondSelected workspace = false :=
            Bool.eq_false_of_not_eq_true secondEq
          let nextData : TapeData Data :=
            { data with
              input := workspaces
              first := () :: data.first
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_first firstSelected secondSelected recipes ending data
              workspace workspaces inputEq firstEq secondFalse)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans
            (TM2.step
              (program firstSelected secondSelected recipes ending))
            1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
            (some (beginPositionCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstEq, if_true, secondFalse]
            rw [show 1 + selectedCount firstSelected workspaces =
                  selectedCount firstSelected workspaces + 1 by omega,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
      · have firstFalse : dataSelected firstSelected workspace = false :=
          Bool.eq_false_of_not_eq_true firstEq
        by_cases secondEq : dataSelected secondSelected workspace = true
        · let nextData : TapeData Data :=
            { data with
              input := workspaces
              remaining := () :: data.remaining
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_second firstSelected secondSelected recipes ending data
              workspace workspaces inputEq firstFalse secondEq)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans
            (TM2.step
              (program firstSelected secondSelected recipes ending))
            1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
            (some (beginPositionCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp only [selectedCount_cons, firstFalse, secondEq, if_true]
            rw [show 1 + selectedCount secondSelected workspaces =
                  selectedCount secondSelected workspaces + 1 by omega,
              replicate_unit_add_one_right]
            simp [nextData, List.reverse_cons, List.append_assoc]
          · simp
        · have secondFalse :
              dataSelected secondSelected workspace = false :=
            Bool.eq_false_of_not_eq_true secondEq
          let nextData : TapeData Data :=
            { data with
              input := workspaces
              outputReverse := workspace :: data.outputReverse }
          have firstStep := oneStep
            (step_scan_neither firstSelected secondSelected recipes ending
              data workspace workspaces inputEq firstFalse secondFalse)
          have rest := induction nextData rfl
          have composed := EvalsToInTime.trans
            (TM2.step
              (program firstSelected secondSelected recipes ending))
            1 (workspaces.length + 1) (scanCfg data) (scanCfg nextData)
            (some (beginPositionCfg
              { nextData with
                input := []
                first := List.replicate
                    (selectedCount firstSelected workspaces) () ++
                  nextData.first
                remaining := List.replicate
                    (selectedCount secondSelected workspaces) () ++
                  nextData.remaining
                outputReverse :=
                  workspaces.reverse ++ nextData.outputReverse }))
            firstStep rest
          convert composed using 1
          · simp [nextData, selectedCount_cons, firstFalse, secondFalse,
              List.reverse_cons, List.append_assoc]
          · simp

def scanFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (base firstStride secondStride : Nat)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride)
    (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (scanFirstCfg index data)
      (some (restoreFirstCfg index
        { data with
          first := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (firstStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanFirst_nil firstSelected secondSelected recipes ending index
          data firstEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate firstStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanFirst_cons_atom firstSelected secondSelected recipes ending
          index base firstStride secondStride data word firstEq recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (scanFirstCfg index data)
        (scanFirstCfg index nextData)
        (some (restoreFirstCfg index
          { nextData with
            first := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (firstStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show firstStride * (word.length + 1) =
            firstStride * word.length + firstStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restoreFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (restoreFirstCfg index data)
      (some (scanPositionCfg index
        { data with
          first := word.reverse ++ data.first
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restoreFirst_nil firstSelected secondSelected recipes ending
          index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          first := () :: data.first
          scratch := word }
      have firstStep := oneStep
        (step_restoreFirst_cons firstSelected secondSelected recipes ending
          index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (restoreFirstCfg index data)
        (restoreFirstCfg index nextData)
        (some (scanPositionCfg index
          { nextData with
            first := word.reverse ++ nextData.first
            scratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def scanPosition_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (ending : List Token) (index : Fin recipes.length)
    (base firstStride secondStride : Nat)
    (recipeEq : recipes.get index =
      .atom base firstStride secondStride)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime
      (TM2.step (program firstSelected secondSelected recipes ending))
      (scanPositionCfg index data)
      (some (restorePositionCfg index
        { data with
          processed := []
          scratch := word.reverse ++ data.scratch
          outputReverse :=
            List.replicate (secondStride * word.length)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_scanPosition_nil firstSelected secondSelected recipes ending
          index data processedEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := word
          scratch := () :: data.scratch
          outputReverse :=
            List.replicate secondStride
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have firstStep := oneStep
        (step_scanPosition_cons_atom firstSelected secondSelected recipes
          ending index base firstStride secondStride data word processedEq
          recipeEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (scanPositionCfg index data)
        (scanPositionCfg index nextData)
        (some (restorePositionCfg index
          { nextData with
            processed := []
            scratch := word.reverse ++ nextData.scratch
            outputReverse :=
              List.replicate (secondStride * word.length)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                nextData.outputReverse }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
        rw [show secondStride * (word.length + 1) =
            secondStride * word.length + secondStride by ring,
          List.replicate_add, List.append_assoc]
      · simp

def restorePosition_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (ending : List Token) (index : Fin recipes.length)
    (word : List Unit) (data : TapeData Data)
    (scratchEq : data.scratch = word) :
    EvalsToInTime
      (TM2.step (program firstSelected secondSelected recipes ending))
      (restorePositionCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          processed := word.reverse ++ data.processed
          scratch := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_restorePosition_nil firstSelected secondSelected recipes ending
          index data scratchEq)
      convert step using 1 <;> simp
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data :=
        { data with
          processed := () :: data.processed
          scratch := word }
      have firstStep := oneStep
        (step_restorePosition_cons firstSelected secondSelected recipes ending
          index data word scratchEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (restorePositionCfg index data)
        (restorePositionCfg index nextData)
        (some (afterRecipeCfg recipes index
          { nextData with
            processed := word.reverse ++ nextData.processed
            scratch := [] }))
        firstStep rest
      convert composed using 1
      · simp [nextData, List.reverse_cons, List.append_assoc]
      · simp

def recipeTime (first position : Nat) : Recipe → Nat
  | .fixed _ => 1
  | .atom _ _ _ => 2 * first + 2 * position + 5

def executeRecipe_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (first position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (executeCfg index data)
      (some (afterRecipeCfg recipes index
        { data with
          first := List.replicate first ()
          processed := List.replicate position ()
          scratch := []
          outputReverse :=
            ((Recipe.tokens first position (recipes.get index)).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeTime first position (recipes.get index)) := by
  cases recipeEq : recipes.get index with
  | fixed token =>
      have step := oneStep
        (step_execute_fixed firstSelected secondSelected recipes ending index
          token data recipeEq)
      convert step using 1 <;>
        simp [Recipe.tokens, recipeTime, firstEq, processedEq, scratchEq]
  | atom base firstStride secondStride =>
      let emittedData : TapeData Data :=
        { data with
          outputReverse :=
            List.replicate base
                (Sum.inr Token.atomUnit : Workspace Data) ++
              data.outputReverse }
      have executed := oneStep
        (step_execute_atom firstSelected secondSelected recipes ending index
          base firstStride secondStride data recipeEq)
      have scannedFirst := scanFirst_evalsInTime firstSelected secondSelected
        recipes ending index base firstStride secondStride recipeEq
        (List.replicate first ()) emittedData (by
          simpa [emittedData] using firstEq)
      let firstScannedData : TapeData Data :=
        { emittedData with
          first := []
          scratch := (List.replicate first ()).reverse
          outputReverse :=
            List.replicate (firstStride * first)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              emittedData.outputReverse }
      have executedAndScanned := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (first + 1) (executeCfg index data)
        (scanFirstCfg index emittedData)
        (some (restoreFirstCfg index firstScannedData)) executed (by
          simpa [firstScannedData, emittedData, scratchEq] using scannedFirst)
      have restoredFirst := restoreFirst_evalsInTime firstSelected
        secondSelected recipes ending index
        (List.replicate first ()).reverse firstScannedData rfl
      let firstRestoredData : TapeData Data :=
        { firstScannedData with
          first := List.replicate first ()
          scratch := [] }
      have throughFirstRaw := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        (first + 2) (first + 1) (executeCfg index data)
        (restoreFirstCfg index firstScannedData)
        (some (scanPositionCfg index firstRestoredData)) executedAndScanned
        (by
          convert restoredFirst using 1 <;>
            simp [firstRestoredData, firstScannedData])
      have throughFirst : EvalsToInTime
          (TM2.step (program firstSelected secondSelected recipes ending))
          (executeCfg index data)
          (some (scanPositionCfg index firstRestoredData))
          (2 * first + 3) := by
        convert throughFirstRaw using 1
        all_goals omega
      have scannedPosition := scanPosition_evalsInTime firstSelected
        secondSelected recipes ending index base firstStride secondStride
        recipeEq (List.replicate position ()) firstRestoredData (by
          simpa [emittedData] using processedEq)
      let positionScannedData : TapeData Data :=
        { firstRestoredData with
          processed := []
          scratch := (List.replicate position ()).reverse
          outputReverse :=
            List.replicate (secondStride * position)
                (Sum.inr Token.atomUnit : Workspace Data) ++
              firstRestoredData.outputReverse }
      have throughPositionScanRaw := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        (2 * first + 3) (position + 1) (executeCfg index data)
        (scanPositionCfg index firstRestoredData)
        (some (restorePositionCfg index positionScannedData)) throughFirst (by
          simpa [positionScannedData, firstRestoredData, firstScannedData,
            emittedData, scratchEq] using scannedPosition)
      have throughPositionScan : EvalsToInTime
          (TM2.step (program firstSelected secondSelected recipes ending))
          (executeCfg index data)
          (some (restorePositionCfg index positionScannedData))
          (2 * first + position + 4) := by
        convert throughPositionScanRaw using 1
        all_goals omega
      have restoredPosition := restorePosition_evalsInTime firstSelected
        secondSelected recipes ending index
        (List.replicate position ()).reverse positionScannedData rfl
      have whole := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        (2 * first + position + 4) (position + 1)
        (executeCfg index data)
        (restorePositionCfg index positionScannedData)
        (some (afterRecipeCfg recipes index
          { data with
            first := List.replicate first ()
            processed := List.replicate position ()
            scratch := []
            outputReverse :=
              List.replicate
                  (base + firstStride * first + secondStride * position)
                  (Sum.inr Token.atomUnit : Workspace Data) ++
                data.outputReverse }))
        throughPositionScan (by
          have outputEq :
              List.replicate
                    (base + firstStride * first + secondStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  data.outputReverse =
                List.replicate (secondStride * position)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                  (List.replicate (firstStride * first)
                    (Sum.inr Token.atomUnit : Workspace Data) ++
                    (List.replicate base
                      (Sum.inr Token.atomUnit : Workspace Data) ++
                      data.outputReverse)) := by
            rw [← List.append_assoc, ← List.append_assoc,
              ← List.replicate_add, ← List.replicate_add]
            congr 2
            ring
          convert restoredPosition using 1
          · simp [positionScannedData, firstRestoredData,
              firstScannedData, emittedData, outputEq]
          · simp)
      convert whole using 1
      · simp [Recipe.tokens]
      · simp [recipeTime]
        ring

def recipeSuffixTokens (recipes : List Recipe) (first position : Nat)
    (index : Fin recipes.length) : List Token :=
  (recipes.drop index.val).flatMap (Recipe.tokens first position)

theorem recipeSuffixTokens_eq (recipes : List Recipe) (first position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTokens recipes first position index =
      Recipe.tokens first position (recipes.get index) ++
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTokens recipes first position
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

def recipeSuffixTime (recipes : List Recipe) (first position : Nat)
    (index : Fin recipes.length) : Nat :=
  ((recipes.drop index.val).map (recipeTime first position)).sum

theorem recipeSuffixTime_eq (recipes : List Recipe) (first position : Nat)
    (index : Fin recipes.length) :
    recipeSuffixTime recipes first position index =
      recipeTime first position (recipes.get index) +
        if nextExists : index.val + 1 < recipes.length then
          recipeSuffixTime recipes first position
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
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (index : Fin recipes.length) (first position : Nat)
    (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (processedEq : data.processed = List.replicate position ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (executeCfg index data)
      (some (beginPositionCfg
        { data with
          first := List.replicate first ()
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes first position index).map fun token =>
              (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (recipeSuffixTime recipes first position index) := by
  have current := executeRecipe_evalsInTime firstSelected secondSelected
    recipes ending index first position data firstEq processedEq scratchEq
  by_cases nextExists : index.val + 1 < recipes.length
  · let nextIndex : Fin recipes.length :=
      ⟨index.val + 1, nextExists⟩
    let currentData : TapeData Data :=
      { data with
        first := List.replicate first ()
        processed := List.replicate position ()
        scratch := []
        outputReverse :=
          ((Recipe.tokens first position (recipes.get index)).map fun token =>
            (Sum.inr token : Workspace Data)).reverse ++
              data.outputReverse }
    have first' : EvalsToInTime
        (TM2.step (program firstSelected secondSelected recipes ending))
        (executeCfg index data) (some (executeCfg nextIndex currentData))
        (recipeTime first position (recipes.get index)) := by
      convert current using 1
      simp [afterRecipeCfg, nextExists, nextIndex, currentData]
    have rest := executeRecipes_evalsInTime firstSelected secondSelected
      recipes ending nextIndex first position currentData rfl rfl rfl
    have composed := EvalsToInTime.trans
      (TM2.step (program firstSelected secondSelected recipes ending))
      (recipeTime first position (recipes.get index))
      (recipeSuffixTime recipes first position nextIndex)
      (executeCfg index data) (executeCfg nextIndex currentData)
      (some (beginPositionCfg
        { currentData with
          processed := () :: List.replicate position ()
          scratch := []
          outputReverse :=
            ((recipeSuffixTokens recipes first position nextIndex).map fun token =>
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
        (TM2.step (program firstSelected secondSelected recipes ending))
        (executeCfg index data)
        (some (beginPositionCfg
          { data with
            first := List.replicate first ()
            processed := () :: List.replicate position ()
            scratch := []
            outputReverse :=
              ((Recipe.tokens first position (recipes.get index)).map
                fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  data.outputReverse }))
        (recipeTime first position (recipes.get index)) := by
      convert current using 1
      simp [afterRecipeCfg, nextExists]
    convert first' using 1
    · rw [recipeSuffixTokens_eq]
      simp [nextExists]
    · rw [recipeSuffixTime_eq]
      simp [nextExists]
termination_by recipes.length - index.val
decreasing_by omega

def templateTime (recipes : List Recipe) (first position : Nat) : Nat :=
  (recipes.map (recipeTime first position)).sum

@[simp]
theorem recipeSuffixTokens_zero (recipes : List Recipe) (first position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTokens recipes first position ⟨0, nonempty⟩ =
      positionTokens recipes first position := by
  simp [recipeSuffixTokens, positionTokens,
    BivariateProgramTemplates.positionTokens]

@[simp]
theorem recipeSuffixTime_zero (recipes : List Recipe) (first position : Nat)
    (nonempty : 0 < recipes.length) :
    recipeSuffixTime recipes first position ⟨0, nonempty⟩ =
      templateTime recipes first position := by
  simp [recipeSuffixTime, templateTime]

def positionRangeTime (recipes : List Recipe) (first firstPosition : Nat) :
    Nat → Nat
  | 0 => 1
  | count + 1 =>
      1 + templateTime recipes first firstPosition +
        positionRangeTime recipes first (firstPosition + 1) count

def positions_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (first firstPosition count : Nat) (data : TapeData Data)
    (firstEq : data.first = List.replicate first ())
    (remainingEq : data.remaining = List.replicate count ())
    (processedEq : data.processed = List.replicate firstPosition ())
    (scratchEq : data.scratch = []) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (beginPositionCfg data)
      (some (emitEndingCfg
        { data with
          first := List.replicate first ()
          remaining := []
          processed := List.replicate (firstPosition + count) ()
          scratch := []
          outputReverse :=
            ((positionRangeTokens recipes first firstPosition count).map
              fun token => (Sum.inr token : Workspace Data)).reverse ++
                data.outputReverse }))
      (positionRangeTime recipes first firstPosition count) := by
  induction count generalizing firstPosition data with
  | zero =>
      have step := oneStep
        (step_beginPosition_nil firstSelected secondSelected recipes ending
          data (by
          simpa using remainingEq))
      convert step using 1 <;>
        simp [positionRangeTime, firstEq, processedEq, scratchEq]
  | succ count induction =>
      by_cases recipesEmpty : recipes = []
      · have stepRun := oneStep
          (step_beginPosition_cons_empty firstSelected secondSelected recipes
            ending recipesEmpty data (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        let nextData : TapeData Data :=
          { data with
            remaining := List.replicate count ()
            processed := () :: data.processed }
        have rest := induction (firstPosition + 1) nextData (by
          simpa [nextData] using firstEq) rfl (by
            simpa [nextData, List.replicate_succ] using processedEq) (by
            simpa [nextData] using scratchEq)
        have composed := EvalsToInTime.trans
          (TM2.step (program firstSelected secondSelected recipes ending))
          1 (positionRangeTime recipes first (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg nextData)
          (some (emitEndingCfg
            { nextData with
              first := List.replicate first ()
              remaining := []
              processed :=
                List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes first (firstPosition + 1)
                    count).map
                  fun token =>
                    (Sum.inr token : Workspace Data)).reverse ++
                      nextData.outputReverse }))
          stepRun rest
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
        have stepRun := oneStep
          (step_beginPosition_cons_nonempty firstSelected secondSelected
            recipes ending recipesNonempty data (List.replicate count ()) (by
              simpa [List.replicate_succ] using remainingEq))
        have templateRun := executeRecipes_evalsInTime firstSelected
          secondSelected recipes ending ⟨0, recipesNonempty⟩ first
          firstPosition selectedData (by
            simpa [selectedData] using firstEq) (by
            simpa [selectedData] using processedEq) (by
            simpa [selectedData] using scratchEq)
        let emittedData : TapeData Data :=
          { selectedData with
            first := List.replicate first ()
            processed := () :: List.replicate firstPosition ()
            scratch := []
            outputReverse :=
              ((positionTokens recipes first firstPosition).map fun token =>
                (Sum.inr token : Workspace Data)).reverse ++
                  selectedData.outputReverse }
        have firstTwo := EvalsToInTime.trans
          (TM2.step (program firstSelected secondSelected recipes ending))
          1 (templateTime recipes first firstPosition)
          (beginPositionCfg data) (executeCfg ⟨0, recipesNonempty⟩ selectedData)
          (some (beginPositionCfg emittedData)) stepRun (by
            simpa [emittedData] using templateRun)
        have rest := induction (firstPosition + 1) emittedData rfl rfl (by
          simp [emittedData, List.replicate_succ]) rfl
        have composed := EvalsToInTime.trans
          (TM2.step (program firstSelected secondSelected recipes ending))
          (templateTime recipes first firstPosition + 1)
          (positionRangeTime recipes first (firstPosition + 1) count)
          (beginPositionCfg data) (beginPositionCfg emittedData)
          (some (emitEndingCfg
            { emittedData with
              first := List.replicate first ()
              remaining := []
              processed :=
                List.replicate (firstPosition + 1 + count) ()
              scratch := []
              outputReverse :=
                ((positionRangeTokens recipes first (firstPosition + 1)
                    count).map
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
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (word : List (Workspace Data)) (data : TapeData Data)
    (outputReverseEq : data.outputReverse = word) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (reverseOutputCfg data)
      (some (haltDataCfg
        { data with
          outputReverse := []
          output := word.reverse ++ data.output }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_reverseOutput_nil firstSelected secondSelected recipes ending data
          outputReverseEq)
      convert step using 1 <;> simp
  | cons workspace word induction =>
      let nextData : TapeData Data :=
        { data with
          outputReverse := word
          output := workspace :: data.output }
      have first := oneStep
        (step_reverseOutput_cons firstSelected secondSelected recipes ending data workspace word
          outputReverseEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
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

def clearFirst_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe)
    (ending : List Token) (word : List Unit) (data : TapeData Data)
    (firstEq : data.first = word) :
    EvalsToInTime
      (TM2.step (program firstSelected secondSelected recipes ending))
      (clearFirstCfg data)
      (some (clearProcessedCfg { data with first := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearFirst_nil firstSelected secondSelected recipes ending data
          firstEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with first := word }
      have firstStep := oneStep
        (step_clearFirst_cons firstSelected secondSelected recipes ending data
          word firstEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (clearFirstCfg data)
        (clearFirstCfg nextData)
        (some (clearProcessedCfg { nextData with first := [] }))
        firstStep rest
      simpa using composed

def clearProcessed_evalsInTime {Data : Type} [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (word : List Unit) (data : TapeData Data)
    (processedEq : data.processed = word) :
    EvalsToInTime (TM2.step (program firstSelected secondSelected recipes ending))
      (clearProcessedCfg data)
      (some (reverseOutputCfg { data with processed := [] }))
      (word.length + 1) := by
  induction word generalizing data with
  | nil =>
      have step := oneStep
        (step_clearProcessed_nil firstSelected secondSelected recipes ending data processedEq)
      simpa using step
  | cons element word induction =>
      have elementEq : element = () := Subsingleton.elim _ _
      subst element
      let nextData : TapeData Data := { data with processed := word }
      have first := oneStep
        (step_clearProcessed_cons firstSelected secondSelected recipes ending data word
          processedEq)
      have rest := induction nextData rfl
      have composed := EvalsToInTime.trans
        (TM2.step (program firstSelected secondSelected recipes ending))
        1 (word.length + 1) (clearProcessedCfg data)
        (clearProcessedCfg nextData)
        (some (reverseOutputCfg { nextData with processed := [] }))
        first rest
      simpa using composed

def totalTime {Data : Type} (firstSelected secondSelected : Data → Bool)
    (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) : Nat :=
  workspace.length + 1 +
    positionRangeTime recipes (selectedCount firstSelected workspace) 0
      (selectedCount secondSelected workspace) +
    1 + (selectedCount firstSelected workspace + 1) +
    (selectedCount secondSelected workspace + 1) +
    (appendedOutput firstSelected secondSelected recipes ending
      workspace).length + 1

theorem initList_eq_scanCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    initList
        (machine Data firstSelected secondSelected recipes ending) workspace =
      scanCfg ⟨workspace, [], [], [], [], [], []⟩ := by
  unfold initList machine scanCfg cfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

theorem haltList_eq_haltCfg {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (output : List (Workspace Data)) :
    haltList (machine Data firstSelected secondSelected recipes ending) output =
      haltCfg (recipes := recipes) output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

@[simp]
theorem haltDataCfg_empty_eq_haltCfg {Data : Type}
    {recipes : List Recipe} (output : List (Workspace Data)) :
    haltDataCfg (recipes := recipes) ⟨[], [], [], [], [], [], output⟩ =
      haltCfg (recipes := recipes) output :=
  rfl

def machine_outputsInTime {Data : Type} [Fintype Data] [Inhabited Data]
    (firstSelected secondSelected : Data → Bool) (recipes : List Recipe) (ending : List Token)
    (workspace : List (Workspace Data)) :
    TM2OutputsInTime
      (machine Data firstSelected secondSelected recipes ending) workspace
      (some (appendedOutput firstSelected secondSelected recipes ending
        workspace))
      (totalTime firstSelected secondSelected recipes ending workspace) := by
  let firstCount := selectedCount firstSelected workspace
  let secondCount := selectedCount secondSelected workspace
  let emitted := positionRangeTokens recipes firstCount 0 secondCount
  let initial : TapeData Data := ⟨workspace, [], [], [], [], [], []⟩
  let scanned : TapeData Data :=
    ⟨[], List.replicate firstCount (), List.replicate secondCount (), [],
      [], workspace.reverse, []⟩
  let positioned : TapeData Data :=
    ⟨[], List.replicate firstCount (), [],
      List.replicate secondCount (), [],
      (emitted.map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse,
      []⟩
  let ended : TapeData Data :=
    ⟨[], List.replicate firstCount (), [],
      List.replicate secondCount (), [],
      (ending.map fun token =>
        (Sum.inr token : Workspace Data)).reverse ++
        (emitted.map fun token =>
          (Sum.inr token : Workspace Data)).reverse ++ workspace.reverse,
      []⟩
  let firstCleared : TapeData Data := { ended with first := [] }
  let cleared : TapeData Data := { firstCleared with processed := [] }
  have scanRun := scan_evalsInTime firstSelected secondSelected recipes ending
    workspace initial rfl
  have positionsRun := positions_evalsInTime firstSelected secondSelected
    recipes ending firstCount 0 secondCount scanned rfl rfl rfl rfl
  have firstTwo := EvalsToInTime.trans
    (TM2.step (program firstSelected secondSelected recipes ending))
    (workspace.length + 1)
    (positionRangeTime recipes firstCount 0 secondCount)
    (scanCfg initial) (beginPositionCfg scanned)
    (some (emitEndingCfg positioned))
    (by simpa [initial, scanned, firstCount, secondCount] using scanRun)
    (by simpa [scanned, positioned, emitted, firstCount, secondCount]
      using positionsRun)
  have endingRun := oneStep
    (step_emitEnding firstSelected secondSelected recipes ending positioned)
  have firstThree := EvalsToInTime.trans
    (TM2.step (program firstSelected secondSelected recipes ending))
    (positionRangeTime recipes firstCount 0 secondCount +
      (workspace.length + 1)) 1
    (scanCfg initial) (emitEndingCfg positioned)
    (some (clearFirstCfg ended)) firstTwo (by
      simpa [ended, positioned, List.append_assoc] using endingRun)
  have clearFirstRun := clearFirst_evalsInTime firstSelected secondSelected
    recipes ending (List.replicate firstCount ()) ended rfl
  have firstFour := EvalsToInTime.trans
    (TM2.step (program firstSelected secondSelected recipes ending))
    (1 + (positionRangeTime recipes firstCount 0 secondCount +
      (workspace.length + 1)))
    (firstCount + 1)
    (scanCfg initial) (clearFirstCfg ended)
    (some (clearProcessedCfg firstCleared)) firstThree (by
      simpa [firstCleared] using clearFirstRun)
  have clearProcessedRun := clearProcessed_evalsInTime firstSelected
    secondSelected recipes ending (List.replicate secondCount ())
    firstCleared rfl
  have firstFive := EvalsToInTime.trans
    (TM2.step (program firstSelected secondSelected recipes ending))
    (firstCount + 1 +
      (1 + (positionRangeTime recipes firstCount 0 secondCount +
        (workspace.length + 1))))
    (secondCount + 1)
    (scanCfg initial) (clearProcessedCfg firstCleared)
    (some (reverseOutputCfg cleared)) firstFour (by
      simpa [cleared] using clearProcessedRun)
  have endedEq : ended.outputReverse =
      (appendedOutput firstSelected secondSelected recipes ending
        workspace).reverse := by
    simp [ended, emitted, firstCount, secondCount, appendedOutput,
      List.map_append,
      List.reverse_append, List.append_assoc]
  have reverseRun := reverseOutput_evalsInTime firstSelected secondSelected
    recipes ending
    (appendedOutput firstSelected secondSelected recipes ending
      workspace).reverse cleared (by
      simpa [cleared] using endedEq)
  have whole := EvalsToInTime.trans
    (TM2.step (program firstSelected secondSelected recipes ending))
    (secondCount + 1 + (firstCount + 1 +
      (1 + (positionRangeTime recipes firstCount 0 secondCount +
        (workspace.length + 1)))))
    ((appendedOutput firstSelected secondSelected recipes ending
      workspace).length + 1)
    (scanCfg initial) (reverseOutputCfg cleared)
    (some (haltCfg
      (appendedOutput firstSelected secondSelected recipes ending workspace)))
    firstFive (by
      simpa [cleared, firstCleared, ended, positioned, scanned, initial,
        haltDataCfg, haltCfg] using reverseRun)
  refine
    { steps := whole.steps
      evals_in_steps := ?_
      steps_le_m := ?_ }
  · change (flip bind (TM2.step (program firstSelected secondSelected recipes ending)))^[whole.steps]
        (some (initList
          (machine Data firstSelected secondSelected recipes ending)
          workspace)) =
          some (haltList
            (machine Data firstSelected secondSelected recipes ending)
            (appendedOutput firstSelected secondSelected recipes ending
              workspace))
    rw [initList_eq_scanCfg, haltList_eq_haltCfg]
    convert whole.evals_in_steps using 1
    rfl
  · exact whole.steps_le_m.trans (by
      simp [totalTime, firstCount, secondCount]
      omega)

end BivariateTemplateEmitterMachine
end PeriodicCNF
end LeanTrominoes
