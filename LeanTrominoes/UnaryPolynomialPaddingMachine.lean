import LeanTrominoes.FiniteBlockTransducer

/-!
# Unary polynomial padding machine

This finite machine evaluates a fixed coefficient list by Horner's rule on
the number of selected symbols in its input.  The input word is preserved in
the eventual output and the polynomial value is appended as unary padding.

The periodic-CNF request generator uses this with the native field delimiter
as the selected symbol.  Thus a source field stream is retained verbatim while
the source decider's space polynomial is materialized as a physical loop
counter.
-/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPolynomialPaddingMachine

inductive Side
  | first
  | second
  deriving DecidableEq, Fintype

@[simp]
def Side.swap : Side → Side
  | .first => .second
  | .second => .first

@[simp]
theorem Side.swap_swap (side : Side) : side.swap.swap = side := by
  cases side <;> rfl

inductive Stack
  | source
  | sourceReverse
  | first
  | second
  | outputReverse
  | output
  deriving DecidableEq, Fintype

@[simp]
def Side.stack : Side → Stack
  | .first => .first
  | .second => .second

@[simp]
theorem Side.stack_swap_ne (side : Side) :
    side.swap.stack ≠ side.stack := by
  cases side <;> decide

inductive Label (coefficientCount : Nat)
  | start
  | multiply (index : Fin coefficientCount) (current : Side)
  | scanSource (index : Fin coefficientCount) (current : Side)
  | restoreSource (index : Fin coefficientCount) (current : Side)
  | emitSource (result : Side)
  | emitPadding (result : Side)
  | reverseOutput
  deriving Fintype

abbrev State (Source : Type) := Option (Source ⊕ Unit)

abbrev Alphabet (Source : Type) : Stack → Type
  | .source | .sourceReverse => Source
  | .first | .second => Unit
  | .outputReverse | .output => Source ⊕ Unit

def coefficientAt (coefficients : List Nat)
    (index : Fin coefficients.length) : Nat :=
  coefficients.reverse.get
    ⟨index.val, by simpa using index.isLt⟩

def afterCoefficient (coefficients : List Nat)
    (index : Fin coefficients.length) (current : Side) :
    Label coefficients.length :=
  if nextExists : index.val + 1 < coefficients.length then
    .multiply ⟨index.val + 1, nextExists⟩ current.swap
  else
    .emitSource current.swap

def unitAtSide {Source : Type} (side : Side) :
    Alphabet Source side.stack := by
  cases side <;> exact ()

def pushUnits {Source : Type} {coefficientCount : Nat}
    (side : Side) : Nat →
      TM2.Stmt (Alphabet Source) (Label coefficientCount) (State Source) →
      TM2.Stmt (Alphabet Source) (Label coefficientCount) (State Source)
  | 0, next => next
  | count + 1, next =>
      .push side.stack (fun _ => unitAtSide side)
        (pushUnits side count next)

def sourceFromState {Source : Type} [Inhabited Source] :
    State Source → Source
  | some (.inl source) => source
  | _ => default

def outputFromState {Source : Type} [Inhabited Source] :
    State Source → Source ⊕ Unit
  | some value => value
  | none => .inr ()

/-- Horner evaluator.  `coefficients` are in increasing-degree order, so the
machine consumes their reverse. -/
def program {Source : Type} [Inhabited Source]
    (selected : Source → Bool) (coefficients : List Nat) :
    Label coefficients.length →
      TM2.Stmt (Alphabet Source) (Label coefficients.length)
        (State Source)
  | .start =>
      if nonempty : 0 < coefficients.length then
        .goto fun _ => .multiply ⟨0, nonempty⟩ .first
      else
        .goto fun _ => .emitSource .first
  | .multiply index current =>
      .pop current.stack (fun _ value => value.map fun _ => Sum.inr ())
        (.branch Option.isNone
          (pushUnits current.swap (coefficientAt coefficients index)
            (.load (fun _ => none)
              (.goto fun _ => afterCoefficient coefficients index current)))
          (.load (fun _ => none)
            (.goto fun _ => .scanSource index current)))
  | .scanSource index current =>
      .pop .source (fun _ value => value.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .restoreSource index current)
          (.branch (fun state =>
              match state with
              | some (.inl source) => selected source
              | _ => false)
            (.push current.swap.stack (fun _ => unitAtSide current.swap)
              (.push .sourceReverse sourceFromState
                (.load (fun _ => none)
                  (.goto fun _ => .scanSource index current))))
            (.push .sourceReverse sourceFromState
              (.load (fun _ => none)
                (.goto fun _ => .scanSource index current)))))
  | .restoreSource index current =>
      .pop .sourceReverse (fun _ value => value.map Sum.inl)
        (.branch Option.isNone
          (.load (fun _ => none)
            (.goto fun _ => .multiply index current))
          (.push .source sourceFromState
            (.load (fun _ => none)
              (.goto fun _ => .restoreSource index current))))
  | .emitSource result =>
      .pop .source (fun _ value => value.map Sum.inl)
        (.branch Option.isNone
          (.load (fun _ => none)
            (.goto fun _ => .emitPadding result))
          (.push .outputReverse outputFromState
            (.load (fun _ => none)
              (.goto fun _ => .emitSource result))))
  | .emitPadding result =>
      .pop result.stack (fun _ value => value.map fun _ => Sum.inr ())
        (.branch Option.isNone
          (.load (fun _ => none)
            (.goto fun _ => .reverseOutput))
          (.push .outputReverse outputFromState
            (.load (fun _ => none)
              (.goto fun _ => .emitPadding result))))
  | .reverseOutput =>
      .pop .outputReverse (fun _ value => value)
        (.branch Option.isNone
          .halt
          (.push .output outputFromState
            (.load (fun _ => none)
              (.goto fun _ => .reverseOutput))))

abbrev machine (Source : Type) [Fintype Source] [Inhabited Source]
    (selected : Source → Bool) (coefficients : List Nat) : FinTM2 where
  K := Stack
  k₀ := .source
  k₁ := .output
  Γ := Alphabet Source
  Λ := Label coefficients.length
  main := .start
  σ := State Source
  initialState := none
  m := program selected coefficients

/-- Number of selected symbols in a source word. -/
def selectedCount {Source : Type} (selected : Source → Bool) :
    List Source → Nat
  | [] => 0
  | source :: sources =>
      (if selected source then 1 else 0) + selectedCount selected sources

@[simp]
theorem selectedCount_cons {Source : Type} (selected : Source → Bool)
    (source : Source) (sources : List Source) :
    selectedCount selected (source :: sources) =
      (if selected source then 1 else 0) +
        selectedCount selected sources := rfl

/-- Evaluation of increasing-degree coefficients by reverse Horner fold. -/
def evalCoefficients (coefficients : List Nat) (input : Nat) : Nat :=
  coefficients.reverse.foldl (fun accumulator coefficient =>
    accumulator * input + coefficient) 0

/-- Semantic output: the retained source word followed by unary padding. -/
def paddedOutput {Source : Type} (selected : Source → Bool)
    (coefficients : List Nat)
    (sources : List Source) : List (Source ⊕ Unit) :=
  sources.map Sum.inl ++
    List.replicate
      (evalCoefficients coefficients (selectedCount selected sources))
      (Sum.inr ())

/-- Accumulator after a given number of Horner coefficients.  Positions past
the coefficient list are harmlessly stationary. -/
def hornerAccumulator (coefficients : List Nat) (input : Nat) : Nat → Nat
  | 0 => 0
  | position + 1 =>
      if inRange : position < coefficients.length then
        hornerAccumulator coefficients input position * input +
          coefficientAt coefficients ⟨position, inRange⟩
      else
        hornerAccumulator coefficients input position

def sideAt : Nat → Side
  | 0 => .first
  | position + 1 => (sideAt position).swap

@[simp]
theorem sideAt_succ (position : Nat) :
    sideAt (position + 1) = (sideAt position).swap := rfl

/-- Exact statement-step allowance accumulated through a Horner prefix. -/
def hornerPrefixTime (coefficients : List Nat) (inputLength input : Nat) :
    Nat → Nat
  | 0 => 0
  | position + 1 =>
      hornerPrefixTime coefficients inputLength input position +
        hornerAccumulator coefficients input position *
          (2 * inputLength + 3) + 1

def tapes {Source : Type} (currentSide : Side)
    (source sourceReverse : List Source)
    (current next : List Unit)
    (outputReverse output : List (Source ⊕ Unit)) :
    ∀ stack, List (Alphabet Source stack)
  | .source => source
  | .sourceReverse => sourceReverse
  | .first => match currentSide with
      | .first => current
      | .second => next
  | .second => match currentSide with
      | .first => next
      | .second => current
  | .outputReverse => outputReverse
  | .output => output

def multiplyCfg {Source : Type} {coefficients : List Nat}
    (index : Fin coefficients.length) (currentSide : Side)
    (source : List Source) (current next : List Unit) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some (.multiply index currentSide), none,
    tapes currentSide source [] current next [] []⟩

def scanCfg {Source : Type} {coefficients : List Nat}
    (index : Fin coefficients.length) (currentSide : Side)
    (source sourceReverse : List Source) (current next : List Unit) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some (.scanSource index currentSide), none,
    tapes currentSide source sourceReverse current next [] []⟩

def restoreCfg {Source : Type} {coefficients : List Nat}
    (index : Fin coefficients.length) (currentSide : Side)
    (source sourceReverse : List Source) (current next : List Unit) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some (.restoreSource index currentSide), none,
    tapes currentSide source sourceReverse current next [] []⟩

def afterCoefficientCfg {Source : Type} (coefficients : List Nat)
    (index : Fin coefficients.length) (currentSide : Side)
    (source : List Source) (result : List Unit) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some (afterCoefficient coefficients index currentSide), none,
    tapes currentSide.swap source [] result [] [] []⟩

def emitSourceDataCfg {Source : Type} {coefficients : List Nat}
    (resultSide : Side) (source : List Source) (result : List Unit) :
    List (Source ⊕ Unit) →
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  fun outputReverse =>
    ⟨some (.emitSource resultSide), none,
      tapes resultSide source [] result [] outputReverse []⟩

def emitSourceCfg {Source : Type} {coefficients : List Nat}
    (resultSide : Side) (source : List Source) (result : List Unit) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  emitSourceDataCfg resultSide source result []

def emitPaddingCfg {Source : Type} {coefficients : List Nat}
    (resultSide : Side) (result : List Unit)
    (outputReverse : List (Source ⊕ Unit)) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some (.emitPadding resultSide), none,
    tapes resultSide [] [] result [] outputReverse []⟩

def reverseOutputCfg {Source : Type} {coefficients : List Nat}
    (outputReverse output : List (Source ⊕ Unit)) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨some .reverseOutput, none,
    tapes .first [] [] [] [] outputReverse output⟩

def haltCfg {Source : Type} {coefficients : List Nat}
    (output : List (Source ⊕ Unit)) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  ⟨none, none, tapes .first [] [] [] [] [] output⟩

/-- Milestone after `position` Horner coefficients. -/
def hornerCfg {Source : Type} (coefficients : List Nat) (input : Nat)
    (position : Nat) (source : List Source) :
    TM2.Cfg (Alphabet Source) (Label coefficients.length) (State Source) :=
  if inRange : position < coefficients.length then
    multiplyCfg ⟨position, inRange⟩ (sideAt position) source
      (List.replicate (hornerAccumulator coefficients input position) ()) []
  else
    emitSourceCfg (coefficients := coefficients) (sideAt position) source
      (List.replicate (hornerAccumulator coefficients input position) ())

theorem afterCoefficientCfg_eq_hornerCfg {Source : Type}
    (coefficients : List Nat) (input : Nat)
    (index : Fin coefficients.length) (source : List Source) :
    afterCoefficientCfg coefficients index (sideAt index.val) source
        (List.replicate
          (hornerAccumulator coefficients input index.val * input +
            coefficientAt coefficients index) ()) =
      hornerCfg coefficients input (index.val + 1) source := by
  unfold afterCoefficientCfg hornerCfg afterCoefficient
  simp only [sideAt_succ]
  rw [show hornerAccumulator coefficients input (index.val + 1) =
      hornerAccumulator coefficients input index.val * input +
        coefficientAt coefficients index by
    simp [hornerAccumulator, index.isLt]]
  split <;> rfl

theorem step_multiply_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources : List Source) (current next : List Unit) :
    TM2.step (program selected coefficients)
        (multiplyCfg index side sources (() :: current) next) =
      some (scanCfg index side sources [] current next) := by
  cases side <;>
    simp [TM2.step, program, multiplyCfg, scanCfg, tapes,
      Function.update] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update]

theorem step_scan_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (source : Source) (sources sourceReverse : List Source)
    (current next : List Unit) :
    TM2.step (program selected coefficients)
        (scanCfg index side (source :: sources) sourceReverse current next) =
      some (scanCfg index side sources (source :: sourceReverse) current
        (if selected source then () :: next else next)) := by
  cases side <;>
    cases choice : selected source <;>
    simp [TM2.step, program, scanCfg, tapes, choice, Function.update,
      sourceFromState, unitAtSide] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update,
      sourceFromState, unitAtSide]

theorem step_scan_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sourceReverse : List Source) (current next : List Unit) :
    TM2.step (program selected coefficients)
        (scanCfg index side [] sourceReverse current next) =
      some (restoreCfg index side [] sourceReverse current next) := by
  cases side <;>
    simp [TM2.step, program, scanCfg, restoreCfg, tapes, Function.update]

theorem step_restore_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (source : Source) (sources sourceReverse : List Source)
    (current next : List Unit) :
    TM2.step (program selected coefficients)
        (restoreCfg index side sources (source :: sourceReverse) current next) =
      some (restoreCfg index side (source :: sources) sourceReverse
        current next) := by
  cases side <;>
    simp [TM2.step, program, restoreCfg, tapes, Function.update,
      sourceFromState] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update,
      sourceFromState]

theorem step_restore_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources : List Source) (current next : List Unit) :
    TM2.step (program selected coefficients)
        (restoreCfg index side sources [] current next) =
      some (multiplyCfg index side sources current next) := by
  cases side <;>
    simp [TM2.step, program, restoreCfg, multiplyCfg, tapes,
      Function.update]

theorem replicate_unit_cons_comm (count : Nat) (tail : List Unit) :
    List.replicate count () ++ () :: tail =
      () :: List.replicate count () ++ tail := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq,
        true_and]
      exact induction

theorem stepAux_pushUnits {Source : Type} {coefficientCount : Nat}
    (side : Side) (count : Nat)
    (next : TM2.Stmt (Alphabet Source) (Label coefficientCount)
      (State Source))
    (state : State Source) (data : ∀ stack, List (Alphabet Source stack)) :
    TM2.stepAux (pushUnits side count next) state data =
      TM2.stepAux next state
        (Function.update data side.stack
          (List.replicate count (unitAtSide side) ++ data side.stack)) := by
  induction count generalizing data with
  | zero =>
      simp only [pushUnits, List.replicate_zero, List.nil_append]
      congr 1
      funext stack
      cases side <;> cases stack <;> simp [Function.update]
  | succ count induction =>
      simp only [pushUnits, TM2.stepAux]
      rw [induction]
      congr 1
      funext stack
      cases side <;> cases stack <;>
        simp [Function.update, List.replicate_succ, unitAtSide]
      all_goals exact replicate_unit_cons_comm count _

theorem step_multiply_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources : List Source) (next : List Unit) :
    TM2.step (program selected coefficients)
        (multiplyCfg index side sources [] next) =
      some (afterCoefficientCfg coefficients index side sources
        (List.replicate (coefficientAt coefficients index) () ++ next)) := by
  cases side <;>
    simp only [TM2.step, program, multiplyCfg, tapes,
      List.map, TM2.stepAux, Option.map_none, Option.isNone_none,
      Bool.true_eq, afterCoefficientCfg] <;>
    rw [stepAux_pushUnits] <;>
    simp [tapes, unitAtSide, Function.update] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update] <;>
    rfl

theorem step_start {Source : Type} [Fintype Source] [Inhabited Source]
    (selected : Source → Bool) (coefficients : List Nat)
    (sources : List Source) :
    TM2.step (program selected coefficients)
        (initList (machine Source selected coefficients) sources) =
      some (hornerCfg coefficients (selectedCount selected sources) 0
        sources) := by
  unfold initList machine
  by_cases nonempty : 0 < coefficients.length
  · simp [TM2.step, program, hornerCfg, nonempty, hornerAccumulator,
      sideAt, multiplyCfg]
    congr 1
    funext stack
    cases stack <;> simp [tapes]
  · simp [TM2.step, program, hornerCfg, nonempty, hornerAccumulator,
      sideAt, emitSourceCfg, emitSourceDataCfg]
    congr 1
    funext stack
    cases stack <;> simp [tapes]

theorem step_emitSource_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (source : Source) (sources : List Source)
    (result : List Unit) (outputReverse : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (emitSourceDataCfg side (source :: sources) result outputReverse) =
      some (emitSourceDataCfg side sources result
        (Sum.inl source :: outputReverse)) := by
  cases side <;>
    simp [TM2.step, program, emitSourceDataCfg, tapes,
      outputFromState, Function.update] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update]

theorem step_emitSource_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (result : List Unit)
    (outputReverse : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (emitSourceDataCfg side [] result outputReverse) =
      some (emitPaddingCfg side result outputReverse) := by
  cases side <;>
    simp [TM2.step, program, emitSourceDataCfg, emitPaddingCfg, tapes,
      Function.update]

theorem step_emitPadding_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (unit : Unit) (result : List Unit)
    (outputReverse : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (emitPaddingCfg side (unit :: result) outputReverse) =
      some (emitPaddingCfg side result (Sum.inr () :: outputReverse)) := by
  have unitEq : unit = () := Subsingleton.elim _ _
  subst unit
  cases side <;>
    simp [TM2.step, program, emitPaddingCfg, tapes,
      outputFromState, Function.update] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update]

theorem step_emitPadding_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (outputReverse : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (emitPaddingCfg side [] outputReverse) =
      some (reverseOutputCfg outputReverse []) := by
  cases side <;>
    simp [TM2.step, program, emitPaddingCfg, reverseOutputCfg, tapes,
      Function.update] <;>
    funext stack <;> cases stack <;> simp [tapes, Function.update]

theorem step_reverseOutput_cons {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (symbol : Source ⊕ Unit) (outputReverse output : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (reverseOutputCfg (symbol :: outputReverse) output) =
      some (reverseOutputCfg outputReverse (symbol :: output)) := by
  simp [TM2.step, program, reverseOutputCfg, tapes,
    outputFromState, Function.update]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_reverseOutput_nil {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (output : List (Source ⊕ Unit)) :
    TM2.step (program selected coefficients)
        (reverseOutputCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseOutputCfg, haltCfg, tapes,
    Function.update]

theorem haltList_eq_haltCfg {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (output : List (Source ⊕ Unit)) :
    haltList (machine Source selected coefficients) output =
      haltCfg output := by
  unfold haltList machine haltCfg
  congr 1
  funext stack
  cases stack <;> simp [tapes]

def oneStep {Configuration : Type}
    {transition : Configuration → Option Configuration}
    {first last : Configuration} (step : transition first = some last) :
    EvalsToInTime transition first (some last) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    change (some first).bind transition = some last
    simpa using step
  steps_le_m := Nat.le_refl 1

def zeroSteps {Configuration : Type}
    {transition : Configuration → Option Configuration}
    (configuration : Configuration) :
    EvalsToInTime transition configuration (some configuration) 0 where
  steps := 0
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl 0

def restore_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources sourceReverse : List Source) (current next : List Unit) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (restoreCfg index side sources sourceReverse current next)
      (some (multiplyCfg index side
        (sourceReverse.reverse ++ sources) current next))
      (sourceReverse.length + 1) := by
  induction sourceReverse generalizing sources with
  | nil =>
      simpa using oneStep
        (step_restore_nil selected coefficients index side sources current next)
  | cons source sourceReverse induction =>
      have first : EvalsToInTime (TM2.step (program selected coefficients))
          (restoreCfg index side sources (source :: sourceReverse) current next)
          (some (restoreCfg index side (source :: sources) sourceReverse
            current next)) 1 :=
        oneStep (step_restore_cons selected coefficients index side source
          sources sourceReverse current next)
      have rest := induction (source :: sources)
      have composed := EvalsToInTime.trans _ 1
        (sourceReverse.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using composed

def scan_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources sourceReverse : List Source) (current next : List Unit) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (scanCfg index side sources sourceReverse current next)
      (some (restoreCfg index side []
        (sources.reverse ++ sourceReverse) current
        (List.replicate (selectedCount selected sources) () ++ next)))
      (sources.length + 1) := by
  induction sources generalizing sourceReverse next with
  | nil =>
      simpa [selectedCount] using oneStep
        (step_scan_nil selected coefficients index side sourceReverse
          current next)
  | cons source sources induction =>
      let next' := if selected source then () :: next else next
      have first : EvalsToInTime (TM2.step (program selected coefficients))
          (scanCfg index side (source :: sources) sourceReverse current next)
          (some (scanCfg index side sources (source :: sourceReverse)
            current next')) 1 := by
        simpa [next'] using
          oneStep (step_scan_cons selected coefficients index side source
            sources sourceReverse current next)
      have rest := induction (source :: sourceReverse) next'
      have composed := EvalsToInTime.trans _ 1
        (sources.length + 1) _ _ _ first rest
      have reverseEq :
          sources.reverse ++ source :: sourceReverse =
            (source :: sources).reverse ++ sourceReverse := by
        simp [List.reverse_cons, List.append_assoc]
      have nextEq :
          List.replicate (selectedCount selected sources) () ++ next' =
            List.replicate (selectedCount selected (source :: sources)) () ++
              next := by
        cases choice : selected source
        · simp [selectedCount, next', choice]
        · have units :
              List.replicate (selectedCount selected sources) () ++ [()] =
                List.replicate
                  (1 + selectedCount selected sources) () := by
            rw [← List.replicate_one, ← List.replicate_add]
            congr 1
            omega
          rw [show next' = () :: next by simp [next', choice]]
          change List.replicate (selectedCount selected sources) () ++
              ([()] ++ next) = _
          rw [← List.append_assoc, units]
          simp [selectedCount, choice]
      rw [reverseEq, nextEq] at composed
      simpa using composed

/-- Consuming one unary accumulator token performs one complete selected-input
scan and restores the source word exactly. -/
def multiplyToken_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources : List Source) (current next : List Unit) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (multiplyCfg index side sources (() :: current) next)
      (some (multiplyCfg index side sources current
        (List.replicate (selectedCount selected sources) () ++ next)))
      (2 * sources.length + 3) := by
  have first : EvalsToInTime (TM2.step (program selected coefficients))
      (multiplyCfg index side sources (() :: current) next)
      (some (scanCfg index side sources [] current next)) 1 :=
    oneStep (step_multiply_cons selected coefficients index side sources
      current next)
  have scan := scan_evalsInTime selected coefficients index side
    sources [] current next
  have restore := restore_evalsInTime selected coefficients index side
    [] sources.reverse current
      (List.replicate (selectedCount selected sources) () ++ next)
  have restore' : EvalsToInTime (TM2.step (program selected coefficients))
      (restoreCfg index side [] (sources.reverse ++ []) current
        (List.replicate (selectedCount selected sources) () ++ next))
      (some (multiplyCfg index side sources current
        (List.replicate (selectedCount selected sources) () ++ next)))
      (sources.length + 1) := by
    simpa using restore
  have throughScan := EvalsToInTime.trans _ 1
    (sources.length + 1) _ _ _ first scan
  have whole := EvalsToInTime.trans _ (sources.length + 2)
    (sources.length + 1) _ _ _ throughScan restore'
  convert whole using 1 <;> omega

/-- One complete Horner phase multiplies the unary accumulator by the selected
input count and adds its fixed coefficient. -/
def multiply_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (index : Fin coefficients.length) (side : Side)
    (sources : List Source) (current next : List Unit) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (multiplyCfg index side sources current next)
      (some (afterCoefficientCfg coefficients index side sources
        (List.replicate
            (current.length * selectedCount selected sources +
              coefficientAt coefficients index) () ++ next)))
      (current.length * (2 * sources.length + 3) + 1) := by
  induction current generalizing next with
  | nil =>
      simpa using oneStep
        (step_multiply_nil selected coefficients index side sources next)
  | cons unit current induction =>
      have unitEq : unit = () := Subsingleton.elim _ _
      subst unit
      let selectedPadding :=
        List.replicate (selectedCount selected sources) () ++ next
      have first := multiplyToken_evalsInTime selected coefficients index side
        sources current next
      have rest := induction selectedPadding
      have resultEq :
          List.replicate
                (current.length * selectedCount selected sources +
                  coefficientAt coefficients index) () ++
              selectedPadding =
            List.replicate
                ((() :: current).length * selectedCount selected sources +
                  coefficientAt coefficients index) () ++ next := by
        unfold selectedPadding
        rw [← List.append_assoc, ← List.replicate_add]
        congr 2
        simp
        ring
      rw [resultEq] at rest
      have whole := EvalsToInTime.trans _
        (2 * sources.length + 3)
        (current.length * (2 * sources.length + 3) + 1)
        _ _ _ first rest
      convert whole using 1 <;> simp <;> ring

/-- Exact execution through any bounded prefix of the fixed coefficient
list. -/
def hornerPrefix_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (sources : List Source) (position : Nat)
    (bounded : position ≤ coefficients.length) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (hornerCfg coefficients (selectedCount selected sources) 0 sources)
      (some (hornerCfg coefficients (selectedCount selected sources)
        position sources))
      (hornerPrefixTime coefficients sources.length
        (selectedCount selected sources) position) := by
  induction position with
  | zero =>
      simpa [hornerPrefixTime] using
        (zeroSteps (transition := TM2.step (program selected coefficients))
          (hornerCfg coefficients (selectedCount selected sources) 0 sources))
  | succ position induction =>
      have positionLt : position < coefficients.length := by omega
      let index : Fin coefficients.length := ⟨position, positionLt⟩
      have prefixRun := induction (by omega)
      have phase := multiply_evalsInTime selected coefficients index
        (sideAt position) sources
        (List.replicate
          (hornerAccumulator coefficients (selectedCount selected sources)
            position) ()) []
      have phase' : EvalsToInTime (TM2.step (program selected coefficients))
          (hornerCfg coefficients (selectedCount selected sources)
            position sources)
          (some (hornerCfg coefficients (selectedCount selected sources)
            (position + 1) sources))
          (hornerAccumulator coefficients (selectedCount selected sources)
              position * (2 * sources.length + 3) + 1) := by
        rw [show hornerCfg coefficients (selectedCount selected sources)
            position sources =
            multiplyCfg index (sideAt position) sources
              (List.replicate
                (hornerAccumulator coefficients
                  (selectedCount selected sources) position) ()) [] by
          simp [hornerCfg, index, positionLt]]
        rw [← afterCoefficientCfg_eq_hornerCfg coefficients
          (selectedCount selected sources) index sources]
        convert phase using 1 <;> simp [index]
      have whole := EvalsToInTime.trans _
        (hornerPrefixTime coefficients sources.length
          (selectedCount selected sources) position)
        (hornerAccumulator coefficients (selectedCount selected sources)
            position * (2 * sources.length + 3) + 1)
        _ _ _ prefixRun phase'
      convert whole using 1 <;> simp [hornerPrefixTime] <;> omega

theorem hornerAccumulator_eq_foldl_take (coefficients : List Nat)
    (input position : Nat) (bounded : position ≤ coefficients.length) :
    hornerAccumulator coefficients input position =
      (coefficients.reverse.take position).foldl
        (fun accumulator coefficient => accumulator * input + coefficient) 0 := by
  induction position with
  | zero => rfl
  | succ position induction =>
      have positionLt : position < coefficients.length := by omega
      rw [hornerAccumulator]
      simp only [dif_pos positionLt]
      rw [List.take_succ, List.foldl_append]
      have getEq : coefficients.reverse[position]? =
          some (coefficientAt coefficients ⟨position, positionLt⟩) := by
        rw [List.getElem?_eq_getElem (by simpa using positionLt)]
        rfl
      rw [getEq]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
      rw [induction (by omega)]

@[simp]
theorem hornerAccumulator_length (coefficients : List Nat) (input : Nat) :
    hornerAccumulator coefficients input coefficients.length =
      evalCoefficients coefficients input := by
  rw [hornerAccumulator_eq_foldl_take coefficients input
    coefficients.length (Nat.le_refl _)]
  rw [show coefficients.length = coefficients.reverse.length by simp,
    List.take_length]
  rfl

def emitSource_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (sources : List Source) (result : List Unit)
    (outputReverse : List (Source ⊕ Unit)) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (emitSourceDataCfg side sources result outputReverse)
      (some (emitPaddingCfg side result
        ((sources.map Sum.inl).reverse ++ outputReverse)))
      (sources.length + 1) := by
  induction sources generalizing outputReverse with
  | nil =>
      simpa using oneStep
        (step_emitSource_nil selected coefficients side result outputReverse)
  | cons source sources induction =>
      have first : EvalsToInTime (TM2.step (program selected coefficients))
          (emitSourceDataCfg side (source :: sources) result outputReverse)
          (some (emitSourceDataCfg side sources result
            (Sum.inl source :: outputReverse))) 1 :=
        oneStep (step_emitSource_cons selected coefficients side source
          sources result outputReverse)
      have rest := induction (Sum.inl source :: outputReverse)
      have whole := EvalsToInTime.trans _ 1
        (sources.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using whole

def emitPadding_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (side : Side) (result : List Unit)
    (outputReverse : List (Source ⊕ Unit)) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (emitPaddingCfg side result outputReverse)
      (some (reverseOutputCfg
        ((result.map fun _ => Sum.inr ()).reverse ++ outputReverse) []))
      (result.length + 1) := by
  induction result generalizing outputReverse with
  | nil =>
      simpa using oneStep
        (step_emitPadding_nil selected coefficients side outputReverse)
  | cons unit result induction =>
      have first : EvalsToInTime (TM2.step (program selected coefficients))
          (emitPaddingCfg side (unit :: result) outputReverse)
          (some (emitPaddingCfg side result
            (Sum.inr () :: outputReverse))) 1 :=
        oneStep (step_emitPadding_cons selected coefficients side unit result
          outputReverse)
      have rest := induction (Sum.inr () :: outputReverse)
      have whole := EvalsToInTime.trans _ 1
        (result.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using whole

def reverseOutput_evalsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (outputReverse output : List (Source ⊕ Unit)) :
    EvalsToInTime (TM2.step (program selected coefficients))
      (reverseOutputCfg outputReverse output)
      (some (haltCfg (outputReverse.reverse ++ output)))
      (outputReverse.length + 1) := by
  induction outputReverse generalizing output with
  | nil =>
      simpa using oneStep
        (step_reverseOutput_nil selected coefficients output)
  | cons symbol outputReverse induction =>
      have first : EvalsToInTime (TM2.step (program selected coefficients))
          (reverseOutputCfg (symbol :: outputReverse) output)
          (some (reverseOutputCfg outputReverse (symbol :: output))) 1 :=
        oneStep (step_reverseOutput_cons selected coefficients symbol
          outputReverse output)
      have rest := induction (symbol :: output)
      have whole := EvalsToInTime.trans _ 1
        (outputReverse.length + 1) _ _ _ first rest
      simpa [List.reverse_cons, List.append_assoc] using whole

/-- Exact complete runtime of the unary polynomial padding machine. -/
def totalTime {Source : Type} (selected : Source → Bool)
    (coefficients : List Nat)
    (sources : List Source) : Nat :=
  let result := evalCoefficients coefficients (selectedCount selected sources)
  1 + hornerPrefixTime coefficients sources.length
      (selectedCount selected sources) coefficients.length +
    (2 * sources.length + 2 * result + 3)

noncomputable def machine_outputsInTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat)
    (sources : List Source) :
    TM2OutputsInTime (machine Source selected coefficients) sources
      (some (paddedOutput selected coefficients sources))
      (totalTime selected coefficients sources) := by
  let input := selectedCount selected sources
  let result := evalCoefficients coefficients input
  let resultList := List.replicate result ()
  have start : EvalsToInTime (TM2.step (program selected coefficients))
      (initList (machine Source selected coefficients) sources)
      (some (hornerCfg coefficients input 0 sources)) 1 :=
    oneStep (step_start selected coefficients sources)
  have horner := hornerPrefix_evalsInTime selected coefficients sources
    coefficients.length (Nat.le_refl _)
  have finalCfg : hornerCfg coefficients input coefficients.length sources =
      emitSourceCfg (coefficients := coefficients)
        (sideAt coefficients.length) sources resultList := by
    simp [hornerCfg, input, result, resultList]
  rw [finalCfg] at horner
  have sourceRun := emitSource_evalsInTime selected coefficients
    (sideAt coefficients.length) sources resultList []
  have paddingRun := emitPadding_evalsInTime selected coefficients
    (sideAt coefficients.length) resultList
      ((sources.map Sum.inl).reverse ++ [])
  let outputReverse :=
    (resultList.map fun _ => Sum.inr ()).reverse ++
      (sources.map Sum.inl).reverse
  have paddingRun' : EvalsToInTime (TM2.step (program selected coefficients))
      (emitPaddingCfg (sideAt coefficients.length) resultList
        ((sources.map Sum.inl).reverse ++ []))
      (some (reverseOutputCfg outputReverse []))
      (resultList.length + 1) := by
    simpa [outputReverse] using paddingRun
  have reverseRun := reverseOutput_evalsInTime selected coefficients
    outputReverse []
  have outputEq : outputReverse.reverse =
      paddedOutput selected coefficients sources := by
    simp [outputReverse, paddedOutput, resultList, result, input,
      List.reverse_append]
  rw [outputEq] at reverseRun
  have reverseRun' : EvalsToInTime (TM2.step (program selected coefficients))
      (reverseOutputCfg outputReverse [])
      (some (haltCfg (paddedOutput selected coefficients sources)))
      (outputReverse.length + 1) := by
    simpa using reverseRun
  have throughHorner := EvalsToInTime.trans _ 1
    (hornerPrefixTime coefficients sources.length input coefficients.length)
    _ _ _ start horner
  have throughSource := EvalsToInTime.trans _
    (hornerPrefixTime coefficients sources.length input coefficients.length + 1)
    (sources.length + 1) _ _ _ throughHorner sourceRun
  have throughPadding := EvalsToInTime.trans _
    (sources.length + 1 +
      (hornerPrefixTime coefficients sources.length input coefficients.length + 1))
    (resultList.length + 1) _ _ _ throughSource paddingRun'
  have whole := EvalsToInTime.trans _
    (resultList.length + 1 +
      (sources.length + 1 +
        (hornerPrefixTime coefficients sources.length input coefficients.length + 1)))
    (outputReverse.length + 1) _ _ _ throughPadding reverseRun'
  unfold TM2OutputsInTime
  change EvalsToInTime (TM2.step (program selected coefficients))
    (initList (machine Source selected coefficients) sources)
    (some (haltList (machine Source selected coefficients)
      (paddedOutput selected coefficients sources)))
    (totalTime selected coefficients sources)
  rw [haltList_eq_haltCfg selected coefficients]
  convert whole using 1
  simp [totalTime, outputReverse, resultList, result, input, paddedOutput]
  omega

theorem selectedCount_le_length {Source : Type} (selected : Source → Bool)
    (sources : List Source) :
    selectedCount selected sources ≤ sources.length := by
  induction sources with
  | nil => rfl
  | cons source sources induction =>
      cases choice : selected source <;>
        simp [selectedCount, choice] at * <;> omega

theorem le_sum_of_mem {value : Nat} {values : List Nat}
    (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp
      · have tailBound := induction member
        simp only [List.sum_cons]
        omega

theorem coefficientAt_le_sum (coefficients : List Nat)
    (index : Fin coefficients.length) :
    coefficientAt coefficients index ≤ coefficients.sum := by
  have member : coefficientAt coefficients index ∈ coefficients.reverse :=
    List.get_mem coefficients.reverse
      ⟨index.val, by simpa using index.isLt⟩
  have bounded := le_sum_of_mem member
  simpa using bounded

/-- Every intermediate Horner accumulator is bounded by a simple power in
the source length and fixed coefficient mass. -/
theorem hornerAccumulator_add_one_le
    (coefficients : List Nat) (input inputBound position : Nat)
    (inputLe : input ≤ inputBound)
    (positionLe : position ≤ coefficients.length) :
    hornerAccumulator coefficients input position + 1 ≤
      (inputBound + coefficients.sum + 1) ^ (position + 1) := by
  induction position with
  | zero =>
      simp [hornerAccumulator]
  | succ position induction =>
      have positionLt : position < coefficients.length := by omega
      let coefficient := coefficientAt coefficients ⟨position, positionLt⟩
      have coefficientLe : coefficient ≤ coefficients.sum :=
        coefficientAt_le_sum coefficients ⟨position, positionLt⟩
      have accumulatorLe := induction (by omega)
      have factorLe : input + coefficient + 1 ≤
          inputBound + coefficients.sum + 1 := by omega
      have productLe := Nat.mul_le_mul accumulatorLe factorLe
      rw [hornerAccumulator]
      simp only [dif_pos positionLt]
      change hornerAccumulator coefficients input position * input +
          coefficient + 1 ≤ _
      calc
        hornerAccumulator coefficients input position * input +
              coefficient + 1 ≤
            (hornerAccumulator coefficients input position + 1) *
              (input + coefficient + 1) := by
          rw [show
            (hornerAccumulator coefficients input position + 1) *
                (input + coefficient + 1) =
              hornerAccumulator coefficients input position * input +
                coefficient + 1 +
                (hornerAccumulator coefficients input position *
                  coefficient +
                  hornerAccumulator coefficients input position + input) by
            ring]
          omega
        _ ≤ (inputBound + coefficients.sum + 1) ^ (position + 1) *
              (inputBound + coefficients.sum + 1) := productLe
        _ = (inputBound + coefficients.sum + 1) ^ (position + 1 + 1) := by
          exact (pow_succ _ (position + 1)).symm

theorem hornerAccumulator_le_commonBound
    (coefficients : List Nat) (input inputBound position : Nat)
    (inputLe : input ≤ inputBound)
    (positionLe : position ≤ coefficients.length) :
    hornerAccumulator coefficients input position ≤
      (inputBound + coefficients.sum + 1) ^ (coefficients.length + 1) := by
  have localBound := hornerAccumulator_add_one_le coefficients input inputBound
    position inputLe positionLe
  have exponent := Nat.pow_le_pow_right (by omega :
      0 < inputBound + coefficients.sum + 1)
    (Nat.add_le_add_right positionLe 1)
  exact (Nat.le_succ _).trans (localBound.trans exponent)

theorem hornerPrefixTime_le (coefficients : List Nat)
    (inputLength input position : Nat)
    (inputLe : input ≤ inputLength)
    (positionLe : position ≤ coefficients.length) :
    hornerPrefixTime coefficients inputLength input position ≤
      position *
        ((inputLength + coefficients.sum + 1) ^
            (coefficients.length + 1) * (2 * inputLength + 3) + 1) := by
  induction position with
  | zero => simp [hornerPrefixTime]
  | succ position induction =>
      have accumulatorLe := hornerAccumulator_le_commonBound coefficients
        input inputLength position inputLe (by omega)
      have phaseLe :
          hornerAccumulator coefficients input position *
                (2 * inputLength + 3) + 1 ≤
            (inputLength + coefficients.sum + 1) ^
                (coefficients.length + 1) * (2 * inputLength + 3) + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (2 * inputLength + 3) accumulatorLe) 1
      have combined := Nat.add_le_add (induction (by omega)) phaseLe
      rw [hornerPrefixTime]
      calc
        hornerPrefixTime coefficients inputLength input position +
              hornerAccumulator coefficients input position *
                (2 * inputLength + 3) + 1 =
            hornerPrefixTime coefficients inputLength input position +
              (hornerAccumulator coefficients input position *
                (2 * inputLength + 3) + 1) := by omega
        _ ≤
            position *
                ((inputLength + coefficients.sum + 1) ^
                    (coefficients.length + 1) *
                    (2 * inputLength + 3) + 1) +
              ((inputLength + coefficients.sum + 1) ^
                    (coefficients.length + 1) *
                    (2 * inputLength + 3) + 1) := combined
        _ = (position + 1) *
              ((inputLength + coefficients.sum + 1) ^
                  (coefficients.length + 1) *
                  (2 * inputLength + 3) + 1) := by ring

noncomputable def commonBoundPolynomial (coefficients : List Nat) :
    Polynomial Nat :=
  (Polynomial.X + Polynomial.C (coefficients.sum + 1)) ^
    (coefficients.length + 1)

noncomputable def timePolynomial (coefficients : List Nat) : Polynomial Nat :=
  let common := commonBoundPolynomial coefficients
  Polynomial.C coefficients.length *
      (common * (Polynomial.C 2 * Polynomial.X + Polynomial.C 3) +
        Polynomial.C 1) +
    Polynomial.C 2 * Polynomial.X + Polynomial.C 2 * common +
      Polynomial.C 4

@[simp]
theorem commonBoundPolynomial_eval (coefficients : List Nat) (length : Nat) :
    (commonBoundPolynomial coefficients).eval length =
      (length + coefficients.sum + 1) ^ (coefficients.length + 1) := by
  simp only [commonBoundPolynomial, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  congr 1 <;> omega

@[simp]
theorem timePolynomial_eval (coefficients : List Nat) (length : Nat) :
    (timePolynomial coefficients).eval length =
      coefficients.length *
          ((length + coefficients.sum + 1) ^ (coefficients.length + 1) *
              (2 * length + 3) + 1) +
        2 * length +
        2 * (length + coefficients.sum + 1) ^
          (coefficients.length + 1) + 4 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, commonBoundPolynomial_eval]

theorem totalTime_le_polynomial_eval {Source : Type}
    (selected : Source → Bool) (coefficients : List Nat)
    (sources : List Source) :
    totalTime selected coefficients sources ≤
      (timePolynomial coefficients).eval sources.length := by
  let input := selectedCount selected sources
  let common :=
    (sources.length + coefficients.sum + 1) ^
      (coefficients.length + 1)
  have inputLe : input ≤ sources.length :=
    selectedCount_le_length selected sources
  have prefixLe := hornerPrefixTime_le coefficients sources.length input
    coefficients.length inputLe (Nat.le_refl _)
  have resultLe : evalCoefficients coefficients input ≤ common := by
    rw [← hornerAccumulator_length]
    exact hornerAccumulator_le_commonBound coefficients input sources.length
      coefficients.length inputLe (Nat.le_refl _)
  rw [timePolynomial_eval]
  unfold totalTime
  dsimp only [input, common] at prefixLe resultLe ⊢
  omega

/-- The fixed Horner padding machine runs in polynomial time in the complete
source-word length. -/
noncomputable def computableInPolyTime {Source : Type} [Fintype Source]
    [Inhabited Source] (selected : Source → Bool) (coefficients : List Nat) :
    @TM2ComputableInPolyTime
      (List Source) (List (Source ⊕ Unit)) Source (Source ⊕ Unit)
      id id (paddedOutput selected coefficients) where
  tm := machine Source selected coefficients
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := timePolynomial coefficients
  outputsFun sources := by
    have run := machine_outputsInTime selected coefficients sources
    have run' : TM2OutputsInTime (machine Source selected coefficients)
        (List.map (Equiv.refl Source).invFun (id sources))
        (some (List.map (Equiv.refl (Source ⊕ Unit)).invFun
          (id (paddedOutput selected coefficients sources))))
        (totalTime selected coefficients sources) := by
      simpa only [FiniteBlockTransducer.map_refl_invFun, id_eq] using run
    refine
      { toEvalsTo := run'.toEvalsTo
        steps_le_m := run'.steps_le_m.trans ?_ }
    exact totalTime_le_polynomial_eval selected coefficients sources

end UnaryPolynomialPaddingMachine
end LeanTrominoes
