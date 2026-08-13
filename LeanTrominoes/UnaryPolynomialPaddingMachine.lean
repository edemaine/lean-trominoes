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

end UnaryPolynomialPaddingMachine
end LeanTrominoes
