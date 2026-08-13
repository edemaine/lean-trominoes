/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2OutputLength

/-!
# Sequential composition of finite multi-stack machines

This file constructs the finite machine underlying polynomial-time sequential
composition.  Two disjoint copies of the component stack systems are joined
by one bridge stack over the intermediate encoding alphabet.  After the first
machine halts, a two-pass transfer reverses its output onto the bridge and
then reverses it again onto the second machine's input stack, preserving the
encoded symbol order.

The construction assumes the intermediate alphabet is finite.  This is the
case needed by the project's finite encodings and lets each transient bridge
symbol be represented in finite control.
-/

noncomputable section

namespace LeanTrominoes

open StateTransition Turing

namespace TM2CompositionMachine

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

inductive Stack (First Second : Type)
  | first (stack : First)
  | bridge
  | second (stack : Second)
deriving DecidableEq, Fintype

inductive Label (First Middle Second : Type)
  | first (label : First)
  | drainFirst
  | pushBridge (symbol : Middle)
  | drainBridge
  | pushSecond (symbol : Middle)
  | second (label : Second)
deriving Fintype

inductive State (First Middle Second : Type)
  | first (state : First)
  | bridge (symbol : Option Middle)
  | second (state : Second)
deriving Fintype

abbrev Alphabet (first second : FinTM2) (Middle : Type) :
    Stack first.K second.K → Type
  | .first stack => first.Γ stack
  | .bridge => Middle
  | .second stack => second.Γ stack

abbrev CombinedLabel (first second : FinTM2) (Middle : Type) :=
  Label first.Λ Middle second.Λ

abbrev CombinedState (first second : FinTM2) (Middle : Type) :=
  State first.σ Middle second.σ

def firstState (first second : FinTM2) (Middle : Type)
    (state : CombinedState first second Middle) : first.σ :=
  match state with
  | .first state => state
  | _ => first.initialState

def secondState (first second : FinTM2) (Middle : Type)
    (state : CombinedState first second Middle) : second.σ :=
  match state with
  | .second state => state
  | _ => second.initialState

/-- Embed a first-machine statement.  Its halt becomes the first bridge
phase, with bridge control cleared. -/
def embedFirstStatement (first second : FinTM2) (Middle : Type) :
    TM2.Stmt first.Γ first.Λ first.σ →
      TM2.Stmt (Alphabet first second Middle)
        (CombinedLabel first second Middle)
        (CombinedState first second Middle)
  | .push stack write next =>
      .push (.first stack)
        (fun state => write (firstState first second Middle state))
        (embedFirstStatement first second Middle next)
  | .peek stack read next =>
      .peek (.first stack)
        (fun state symbol =>
          .first (read (firstState first second Middle state) symbol))
        (embedFirstStatement first second Middle next)
  | .pop stack read next =>
      .pop (.first stack)
        (fun state symbol =>
          .first (read (firstState first second Middle state) symbol))
        (embedFirstStatement first second Middle next)
  | .load update next =>
      .load (fun state =>
        .first (update (firstState first second Middle state)))
        (embedFirstStatement first second Middle next)
  | .branch test yes no =>
      .branch (fun state => test (firstState first second Middle state))
        (embedFirstStatement first second Middle yes)
        (embedFirstStatement first second Middle no)
  | .goto target =>
      .goto fun state =>
        .first (target (firstState first second Middle state))
  | .halt =>
      .load (fun _ => .bridge none) (.goto fun _ => .drainFirst)

/-- Embed a second-machine statement.  Its halt resets the combined finite
control to the combined machine's initial state, as required by `haltList`. -/
def embedSecondStatement (first second : FinTM2) (Middle : Type) :
    TM2.Stmt second.Γ second.Λ second.σ →
      TM2.Stmt (Alphabet first second Middle)
        (CombinedLabel first second Middle)
        (CombinedState first second Middle)
  | .push stack write next =>
      .push (.second stack)
        (fun state => write (secondState first second Middle state))
        (embedSecondStatement first second Middle next)
  | .peek stack read next =>
      .peek (.second stack)
        (fun state symbol =>
          .second (read (secondState first second Middle state) symbol))
        (embedSecondStatement first second Middle next)
  | .pop stack read next =>
      .pop (.second stack)
        (fun state symbol =>
          .second (read (secondState first second Middle state) symbol))
        (embedSecondStatement first second Middle next)
  | .load update next =>
      .load (fun state =>
        .second (update (secondState first second Middle state)))
        (embedSecondStatement first second Middle next)
  | .branch test yes no =>
      .branch (fun state => test (secondState first second Middle state))
        (embedSecondStatement first second Middle yes)
        (embedSecondStatement first second Middle no)
  | .goto target =>
      .goto fun state =>
        .second (target (secondState first second Middle state))
  | .halt =>
      .load (fun _ => .first first.initialState) .halt

def bridgeSymbol (first second : FinTM2) (Middle : Type)
    (state : CombinedState first second Middle) : Option Middle :=
  match state with
  | .bridge symbol => symbol
  | _ => none

def program
    {α β γ αΓ βΓ γΓ : Type} [Fintype βΓ]
    {encodeA : α → List αΓ} {encodeB : β → List βΓ}
    {encodeC : γ → List γΓ} {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g) :
    CombinedLabel first.tm second.tm βΓ →
      TM2.Stmt (Alphabet first.tm second.tm βΓ)
        (CombinedLabel first.tm second.tm βΓ)
        (CombinedState first.tm second.tm βΓ)
  | .first label =>
      embedFirstStatement first.tm second.tm βΓ (first.tm.m label)
  | .drainFirst =>
      .pop (.first first.tm.k₁)
        (fun _ symbol =>
          .bridge (symbol.map first.outputAlphabet))
        (.goto fun state =>
          match bridgeSymbol first.tm second.tm βΓ state with
          | none => .drainBridge
          | some symbol => .pushBridge symbol)
  | .pushBridge symbol =>
      .push .bridge (fun _ => symbol)
        (.load (fun _ => .bridge none) (.goto fun _ => .drainFirst))
  | .drainBridge =>
      .pop .bridge (fun _ symbol =>
        match symbol with
        | none => .second second.tm.initialState
        | some symbol => .bridge (some symbol))
        (.goto fun state =>
          match bridgeSymbol first.tm second.tm βΓ state with
          | none => .second second.tm.main
          | some symbol => .pushSecond symbol)
  | .pushSecond symbol =>
      .push (.second second.tm.k₀)
        (fun _ => second.inputAlphabet.invFun symbol)
        (.load (fun _ => .bridge none) (.goto fun _ => .drainBridge))
  | .second label =>
      embedSecondStatement first.tm second.tm βΓ (second.tm.m label)

/-- The disjoint-union machine with a finite intermediate bridge alphabet. -/
def machine
    {α β γ αΓ βΓ γΓ : Type} [Fintype βΓ]
    {encodeA : α → List αΓ} {encodeB : β → List βΓ}
    {encodeC : γ → List γΓ} {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g) : FinTM2 where
  K := Stack first.tm.K second.tm.K
  kDecidableEq := instDecidableEqStack
  k₀ := .first first.tm.k₀
  k₁ := .second second.tm.k₁
  Γ := Alphabet first.tm second.tm βΓ
  Γk₀Fin := first.tm.Γk₀Fin
  Λ := CombinedLabel first.tm second.tm βΓ
  main := .first first.tm.main
  σ := CombinedState first.tm second.tm βΓ
  initialState := .first first.tm.initialState
  m := program first second

def firstStacks (first second : FinTM2) (Middle : Type)
    (stackContents : ∀ stack, List (first.Γ stack)) :
    ∀ stack, List (Alphabet first second Middle stack)
  | .first stack => stackContents stack
  | .bridge => []
  | .second _ => []

def secondStacks (first second : FinTM2) (Middle : Type)
    (stackContents : ∀ stack, List (second.Γ stack)) :
    ∀ stack, List (Alphabet first second Middle stack)
  | .first _ => []
  | .bridge => []
  | .second stack => stackContents stack

def liftFirstCfg (first second : FinTM2) (Middle : Type)
    (configuration : first.Cfg) :
    TM2.Cfg (Alphabet first second Middle)
      (CombinedLabel first second Middle)
      (CombinedState first second Middle) where
  l := match configuration.l with
    | some label => some (.first label)
    | none => some .drainFirst
  var := match configuration.l with
    | some _ => .first configuration.var
    | none => .bridge none
  stk := firstStacks first second Middle configuration.stk

def liftSecondCfg (first second : FinTM2) (Middle : Type)
    (configuration : second.Cfg) :
    TM2.Cfg (Alphabet first second Middle)
      (CombinedLabel first second Middle)
      (CombinedState first second Middle) where
  l := configuration.l.map Label.second
  var := match configuration.l with
    | some _ => .second configuration.var
    | none => .first first.initialState
  stk := secondStacks first second Middle configuration.stk

@[simp]
theorem update_firstStacks
    (first second : FinTM2) (Middle : Type)
    (stackContents : ∀ stack, List (first.Γ stack))
    (target : first.K) (value : List (first.Γ target)) :
    Function.update (firstStacks first second Middle stackContents)
        (.first target) value =
      firstStacks first second Middle
        (Function.update stackContents target value) := by
  funext stack
  cases stack with
  | first stack =>
      by_cases equal : stack = target
      · subst stack
        simp [firstStacks]
      · have taggedNe :
            (Stack.first stack : Stack first.K second.K) ≠
              Stack.first target := by
          intro taggedEq
          exact equal (Stack.first.inj taggedEq)
        simp [firstStacks, Function.update_of_ne equal,
          Function.update_of_ne taggedNe]
  | bridge => simp [firstStacks]
  | second stack => simp [firstStacks]

@[simp]
theorem update_secondStacks
    (first second : FinTM2) (Middle : Type)
    (stackContents : ∀ stack, List (second.Γ stack))
    (target : second.K) (value : List (second.Γ target)) :
    Function.update (secondStacks first second Middle stackContents)
        (.second target) value =
      secondStacks first second Middle
        (Function.update stackContents target value) := by
  funext stack
  cases stack with
  | first stack => simp [secondStacks]
  | bridge => simp [secondStacks]
  | second stack =>
      by_cases equal : stack = target
      · subst stack
        simp [secondStacks]
      · have taggedNe :
            (Stack.second stack : Stack first.K second.K) ≠
              Stack.second target := by
          intro taggedEq
          exact equal (Stack.second.inj taggedEq)
        simp [secondStacks, Function.update_of_ne equal,
          Function.update_of_ne taggedNe]

/-- Embedded first statements commute exactly with configuration lifting. -/
theorem embedFirstStatement_stepAux
    (first second : FinTM2) (Middle : Type)
    (statement : TM2.Stmt first.Γ first.Λ first.σ)
    (state : first.σ)
    (stackContents : ∀ stack, List (first.Γ stack)) :
    TM2.stepAux (embedFirstStatement first second Middle statement)
        (.first state) (firstStacks first second Middle stackContents) =
      liftFirstCfg first second Middle
        (TM2.stepAux statement state stackContents) := by
  induction statement generalizing state stackContents with
  | push stack write next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      rw [update_firstStacks]
      exact induction state _
  | peek stack read next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState,
        firstStacks]
      exact induction _ _
  | pop stack read next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState,
        firstStacks]
      rw [update_firstStacks]
      exact induction _ _
  | load update next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      exact induction _ _
  | branch test yes no yesInduction noInduction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      cases test state
      · exact noInduction _ _
      · exact yesInduction _ _
  | goto target => rfl
  | halt => rfl

/-- Embedded second statements commute exactly with configuration lifting. -/
theorem embedSecondStatement_stepAux
    (first second : FinTM2) (Middle : Type)
    (statement : TM2.Stmt second.Γ second.Λ second.σ)
    (state : second.σ)
    (stackContents : ∀ stack, List (second.Γ stack)) :
    TM2.stepAux (embedSecondStatement first second Middle statement)
        (.second state) (secondStacks first second Middle stackContents) =
      liftSecondCfg first second Middle
        (TM2.stepAux statement state stackContents) := by
  induction statement generalizing state stackContents with
  | push stack write next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      rw [update_secondStacks]
      exact induction state _
  | peek stack read next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState,
        secondStacks]
      exact induction _ _
  | pop stack read next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState,
        secondStacks]
      rw [update_secondStacks]
      exact induction _ _
  | load update next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      exact induction _ _
  | branch test yes no yesInduction noInduction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      cases test state
      · exact noInduction _ _
      · exact yesInduction _ _
  | goto target => rfl
  | halt => rfl

/-- Every live step of the first component is reproduced exactly by its
embedded copy. -/
theorem liftFirst_step
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    {before after : first.tm.Cfg}
    (step : first.tm.step before = some after) :
    (machine first second).step
        (liftFirstCfg first.tm second.tm BΓ before) =
      some (liftFirstCfg first.tm second.tm BΓ after) := by
  rcases before with ⟨label, state, stackContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      simp only [FinTM2.step, TM2.step, liftFirstCfg, machine, program]
      exact congrArg some
        (embedFirstStatement_stepAux first.tm second.tm BΓ
          (first.tm.m label) state stackContents)

/-- Every live step of the second component is reproduced exactly by its
embedded copy. -/
theorem liftSecond_step
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    {before after : second.tm.Cfg}
    (step : second.tm.step before = some after) :
    (machine first second).step
        (liftSecondCfg first.tm second.tm BΓ before) =
      some (liftSecondCfg first.tm second.tm BΓ after) := by
  rcases before with ⟨label, state, stackContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      simp only [FinTM2.step, TM2.step, liftSecondCfg, machine, program]
      exact congrArg some
        (embedSecondStatement_stepAux first.tm second.tm BΓ
          (second.tm.m label) state stackContents)

private theorem iterate_none {Configuration : Type}
    (transition : Configuration → Option Configuration) (steps : Nat) :
    (flip bind transition)^[steps] none = none := by
  induction steps with
  | zero => rfl
  | succ steps induction =>
      rw [Function.iterate_succ_apply]
      exact induction

private theorem lift_iterate
    {Source Target : Type}
    (source : Source → Option Source)
    (target : Target → Option Target) (lift : Source → Target)
    (stepLift : ∀ {before after}, source before = some after →
      target (lift before) = some (lift after)) :
    ∀ (steps : Nat) (before after : Source),
      (flip bind source)^[steps] (some before) = some after →
      (flip bind target)^[steps] (some (lift before)) =
        some (lift after) := by
  intro steps
  induction steps with
  | zero =>
      intro before after equality
      simp only [Function.iterate_zero, id_eq,
        Option.some.injEq] at equality ⊢
      subst after
      rfl
  | succ steps induction =>
      intro before after equality
      rw [Function.iterate_succ_apply] at equality ⊢
      cases firstStep : source before with
      | none =>
          change (flip bind source)^[steps] (source before) =
            some after at equality
          rw [firstStep, iterate_none] at equality
          cases equality
      | some middle =>
          change (flip bind source)^[steps] (source before) =
            some after at equality
          change (flip bind target)^[steps] (target (lift before)) =
            some (lift after)
          rw [stepLift firstStep]
          exact induction middle after (by simpa [firstStep] using equality)

/-- Lift a bounded first-component execution without changing its counted
number of steps. -/
def liftFirstEvalsToInTime
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    {before after : first.tm.Cfg} {bound : Nat}
    (run : EvalsToInTime first.tm.step before (some after) bound) :
    EvalsToInTime (machine first second).step
      (liftFirstCfg first.tm second.tm BΓ before)
      (some (liftFirstCfg first.tm second.tm BΓ after)) bound where
  steps := run.steps
  evals_in_steps := lift_iterate first.tm.step
    (machine first second).step
    (liftFirstCfg first.tm second.tm BΓ)
    (liftFirst_step first second) run.steps before after
    run.evals_in_steps
  steps_le_m := run.steps_le_m

/-- Lift a bounded second-component execution without changing its counted
number of steps. -/
def liftSecondEvalsToInTime
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    {before after : second.tm.Cfg} {bound : Nat}
    (run : EvalsToInTime second.tm.step before (some after) bound) :
    EvalsToInTime (machine first second).step
      (liftSecondCfg first.tm second.tm BΓ before)
      (some (liftSecondCfg first.tm second.tm BΓ after)) bound where
  steps := run.steps
  evals_in_steps := lift_iterate second.tm.step
    (machine first second).step
    (liftSecondCfg first.tm second.tm BΓ)
    (liftSecond_step first second) run.steps before after
    run.evals_in_steps
  steps_le_m := run.steps_le_m

/-- Stack contents during the bridge phase: the first and second sides use
their canonical halted and initial layouts, while the bridge is explicit. -/
def transferStacks (first second : FinTM2) (Middle : Type)
    (firstOutput : List (first.Γ first.k₁))
    (bridgeContents : List Middle)
    (secondInput : List (second.Γ second.k₀)) :
    ∀ stack, List (Alphabet first second Middle stack)
  | .first stack => (haltList first firstOutput).stk stack
  | .bridge => bridgeContents
  | .second stack => (initList second secondInput).stk stack

def transferCfg (first second : FinTM2) (Middle : Type)
    (label : Option (CombinedLabel first second Middle))
    (state : CombinedState first second Middle)
    (firstOutput : List (first.Γ first.k₁))
    (bridgeContents : List Middle)
    (secondInput : List (second.Γ second.k₀)) :
    TM2.Cfg (Alphabet first second Middle)
      (CombinedLabel first second Middle)
      (CombinedState first second Middle) where
  l := label
  var := state
  stk := transferStacks first second Middle
    firstOutput bridgeContents secondInput

private def evalsToInTime_single
    {Configuration : Type} {transition : Configuration → Option Configuration}
    {before after : Configuration} (step : transition before = some after) :
    EvalsToInTime transition before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    change transition before = some after
    exact step
  steps_le_m := Nat.le_refl 1

@[simp]
theorem update_transferStacks_first
    (first second : FinTM2) (Middle : Type)
    (symbol : first.Γ first.k₁)
    (remaining : List (first.Γ first.k₁))
    (bridgeContents : List Middle)
    (secondInput : List (second.Γ second.k₀)) :
    Function.update
        (transferStacks first second Middle
          (symbol :: remaining) bridgeContents secondInput)
        (.first first.k₁) remaining =
      transferStacks first second Middle
        remaining bridgeContents secondInput := by
  funext stack
  cases stack with
  | bridge => simp [transferStacks]
  | second stack => simp [transferStacks]
  | first stack =>
      by_cases equal : stack = first.k₁
      · subst stack
        simp [transferStacks, haltList]
      · have taggedNe :
            (Stack.first stack : Stack first.K second.K) ≠
              Stack.first first.k₁ := by
          intro taggedEq
          exact equal (Stack.first.inj taggedEq)
        simp [transferStacks, haltList, equal]

theorem step_drainFirst_cons
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (symbol : first.tm.Γ first.tm.k₁)
    (remaining : List (first.tm.Γ first.tm.k₁))
    (bridgeContents : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ (some .drainFirst)
          (.bridge none) (symbol :: remaining) bridgeContents secondInput) =
      some (transferCfg first.tm second.tm BΓ
        (some (.pushBridge (first.outputAlphabet symbol)))
        (.bridge (some (first.outputAlphabet symbol)))
        remaining bridgeContents secondInput) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program, bridgeSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | bridge => simp [transferStacks]
  | second stack => simp [transferStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [transferStacks, haltList]
      · simp [transferStacks, haltList, equal]

theorem step_pushBridge
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (symbol : BΓ)
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (bridgeContents : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ
          (some (.pushBridge symbol)) (.bridge (some symbol))
          firstOutput bridgeContents secondInput) =
      some (transferCfg first.tm second.tm BΓ
        (some .drainFirst) (.bridge none)
        firstOutput (symbol :: bridgeContents) secondInput) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program]
  congr 2
  funext stack
  cases stack <;> simp [transferStacks]

theorem step_drainFirst_nil
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (bridgeContents : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ (some .drainFirst)
          (.bridge none) [] bridgeContents secondInput) =
      some (transferCfg first.tm second.tm BΓ
        (some .drainBridge) (.bridge none)
        [] bridgeContents secondInput) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program, bridgeSymbol, haltList]
  congr 2
  funext stack
  cases stack with
  | bridge => simp [transferStacks]
  | second stack => simp [transferStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [transferStacks, haltList]
      · simp [transferStacks, haltList, equal]

theorem step_drainBridge_cons
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (symbol : BΓ) (remaining : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ (some .drainBridge)
          (.bridge none) [] (symbol :: remaining) secondInput) =
      some (transferCfg first.tm second.tm BΓ
        (some (.pushSecond symbol)) (.bridge (some symbol))
        [] remaining secondInput) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program, bridgeSymbol]
  congr 2
  funext stack
  cases stack <;> simp [transferStacks]

theorem step_pushSecond
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (symbol : BΓ) (remaining : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ
          (some (.pushSecond symbol)) (.bridge (some symbol))
          [] remaining secondInput) =
      some (transferCfg first.tm second.tm BΓ
        (some .drainBridge) (.bridge none) [] remaining
        (second.inputAlphabet.invFun symbol :: secondInput)) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program]
  congr 2
  funext stack
  cases stack with
  | first stack => simp [transferStacks]
  | bridge => simp [transferStacks]
  | second stack =>
      by_cases equal : stack = second.tm.k₀
      · subst stack
        simp [transferStacks, initList]
      · simp [transferStacks, initList, equal]

theorem step_drainBridge_nil
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    (machine first second).step
        (transferCfg first.tm second.tm BΓ (some .drainBridge)
          (.bridge none) [] [] secondInput) =
      some (liftSecondCfg first.tm second.tm BΓ
        (initList second.tm secondInput)) := by
  simp [FinTM2.step, TM2.step, machine, transferCfg, transferStacks,
    program, bridgeSymbol, liftSecondCfg, initList]
  congr 2
  funext stack
  cases stack with
  | first stack =>
      by_cases equal : stack = first.tm.k₁
      · subst stack
        simp [transferStacks, secondStacks, haltList]
      · simp [transferStacks, secondStacks, haltList, equal]
  | bridge => simp [secondStacks]
  | second stack => rfl

/-- The first transfer pass reverses the first output onto the bridge. -/
def drainFirstRun
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (firstOutput : List (first.tm.Γ first.tm.k₁))
    (bridgeContents : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    EvalsToInTime (machine first second).step
      (transferCfg first.tm second.tm BΓ (some .drainFirst)
        (.bridge none) firstOutput bridgeContents secondInput)
      (some (transferCfg first.tm second.tm BΓ
        (some .drainBridge) (.bridge none) []
        ((List.map first.outputAlphabet firstOutput).reverse ++
          bridgeContents)
        secondInput))
      (2 * firstOutput.length + 1) := by
  induction firstOutput generalizing bridgeContents with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
          (transferCfg first.tm second.tm BΓ (some .drainFirst)
            (.bridge none) [] bridgeContents secondInput) = _
      convert step_drainFirst_nil first second
        bridgeContents secondInput using 1
      all_goals rfl
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainFirst_cons first second symbol remaining
          bridgeContents secondInput)
      let pushed := evalsToInTime_single
        (step_pushBridge first second (first.outputAlphabet symbol)
          remaining bridgeContents secondInput)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction
        (first.outputAlphabet symbol :: bridgeContents)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, Nat.mul_add,
        Nat.add_assoc] using whole

/-- The second transfer pass reverses the bridge onto the second input. -/
def drainBridgeRun
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (bridgeContents : List BΓ)
    (secondInput : List (second.tm.Γ second.tm.k₀)) :
    EvalsToInTime (machine first second).step
      (transferCfg first.tm second.tm BΓ (some .drainBridge)
        (.bridge none) [] bridgeContents secondInput)
      (some (liftSecondCfg first.tm second.tm BΓ
        (initList second.tm
          ((List.map second.inputAlphabet.invFun bridgeContents).reverse ++
            secondInput))))
      (2 * bridgeContents.length + 1) := by
  induction bridgeContents generalizing secondInput with
  | nil =>
      refine
        { steps := 1
          evals_in_steps := ?_
          steps_le_m := by simp }
      simp only [Function.iterate_one]
      change (machine first second).step
          (transferCfg first.tm second.tm BΓ (some .drainBridge)
            (.bridge none) [] [] secondInput) = _
      convert step_drainBridge_nil first second secondInput using 1
      all_goals rfl
  | cons symbol remaining induction =>
      let popped := evalsToInTime_single
        (step_drainBridge_cons first second symbol remaining secondInput)
      let pushed := evalsToInTime_single
        (step_pushSecond first second symbol remaining secondInput)
      let firstTwo := EvalsToInTime.trans (machine first second).step
        1 1 _ _ _ popped pushed
      let rest := induction
        (second.inputAlphabet.invFun symbol :: secondInput)
      let whole := EvalsToInTime.trans (machine first second).step
        2 (2 * remaining.length + 1) _ _ _ firstTwo rest
      simpa [whole, List.reverse_cons, Nat.mul_add,
        Nat.add_assoc] using whole

theorem liftFirst_haltList_eq_transfer
    (first second : FinTM2) (Middle : Type)
    (firstOutput : List (first.Γ first.k₁)) :
    liftFirstCfg first second Middle (haltList first firstOutput) =
      transferCfg first second Middle (some .drainFirst)
        (.bridge none) firstOutput [] [] := by
  simp only [liftFirstCfg, transferCfg]
  congr 1
  funext stack
  cases stack with
  | first stack => rfl
  | bridge => rfl
  | second stack =>
      by_cases equal : stack = second.k₀
      · subst stack
        simp [firstStacks, transferStacks, initList]
      · simp [firstStacks, transferStacks, initList, equal]

/-- The bridge transfers an encoded intermediate word in order, using
exactly two counted steps per symbol in each pass plus the two empty-stack
tests. -/
def bridgeRun
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (middle : List BΓ) :
    EvalsToInTime (machine first second).step
      (liftFirstCfg first.tm second.tm BΓ
        (haltList first.tm
          (List.map first.outputAlphabet.invFun middle)))
      (some (liftSecondCfg first.tm second.tm BΓ
        (initList second.tm
          (List.map second.inputAlphabet.invFun middle))))
      (4 * middle.length + 2) := by
  let firstOutput := List.map first.outputAlphabet.invFun middle
  have passOne : EvalsToInTime (machine first second).step
      (transferCfg first.tm second.tm BΓ (some .drainFirst)
        (.bridge none) firstOutput [] [])
      (some (transferCfg first.tm second.tm BΓ
        (some .drainBridge) (.bridge none) [] middle.reverse []))
      (2 * middle.length + 1) := by
    simpa [firstOutput, List.map_map] using
      drainFirstRun first second firstOutput [] []
  have passTwo : EvalsToInTime (machine first second).step
      (transferCfg first.tm second.tm BΓ
        (some .drainBridge) (.bridge none) [] middle.reverse [])
      (some (liftSecondCfg first.tm second.tm BΓ
        (initList second.tm
          (List.map second.inputAlphabet.invFun middle))))
      (2 * middle.length + 1) := by
    simpa [List.map_reverse] using
      drainBridgeRun first second middle.reverse []
  let whole := EvalsToInTime.trans (machine first second).step
    (2 * middle.length + 1) (2 * middle.length + 1)
    _ _ _ passOne passTwo
  rw [liftFirst_haltList_eq_transfer first.tm second.tm BΓ]
  refine
    { toEvalsTo := by simpa [firstOutput] using whole.toEvalsTo
      steps_le_m := ?_ }
  have bounded := whole.steps_le_m
  dsimp [whole]
  dsimp [whole] at bounded
  omega

theorem initList_machine_eq_liftFirst
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (input : List (first.tm.Γ first.tm.k₀)) :
    initList (machine first second) input =
      liftFirstCfg first.tm second.tm BΓ
        (initList first.tm input) := by
  simp only [initList, machine, liftFirstCfg]
  congr 1
  funext stack
  cases stack with
  | bridge => simp [firstStacks]
  | second stack => simp [firstStacks]
  | first stack =>
      by_cases equal : stack = first.tm.k₀
      · subst stack
        simp [firstStacks]
      · simp [firstStacks, equal]

theorem haltList_machine_eq_liftSecond
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (output : List (second.tm.Γ second.tm.k₁)) :
    haltList (machine first second) output =
      liftSecondCfg first.tm second.tm BΓ
        (haltList second.tm output) := by
  simp only [haltList, machine, liftSecondCfg]
  congr 1
  funext stack
  cases stack with
  | first stack => simp [secondStacks]
  | bridge => simp [secondStacks]
  | second stack =>
      by_cases equal : stack = second.tm.k₁
      · subst stack
        simp [secondStacks]
      · simp [secondStacks, equal]

/-- Semantic sequential composition before replacing the intermediate word
length by its polynomial envelope. -/
def compositionRun
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (input : A) :
    let middleLength := (encodeB (f input)).length
    TM2OutputsInTime (machine first second)
      (List.map first.inputAlphabet.invFun (encodeA input))
      (some (List.map second.outputAlphabet.invFun
        (encodeC (g (f input)))))
      (second.time.eval middleLength +
        (4 * middleLength + 2 +
          first.time.eval (encodeA input).length)) := by
  let firstRun := liftFirstEvalsToInTime first second
    (first.outputsFun input)
  let transfer := bridgeRun first second (encodeB (f input))
  let secondRun := liftSecondEvalsToInTime first second
    (second.outputsFun (f input))
  let throughBridge := EvalsToInTime.trans (machine first second).step
    (first.time.eval (encodeA input).length)
    (4 * (encodeB (f input)).length + 2)
    _ _ _ firstRun transfer
  let whole := EvalsToInTime.trans (machine first second).step
    (4 * (encodeB (f input)).length + 2 +
      first.time.eval (encodeA input).length)
    (second.time.eval (encodeB (f input)).length)
    _ _ _ throughBridge secondRun
  dsimp only
  unfold TM2OutputsInTime
  convert whole using 1
  · exact initList_machine_eq_liftFirst first second _
  · simp only [Option.map_some, Option.some.injEq]
    convert haltList_machine_eq_liftSecond first second
      (List.map second.outputAlphabet.invFun
        (encodeC (g (f input)))) using 1
    congr 1

/-- A polynomial over natural coefficients is monotone on natural inputs. -/
theorem polynomial_eval_monotone (polynomial : Polynomial Nat) :
    Monotone polynomial.eval := by
  intro smaller larger bound
  induction polynomial using Polynomial.induction_on' with
  | add left right leftInduction rightInduction =>
      simp only [Polynomial.eval_add]
      exact Nat.add_le_add leftInduction rightInduction
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient
        (Nat.pow_le_pow_left bound degree)

/-- Explicit polynomial time envelope for sequential composition. -/
def compositionTimePolynomial
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g) :
    Polynomial Nat :=
  let outputBound := TM2OutputLength.outputLengthPolynomial first
  first.time + Polynomial.C 4 * outputBound + Polynomial.C 2 +
    second.time.comp outputBound

@[simp]
theorem compositionTimePolynomial_eval
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g)
    (length : Nat) :
    (compositionTimePolynomial first second).eval length =
      first.time.eval length +
        4 * (TM2OutputLength.outputLengthPolynomial first).eval length + 2 +
        second.time.eval
          ((TM2OutputLength.outputLengthPolynomial first).eval length) := by
  simp [compositionTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_comp]

/-- Polynomial-time sequential composition through a finite intermediate
encoding alphabet. -/
def computableInPolyTime
    {A B C AΓ BΓ CΓ : Type} [Fintype BΓ]
    {encodeA : A → List AΓ} {encodeB : B → List BΓ}
    {encodeC : C → List CΓ} {f : A → B} {g : B → C}
    (first : TM2ComputableInPolyTime encodeA encodeB f)
    (second : TM2ComputableInPolyTime encodeB encodeC g) :
    TM2ComputableInPolyTime encodeA encodeC (fun input => g (f input)) where
  tm := machine first second
  inputAlphabet := first.inputAlphabet
  outputAlphabet := second.outputAlphabet
  time := compositionTimePolynomial first second
  outputsFun input := by
    let raw := compositionRun first second input
    let middleLength := (encodeB (f input)).length
    let outputBound :=
      (TM2OutputLength.outputLengthPolynomial first).eval
        (encodeA input).length
    have middleBound : middleLength ≤ outputBound :=
      TM2OutputLength.output_length_le_polynomial_eval first input
    have secondBound : second.time.eval middleLength ≤
        second.time.eval outputBound :=
      polynomial_eval_monotone second.time middleBound
    refine
      { toEvalsTo := raw.toEvalsTo
        steps_le_m := ?_ }
    have rawBound := raw.steps_le_m
    rw [compositionTimePolynomial_eval]
    dsimp [middleLength, outputBound] at middleBound secondBound ⊢
    omega

end TM2CompositionMachine

end LeanTrominoes
