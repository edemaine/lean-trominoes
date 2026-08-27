/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMContractedDirectionAssemblerData

/-! # Inner machine for one role-tagged contracted incidence word -/

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace ContractedDirectionAssembler

open Computability StateTransition Turing
open NormalizationDirectionRequest.Batch

local instance contractedAssemblerAxisDirectionInhabited :
    Inhabited AxisDirection :=
  ⟨.invalid⟩

inductive Stack
  | input
  | forwardReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | start
  | initializeForward (terminal : Bool)
      (first : Option AxisDirection)
  | initializeReverse
  | scanForward
  | scanReverse
  | drainForward
  deriving DecidableEq, Fintype

abbrev State := Option (Token ⊕ AxisDirection)

abbrev Alphabet : Stack → Type
  | .input => Token
  | .forwardReverse => AxisDirection
  | .output => NormalizedToken

def forwardInitialization
    (terminal : Bool) (first : Option AxisDirection)
    (next : TM2.Stmt Alphabet Label State) :
    TM2.Stmt Alphabet Label State :=
  let withFirst := match first with
    | none => next
    | some direction =>
        .push .forwardReverse (fun _ => direction) next
  if terminal then
    .push .output (fun _ => .routeEnd) withFirst
  else
    withFirst

def program : Label → TM2.Stmt Alphabet Label State
  | .start =>
      .pop .input (fun _ token => token.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .initializeForward true none)
          (.goto fun state =>
            match state with
            | some (.inl (.role .retained)) =>
                .initializeForward true none
            | some (.inl (.role .throughFirst)) =>
                .initializeForward false none
            | some (.inl (.role .throughSecond)) =>
                .initializeReverse
            | some (.inl (.direction direction)) =>
                .initializeForward true (some direction)
            | some (.inl .incidenceEnd) =>
                .initializeForward true none
            | _ => .initializeForward true none))
  | .initializeForward terminal first =>
      forwardInitialization terminal first
        (.load (fun _ => none) (.goto fun _ => .scanForward))
  | .initializeReverse =>
      .push .output (fun _ => .routeEnd)
        (.load (fun _ => none) (.goto fun _ => .scanReverse))
  | .scanForward =>
      .pop .input (fun _ token => token.map Sum.inl)
        (.branch Option.isNone
          (.goto fun _ => .drainForward)
          (.branch (fun state =>
              match state with
              | some (.inl (.direction _)) => true
              | _ => false)
            (.push .forwardReverse
              (fun state =>
                match state with
                | some (.inl (.direction direction)) => direction
                | _ => default)
              (.load (fun _ => none) (.goto fun _ => .scanForward)))
            (.load (fun _ => none) (.goto fun _ => .scanForward))))
  | .scanReverse =>
      .pop .input (fun _ token => token.map Sum.inl)
        (.branch Option.isNone
          .halt
          (.branch (fun state =>
              match state with
              | some (.inl (.direction _)) => true
              | _ => false)
            (.push .output
              (fun state =>
                match state with
                | some (.inl (.direction direction)) =>
                    .direction direction.opposite
                | _ => .routeEnd)
              (.load (fun _ => none) (.goto fun _ => .scanReverse)))
            (.load (fun _ => none) (.goto fun _ => .scanReverse))))
  | .drainForward =>
      .pop .forwardReverse (fun _ direction => direction.map Sum.inr)
        (.branch Option.isNone
          .halt
          (.push .output
            (fun state =>
              match state with
              | some (.inr direction) => .direction direction
              | _ => .routeEnd)
            (.load (fun _ => none) (.goto fun _ => .drainForward))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .start
  σ := State
  initialState := none
  m := program

def tapes (input : List Token) (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) : ∀ stack, List (Alphabet stack)
  | .input => input
  | .forwardReverse => forwardReverse
  | .output => output

def startCfg (input : List Token) : TM2.Cfg Alphabet Label State :=
  ⟨some .start, none, tapes input [] []⟩

def initializeForwardCfg (terminal : Bool)
    (first : Option AxisDirection) (state : State)
    (input : List Token) : TM2.Cfg Alphabet Label State :=
  ⟨some (.initializeForward terminal first), state, tapes input [] []⟩

def initializeReverseCfg (state : State) (input : List Token) :
    TM2.Cfg Alphabet Label State :=
  ⟨some .initializeReverse, state, tapes input [] []⟩

def forwardCfg (input : List Token)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) : TM2.Cfg Alphabet Label State :=
  ⟨some .scanForward, none, tapes input forwardReverse output⟩

def reverseCfg (input : List Token)
    (output : List NormalizedToken) : TM2.Cfg Alphabet Label State :=
  ⟨some .scanReverse, none, tapes input [] output⟩

def drainCfg (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) : TM2.Cfg Alphabet Label State :=
  ⟨some .drainForward, none, tapes [] forwardReverse output⟩

def haltCfg (output : List NormalizedToken) :
    TM2.Cfg Alphabet Label State :=
  ⟨none, none, tapes [] [] output⟩

@[simp] theorem update_tapes_input (head : Token) (input : List Token)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    Function.update (tapes (head :: input) forwardReverse output)
        Stack.input input =
      tapes input forwardReverse output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_forwardReverse
    (input : List Token) (head : AxisDirection)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    Function.update (tapes input forwardReverse output)
        Stack.forwardReverse (head :: forwardReverse) =
      tapes input (head :: forwardReverse) output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_forwardReverse
    (head : AxisDirection) (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    Function.update (tapes [] (head :: forwardReverse) output)
        Stack.forwardReverse forwardReverse =
      tapes [] forwardReverse output := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem push_tapes_output
    (input : List Token) (forwardReverse : List AxisDirection)
    (head : NormalizedToken) (output : List NormalizedToken) :
    Function.update (tapes input forwardReverse output)
        Stack.output (head :: output) =
      tapes input forwardReverse (head :: output) := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_start_nil :
    TM2.step program (startCfg []) =
      some (initializeForwardCfg true none none []) := by
  simp [TM2.step, program, startCfg, initializeForwardCfg, tapes]

theorem step_start_cons (token : Token) (input : List Token) :
    TM2.step program (startCfg (token :: input)) =
      some (match token with
        | .role .retained =>
            initializeForwardCfg true none (some (.inl token)) input
        | .role .throughFirst =>
            initializeForwardCfg false none (some (.inl token)) input
        | .role .throughSecond =>
            initializeReverseCfg (some (.inl token)) input
        | .direction direction =>
            initializeForwardCfg true (some direction)
              (some (.inl token)) input
        | .incidenceEnd =>
            initializeForwardCfg true none (some (.inl token)) input) := by
  cases token with
  | role role => cases role <;>
      simp [TM2.step, program, startCfg, initializeForwardCfg,
        initializeReverseCfg, tapes]
  | direction direction =>
      simp [TM2.step, program, startCfg, initializeForwardCfg, tapes]
  | incidenceEnd =>
      simp [TM2.step, program, startCfg, initializeForwardCfg, tapes]

theorem step_initializeForward
    (terminal : Bool) (first : Option AxisDirection)
    (state : State) (input : List Token) :
    TM2.step program
        (initializeForwardCfg terminal first state input) =
      some (forwardCfg input first.toList
        (if terminal then [.routeEnd] else [])) := by
  cases terminal <;> cases first <;>
    simp [TM2.step, program, forwardInitialization,
      initializeForwardCfg, forwardCfg, tapes,
      push_tapes_forwardReverse, push_tapes_output]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_initializeReverse (state : State) (input : List Token) :
    TM2.step program (initializeReverseCfg state input) =
      some (reverseCfg input [.routeEnd]) := by
  simp [TM2.step, program, initializeReverseCfg, reverseCfg, tapes,
    push_tapes_output]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_forward_cons (token : Token) (input : List Token)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    TM2.step program
        (forwardCfg (token :: input) forwardReverse output) =
      some (forwardCfg input
        ((directionBlock token).reverse ++ forwardReverse) output) := by
  cases token <;>
    simp [TM2.step, program, forwardCfg, directionBlock, tapes,
      push_tapes_forwardReverse]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_forward_nil (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    TM2.step program (forwardCfg [] forwardReverse output) =
      some (drainCfg forwardReverse output) := by
  simp [TM2.step, program, forwardCfg, drainCfg, tapes]

theorem step_reverse_cons (token : Token) (input : List Token)
    (output : List NormalizedToken) :
    TM2.step program (reverseCfg (token :: input) output) =
      some (reverseCfg input
        ((Gadget.reverseDirections (directionBlock token)).map
          .direction ++ output)) := by
  cases token <;>
    simp [TM2.step, program, reverseCfg, directionBlock, tapes,
      push_tapes_output, Gadget.reverseDirections]
  all_goals
    funext stack
    cases stack <;> simp [tapes, Function.update]

theorem step_reverse_nil (output : List NormalizedToken) :
    TM2.step program (reverseCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, reverseCfg, haltCfg, tapes]

theorem step_drain_cons (direction : AxisDirection)
    (forwardReverse : List AxisDirection)
    (output : List NormalizedToken) :
    TM2.step program (drainCfg (direction :: forwardReverse) output) =
      some (drainCfg forwardReverse (.direction direction :: output)) := by
  simp [TM2.step, program, drainCfg, tapes,
    update_tapes_forwardReverse, push_tapes_output]
  funext stack
  cases stack <;> simp [tapes, Function.update]

theorem step_drain_nil (output : List NormalizedToken) :
    TM2.step program (drainCfg [] output) =
      some (haltCfg output) := by
  simp [TM2.step, program, drainCfg, haltCfg, tapes]

end ContractedDirectionAssembler
end PeriodicThreeDM
end LeanTrominoes
