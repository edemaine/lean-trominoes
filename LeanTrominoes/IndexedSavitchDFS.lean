import LeanTrominoes.IndexedSavitch
import Mathlib.Computability.Primrec.List

/-!
# Depth-first indexed Savitch evaluation

`divideReachIndexBool` is a convenient recursive specification, but a direct
compilation of its recursion can retain the whole recursive-call tree.  This
file gives the recurrence an explicit depth-first evaluator.  A configuration
contains one current query and one continuation frame per unfinished query.
In particular, it never stores the exponentially large set of graph states or
the exponentially large recursion tree.

The evaluator deliberately checks every midpoint instead of short-circuiting.
This gives every query of a fixed depth an exact, input-independent running
time, which makes the later correctness proof by induction on the depth
straightforward.  It affects time but not the polynomial stack bound.
-/

namespace LeanTrominoes.FiniteState

/-- One reachability subproblem: at `depth`, connect `first` to `last`. -/
structure DivideQuery where
  depth : Nat
  first : Nat
  last : Nat
  deriving DecidableEq, Repr

namespace DivideQuery

def equivData : DivideQuery ≃ Nat × Nat × Nat where
  toFun query := (query.depth, query.first, query.last)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv query := by cases query; rfl
  right_inv data := by rcases data with ⟨depth, first, last⟩; rfl

noncomputable instance : Primcodable DivideQuery :=
  Primcodable.ofEquiv (Nat × Nat × Nat) equivData

end DivideQuery

/-- Continuation for one unfinished positive-depth query.

`depth` is the depth of either child query.  Midpoints are visited from
`middle` down to zero.  `accumulated` records whether an earlier midpoint
worked, and `leftAnswer` distinguishes waiting for the left child from
waiting for the right child. -/
structure DivideFrame where
  depth : Nat
  first : Nat
  last : Nat
  middle : Nat
  accumulated : Bool
  leftAnswer : Option Bool
  deriving DecidableEq, Repr

namespace DivideFrame

def equivData :
    DivideFrame ≃ Nat × Nat × Nat × Nat × Bool × Option Bool where
  toFun frame :=
    (frame.depth, frame.first, frame.last, frame.middle,
      frame.accumulated, frame.leftAnswer)
  invFun data :=
    ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.1,
      data.2.2.2.2.1, data.2.2.2.2.2⟩
  left_inv frame := by cases frame; rfl
  right_inv data := by
    rcases data with ⟨depth, first, last, middle, accumulated, leftAnswer⟩
    rfl

noncomputable instance : Primcodable DivideFrame :=
  Primcodable.ofEquiv
    (Nat × Nat × Nat × Nat × Bool × Option Bool) equivData

end DivideFrame

/-- State of the depth-first evaluator.

When `answer = none`, `query` is about to be evaluated.  When
`answer = some result`, the result is about to be delivered to the top stack
frame; an empty stack means evaluation has halted. -/
structure DivideEvalState where
  query : DivideQuery
  stack : List DivideFrame
  answer : Option Bool
  deriving DecidableEq, Repr

namespace DivideEvalState

def equivData :
    DivideEvalState ≃ DivideQuery × List DivideFrame × Option Bool where
  toFun state := (state.query, state.stack, state.answer)
  invFun data := ⟨data.1, data.2.1, data.2.2⟩
  left_inv state := by cases state; rfl
  right_inv data := by rcases data with ⟨query, stack, answer⟩; rfl

noncomputable instance : Primcodable DivideEvalState :=
  Primcodable.ofEquiv
    (DivideQuery × List DivideFrame × Option Bool) equivData

end DivideEvalState

/-- Initial configuration for one reachability query. -/
def divideEvalInitial (depth first last : Nat) : DivideEvalState :=
  ⟨⟨depth, first, last⟩, [], none⟩

/-- One small step of depth-first Savitch evaluation. -/
def divideEvalStep (stateCount : Nat)
    (relation : Nat → Nat → Bool)
    (state : DivideEvalState) : DivideEvalState :=
  match state.answer with
  | none =>
      match state.query.depth with
      | 0 =>
          { state with
            answer := some
              (decide (state.query.first = state.query.last) ||
                relation state.query.first state.query.last) }
      | depth + 1 =>
          match stateCount with
          | 0 => { state with answer := some false }
          | middle + 1 =>
              { query := ⟨depth, state.query.first, middle⟩
                stack :=
                  { depth
                    first := state.query.first
                    last := state.query.last
                    middle
                    accumulated := false
                    leftAnswer := none } :: state.stack
                answer := none }
  | some answer =>
      match state.stack with
      | [] => state
      | frame :: rest =>
          match frame.leftAnswer with
          | none =>
              { query := ⟨frame.depth, frame.middle, frame.last⟩
                stack := { frame with leftAnswer := some answer } :: rest
                answer := none }
          | some leftAnswer =>
              let accumulated :=
                frame.accumulated || (leftAnswer && answer)
              match frame.middle with
              | 0 =>
                  { state with
                    stack := rest
                    answer := some accumulated }
              | middle + 1 =>
                  { query := ⟨frame.depth, frame.first, middle⟩
                    stack :=
                      { frame with
                        middle
                        accumulated
                        leftAnswer := none } :: rest
                    answer := none }

/-- Exact number of evaluator steps allocated to a query.  Evaluation does
not short-circuit, so the recurrence accounts for both children of every
midpoint. -/
def divideEvalFuel (stateCount : Nat) : Nat → Nat
  | 0 => 1
  | depth + 1 =>
      1 + stateCount * (2 * divideEvalFuel stateCount depth + 2)

/-- Result produced by the explicit depth-first evaluator. -/
def divideReachIndexDFSBool (stateCount : Nat)
    (relation : Nat → Nat → Bool)
    (depth first last : Nat) : Bool :=
  (((divideEvalStep stateCount relation)^[divideEvalFuel stateCount depth])
    (divideEvalInitial depth first last)).answer.getD false

/-- Directed-cycle search using the explicit depth-first reachability
evaluator. -/
def cycleSearchIndexDFSBoolAtDepth (stateCount depth : Nat)
    (relation : Nat → Nat → Bool) : Bool :=
  boundedAny (fun first =>
    boundedAny (fun second =>
      relation first second &&
        divideReachIndexDFSBool stateCount relation depth second first)
      stateCount)
    stateCount

/-- Every saved frame fits below a root-depth budget.  For a stack whose
innermost frame is at the head, a frame's child depth plus the length of its
suffix is at most the original root depth. -/
def DivideStackFits (rootDepth : Nat) : List DivideFrame → Prop
  | [] => True
  | frame :: rest =>
      frame.depth + (frame :: rest).length ≤ rootDepth ∧
        DivideStackFits rootDepth rest

/-- The current query and every continuation frame fit within the original
root-depth budget. -/
def DivideEvalState.FitsDepth
    (rootDepth : Nat) (state : DivideEvalState) : Prop :=
  state.query.depth + state.stack.length ≤ rootDepth ∧
    DivideStackFits rootDepth state.stack

theorem divideEvalInitial_fitsDepth (depth first last : Nat) :
    (divideEvalInitial depth first last).FitsDepth depth := by
  simp [DivideEvalState.FitsDepth, DivideStackFits, divideEvalInitial]

theorem divideEvalStep_fitsDepth
    (stateCount rootDepth : Nat) (relation : Nat → Nat → Bool)
    (state : DivideEvalState)
    (fits : state.FitsDepth rootDepth) :
    (divideEvalStep stateCount relation state).FitsDepth rootDepth := by
  rcases fits with ⟨queryFits, stackFits⟩
  cases answer : state.answer with
  | none =>
      cases queryDepth : state.query.depth with
      | zero =>
          simpa [divideEvalStep, DivideEvalState.FitsDepth, answer,
            queryDepth] using And.intro queryFits stackFits
      | succ depth =>
          cases count : stateCount with
          | zero =>
              simpa [divideEvalStep, DivideEvalState.FitsDepth, answer,
                queryDepth, count] using And.intro queryFits stackFits
          | succ middle =>
              simp only [divideEvalStep, answer, queryDepth,
                DivideEvalState.FitsDepth, List.length_cons]
              constructor
              · omega
              · constructor
                · change depth + (state.stack.length + 1) ≤ rootDepth
                  omega
                · exact stackFits
  | some answerValue =>
      cases stack : state.stack with
      | nil =>
          simpa [divideEvalStep, DivideEvalState.FitsDepth, answer, stack]
            using And.intro queryFits stackFits
      | cons frame rest =>
          simp only [stack, List.length_cons] at queryFits
          simp only [stack, DivideStackFits] at stackFits
          rcases stackFits with ⟨frameFits, restFits⟩
          cases left : frame.leftAnswer with
          | none =>
              simp only [divideEvalStep, answer, stack, left,
                DivideEvalState.FitsDepth, List.length_cons]
              exact ⟨frameFits, frameFits, restFits⟩
          | some leftAnswer =>
              cases middle : frame.middle with
              | zero =>
                  simp only [divideEvalStep, answer, stack, left, middle,
                    DivideEvalState.FitsDepth]
                  constructor
                  · omega
                  · exact restFits
              | succ middle =>
                  simp only [divideEvalStep, answer, stack, left, middle,
                    DivideEvalState.FitsDepth, List.length_cons]
                  exact ⟨frameFits, frameFits, restFits⟩

theorem divideEvalIterate_fitsDepth
    (stateCount rootDepth steps : Nat)
    (relation : Nat → Nat → Bool) (state : DivideEvalState)
    (fits : state.FitsDepth rootDepth) :
    ((divideEvalStep stateCount relation)^[steps] state).FitsDepth
      rootDepth := by
  induction steps generalizing state with
  | zero => exact fits
  | succ steps induction =>
      rw [Function.iterate_succ_apply']
      exact divideEvalStep_fitsDepth stateCount rootDepth relation _
        (induction state fits)

theorem divideEvalIterate_stack_length_le_depth
    (stateCount depth first last steps : Nat)
    (relation : Nat → Nat → Bool) :
    (((divideEvalStep stateCount relation)^[steps]
      (divideEvalInitial depth first last)).stack).length ≤ depth := by
  have fits := divideEvalIterate_fitsDepth
    stateCount depth steps relation
    (divideEvalInitial depth first last)
    (divideEvalInitial_fitsDepth depth first last)
  exact (Nat.le_add_left _ _).trans fits.1

end LeanTrominoes.FiniteState
