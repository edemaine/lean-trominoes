/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedSavitchDFSCorrectness
import LeanTrominoes.IndexedSavitchComputability

/-!
# Computability of depth-first indexed Savitch evaluation

The explicit query, continuation-frame, and evaluator-state encodings are
finite products and lists.  This file proves that constructing and inspecting
those values, taking one evaluator step, computing its exact fuel, and running
the complete directed-cycle search are primitive recursive.
-/

namespace LeanTrominoes.FiniteState

namespace DivideQuery

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem depth_primrec : Primrec DivideQuery.depth := by
  exact (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem first_primrec : Primrec DivideQuery.first := by
  exact (Primrec.fst.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem last_primrec : Primrec DivideQuery.last := by
  exact (Primrec.snd.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem mk_primrec :
    Primrec fun data : Nat × Nat × Nat =>
      DivideQuery.mk data.1 data.2.1 data.2.2 := by
  change Primrec equivData.symm
  exact Primrec.of_equiv_symm

end DivideQuery

namespace DivideFrame

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem depth_primrec : Primrec DivideFrame.depth := by
  exact (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem first_primrec : Primrec DivideFrame.first := by
  exact (Primrec.fst.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem last_primrec : Primrec DivideFrame.last := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp equivData_primrec))).of_eq
      fun _ => rfl

theorem middle_primrec : Primrec DivideFrame.middle := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp
      (Primrec.snd.comp (Primrec.snd.comp equivData_primrec)))).of_eq
        fun _ => rfl

theorem accumulated_primrec : Primrec DivideFrame.accumulated := by
  exact (Primrec.fst.comp
    (Primrec.snd.comp
      (Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp equivData_primrec))))).of_eq
            fun _ => rfl

theorem leftAnswer_primrec : Primrec DivideFrame.leftAnswer := by
  exact (Primrec.snd.comp
    (Primrec.snd.comp
      (Primrec.snd.comp
        (Primrec.snd.comp
          (Primrec.snd.comp equivData_primrec))))).of_eq
            fun _ => rfl

theorem mk_primrec :
    Primrec fun data :
      Nat × Nat × Nat × Nat × Bool × Option Bool =>
      DivideFrame.mk data.1 data.2.1 data.2.2.1 data.2.2.2.1
        data.2.2.2.2.1 data.2.2.2.2.2 := by
  change Primrec equivData.symm
  exact Primrec.of_equiv_symm

end DivideFrame

namespace DivideEvalState

theorem equivData_primrec : Primrec equivData :=
  Primrec.of_equiv

theorem query_primrec : Primrec DivideEvalState.query := by
  exact (Primrec.fst.comp equivData_primrec).of_eq fun _ => rfl

theorem stack_primrec : Primrec DivideEvalState.stack := by
  exact (Primrec.fst.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem answer_primrec : Primrec DivideEvalState.answer := by
  exact (Primrec.snd.comp (Primrec.snd.comp equivData_primrec)).of_eq
    fun _ => rfl

theorem mk_primrec :
    Primrec fun data :
      DivideQuery × List DivideFrame × Option Bool =>
      DivideEvalState.mk data.1 data.2.1 data.2.2 := by
  change Primrec equivData.symm
  exact Primrec.of_equiv_symm

end DivideEvalState

theorem divideEvalInitial_primrec :
    Primrec fun data : Nat × Nat × Nat =>
      divideEvalInitial data.1 data.2.1 data.2.2 := by
  unfold divideEvalInitial
  exact DivideEvalState.mk_primrec.comp
    (Primrec.pair
      (DivideQuery.mk_primrec.comp Primrec.id)
      (Primrec.pair (Primrec.const []) (Primrec.const none)))

private def positiveDepth (stateCount depth : Nat)
    (state : DivideEvalState) : DivideEvalState :=
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

private def noAnswer (stateCount : Nat)
    (relation : Nat → Nat → Bool)
    (state : DivideEvalState) : DivideEvalState :=
  match state.query.depth with
  | 0 =>
      { state with
        answer := some
          (decide (state.query.first = state.query.last) ||
            relation state.query.first state.query.last) }
  | depth + 1 => positiveDepth stateCount depth state

private abbrev WaitData :=
  Bool × DivideFrame × List DivideFrame

private def waitRight (data : WaitData) : DivideEvalState :=
  { query := ⟨data.2.1.depth, data.2.1.middle, data.2.1.last⟩
    stack :=
      { data.2.1 with leftAnswer := some data.1 } :: data.2.2
    answer := none }

private abbrev FinishData :=
  (DivideQuery × Bool) ×
    (DivideFrame × List DivideFrame)

private def finishZero (data : FinishData) : DivideEvalState :=
  { query := data.1.1
    stack := data.2.2
    answer := some data.1.2 }

private def finishSucc
    (data : FinishData) (middle : Nat) : DivideEvalState :=
  { query := ⟨data.2.1.depth, data.2.1.first, middle⟩
    stack :=
      { data.2.1 with
        middle
        accumulated := data.1.2
        leftAnswer := none } :: data.2.2
    answer := none }

private def finishRight (data : FinishData) : DivideEvalState :=
  match data.2.1.middle with
  | 0 => finishZero data
  | middle + 1 => finishSucc data middle

private def deliver (returned : Bool)
    (state : DivideEvalState) : DivideEvalState :=
  match state.stack with
  | [] => state
  | frame :: rest =>
      match frame.leftAnswer with
      | none => waitRight (returned, frame, rest)
      | some leftAnswer =>
          finishRight
            ((state.query,
              frame.accumulated || (leftAnswer && returned)),
              frame, rest)

private theorem positiveDepth_primrec
    {α : Type*} [Primcodable α] {stateCount : α → Nat}
    (stateCountPrimrec : Primrec stateCount) :
    Primrec₂ fun (input : α × DivideEvalState) depth =>
      positiveDepth (stateCount input.1) depth input.2 := by
  let original : Primrec fun
      data : (α × DivideEvalState) × Nat => data.1 :=
    Primrec.fst
  let depth : Primrec fun
      data : (α × DivideEvalState) × Nat => data.2 :=
    Primrec.snd
  let state := DivideEvalState.query_primrec.comp
    (Primrec.snd.comp original)
  let stack := DivideEvalState.stack_primrec.comp
    (Primrec.snd.comp original)
  let first := DivideQuery.first_primrec.comp state
  let last := DivideQuery.last_primrec.comp state
  let count := stateCountPrimrec.comp (Primrec.fst.comp original)
  let zeroState :=
    DivideEvalState.mk_primrec.comp
      (Primrec.pair state
        (Primrec.pair stack (Primrec.const (some false))))
  have successorState :
      Primrec₂ fun
          (data : (α × DivideEvalState) × Nat) middle =>
        DivideEvalState.mk
          (DivideQuery.mk data.2 data.1.2.query.first middle)
          (DivideFrame.mk data.2 data.1.2.query.first
            data.1.2.query.last middle false none :: data.1.2.stack)
          none := by
    let data : Primrec fun
        input : ((α × DivideEvalState) × Nat) × Nat => input.1 :=
      Primrec.fst
    let middle : Primrec fun
        input : ((α × DivideEvalState) × Nat) × Nat => input.2 :=
      Primrec.snd
    let childDepth := depth.comp data
    let first := first.comp data
    let last := last.comp data
    let rest := stack.comp data
    let childQuery :=
      DivideQuery.mk_primrec.comp
        (Primrec.pair childDepth (Primrec.pair first middle))
    let frame :=
      DivideFrame.mk_primrec.comp
        (Primrec.pair childDepth
          (Primrec.pair first
            (Primrec.pair last
              (Primrec.pair middle
                (Primrec.pair
                  (Primrec.const false) (Primrec.const none))))))
    exact DivideEvalState.mk_primrec.comp
      (Primrec.pair childQuery
        (Primrec.pair
          (Primrec.list_cons.comp frame rest)
          (Primrec.const none)))
  exact (Primrec.nat_casesOn count zeroState successorState).of_eq
    fun data => by
      dsimp only
      unfold positiveDepth
      cases stateCount data.1.1 <;> rfl

private theorem noAnswer_primrec
    {α : Type*} [Primcodable α]
    {stateCount : α → Nat} {relation : α → Nat → Nat → Bool}
    (stateCountPrimrec : Primrec stateCount)
    (relationPrimrec : Primrec fun input : (α × Nat) × Nat =>
      relation input.1.1 input.1.2 input.2) :
    Primrec fun input : α × DivideEvalState =>
      noAnswer (stateCount input.1) (relation input.1) input.2 := by
  let state : Primrec fun input : α × DivideEvalState => input.2 :=
    Primrec.snd
  let query := DivideEvalState.query_primrec.comp state
  let stack := DivideEvalState.stack_primrec.comp state
  let depth := DivideQuery.depth_primrec.comp query
  let first := DivideQuery.first_primrec.comp query
  let last := DivideQuery.last_primrec.comp query
  let relationAtQuery := relationPrimrec.comp
    (Primrec.pair
      (Primrec.pair Primrec.fst first) last)
  let baseAnswer := Primrec.or.comp
    (Primrec.eq.decide.comp first last) relationAtQuery
  let baseState :=
    DivideEvalState.mk_primrec.comp
      (Primrec.pair query
        (Primrec.pair stack
          (Primrec.option_some.comp baseAnswer)))
  exact (Primrec.nat_casesOn depth baseState
    (positiveDepth_primrec stateCountPrimrec)).of_eq fun input => by
      dsimp only
      unfold noAnswer
      cases input.2.query.depth <;> rfl

private theorem waitRight_primrec : Primrec waitRight := by
  let returned : Primrec fun data : WaitData => data.1 :=
    Primrec.fst
  let frame : Primrec fun data : WaitData => data.2.1 :=
    Primrec.fst.comp Primrec.snd
  let rest : Primrec fun data : WaitData => data.2.2 :=
    Primrec.snd.comp Primrec.snd
  let depth := DivideFrame.depth_primrec.comp frame
  let first := DivideFrame.first_primrec.comp frame
  let last := DivideFrame.last_primrec.comp frame
  let middle := DivideFrame.middle_primrec.comp frame
  let accumulated := DivideFrame.accumulated_primrec.comp frame
  let query := DivideQuery.mk_primrec.comp
    (Primrec.pair depth (Primrec.pair middle last))
  let waitingFrame := DivideFrame.mk_primrec.comp
    (Primrec.pair depth
      (Primrec.pair first
        (Primrec.pair last
          (Primrec.pair middle
            (Primrec.pair accumulated
              (Primrec.option_some.comp returned))))))
  exact (DivideEvalState.mk_primrec.comp
    (Primrec.pair query
      (Primrec.pair (Primrec.list_cons.comp waitingFrame rest)
        (Primrec.const none)))).of_eq fun _ => rfl

private theorem finishZero_primrec : Primrec finishZero := by
  let query : Primrec fun data : FinishData => data.1.1 :=
    Primrec.fst.comp Primrec.fst
  let accumulated : Primrec fun data : FinishData => data.1.2 :=
    Primrec.snd.comp Primrec.fst
  let rest : Primrec fun data : FinishData => data.2.2 :=
    Primrec.snd.comp Primrec.snd
  exact (DivideEvalState.mk_primrec.comp
    (Primrec.pair query
      (Primrec.pair rest
        (Primrec.option_some.comp accumulated)))).of_eq
          fun _ => rfl

private theorem finishSucc_primrec : Primrec₂ finishSucc := by
  let frame : Primrec fun data : FinishData => data.2.1 :=
    Primrec.fst.comp Primrec.snd
  let rest : Primrec fun data : FinishData => data.2.2 :=
    Primrec.snd.comp Primrec.snd
  let depth := DivideFrame.depth_primrec.comp frame
  let first := DivideFrame.first_primrec.comp frame
  let last := DivideFrame.last_primrec.comp frame
  let data : Primrec fun input : FinishData × Nat => input.1 :=
    Primrec.fst
  let nextMiddle : Primrec fun input : FinishData × Nat => input.2 :=
    Primrec.snd
  let depth := depth.comp data
  let first := first.comp data
  let last := last.comp data
  let rest := rest.comp data
  let accumulated :=
    (Primrec.snd.comp Primrec.fst).comp data
  let nextQuery := DivideQuery.mk_primrec.comp
    (Primrec.pair depth (Primrec.pair first nextMiddle))
  let nextFrame := DivideFrame.mk_primrec.comp
    (Primrec.pair depth
      (Primrec.pair first
        (Primrec.pair last
          (Primrec.pair nextMiddle
            (Primrec.pair accumulated (Primrec.const none))))))
  exact (DivideEvalState.mk_primrec.comp
    (Primrec.pair nextQuery
      (Primrec.pair
        (Primrec.list_cons.comp nextFrame rest)
        (Primrec.const none)))).of_eq fun _ => rfl

private theorem finishRight_primrec : Primrec finishRight := by
  let middle := DivideFrame.middle_primrec.comp
    (Primrec.fst.comp
      (Primrec.snd (α := DivideQuery × Bool)
        (β := DivideFrame × List DivideFrame)))
  exact (Primrec.nat_casesOn middle finishZero_primrec
    finishSucc_primrec).of_eq fun data => by
      unfold finishRight
      cases data.2.1.middle <;> rfl

private theorem deliver_primrec :
    Primrec fun data : Bool × DivideEvalState =>
      deliver data.1 data.2 := by
  let returned : Primrec fun data : Bool × DivideEvalState => data.1 :=
    Primrec.fst
  let state : Primrec fun data : Bool × DivideEvalState => data.2 :=
    Primrec.snd
  let stack := DivideEvalState.stack_primrec.comp state
  have frameBranch :
      Primrec₂ fun (data : Bool × DivideEvalState)
          (entry : DivideFrame × List DivideFrame) =>
        match entry.1.leftAnswer with
        | none => waitRight (data.1, entry.1, entry.2)
        | some leftAnswer =>
            finishRight
              ((data.2.query,
                entry.1.accumulated || (leftAnswer && data.1)),
                entry.1, entry.2) := by
    let data : Primrec fun input :
        (Bool × DivideEvalState) ×
          (DivideFrame × List DivideFrame) => input.1 :=
      Primrec.fst
    let returned := returned.comp data
    let state := state.comp data
    let entry : Primrec fun input :
        (Bool × DivideEvalState) ×
          (DivideFrame × List DivideFrame) => input.2 :=
      Primrec.snd
    let frame := Primrec.fst.comp entry
    let rest := Primrec.snd.comp entry
    let savedLeft := DivideFrame.leftAnswer_primrec.comp frame
    let waiting := waitRight_primrec.comp
      (Primrec.pair returned (Primrec.pair frame rest))
    let after : Primrec₂ fun
        (input : (Bool × DivideEvalState) ×
          (DivideFrame × List DivideFrame)) leftAnswer =>
        finishRight
          ((input.1.2.query,
            input.2.1.accumulated || (leftAnswer && input.1.1)),
            input.2.1, input.2.2) := by
      let originalQuery : Primrec fun input :
          (((Bool × DivideEvalState) ×
            (DivideFrame × List DivideFrame)) × Bool) =>
            input.1.1.2.query :=
        DivideEvalState.query_primrec.comp
          (state.comp₂ Primrec₂.left)
      let accumulated : Primrec fun input :
          (((Bool × DivideEvalState) ×
            (DivideFrame × List DivideFrame)) × Bool) =>
            input.1.2.1.accumulated ||
              (input.2 && input.1.1.1) :=
        Primrec.or.comp
          (DivideFrame.accumulated_primrec.comp
            (frame.comp₂ Primrec₂.left))
          (Primrec.and.comp Primrec₂.right
            (returned.comp₂ Primrec₂.left))
      exact finishRight_primrec.comp
        (Primrec.pair
          (Primrec.pair originalQuery accumulated)
          (Primrec.pair
            (frame.comp₂ Primrec₂.left)
            (rest.comp₂ Primrec₂.left)))
    exact (Primrec.option_casesOn savedLeft waiting after).of_eq
      fun input => by
        cases leftAnswer : input.2.1.leftAnswer <;>
          simp [leftAnswer]
  exact (Primrec.list_casesOn stack state frameBranch).of_eq
    fun data => by
      cases stackValue : data.2.stack <;>
        simp [deliver, stackValue]

theorem divideEvalStep_primrec
    {α : Type*} [Primcodable α]
    {stateCount : α → Nat} {relation : α → Nat → Nat → Bool}
    (stateCountPrimrec : Primrec stateCount)
    (relationPrimrec : Primrec fun input : (α × Nat) × Nat =>
      relation input.1.1 input.1.2 input.2) :
    Primrec fun input : α × DivideEvalState =>
      divideEvalStep (stateCount input.1) (relation input.1) input.2 := by
  let answer := DivideEvalState.answer_primrec.comp
    (Primrec.snd (α := α))
  let noAnswerProof :=
    noAnswer_primrec stateCountPrimrec relationPrimrec
  have hasAnswer :
      Primrec₂ fun (input : α × DivideEvalState) returned =>
        deliver returned input.2 :=
    deliver_primrec.comp
      (Primrec.pair Primrec₂.right
        (Primrec.snd.comp₂ Primrec₂.left))
  exact (Primrec.option_casesOn answer noAnswerProof hasAnswer).of_eq
    fun input => by
      cases answerValue : input.2.answer with
      | none =>
          simp only [divideEvalStep, answerValue]
          unfold noAnswer positiveDepth
          rfl
      | some returned =>
          simp only [divideEvalStep, answerValue]
          unfold deliver waitRight finishRight
          rfl

theorem divideEvalFuel_primrec : Primrec₂ divideEvalFuel := by
  let step : Nat → Nat × Nat → Nat :=
    fun stateCount data =>
      1 + stateCount * (2 * data.2 + 2)
  have stepPrimrec : Primrec₂ step := by
    exact Primrec.nat_add.comp₂
      (Primrec.const 1)
      (Primrec.nat_mul.comp₂ Primrec₂.left
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp
            (Primrec.const 2)
            (Primrec.snd.comp₂ Primrec₂.right))
          (Primrec.const 2)))
  exact (Primrec.nat_rec (Primrec.const 1) stepPrimrec).of_eq
    fun stateCount depth => by
      induction depth with
      | zero => rfl
      | succ depth induction =>
          simp [divideEvalFuel, step, induction]

theorem divideReachIndexDFSBool_primrec
    {α : Type*} [Primcodable α]
    {stateCount depth first last : α → Nat}
    {relation : α → Nat → Nat → Bool}
    (stateCountPrimrec : Primrec stateCount)
    (depthPrimrec : Primrec depth)
    (firstPrimrec : Primrec first)
    (lastPrimrec : Primrec last)
    (relationPrimrec : Primrec fun input : (α × Nat) × Nat =>
      relation input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      divideReachIndexDFSBool (stateCount input) (relation input)
        (depth input) (first input) (last input) := by
  let fuel := divideEvalFuel_primrec.comp
    stateCountPrimrec depthPrimrec
  let initial := divideEvalInitial_primrec.comp
    (Primrec.pair depthPrimrec
      (Primrec.pair firstPrimrec lastPrimrec))
  have step : Primrec₂ fun input state =>
      divideEvalStep (stateCount input) (relation input) state :=
    divideEvalStep_primrec stateCountPrimrec relationPrimrec
  have run : Primrec fun input =>
      ((divideEvalStep (stateCount input) (relation input))^[
        divideEvalFuel (stateCount input) (depth input)])
        (divideEvalInitial (depth input) (first input) (last input)) :=
    Primrec.nat_iterate fuel initial step
  exact (Primrec.option_getD_default.comp
    (DivideEvalState.answer_primrec.comp run)).of_eq fun input => by
      rfl

theorem cycleSearchIndexDFSBoolAtDepth_primrec
    {α : Type*} [Primcodable α]
    {stateCount depth : α → Nat}
    {relation : α → Nat → Nat → Bool}
    (stateCountPrimrec : Primrec stateCount)
    (depthPrimrec : Primrec depth)
    (relationPrimrec : Primrec fun input : (α × Nat) × Nat =>
      relation input.1.1 input.1.2 input.2) :
    Primrec fun input =>
      cycleSearchIndexDFSBoolAtDepth
        (stateCount input) (depth input) (relation input) := by
  have reach : Primrec fun input : (α × Nat) × Nat =>
      divideReachIndexDFSBool
        (stateCount input.1.1) (relation input.1.1)
        (depth input.1.1) input.2 input.1.2 := by
    have liftedRelation : Primrec fun input :
        ((((α × Nat) × Nat) × Nat) × Nat) =>
          relation input.1.1.1.1 input.1.2 input.2 :=
      relationPrimrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.fst.comp Primrec.fst)))
            (Primrec.snd.comp Primrec.fst))
          Primrec.snd)
    apply divideReachIndexDFSBool_primrec
    · exact stateCountPrimrec.comp
        (Primrec.fst.comp Primrec.fst)
    · exact depthPrimrec.comp
        (Primrec.fst.comp Primrec.fst)
    · exact Primrec.snd
    · exact Primrec.snd.comp Primrec.fst
    · exact liftedRelation
  have predicate : Primrec fun input : (α × Nat) × Nat =>
      relation input.1.1 input.1.2 input.2 &&
        divideReachIndexDFSBool
          (stateCount input.1.1) (relation input.1.1)
          (depth input.1.1) input.2 input.1.2 :=
    Primrec.and.comp relationPrimrec reach
  have loops := nestedBoundedAny_primrec
    (α := α)
    (predicate := fun input first last =>
      relation input first last &&
        divideReachIndexDFSBool
          (stateCount input) (relation input)
          (depth input) last first)
    predicate
  exact loops.comp Primrec.id stateCountPrimrec

end LeanTrominoes.FiniteState
