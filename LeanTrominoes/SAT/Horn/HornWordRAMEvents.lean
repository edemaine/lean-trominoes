/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMStackInvariant

/-! # Instruction certificates for one premise event -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.rules Reg.heads Reg.counters Reg.links Reg.stack Reg.index
  Reg.rule Reg.value Reg.top Reg.event Reg.scratch Reg.headValue

theorem pushState_bounded {B : ℕ} {data : Data} (before : NaturalData.Bounded B data) :
    NaturalData.Bounded (8*B) (pushState data) := by
  have a : NaturalData.Bounded (2*B) (push1 data) := readState_bounded before _ _ _
  have b : NaturalData.Bounded (4*B) (push2 data) := by
    simpa only [push2,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded a Reg.headValue Reg.stack Reg.top
  exact (b.mono (by omega)).set Reg.top (by have := b.1 Reg.top; have := b.1 Reg.one; omega)

def loweredCounter (data : Data) := data.set Reg.value (data.1 Reg.value-data.1 Reg.one)
def storedCounter (data : Data) := writeState (loweredCounter data) Reg.value Reg.counters Reg.rule

def eventAction : Code := .branch (.eq Reg.value Reg.zero) skip
  (.seq (decrement Reg.value) <| .seq (write Reg.value Reg.counters Reg.rule)
    (.branch (.eq Reg.value Reg.zero) pushHead skip))

def eventActionState (data : Data) :=
  if data.1 Reg.value=data.1 Reg.zero then data
  else if (storedCounter data).1 Reg.value=(storedCounter data).1 Reg.zero then pushState (storedCounter data)
  else storedCounter data

def eventActionCost (data : Data) : ℕ :=
  if data.1 Reg.value=data.1 Reg.zero then 2
  else if (storedCounter data).1 Reg.value=(storedCounter data).1 Reg.zero then 11 else 8

theorem eventActionCost_le (data : Data) : eventActionCost data≤11 := by
  unfold eventActionCost
  split <;> first | omega | (split <;> omega)

/-- A zero counter is ignored. Otherwise the stored counter decreases by one,
and exactly its transition to zero pushes a head. -/
theorem eventAction_exec {w B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0) (width : Fits w (16*B : ℕ)) :
    NaturalData.Exec w eventAction data (eventActionState data) (eventActionCost data) ∧
      NaturalData.Bounded (16*B) (eventActionState data) := by
  have lower : NaturalData.Bounded B (loweredCounter data) :=
    before.set Reg.value ((Nat.sub_le _ _).trans (before.1 _))
  have stored : NaturalData.Bounded (2*B) (storedCounter data) := writeState_bounded lower _ _ _
  let noProgram : Code := .seq (decrement Reg.value) <| .seq (write Reg.value Reg.counters Reg.rule)
    (.branch (.eq Reg.value Reg.zero) pushHead skip)
  by_cases empty : data.1 Reg.value=data.1 Reg.zero
  · have skipped := skip_exec before (Allocation.nat_fits_le width (by omega))
    have run := Structured.Exec.branch_yes (no := noProgram)
      (show Structured.Condition.Holds (.eq Reg.value Reg.zero) data.word by
        simpa [Structured.Condition.Holds,NaturalData.word] using empty) skipped
    exact ⟨by simpa only [eventAction,noProgram,eventActionState,eventActionCost,empty,ite_true,Nat.reduceAdd] using run,
      by simpa only [eventActionState,empty,ite_true] using before.mono (show B≤16*B by omega)⟩
  · have nonnegative : data.1 Reg.one≤data.1 Reg.value := by rw [unit,zero] at *; omega
    have first := NaturalData.sub_exec data Reg.value Reg.value Reg.one nonnegative
      (Allocation.nat_fits_le width ((Nat.sub_le _ _).trans ((before.1 _).trans (by omega))))
    have second := writeState_exec (loweredCounter data) Reg.value Reg.counters Reg.rule
      (by decide) (write_fits_of_bound lower width (by omega) _ _ _)
    by_cases ready : (storedCounter data).1 Reg.value=(storedCounter data).1 Reg.zero
    · have pushed := pushState_exec_bounded stored (Allocation.nat_fits_le width (by omega))
      have inner := Structured.Exec.branch_yes (no := skip)
        (show Structured.Condition.Holds (.eq Reg.value Reg.zero) (storedCounter data).word by
          simpa [Structured.Condition.Holds,NaturalData.word] using ready) pushed
      have branch := first.seq (second.seq inner)
      have run := Structured.Exec.branch_no (yes := skip)
        (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) data.word by
          simpa [Structured.Condition.Holds,NaturalData.word] using empty) branch
      refine ⟨?_,?_⟩
      · simpa only [eventAction,eventActionState,eventActionCost,empty,ready,ite_false,ite_true,
          decrement,loweredCounter,Nat.reduceAdd] using run
      · simpa only [eventActionState,empty,ready,ite_false,ite_true,← Nat.mul_assoc,Nat.reduceMul]
          using pushState_bounded stored
    · have skipped := skip_exec stored (Allocation.nat_fits_le width (by omega))
      have inner := Structured.Exec.branch_no (yes := pushHead)
        (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) (storedCounter data).word by
          simpa [Structured.Condition.Holds,NaturalData.word] using ready) skipped
      have branch := first.seq (second.seq inner)
      have run := Structured.Exec.branch_no (yes := skip)
        (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) data.word by
          simpa [Structured.Condition.Holds,NaturalData.word] using empty) branch
      refine ⟨?_,?_⟩
      · simpa only [eventAction,eventActionState,eventActionCost,empty,ready,ite_false,
          decrement,loweredCounter,Nat.reduceAdd] using run
      · simpa only [eventActionState,empty,ready,ite_false] using stored.mono (show 2*B≤16*B by omega)

def event0 (data : Data) := data.set Reg.event (data.1 Reg.event-data.1 Reg.one)
def event1 (data : Data) := readState (event0 data) Reg.rule Reg.edgeRules Reg.event
def event2 (data : Data) := readState (event1 data) Reg.value Reg.counters Reg.rule
def event3 (data : Data) := eventActionState (event2 data)
def eventState (data : Data) := readState (event3 data) Reg.event Reg.links Reg.event

def eventBodyCost (data : Data) : ℕ := 7+eventActionCost (event2 data)

theorem eventBodyCost_le (data : Data) : eventBodyCost data≤18 := by
  have bound := eventActionCost_le (event2 data)
  change 7+eventActionCost (event2 data)≤18
  omega

/-- One occurrence uses at most eighteen actual RAM instructions. -/
theorem eventBody_exec {w B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (zero : data.1 Reg.zero=0) (positive : 0<data.1 Reg.event)
    (width : Fits w (128*B : ℕ)) :
    NaturalData.Exec w eventBody data (eventState data) (eventBodyCost data) ∧
      NaturalData.Bounded (128*B) (eventState data) := by
  have b0 : NaturalData.Bounded B (event0 data) :=
    before.set Reg.event ((Nat.sub_le _ _).trans (before.1 _))
  have b1 : NaturalData.Bounded (2*B) (event1 data) := readState_bounded b0 _ _ _
  have b2 : NaturalData.Bounded (4*B) (event2 data) := by
    simpa only [event2,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded b1 Reg.value Reg.counters Reg.rule
  have first := NaturalData.sub_exec data Reg.event Reg.event Reg.one (by rw [unit]; omega)
    (Allocation.nat_fits_le width ((Nat.sub_le _ _).trans ((before.1 _).trans (by omega))))
  have second := readState_exec (event0 data) Reg.rule Reg.edgeRules Reg.event
    (read_fits_of_bound b0 width (by omega) _ _)
  have third := readState_exec (event1 data) Reg.value Reg.counters Reg.rule
    (read_fits_of_bound b1 width (by omega) _ _)
  have action := eventAction_exec b2
    (by simpa [event2,event1,event0,readState,NaturalData.set,Reg.edgeRules] using unit)
    (by simpa [event2,event1,event0,readState,NaturalData.set,Reg.edgeRules] using zero)
    (Allocation.nat_fits_le width (by omega))
  have b3 : NaturalData.Bounded (64*B) (event3 data) := by
    simpa only [event3,← Nat.mul_assoc,Nat.reduceMul] using action.2
  have last := readState_exec (event3 data) Reg.event Reg.links Reg.event
    (read_fits_of_bound b3 width (by omega) _ _)
  refine ⟨?_,?_⟩
  · simpa only [eventBody,eventState,eventBodyCost,event0,event1,event2,event3,eventAction,
      decrement,← Nat.add_assoc,Nat.reduceAdd,Nat.add_comm,Nat.add_left_comm] using
        first.seq (second.seq (third.seq (action.1.seq last)))
  · simpa only [eventState,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded b3 Reg.event Reg.links Reg.event

end LeanTrominoes.Horn.WordRAM
