/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMEventBounds

/-! # Instruction certificates for popping a Horn work item -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.zero Reg.one Reg.seen Reg.buckets Reg.stack Reg.atom Reg.value
  Reg.top Reg.event Reg.scratch

def pop0 (data : Data) := data.set Reg.top (data.1 Reg.top-data.1 Reg.one)
def pop1 (data : Data) := readState (pop0 data) Reg.atom Reg.stack Reg.top
def pop2 (data : Data) := readState (pop1 data) Reg.value Reg.seen Reg.atom
def pop3 (data : Data) := (pop2 data).set Reg.value 1
def pop4 (data : Data) := writeState (pop3 data) Reg.value Reg.seen Reg.atom
def pop5 (data : Data) := readState (pop4 data) Reg.event Reg.buckets Reg.atom

def popFront : Code := .seq (decrement Reg.top) <|
  .seq (read Reg.atom Reg.stack Reg.top) (read Reg.value Reg.seen Reg.atom)

def freshPop : Code := .seq (constant Reg.value 1) <|
  .seq (write Reg.value Reg.seen Reg.atom) <|
  .seq (read Reg.event Reg.buckets Reg.atom) processEvents

theorem popFront_exec {w B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (positive : 0<data.1 Reg.top) (width : Fits w (128*B : ℕ)) :
    NaturalData.Exec w popFront data (pop2 data) 5 ∧ NaturalData.Bounded (4*B) (pop2 data) := by
  have b0 : NaturalData.Bounded B (pop0 data) :=
    before.set Reg.top ((Nat.sub_le _ _).trans (before.1 _))
  have b1 : NaturalData.Bounded (2*B) (pop1 data) := readState_bounded b0 _ _ _
  have first := NaturalData.sub_exec data Reg.top Reg.top Reg.one (by rw [unit]; omega)
    (Allocation.nat_fits_le width ((Nat.sub_le _ _).trans ((before.1 _).trans (by omega))))
  have second := readState_exec (pop0 data) Reg.atom Reg.stack Reg.top
    (read_fits_of_bound b0 width (by omega) _ _)
  have third := readState_exec (pop1 data) Reg.value Reg.seen Reg.atom
    (read_fits_of_bound b1 width (by omega) _ _)
  refine ⟨?_,?_⟩
  · simpa only [popFront,pop0,pop1,pop2,decrement,Nat.reduceAdd] using first.seq (second.seq third)
  · simpa only [pop2,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded b1 Reg.value Reg.seen Reg.atom

theorem popBody_branch_exec {w B cost : ℕ} {data result : Data}
    (before : NaturalData.Bounded B data) (unit : data.1 Reg.one=1)
    (positive : 0<data.1 Reg.top) (width : Fits w (128*B : ℕ))
    (branch : NaturalData.Exec w (.branch (.eq Reg.value Reg.zero) freshPop skip) (pop2 data) result cost) :
    NaturalData.Exec w popBody data result (cost+5) := by
  have b0 : NaturalData.Bounded B (pop0 data) :=
    before.set Reg.top ((Nat.sub_le _ _).trans (before.1 _))
  have b1 : NaturalData.Bounded (2*B) (pop1 data) := readState_bounded b0 _ _ _
  have first := NaturalData.sub_exec data Reg.top Reg.top Reg.one (by rw [unit]; omega)
    (Allocation.nat_fits_le width ((Nat.sub_le _ _).trans ((before.1 _).trans (by omega))))
  have second := readState_exec (pop0 data) Reg.atom Reg.stack Reg.top
    (read_fits_of_bound b0 width (by omega) _ _)
  have third := readState_exec (pop1 data) Reg.value Reg.seen Reg.atom
    (read_fits_of_bound b1 width (by omega) _ _)
  have count : 1+(2+(2+cost))=cost+5 := by omega
  simpa only [popBody,freshPop,pop0,pop1,pop2,decrement,count] using
    first.seq (second.seq (third.seq branch))

/-- A previously seen atom is popped without traversing its bucket again. -/
theorem popBody_seen_exec {w B : ℕ} {data : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (positive : 0<data.1 Reg.top) (zero : data.1 Reg.zero=0)
    (seen : (pop2 data).1 Reg.value≠0) (width : Fits w (128*B : ℕ)) :
    NaturalData.Exec w popBody data (pop2 data) 8 := by
  have front := popFront_exec before unit positive width
  have skipped := skip_exec front.2 (Allocation.nat_fits_le width (by omega))
  have zeroAfter : (pop2 data).1 Reg.zero=0 := by
    simpa [pop2,pop1,pop0,readState,NaturalData.set] using zero
  have branch := Structured.Exec.branch_no (yes := freshPop)
    (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) (pop2 data).word by
      simpa [Structured.Condition.Holds,NaturalData.word,zeroAfter] using seen) skipped
  simpa only [Nat.reduceAdd] using popBody_branch_exec before unit positive width branch

/-- The prefix marks a fresh atom and loads its occurrence-list pointer.
The traversal certificate supplies the inner loop's result and exact cost. -/
theorem popBody_fresh_exec {w B cost : ℕ} {data result : Data} (before : NaturalData.Bounded B data)
    (unit : data.1 Reg.one=1) (positive : 0<data.1 Reg.top) (zero : data.1 Reg.zero=0)
    (fresh : (pop2 data).1 Reg.value=0) (width : Fits w (128*B : ℕ))
    (events : NaturalData.Exec w processEvents (pop5 data) result cost) :
    NaturalData.Exec w popBody data result (cost+11) := by
  have front := popFront_exec before unit positive width
  have enough : 1≤B := by have h := before.1 Reg.one; rw [unit] at h; exact h
  have b3 : NaturalData.Bounded (4*B) (pop3 data) := front.2.set Reg.value (by omega)
  have b4 : NaturalData.Bounded (8*B) (pop4 data) := by
    simpa only [pop4,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded b3 Reg.value Reg.seen Reg.atom
  have first := NaturalData.constant_exec (pop2 data) Reg.value 1 (Allocation.nat_fits_le width (by omega))
  have second := writeState_exec (pop3 data) Reg.value Reg.seen Reg.atom (by decide)
    (write_fits_of_bound b3 width (by omega) _ _ _)
  have third := readState_exec (pop4 data) Reg.event Reg.buckets Reg.atom
    (read_fits_of_bound b4 width (by omega) _ _)
  have zeroAfter : (pop2 data).1 Reg.zero=0 := by
    simpa [pop2,pop1,pop0,readState,NaturalData.set] using zero
  have inner := first.seq (second.seq (third.seq events))
  have branch := Structured.Exec.branch_yes (no := skip)
    (show Structured.Condition.Holds (.eq Reg.value Reg.zero) (pop2 data).word by
      simp [Structured.Condition.Holds,NaturalData.word,zeroAfter,fresh]) inner
  have run := popBody_branch_exec before unit positive width (by
    simpa only [freshPop,pop3,constant] using branch)
  have count : (1+(2+(2+cost))+1)+5=cost+11 := by omega
  simpa only [count] using run

end LeanTrominoes.Horn.WordRAM
