/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Horn.HornWordRAMIndexInvariant

/-! # Instruction certificates for the Horn work stack -/
namespace LeanTrominoes.Horn.WordRAM
open ComplexityAbstract.RAM

attribute [local simp] Reg.heap Reg.request Reg.allocated Reg.cursor Reg.zero Reg.one Reg.atoms
  Reg.rules Reg.occurrences Reg.heads Reg.edgeAtoms Reg.edgeRules Reg.seen Reg.buckets Reg.counters
  Reg.links Reg.stack Reg.index Reg.atom Reg.rule Reg.value Reg.top Reg.event Reg.scratch Reg.headValue Reg.output

def push1 (data : Data) := readState data Reg.headValue Reg.heads Reg.rule
def push2 (data : Data) := writeState (push1 data) Reg.headValue Reg.stack Reg.top
def pushState (data : Data) := (push2 data).set Reg.top ((push2 data).1 Reg.top+(push2 data).1 Reg.one)

theorem pushState_exec {w : ℕ} (data : Data)
    (readFits : ReadFits w data Reg.heads Reg.rule)
    (writeFits : WriteFits w (push1 data) Reg.headValue Reg.stack Reg.top)
    (incrementFits : Fits w ((push2 data).1 Reg.top+(push2 data).1 Reg.one : ℕ)) :
    NaturalData.Exec w pushHead data (pushState data) 5 := by
  have first := readState_exec data Reg.headValue Reg.heads Reg.rule readFits
  have second := writeState_exec (push1 data) Reg.headValue Reg.stack Reg.top (by decide) writeFits
  have third := NaturalData.add_exec (push2 data) Reg.top Reg.top Reg.one incrementFits
  simpa only [pushHead,pushState,push1,push2,increment,add,Nat.reduceAdd] using first.seq (second.seq third)

theorem pushState_exec_bounded {w B : ℕ} {data : Data} (bounded : NaturalData.Bounded B data)
    (width : Fits w (8*B : ℕ)) : NaturalData.Exec w pushHead data (pushState data) 5 := by
  have one : NaturalData.Bounded (2*B) (push1 data) := readState_bounded bounded _ _ _
  have two : NaturalData.Bounded (4*B) (push2 data) := by
    simpa only [push2,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded one Reg.headValue Reg.stack Reg.top
  exact pushState_exec data (read_fits_of_bound bounded width (by omega) _ _)
    (write_fits_of_bound one width (by omega) _ _ _)
    (Allocation.nat_fits_le width (by have := two.1 Reg.top; have := two.1 Reg.one; omega))

theorem pushState_memory (data : Data) :
    (pushState data).2=Function.update data.2 (data.1 Reg.stack+data.1 Reg.top)
      (data.2 (data.1 Reg.heads+data.1 Reg.rule)) := by
  simp [pushState,push2,push1,readState,writeState,NaturalData.set,NaturalData.store]

theorem pushState_registers (data : Data) :
    (pushState data).1=Function.update
      (Function.update (Function.update data.1 Reg.headValue
        (data.2 (data.1 Reg.heads+data.1 Reg.rule))) Reg.scratch
          (data.1 Reg.stack+data.1 Reg.top)) Reg.top (data.1 Reg.top+data.1 Reg.one) := by
  funext i
  simp only [pushState,push2,push1,readState,writeState,NaturalData.set,NaturalData.store]
  by_cases a : i=Reg.top
  · subst i; simp
  · by_cases b : i=Reg.scratch
    · subst i; simp
    · by_cases c : i=Reg.headValue
      · subst i; simp
      · simp_all

def stackRead (data : Data) := readState data Reg.value Reg.counters Reg.index

def stackBranch (data : Data) : Data :=
  if (stackRead data).1 Reg.value=(stackRead data).1 Reg.zero then
    pushState ((stackRead data).set Reg.rule ((stackRead data).1 Reg.index))
  else stackRead data

def stackBodyState (data : Data) :=
  (stackBranch data).set Reg.index ((stackBranch data).1 Reg.index+(stackBranch data).1 Reg.one)

def stackBodyCost (data : Data) : ℕ :=
  if (stackRead data).1 Reg.value=(stackRead data).1 Reg.zero then 10 else 6

theorem skip_exec {w B : ℕ} {data : Data} (bounded : NaturalData.Bounded B data)
    (width : Fits w B) : NaturalData.Exec w skip data data 1 := by
  have run := NaturalData.copy_exec data Reg.zero Reg.zero
    (Allocation.nat_fits_le width (bounded.1 _))
  have same : data.set Reg.zero (data.1 Reg.zero)=data := by
    apply Prod.ext <;> simp [NaturalData.set]
  simpa only [skip,copy,same] using run

theorem stackBody_exec {w B : ℕ} {data : Data} (bounded : NaturalData.Bounded B data)
    (width : Fits w (64*B : ℕ)) :
    NaturalData.Exec w initialStackBody data (stackBodyState data) (stackBodyCost data) := by
  have loaded : NaturalData.Bounded (2*B) (stackRead data) := readState_bounded bounded _ _ _
  have first := readState_exec data Reg.value Reg.counters Reg.index
    (read_fits_of_bound bounded width (by omega) _ _)
  have branchBound : NaturalData.Bounded (32*B) (stackBranch data) := by
    unfold stackBranch
    split
    · have copied := loaded.set Reg.rule (loaded.1 Reg.index)
      have a : NaturalData.Bounded (4*B)
          (push1 ((stackRead data).set Reg.rule ((stackRead data).1 Reg.index))) := by
        simpa only [push1,← Nat.mul_assoc,Nat.reduceMul] using readState_bounded copied Reg.headValue Reg.heads Reg.rule
      have b : NaturalData.Bounded (8*B)
          (push2 ((stackRead data).set Reg.rule ((stackRead data).1 Reg.index))) := by
        simpa only [push2,← Nat.mul_assoc,Nat.reduceMul] using writeState_bounded a Reg.headValue Reg.stack Reg.top
      exact (b.mono (by omega)).set Reg.top (by have := b.1 Reg.top; have := b.1 Reg.one; omega)
    · exact loaded.mono (by omega)
  have last := NaturalData.add_exec (stackBranch data) Reg.index Reg.index Reg.one
    (Allocation.nat_fits_le width (by have := branchBound.1 Reg.index; have := branchBound.1 Reg.one; omega))
  by_cases ready : (stackRead data).1 Reg.value=(stackRead data).1 Reg.zero
  · have copied := NaturalData.copy_exec (stackRead data) Reg.rule Reg.index
      (Allocation.nat_fits_le width ((loaded.1 _).trans (by omega)))
    have pushed := pushState_exec_bounded (loaded.set Reg.rule (loaded.1 Reg.index))
      (Allocation.nat_fits_le width (by omega))
    have branch := Structured.Exec.branch_yes
      (c := Structured.Condition.eq Reg.value Reg.zero) (no := skip)
      (show Structured.Condition.Holds (.eq Reg.value Reg.zero) (stackRead data).word by
        simpa [Structured.Condition.Holds,NaturalData.word] using ready) (copied.seq pushed)
    simp only [stackBranch,ready,ite_true] at last
    simp only [stackBodyState,stackBodyCost,stackBranch,ready,ite_true]
    simpa only [initialStackBody,stackRead,copy,increment,add,Nat.reduceAdd] using first.seq (branch.seq last)
  · have skipped := skip_exec loaded (Allocation.nat_fits_le width (by omega))
    have branch := Structured.Exec.branch_no
      (c := Structured.Condition.eq Reg.value Reg.zero) (yes := .seq (copy Reg.rule Reg.index) pushHead)
      (show ¬Structured.Condition.Holds (.eq Reg.value Reg.zero) (stackRead data).word by
        simpa [Structured.Condition.Holds,NaturalData.word] using ready) skipped
    simp only [stackBranch,ready,ite_false] at last
    simp only [stackBodyState,stackBodyCost,stackBranch,ready,ite_false]
    simpa only [initialStackBody,stackRead,increment,add,Nat.reduceAdd] using first.seq (branch.seq last)

end LeanTrominoes.Horn.WordRAM
