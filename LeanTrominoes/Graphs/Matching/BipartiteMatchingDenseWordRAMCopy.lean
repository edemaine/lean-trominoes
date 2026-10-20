/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Matching.BipartiteMatchingDenseWordRAMSemantics

/-! # Exact primitive execution of one stored-prefix pair copy -/
namespace LeanTrominoes.BipartiteMatching.DenseWordRAM
open ComplexityAbstract.RAM
attribute [local simp] Reg.one Reg.rowLeft Reg.rowRight Reg.source Reg.target Reg.copyIndex Reg.rowIndex Reg.value Reg.scratch

def copy1 (d : Data) := d.set Reg.rowIndex (d.1 Reg.source+d.1 Reg.copyIndex)
def copy2 (d : Data) := readState (copy1 d) Reg.rowLeft Reg.rowIndex Reg.value
def copy3 (d : Data) := (copy2 d).set Reg.rowIndex (d.1 Reg.target+d.1 Reg.copyIndex)
def copy4 (d : Data) := writeState (copy3 d) Reg.rowLeft Reg.rowIndex Reg.value
def copy5 (d : Data) := (copy4 d).set Reg.rowIndex (d.1 Reg.source+d.1 Reg.copyIndex)
def copy6 (d : Data) := readState (copy5 d) Reg.rowRight Reg.rowIndex Reg.value
def copy7 (d : Data) := (copy6 d).set Reg.rowIndex (d.1 Reg.target+d.1 Reg.copyIndex)
def copy8 (d : Data) := writeState (copy7 d) Reg.rowRight Reg.rowIndex Reg.value
def copyState (d : Data) := (copy8 d).set Reg.copyIndex (d.1 Reg.copyIndex+d.1 Reg.one)

attribute [local simp] copy1 copy2 copy3 copy4 copy5 copy6 copy7 copy8 copyState readState writeState NaturalData.set NaturalData.store

theorem copyPair_exec {B : Nat} (d : Data) (before : NaturalData.Bounded B d)
    (indices : d.1 Reg.source+d.1 Reg.copyIndex≤B ∧ d.1 Reg.target+d.1 Reg.copyIndex≤B)
    (addresses : d.1 Reg.rowLeft+(d.1 Reg.source+d.1 Reg.copyIndex)≤B ∧
      d.1 Reg.rowLeft+(d.1 Reg.target+d.1 Reg.copyIndex)≤B ∧
      d.1 Reg.rowRight+(d.1 Reg.source+d.1 Reg.copyIndex)≤B ∧
      d.1 Reg.rowRight+(d.1 Reg.target+d.1 Reg.copyIndex)≤B)
    (incrementFits : d.1 Reg.copyIndex+d.1 Reg.one≤B) :
    Natural.Exec B copyPair d (copyState d) 13 := by
  have a : Natural.Exec B (add Reg.rowIndex Reg.source Reg.copyIndex) d (copy1 d) 1 :=
    Natural.Exec.atom (Natural.Step.add d Reg.rowIndex Reg.source Reg.copyIndex indices.1)
  have b : Natural.Exec B (read Reg.rowLeft Reg.rowIndex Reg.value) (copy1 d) (copy2 d) 2 :=
    native_read _ _ _ _ (by simpa using addresses.1) (before.2 _)
  have bBound := b.bounded (a.bounded before)
  have c : Natural.Exec B (add Reg.rowIndex Reg.target Reg.copyIndex) (copy2 d) (copy3 d) 1 := by
    simpa [add] using Natural.Exec.atom (Natural.Step.add (bound := B) (copy2 d) Reg.rowIndex Reg.target Reg.copyIndex (by simpa using indices.2))
  have cBound := c.bounded bBound
  have e : Natural.Exec B (write Reg.rowLeft Reg.rowIndex Reg.value) (copy3 d) (copy4 d) 2 :=
    native_write _ _ _ _ (by decide) (by simpa using addresses.2.1) (cBound.1 _)
  have eBound := e.bounded cBound
  have f : Natural.Exec B (add Reg.rowIndex Reg.source Reg.copyIndex) (copy4 d) (copy5 d) 1 := by
    simpa [add] using Natural.Exec.atom (Natural.Step.add (bound := B) (copy4 d) Reg.rowIndex Reg.source Reg.copyIndex (by simpa using indices.1))
  have fBound := f.bounded eBound
  have g : Natural.Exec B (read Reg.rowRight Reg.rowIndex Reg.value) (copy5 d) (copy6 d) 2 :=
    native_read _ _ _ _ (by simpa using addresses.2.2.1) (fBound.2 _)
  have gBound := g.bounded fBound
  have h : Natural.Exec B (add Reg.rowIndex Reg.target Reg.copyIndex) (copy6 d) (copy7 d) 1 := by
    simpa [add] using Natural.Exec.atom (Natural.Step.add (bound := B) (copy6 d) Reg.rowIndex Reg.target Reg.copyIndex (by simpa using indices.2))
  have hBound := h.bounded gBound
  have i : Natural.Exec B (write Reg.rowRight Reg.rowIndex Reg.value) (copy7 d) (copy8 d) 2 :=
    native_write _ _ _ _ (by decide) (by simpa using addresses.2.2.2) (hBound.1 _)
  have j : Natural.Exec B (increment Reg.copyIndex) (copy8 d) (copyState d) 1 := by
    simpa [increment,add] using Natural.Exec.atom (Natural.Step.add (bound := B) (copy8 d) Reg.copyIndex Reg.copyIndex Reg.one (by simpa using incrementFits))
  simpa only [copyPair,Nat.reduceAdd] using a.seq (b.seq (c.seq (e.seq (f.seq (g.seq (h.seq (i.seq j)))))))

theorem copyState_controls (d : Data) :
    (copyState d).1 Reg.copyIndex=d.1 Reg.copyIndex+d.1 Reg.one ∧
    (copyState d).1 Reg.one=d.1 Reg.one ∧
    (copyState d).1 Reg.source=d.1 Reg.source ∧
    (copyState d).1 Reg.target=d.1 Reg.target ∧
    (copyState d).1 Reg.length=d.1 Reg.length := by simp [Reg.length]

theorem row_index_bound {n row col : Nat} (rowBound : row<n) (colBound : col<n) : row*n+col<n*n := by
  have step : row*n+col<(row+1)*n := by nlinarith
  exact step.trans_le (Nat.mul_le_mul_right n (by omega))

theorem row_index_disjoint {n a b i j : Nat} (hi : i<n) (hj : j<n) (different : a≠b) :
    a*n+i≠b*n+j := by
  intro same
  have positive : 0<n := by omega
  have one : (a*n+i)/n=a := by simpa [Nat.mul_comm,Nat.div_eq_of_lt hi] using Nat.mul_add_div positive a i
  have two : (b*n+j)/n=b := by simpa [Nat.mul_comm,Nat.div_eq_of_lt hj] using Nat.mul_add_div positive b j
  exact different (one.symm.trans ((congrArg (fun k => k/n) same).trans two))

end LeanTrominoes.BipartiteMatching.DenseWordRAM
