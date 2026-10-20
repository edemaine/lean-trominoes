/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Allocation
import Mathlib.Tactic

/-! # Clearing the low-memory call arena and resetting registers

These programs implement the ordinary cold-input convention before invoking
Horn. The initialized output table is retained; the gap below caller data is
explicitly cleared one word at a time.
-/
namespace LeanTrominoes.ImplicationGraph.TwoSATExpression
open ComplexityAbstract.RAM

private theorem constant_exec {r w : ℕ} (data : Data r) (reg : Fin r) (value : ℤ) (fits : Fits w value) :
    Structured.Exec w (.atom (.constant reg value)) data (Function.update data.1 reg value,data.2) 1 := by
  apply Structured.Exec.atom
  simp [Structured.Primitive.eval,fits]

private theorem copy_exec {r w : ℕ} (data : Data r) (reg src : Fin r) (fits : Fits w (data.1 src)) :
    Structured.Exec w (.atom (.copy reg src)) data (Function.update data.1 reg (data.1 src),data.2) 1 := by
  apply Structured.Exec.atom
  simp [Structured.Primitive.eval,fits]

def coldGapPrefix : Structured.Code 32 :=
  .seq (.atom (.copy 0 5)) (.seq (.atom (.copy 3 1))
    (.seq (.atom (.constant 4 0)) (.atom (.constant 5 1))))

def coldGap : Structured.Code 32 :=
  .seq coldGapPrefix (.loop (.lt 3 0)
    (.seq (.atom (.store 3 4)) (.atom (.arithmetic .add 3 3 5))))

theorem coldGap_exec {w start finish : ℕ} (data : Data 32)
    (index : data.1 1=start) (length : data.1 2=start) (arena : data.1 5=finish)
    (within : start≤finish) (word : Fits w finish) (unit : Fits w 1) :
    Structured.Exec w coldGap data
      (Allocation.registers data.1 finish start start finish,Allocation.clear data.2 start (finish-start))
      (4*(finish-start)+6) := by
  have startFits := Allocation.nat_fits_le word within
  have zeroFits := Allocation.nat_fits_le (a:=0) (b:=1) unit (by omega)
  let first : Data 32 := (Function.update data.1 0 (finish : ℕ),data.2)
  let second : Data 32 := (Function.update first.1 3 (start : ℕ),data.2)
  let third : Data 32 := (Function.update second.1 4 0,data.2)
  let fourth : Data 32 := (Function.update third.1 5 1,data.2)
  have h1 : Structured.Exec w (.atom (.copy 0 5)) data first 1 := by
    simpa only [first,arena] using copy_exec data 0 5 (by simpa only [arena] using word)
  have h2 : Structured.Exec w (.atom (.copy 3 1)) first second 1 := by
    simpa [second,first,Function.update_apply,index] using
      copy_exec first 3 1 (by simpa [first,Function.update_apply,index] using startFits)
  have h3 := constant_exec second 4 0 zeroFits
  have h4 := constant_exec third 5 1 unit
  have initialRegisters : fourth.1=Allocation.registers data.1 finish start start start := by
    funext i
    fin_cases i <;>
      simp [fourth,third,second,first,Allocation.registers,Allocation.frontier,Allocation.count,
        Allocation.result,Allocation.cursor,Allocation.zero,Allocation.one,index,length,arena,Function.update_apply]
  have prefixExec : Structured.Exec w coldGapPrefix data fourth 4 := by
    simpa only [coldGapPrefix,first,second,third,fourth,arena,index,Nat.reduceAdd] using h1.seq (h2.seq (h3.seq h4))
  have loopExec := Allocation.clear_exec (r:=26) (w:=w) data.1 data.2 finish start start start (finish-start)
    (by omega) word unit
  have startData : fourth=(Allocation.registers data.1 finish start start start,data.2) :=
    Prod.ext initialRegisters rfl
  rw [← startData] at loopExec
  have execution := prefixExec.seq loopExec
  change Structured.Exec w coldGap data _ (4+(4*(finish-start)+2)) at execution
  convert execution using 1 <;> omega

def resetUpto (r : ℕ) : (n : ℕ) → n≤r → Structured.Code (r+1)
  | 0, _ => .atom (.constant 0 0)
  | n+1, within => .seq (resetUpto r n (by omega)) (.atom (.constant ⟨n+1,by omega⟩ 0))

def resetRegisters {r : ℕ} (frame : Fin (r+1) → ℤ) (n : ℕ) : Fin (r+1) → ℤ :=
  fun i => if i.val≤n then 0 else frame i

theorem resetUpto_exec {r w : ℕ} (data : Data (r+1)) (n : ℕ) (within : n≤r) (zero : Fits w 0) :
    Structured.Exec w (resetUpto r n within) data (resetRegisters data.1 n,data.2) (n+1) := by
  induction n with
  | zero =>
    have registers : Function.update data.1 0 0=resetRegisters data.1 0 := by
      funext i
      simp only [Function.update_apply,resetRegisters]
      by_cases equal : i=0
      · simp [equal]
      · have val : i.val≠0 := by intro h; apply equal; exact Fin.ext h
        simp [equal,val]
    simpa only [resetUpto,registers] using constant_exec data 0 0 zero
  | succ n ih =>
    have first := ih (by omega)
    have last := constant_exec (resetRegisters data.1 n,data.2) (⟨n+1,by omega⟩ : Fin (r+1)) 0 zero
    have registers : Function.update (resetRegisters data.1 n) (⟨n+1,by omega⟩ : Fin (r+1)) 0=
        resetRegisters data.1 (n+1) := by
      funext i
      simp only [Function.update_apply,resetRegisters]
      split_ifs <;> first | rfl | (exfalso; simp_all [Fin.ext_iff] <;> omega)
    simpa only [resetUpto,registers,Nat.add_assoc] using first.seq last

/-- Exactly thirty-two ordinary constant instructions reset the Horn registers. -/
def reset32 : Structured.Code 32 := resetUpto 31 31 (by omega)

theorem reset32_exec {w : ℕ} (data : Data 32) (zero : Fits w 0) :
    Structured.Exec w reset32 data (fun _ => 0,data.2) 32 := by
  have registers : resetRegisters data.1 31=(fun _ => 0) := by
    funext i
    simp only [resetRegisters]
    exact ite_eq_left (by omega)
  simpa only [reset32,registers] using resetUpto_exec data 31 (by omega) zero

end LeanTrominoes.ImplicationGraph.TwoSATExpression
