/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition
import LeanTrominoes.Computation.RAM.RegisterFrame

/-! # Binary multiplication by bounded-word additions

Horner evaluation scans the second operand from its most significant digit.
Every iteration doubles the accumulator and conditionally adds the first
operand. The accumulator is truncated to the chosen binary precision.
-/
namespace LeanTrominoes.Domino.WordRAM.Binary
open ComplexityAbstract.RAM

/-- Binary digits give a value strictly below the precision modulus. -/
theorem value_lt_pow (memory : ℕ → ℕ) (base length : ℕ)
    (bits : ∀ i< length, memory (base+i)≤1) : value memory base length<2^length := by
  induction length with
  | zero => simp
  | succ length ih =>
    have old := ih (fun i hi => bits i (by omega))
    have last := bits length (by omega)
    rw [value_succ, pow_succ]
    nlinarith

/-- Removing the least significant digit is multiplication by two. -/
theorem value_low (memory : ℕ → ℕ) (base length : ℕ) :
    value memory base (length+1)=memory base+2*value memory (base+1) length := by
  simp only [value,Finset.sum_range_succ',pow_succ,Nat.pow_zero,mul_one,add_zero]
  rw [add_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.add_comm,Nat.add_left_comm,Nat.mul_comm,Nat.mul_left_comm]

/-- The addition certificate also gives exact truncation modulo the precision. -/
theorem Represents.mod_result {p : Layout} {source : ℕ → ℕ} {data : Data} {bias : ℕ}
    (h : Represents p source p.length data bias) :
    value data.2 p.output p.length=
      (value source p.first p.length+value source p.second p.length+bias)%2^p.length := by
  have bounded := value_lt_pow data.2 p.output p.length h.output_bits
  have eq := congrArg (fun n : ℕ => n%2^p.length) h.result
  simpa [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt bounded] using eq

namespace Multiply
abbrev savedSecond : Fin 16 := 13
abbrev savedFirst : Fin 16 := 14
abbrev remaining : Fin 16 := 15

structure Layout where
  first : ℕ
  second : ℕ
  output : ℕ
  length : ℕ
  first_disjoint : ∀ i< length, ∀ j< length, output+i≠first+j
  second_disjoint : ∀ i< length, ∀ j< length, output+i≠second+j

def Layout.double (p : Layout) : Binary.Layout where
  first := p.output
  second := p.output
  output := p.output
  length := p.length
  first_disjoint := by intros; omega
  second_disjoint := by intros; omega

def Layout.add (p : Layout) : Binary.Layout where
  first := p.first
  second := p.output
  output := p.output
  length := p.length
  first_disjoint := by intro i hi j hj _; exact p.first_disjoint i hi j hj
  second_disjoint := by intros; omega

/-- Caller-private multiplication controls survive every full addition. -/
theorem addition_private {w : ℕ} {data result : Data} {steps : ℕ}
    (execution : NaturalData.Exec w addProgram data result steps) (i : Fin 16)
    (high : 13 ≤ i.val) : result.1 i=data.1 i := by
  have unchanged : addProgram.PreservesRegister i := by
    fin_cases i <;> simp_all [addProgram,addInitialize,addLoop,addBody,
      Structured.Code.PreservesRegister,Structured.Primitive.PreservesRegister,
      Reg.index,Reg.carry,Reg.two,Reg.one,Reg.address,Reg.left,Reg.right,Reg.sum,Reg.digit]
  have equal := execution.register_eq unchanged
  simpa only [NaturalData.word,Int.natCast_inj] using equal

def accumulateProgram (left : Fin 16) : Code :=
  .seq (.atom (.copy Reg.first left)) <|
  .seq (.atom (.copy Reg.second Reg.output)) addProgram

structure Accumulated (p : Layout) (before after : Data) (left : ℕ) : Prop where
  length : after.1 Reg.length=p.length
  output : after.1 Reg.output=p.output
  one : after.1 Reg.one=1
  private_eq : ∀ i : Fin 16, 13 ≤ i.val → after.1 i=before.1 i
  bits : ∀ i< p.length, after.2 (p.output+i)≤1
  frame : ∀ address, (address< p.output ∨ p.output+p.length≤address) → after.2 address=before.2 address
  result : value after.2 p.output p.length=
    (value before.2 left p.length+value before.2 p.output p.length)%2^p.length

/-- Set the two argument pointers and execute a complete truncated addition. -/
theorem accumulate_exec {w : ℕ} (p : Layout) (data : Data) (left : Fin 16)
    (length : data.1 Reg.length=p.length) (output : data.1 Reg.output=p.output)
    (disjoint : ∀ i< p.length, ∀ j< p.length, i< j → p.output+i≠data.1 left+j)
    (leftBits : ∀ i< p.length, data.2 (data.1 left+i)≤1)
    (outputBits : ∀ i< p.length, data.2 (p.output+i)≤1)
    (small : Fits w (3:ℕ)) (leftFits : Fits w (data.1 left+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result, NaturalData.Exec w (accumulateProgram left) data result (13*p.length+8) ∧
      Accumulated p data result (data.1 left) := by
  let q : Binary.Layout := ⟨data.1 left,p.output,p.output,p.length,disjoint,by intros; omega⟩
  let first := data.set Reg.first (data.1 left)
  let prepared := first.set Reg.second (data.1 Reg.output)
  have firstExec := NaturalData.copy_exec data Reg.first left
    (Allocation.nat_fits_le leftFits (by omega : data.1 left≤data.1 left+p.length))
  have secondExec : NaturalData.Exec w (.atom (.copy Reg.second Reg.output)) first prepared 1 := by
    apply NaturalData.copy_exec
    simpa [first,NaturalData.set,Reg.first,Reg.output,output] using
      Allocation.nat_fits_le outputFits (by omega : p.output≤p.output+p.length)
  obtain ⟨result,execution,correct⟩ := addProgram_exec q prepared
    (by simpa [prepared,first,NaturalData.set,Reg.first,Reg.second,Reg.length] using length)
    (by simp [q,prepared,first,NaturalData.set,Reg.first,Reg.second])
    (by simp [q,prepared,first,NaturalData.set,output,Reg.first,Reg.second,Reg.output])
    (by simpa [q,prepared,first,NaturalData.set,Reg.first,Reg.second,Reg.output] using output)
    leftBits outputBits small leftFits outputFits outputFits lengthFits
  refine ⟨result,?_,?_⟩
  · convert firstExec.seq (secondExec.seq execution) using 1 <;>
      (try rfl) <;> simp only [q] <;> omega
  · constructor
    · exact correct.length
    · exact correct.output
    · exact correct.one
    · intro i high
      rw [addition_private execution i high]
      simp only [prepared,first,NaturalData.set]
      rw [Function.update_of_ne (by intro same; have := congrArg Fin.val same; norm_num [Reg.second] at this; omega),
        Function.update_of_ne (by intro same; have := congrArg Fin.val same; norm_num [Reg.first] at this; omega)]
    · exact correct.output_bits
    · exact correct.frame
    · simpa only [q,prepared,first,NaturalData.set,Nat.add_zero] using correct.mod_result

theorem Layout.first_outside (p : Layout) (j : ℕ) (within : j< p.length) :
    p.first+j< p.output ∨ p.output+p.length≤p.first+j := by
  by_contra absent
  push Not at absent
  have neq := p.first_disjoint (p.first+j-p.output) (by omega) j within
  omega

theorem Layout.second_outside (p : Layout) (j : ℕ) (within : j< p.length) :
    p.second+j< p.output ∨ p.output+p.length≤p.second+j := by
  by_contra absent
  push Not at absent
  have neq := p.second_disjoint (p.second+j-p.output) (by omega) j within
  omega

structure Represents (p : Layout) (source : ℕ → ℕ) (k : ℕ) (data : Data) : Prop where
  length : data.1 Reg.length=p.length
  output : data.1 Reg.output=p.output
  first : data.1 savedFirst=p.first
  second : data.1 savedSecond=p.second
  remaining : data.1 remaining=k
  one : data.1 Reg.one=1
  zero : data.1 Reg.index=0
  within : k≤p.length
  first_bits : ∀ i< p.length, source (p.first+i)≤1
  second_bits : ∀ i< p.length, source (p.second+i)≤1
  output_bits : ∀ i< p.length, data.2 (p.output+i)≤1
  frame : ∀ address, (address< p.output ∨ p.output+p.length≤address) → data.2 address=source address
  result : value data.2 p.output p.length=
    (value source p.first p.length*value source (p.second+k) (p.length-k))%2^p.length

theorem Represents.first_source {p : Layout} {source : ℕ → ℕ} {k : ℕ} {data : Data}
    (h : Represents p source k data) (j : ℕ) (within : j< p.length) :
    data.2 (p.first+j)=source (p.first+j) := h.frame _ (p.first_outside j within)

theorem Represents.second_source {p : Layout} {source : ℕ → ℕ} {k : ℕ} {data : Data}
    (h : Represents p source k data) (j : ℕ) (within : j< p.length) :
    data.2 (p.second+j)=source (p.second+j) := h.frame _ (p.second_outside j within)

/-- Arithmetic induction behind Horner multiplication at fixed precision. -/
theorem horner_step (a previous tail digit modulus : ℕ)
    (before : previous=a*tail%modulus) :
    ((previous+previous)%modulus+a*digit)%modulus=
      (a*(digit+2*tail))%modulus := by
  have doubled : (previous+previous)%modulus=(a*tail+a*tail)%modulus := by
    rw [before]
    exact (Nat.add_mod _ _ _).symm
  rw [doubled,Nat.mod_add_mod]
  congr 1
  ring

structure Stable (p : Layout) (before after : Data) : Prop where
  length : after.1 Reg.length=p.length
  output : after.1 Reg.output=p.output
  one : after.1 Reg.one=1
  private_eq : ∀ i : Fin 16, 13 ≤ i.val → after.1 i=before.1 i
  bits : ∀ i< p.length, after.2 (p.output+i)≤1
  frame : ∀ address, (address< p.output ∨ p.output+p.length≤address) → after.2 address=before.2 address

theorem Accumulated.stable {p : Layout} {before after : Data} {left : ℕ}
    (h : Accumulated p before after left) : Stable p before after :=
  ⟨h.length,h.output,h.one,h.private_eq,h.bits,h.frame⟩

def conditionalProgram : Code :=
  .branch (.eq Reg.left Reg.right) (.atom (.copy Reg.output Reg.output))
    (accumulateProgram savedFirst)

/-- Branch on the current source digit and optionally add the multiplicand. -/
theorem conditional_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (output : data.1 Reg.output=p.output)
    (one : data.1 Reg.one=1) (first : data.1 savedFirst=p.first)
    (bit : data.1 Reg.left≤1) (zero : data.1 Reg.right=0)
    (firstBits : ∀ i< p.length, data.2 (p.first+i)≤1)
    (outputBits : ∀ i< p.length, data.2 (p.output+i)≤1)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w conditionalProgram data result cost ∧ cost≤13*p.length+10 ∧
      Stable p data result ∧ value result.2 p.output p.length=
        (value data.2 p.output p.length+value data.2 p.first p.length*data.1 Reg.left)%2^p.length := by
  by_cases absent : data.1 Reg.left=0
  · have run : NaturalData.Exec w (.atom (.copy Reg.output Reg.output)) data data 1 := by
      have copy := NaturalData.copy_exec data Reg.output Reg.output
        (by rw [output]; exact Allocation.nat_fits_le outputFits (by omega))
      simpa [NaturalData.set] using copy
    refine ⟨data,2,?_,by omega,⟨length,output,one,fun _ _ => rfl,outputBits,fun _ _ => rfl⟩,?_⟩
    · exact Structured.Exec.branch_yes
        (by simp [Structured.Condition.Holds,NaturalData.word,absent,zero]) run
    · simp only [absent,Nat.mul_zero,Nat.add_zero]
      exact (Nat.mod_eq_of_lt (value_lt_pow _ _ _ outputBits)).symm
  · have present : data.1 Reg.left=1 := by omega
    obtain ⟨result,run,correct⟩ := accumulate_exec p data savedFirst length output
      (by intro i hi j hj _; simpa only [first] using p.first_disjoint i hi j hj)
      (by simpa only [first] using firstBits) outputBits small (by simpa only [first] using firstFits)
      outputFits lengthFits
    refine ⟨result,13*p.length+10,?_,le_refl _,correct.stable,?_⟩
    · exact Structured.Exec.branch_no
        (by simp [Structured.Condition.Holds,NaturalData.word,present,zero]) run
    · simpa [present,first,Nat.add_comm] using correct.result

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.output Reg.one
  Reg.left Reg.right Reg.address savedFirst savedSecond remaining

def body : Code :=
  .seq (.atom (.arithmetic .sub remaining remaining Reg.one)) <|
  .seq (accumulateProgram Reg.output) <|
  .seq (.atom (.arithmetic .add Reg.address savedSecond remaining)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.constant Reg.right 0)) <|
  .seq conditionalProgram (.atom (.constant Reg.index 0))

/-- One Horner iteration executes only ordinary primitive instructions. -/
theorem body_exec {w k : ℕ} (p : Layout) (source : ℕ → ℕ) (data : Data)
    (h : Represents p source k data) (positive : 0< k)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w body data result cost ∧ cost≤26*p.length+24 ∧
      Represents p source (k-1) result := by
  have within := h.within
  let decremented := data.set remaining (k-1)
  have decrement : NaturalData.Exec w (.atom (.arithmetic .sub remaining remaining Reg.one))
      data decremented 1 := by
    have run := NaturalData.sub_exec data remaining remaining Reg.one
      (by rw [h.remaining,h.one]; omega)
      (by rw [h.remaining,h.one]; exact Allocation.nat_fits_le lengthFits (by omega))
    simpa only [h.remaining,h.one] using run
  obtain ⟨doubled,doubleRun,doubleCorrect⟩ := accumulate_exec p decremented Reg.output
    (by simpa [decremented,NaturalData.set] using h.length)
    (by simpa [decremented,NaturalData.set] using h.output)
    (by intros; simp [decremented,NaturalData.set,h.output]; omega)
    (by simpa [decremented,NaturalData.set,h.output] using h.output_bits)
    (by simpa [decremented,NaturalData.set] using h.output_bits) small
    (by simpa [decremented,NaturalData.set,h.output] using outputFits) outputFits lengthFits
  have doublePrivate (i : Fin 16) (high : 13 ≤ i.val) := doubleCorrect.private_eq i high
  have doubleFirst : doubled.1 savedFirst=p.first := by
    simpa [decremented,NaturalData.set] using (doublePrivate savedFirst (by decide)).trans h.first
  have doubleSecond : doubled.1 savedSecond=p.second := by
    simpa [decremented,NaturalData.set] using (doublePrivate savedSecond (by decide)).trans h.second
  have doubleRemaining : doubled.1 remaining=k-1 := by
    simpa [decremented,NaturalData.set] using doublePrivate remaining (by decide)
  have doubleFrame (address : ℕ) (outside : address< p.output ∨ p.output+p.length≤address) :
      doubled.2 address=source address :=
    (doubleCorrect.frame address outside).trans (h.frame address outside)
  let addressed := doubled.set Reg.address (p.second+(k-1))
  let loaded := addressed.set Reg.left (source (p.second+(k-1)))
  let compared := loaded.set Reg.right 0
  have addressRun : NaturalData.Exec w (.atom (.arithmetic .add Reg.address savedSecond remaining))
      doubled addressed 1 := by
    have run := NaturalData.add_exec doubled Reg.address savedSecond remaining
      (by rw [doubleSecond,doubleRemaining]; exact Allocation.nat_fits_le secondFits (by omega))
    simpa only [doubleSecond,doubleRemaining] using run
  have loadRun : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) addressed loaded 1 := by
    have bits := h.second_bits (k-1) (by omega)
    have mem : doubled.2 (p.second+(k-1))=source (p.second+(k-1)) :=
      doubleFrame _ (p.second_outside _ (by omega))
    simpa [addressed,loaded,NaturalData.set,mem] using NaturalData.load_exec addressed Reg.left Reg.address
      (by simp only [addressed,NaturalData.set,Function.update_self]; exact Allocation.nat_fits_le secondFits (by omega))
      (by simp only [addressed,NaturalData.set,Function.update_self,mem]; exact Allocation.nat_fits_le small (by omega))
  have zeroRun := NaturalData.constant_exec loaded Reg.right 0
    (Allocation.nat_fits_le small (by omega : 0≤3))
  obtain ⟨chosen,branchCost,branchRun,branchBound,branchCorrect,branchValue⟩ := conditional_exec p compared
    (by simpa [compared,loaded,addressed,NaturalData.set] using doubleCorrect.length)
    (by simpa [compared,loaded,addressed,NaturalData.set] using doubleCorrect.output)
    (by simpa [compared,loaded,addressed,NaturalData.set] using doubleCorrect.one)
    (by simpa [compared,loaded,addressed,NaturalData.set] using doubleFirst)
    (by simpa [compared,loaded,addressed,NaturalData.set] using h.second_bits (k-1) (by omega))
    (by simp [compared,NaturalData.set])
    (by intro i hi; simpa only [compared,loaded,addressed,NaturalData.set,
        doubleFrame _ (p.first_outside i hi)] using h.first_bits i hi)
    doubleCorrect.bits small firstFits outputFits lengthFits
  let result := chosen.set Reg.index 0
  have resetRun := NaturalData.constant_exec chosen Reg.index 0
    (Allocation.nat_fits_le small (by omega : 0≤3))
  refine ⟨result,1+((13*p.length+8)+(1+(1+(1+(branchCost+1))))),?_,by omega,?_⟩
  · exact decrement.seq (doubleRun.seq (addressRun.seq (loadRun.seq (zeroRun.seq (branchRun.seq resetRun)))))
  · have sourceA : value doubled.2 p.first p.length=value source p.first p.length :=
      value_congr (fun i hi => doubleFrame _ (p.first_outside i hi))
    have sourceSuffix : value source (p.second+(k-1)) (p.length-(k-1))=
        source (p.second+(k-1))+2*value source (p.second+k) (p.length-k) := by
      have base : p.second+(k-1)+1=p.second+k := by omega
      have len : p.length-(k-1)=p.length-k+1 := by omega
      rw [len,value_low,base]
    constructor
    · simpa [result,NaturalData.set] using branchCorrect.length
    · simpa [result,NaturalData.set] using branchCorrect.output
    · simpa [result,compared,loaded,addressed,decremented,NaturalData.set] using
        (branchCorrect.private_eq savedFirst (by decide)).trans doubleFirst
    · simpa [result,compared,loaded,addressed,decremented,NaturalData.set] using
        (branchCorrect.private_eq savedSecond (by decide)).trans doubleSecond
    · simpa [result,compared,loaded,addressed,NaturalData.set] using
        (branchCorrect.private_eq remaining (by decide)).trans doubleRemaining
    · simpa [result,NaturalData.set] using branchCorrect.one
    · simp [result,NaturalData.set]
    · omega
    · exact h.first_bits
    · exact h.second_bits
    · exact branchCorrect.bits
    · intro address outside
      exact (branchCorrect.frame address outside).trans (doubleFrame address outside)
    · have doubling : value doubled.2 p.output p.length=
          (value data.2 p.output p.length+value data.2 p.output p.length)%2^p.length := by
        simpa [decremented,NaturalData.set,h.output] using doubleCorrect.result
      simp only [compared,loaded,addressed,NaturalData.set,Function.update_apply] at branchValue
      norm_num only [Reg.left,Reg.right,Reg.address] at branchValue
      rw [sourceA,doubling] at branchValue
      rw [show value result.2 p.output p.length=value chosen.2 p.output p.length from rfl,
        branchValue,sourceSuffix]
      exact horner_step _ _ _ _ _ h.result

def loop : Code := .loop (.lt Reg.index remaining) body

/-- The finite scan includes every loop test and back jump in its budget. -/
theorem loop_exec {w : ℕ} (p : Layout) (source : ℕ → ℕ)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∀ k data, Represents p source k data →
    ∃ result cost, NaturalData.Exec w loop data result cost ∧
      cost≤(26*p.length+26)*k+2 ∧ Represents p source 0 result := by
  intro k
  induction k with
  | zero =>
    intro data h
    refine ⟨data,2,?_,by omega,h⟩
    apply Structured.Exec.loop_done
    simp [Structured.Condition.Holds,NaturalData.word,h.zero,h.remaining]
  | succ k ih =>
    intro data h
    obtain ⟨middle,firstCost,firstRun,firstBound,middleRep⟩ :=
      body_exec p source data h (by omega) small firstFits secondFits outputFits lengthFits
    have middleRep : Represents p source k middle := by simpa only [Nat.add_sub_cancel] using middleRep
    obtain ⟨result,restCost,restRun,restBound,correct⟩ := ih middle middleRep
    refine ⟨result,firstCost+restCost+2,?_,by nlinarith,correct⟩
    exact Structured.Exec.loop_more
      (by simp [Structured.Condition.Holds,NaturalData.word,h.zero,h.remaining]) firstRun restRun

def setupProgram : Code :=
  .seq (.atom (.copy savedFirst Reg.first)) <|
  .seq (.atom (.copy savedSecond Reg.second)) <|
  .seq (.atom (.copy remaining Reg.length)) <|
  .seq (.atom (.constant Reg.one 1)) (.atom (.constant Reg.index 0))

def initialized (data : Data) : Data :=
  ((((data.set savedFirst (data.1 Reg.first)).set savedSecond (data.1 Reg.second)).set
    remaining (data.1 Reg.length)).set Reg.one 1).set Reg.index 0

def program : Code := .seq setupProgram loop

theorem program_size : program.size<128 := by decide

theorem setup_exec {w : ℕ} (p : Layout) (data : Data)
    (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (length : data.1 Reg.length=p.length)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ)) (lengthFits : Fits w p.length) :
    NaturalData.Exec w setupProgram data (initialized data) 5 := by
  let a := data.set savedFirst (data.1 Reg.first)
  let b := a.set savedSecond (data.1 Reg.second)
  let c := b.set remaining (data.1 Reg.length)
  let d := c.set Reg.one 1
  have r1 := NaturalData.copy_exec data savedFirst Reg.first
    (by rw [first]; exact Allocation.nat_fits_le firstFits (by omega))
  have r2 : NaturalData.Exec w (.atom (.copy savedSecond Reg.second)) a b 1 := by
    simpa [a,b,NaturalData.set] using NaturalData.copy_exec a savedSecond Reg.second
      (by simpa [a,NaturalData.set,second] using Allocation.nat_fits_le secondFits (by omega : p.second≤p.second+p.length))
  have r3 : NaturalData.Exec w (.atom (.copy remaining Reg.length)) b c 1 := by
    simpa [b,c,a,NaturalData.set] using NaturalData.copy_exec b remaining Reg.length
      (by simpa [a,b,NaturalData.set,length] using lengthFits)
  have r4 := NaturalData.constant_exec c Reg.one 1 (Allocation.nat_fits_le small (by omega : 1≤3))
  have r5 := NaturalData.constant_exec d Reg.index 0 (Allocation.nat_fits_le small (by omega : 0≤3))
  exact r1.seq (r2.seq (r3.seq (r4.seq r5)))

/-- One fixed ordinary word-RAM program multiplies arbitrary-precision binary
arrays modulo the output precision. Input digits and all external memory are
preserved. Only pointers, precision, and constants through three need fit a
machine word. The output array is initially zero. -/
theorem program_exec {w : ℕ} (p : Layout) (data : Data)
    (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (output : data.1 Reg.output=p.output) (length : data.1 Reg.length=p.length)
    (firstBits : ∀ i< p.length, data.2 (p.first+i)≤1)
    (secondBits : ∀ i< p.length, data.2 (p.second+i)≤1)
    (zero : ∀ i< p.length, data.2 (p.output+i)=0)
    (small : Fits w (3:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ))
    (outputFits : Fits w (p.output+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧
      cost≤26*p.length^2+26*p.length+7 ∧
      Represents p data.2 0 result ∧ value result.2 p.output p.length=
        (value data.2 p.first p.length*value data.2 p.second p.length)%2^p.length := by
  have initial : Represents p data.2 p.length (initialized data) := by
    constructor
    · simpa [initialized,NaturalData.set] using length
    · simpa [initialized,NaturalData.set] using output
    · simp [initialized,NaturalData.set,first]
    · simp [initialized,NaturalData.set,second]
    · simp [initialized,NaturalData.set,length]
    · simp [initialized,NaturalData.set]
    · simp [initialized,NaturalData.set]
    · exact le_refl _
    · exact firstBits
    · exact secondBits
    · intro i hi
      simp [initialized,NaturalData.set,zero i hi]
    · intros; rfl
    · simp only [initialized,NaturalData.set,Nat.sub_self,value_zero,Nat.mul_zero,Nat.zero_mod]
      simp only [value]
      apply Finset.sum_eq_zero
      intro i hi
      rw [zero i (Finset.mem_range.mp hi),Nat.zero_mul]
  obtain ⟨result,cost,run,bound,correct⟩ :=
    loop_exec p data.2 small firstFits secondFits outputFits lengthFits p.length (initialized data) initial
  refine ⟨result,5+cost,(setup_exec p data first second length small firstFits secondFits lengthFits).seq run,
    by nlinarith,correct,?_⟩
  simpa using correct.result

end Multiply
end LeanTrominoes.Domino.WordRAM.Binary
