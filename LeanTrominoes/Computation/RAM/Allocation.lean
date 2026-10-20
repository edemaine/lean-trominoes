/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.StructuredCompile

/-! # Word RAM with memory allocation

Arrays are fresh consecutive blocks of bounded words. Allocation reserves a
block above a monotonically increasing frontier and explicitly initializes its
cells. It does not reclaim storage. Indexed access uses a pointer plus an index.
The implementations below use only ordinary word-RAM instructions; allocation
and array access do not introduce unit-cost Lean functions.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Allocation

/-- A block describes the addresses owned by one allocated array. Its length
is specification data; programs store lengths in words when they need them. -/
structure Block where
  base : ℕ
  length : ℕ
  deriving DecidableEq, Repr

def Block.Owns (block : Block) (address : ℕ) : Prop :=
  block.base ≤ address ∧ address < block.base+block.length

def Block.read (block : Block) (memory : ℕ → ℤ) (i : Fin block.length) : ℤ :=
  memory (block.base+i.val)

/-- Clearing is implemented one cell at a time, rather than assumed free. -/
def clear (memory : ℕ → ℤ) (base : ℕ) : ℕ → (ℕ → ℤ)
  | 0 => memory
  | n+1 => clear (Function.update memory base 0) (base+1) n

theorem clear_apply (memory : ℕ → ℤ) (base count address : ℕ) :
    clear memory base count address =
      if base ≤ address ∧ address < base+count then 0 else memory address := by
  induction count generalizing memory base with
  | zero => simp [clear]
  | succ n ih =>
    rw [clear,ih]
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- Allocation preserves every cell outside its block, including all earlier
arrays and the input. -/
theorem clear_frame {memory : ℕ → ℤ} {base count address : ℕ}
    (outside : ¬(base ≤ address ∧ address < base+count)) :
    clear memory base count address=memory address := by
  simp [clear_apply,outside]

theorem clear_zero {memory : ℕ → ℤ} {base count address : ℕ}
    (inside : base ≤ address ∧ address < base+count) :
    clear memory base count address=0 := by
  simp [clear_apply,inside]

/-- Earlier blocks remain disjoint from a fresh allocation. The total frontier,
rather than just the live storage, must fit the address space. -/
theorem fresh_disjoint (old : Block) {frontier count : ℕ}
    (earlier : old.base+old.length ≤ frontier) :
    ∀ address, old.Owns address → ¬(Block.Owns ⟨frontier,count⟩ address) := by
  simp only [Block.Owns]
  omega

/-- Six reserved registers belong to the allocator. User registers have indices
at least six and are preserved. `count` is the requested number of cells. -/
def frontier (r : ℕ) : Fin (r+6) := ⟨0,by omega⟩
def count (r : ℕ) : Fin (r+6) := ⟨1,by omega⟩
def result (r : ℕ) : Fin (r+6) := ⟨2,by omega⟩
def cursor (r : ℕ) : Fin (r+6) := ⟨3,by omega⟩
def zero (r : ℕ) : Fin (r+6) := ⟨4,by omega⟩
def one (r : ℕ) : Fin (r+6) := ⟨5,by omega⟩

/-- The allocator uses ten static instructions. A request for n cells executes
4n+7 instructions, including every store and loop-control instruction. -/
def program (r : ℕ) : Structured.Code (r+6) :=
  .seq (.atom (.constant (zero r) 0)) <|
  .seq (.atom (.constant (one r) 1)) <|
  .seq (.atom (.copy (result r) (frontier r))) <|
  .seq (.atom (.copy (cursor r) (frontier r))) <|
  .seq (.atom (.arithmetic .add (frontier r) (frontier r) (count r))) <|
  .loop (.lt (cursor r) (frontier r))
    (.seq (.atom (.store (cursor r) (zero r)))
      (.atom (.arithmetic .add (cursor r) (cursor r) (one r))))

theorem program_size (r : ℕ) : (program r).size=10 := rfl

/-- The loop's register configuration. Registers outside the six reserved ones
retain their original values. -/
def registers {r : ℕ} (frame : Fin (r+6) → ℤ) (endAddress length pointer position : ℕ) :
    Fin (r+6) → ℤ := fun i =>
  if i=frontier r then endAddress else
  if i=count r then length else
  if i=result r then pointer else
  if i=cursor r then position else
  if i=zero r then 0 else
  if i=one r then 1 else frame i

@[simp] theorem registers_frontier {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (frontier r)=e := by simp [registers]
@[simp] theorem registers_count {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (count r)=n := by simp [registers,frontier,count]
@[simp] theorem registers_result {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (result r)=b := by simp [registers,frontier,count,result]
@[simp] theorem registers_cursor {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (cursor r)=p := by simp [registers,frontier,count,result,cursor]
@[simp] theorem registers_zero {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (zero r)=0 := by simp [registers,frontier,count,result,cursor,zero]
@[simp] theorem registers_one {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ) :
    registers frame e n b p (one r)=1 := by simp [registers,frontier,count,result,cursor,zero,one]

theorem registers_update_cursor {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p q : ℕ) :
    Function.update (registers frame e n b p) (cursor r) q=registers frame e n b q := by
  funext i
  simp only [Function.update_apply,registers]
  split_ifs <;> subst_vars <;> simp_all [frontier,count,result,cursor,zero,one]

theorem registers_user {r : ℕ} (frame : Fin (r+6) → ℤ) (e n b p : ℕ)
    (i : Fin (r+6)) (user : 6 ≤ i.val) : registers frame e n b p i=frame i := by
  have different (j : Fin (r+6)) (reserved : j.val<6) : i≠j := by
    intro eq
    subst j
    omega
  simp only [registers,ite_eq_right (different (frontier r) (by simp [frontier])),
    ite_eq_right (different (count r) (by simp [count])),ite_eq_right (different (result r) (by simp [result])),
    ite_eq_right (different (cursor r) (by simp [cursor])),ite_eq_right (different (zero r) (by simp [zero])),
    ite_eq_right (different (one r) (by simp [one]))]

theorem nat_fits_le {w a b : ℕ} (bound : Fits w b) (le : a≤b) : Fits w a := by
  rcases bound with ⟨positive,low,high⟩
  refine ⟨positive,?_,?_⟩ <;> omega

theorem nat_address {w a : ℕ} (fits : Fits w a) : (a : ℤ)<(2^w : ℕ) := by
  have exp : w-1≤w := Nat.sub_le _ _
  have pow : (2 : ℤ)^(w-1)≤2^w := pow_le_pow_right₀ (by norm_num) exp
  have upper := fits.2.2
  exact lt_of_lt_of_le upper (by exact_mod_cast pow)

/-- Operational proof for the initialization loop, including bounded arithmetic
and addresses on every iteration. -/
theorem clear_exec {r w : ℕ} (frame : Fin (r+6) → ℤ) (memory : ℕ → ℤ)
    (endAddress length pointer position remaining : ℕ)
    (end_eq : position+remaining=endAddress) (width : Fits w endAddress) (unit : Fits w 1) :
    Structured.Exec w
      (.loop (.lt (cursor r) (frontier r))
        (.seq (.atom (.store (cursor r) (zero r)))
          (.atom (.arithmetic .add (cursor r) (cursor r) (one r)))))
      (registers frame endAddress length pointer position,memory)
      (registers frame endAddress length pointer endAddress,clear memory position remaining)
      (4*remaining+2) := by
  induction remaining generalizing position memory with
  | zero =>
    have same : position=endAddress := by omega
    subst position
    simpa [clear] using (Structured.Exec.loop_done (w := w)
      (c := Structured.Condition.lt (cursor r) (frontier r))
      (body := Structured.Code.seq (.atom (.store (cursor r) (zero r)))
        (.atom (.arithmetic .add (cursor r) (cursor r) (one r))))
      (data := (registers frame endAddress length pointer endAddress,memory))
      (by simp [Structured.Condition.Holds]))
  | succ remaining ih =>
    have pos_fit := nat_fits_le width (show position≤endAddress by omega)
    have next_fit := nat_fits_le width (show position+1≤endAddress by omega)
    have zero_fit : Fits w 0 := by simpa using nat_fits_le (a := 0) (b := 1) unit (by omega)
    have addr : (position : ℤ)<2^w := by exact_mod_cast nat_address pos_fit
    have stored : Structured.Exec w (.atom (.store (cursor r) (zero r)))
        (registers frame endAddress length pointer position,memory)
        (registers frame endAddress length pointer position,Function.update memory position 0) 1 := by
      apply Structured.Exec.atom
      simp [Structured.Primitive.eval,addr,zero_fit]
    have increment : Structured.Exec w
        (.atom (.arithmetic .add (cursor r) (cursor r) (one r)))
        (registers frame endAddress length pointer position,Function.update memory position 0)
        (registers frame endAddress length pointer (position+1),Function.update memory position 0) 1 := by
      apply Structured.Exec.atom
      have update := registers_update_cursor frame endAddress length pointer position (position+1)
      simp only [Nat.cast_add,Nat.cast_one] at next_fit update
      simp [Structured.Primitive.eval,Arithmetic.eval,next_fit,update]
    have body := stored.seq increment
    have rest := ih (Function.update memory position 0) (position+1) (by omega)
    have loop := Structured.Exec.loop_more (c := Structured.Condition.lt (cursor r) (frontier r))
      (by simp [Structured.Condition.Holds]; omega) body rest
    have cost : 1+1+(4*remaining+2)+2=4*(remaining+1)+2 := by omega
    simpa only [clear,cost] using loop

/-- Complete allocation from arbitrary scratch-register contents. The frontier
and count are the only input registers. The returned pointer names a zeroed block;
all user registers and memory outside that block retain their values. -/
theorem exec {r w : ℕ} (frame : Fin (r+6) → ℤ) (memory : ℕ → ℤ) (base length : ℕ)
    (front : frame (frontier r)=base) (request : frame (count r)=length)
    (width : Fits w (base+length)) (unit : Fits w 1) :
    Structured.Exec w (program r) (frame,memory)
      (registers frame (base+length) length base (base+length),clear memory base length)
      (4*length+7) := by
  simp only [frontier,count] at front request
  let f1 := Function.update frame (zero r) 0
  let f2 := Function.update f1 (one r) 1
  let f3 := Function.update f2 (result r) (base : ℤ)
  let f4 := Function.update f3 (cursor r) (base : ℤ)
  have base_fit := nat_fits_le width (show base≤base+length by omega)
  have zero_fit : Fits w 0 := by simpa using nat_fits_le (a := 0) (b := 1) unit (by omega)
  have start0 : Structured.Exec w (.atom (.constant (zero r) 0)) (frame,memory) (f1,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,zero_fit,f1]
  have start1 : Structured.Exec w (.atom (.constant (one r) 1)) (f1,memory) (f2,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,unit,f2]
  have save : Structured.Exec w (.atom (.copy (result r) (frontier r)))
      (f2,memory) (f3,memory) 1 := by
    apply Structured.Exec.atom
    have source : f2 (frontier r)=base := by simpa [f2,f1,frontier,zero,one] using front
    simp [Structured.Primitive.eval,source,base_fit,f3]
  have position : Structured.Exec w (.atom (.copy (cursor r) (frontier r)))
      (f3,memory) (f4,memory) 1 := by
    apply Structured.Exec.atom
    have source : f3 (frontier r)=base := by simpa [f3,f2,f1,frontier,result,zero,one] using front
    simp [Structured.Primitive.eval,source,base_fit,f4]
  have frame_eq : Function.update f4 (frontier r) (↑base+↑length)=
      registers frame (base+length) length base base := by
    funext i
    simp only [registers,Function.update_apply,f4,f3,f2,f1,Nat.cast_add]
    split_ifs <;> subst_vars <;>
      simp_all [frontier,count,result,cursor,zero,one]
  have reserve : Structured.Exec w (.atom (.arithmetic .add (frontier r) (frontier r) (count r)))
      (f4,memory) (registers frame (base+length) length base base,memory) 1 := by
    apply Structured.Exec.atom
    have width' : Fits w ((base : ℤ)+length) := by simpa using width
    have source : f4 (frontier r)=base := by
      simpa [f4,f3,f2,f1,frontier,result,cursor,zero,one] using front
    have size : f4 (count r)=length := by
      simpa [f4,f3,f2,f1,count,result,cursor,zero,one] using request
    simp [Structured.Primitive.eval,Arithmetic.eval,source,size,width',frame_eq]
  have initialized := clear_exec frame memory (base+length) length base base length rfl width unit
  have trace := start0.seq (start1.seq (save.seq (position.seq (reserve.seq initialized))))
  have cost : 1+(1+(1+(1+(1+(4*length+2)))))=4*length+7 := by omega
  simpa only [program,cost] using trace

/-- Establish the allocation frontier immediately above the input and header.
These four instructions are part of the program's cost. -/
def initializeProgram (r : ℕ) : Structured.Code (r+6) :=
  .seq (.atom (.constant (zero r) 0)) <|
  .seq (.atom (.load (frontier r) (zero r))) <|
  .seq (.atom (.constant (one r) 1)) <|
  .atom (.arithmetic .add (frontier r) (frontier r) (one r))

theorem initialize_exec {r w : ℕ} (frame : Fin (r+6) → ℤ) (memory : ℕ → ℤ) (inputLength : ℕ)
    (header : memory 0=inputLength) (width : Fits w (inputLength+1)) (unit : Fits w 1) :
    Structured.Exec w (initializeProgram r) (frame,memory)
      (Function.update (Function.update (Function.update frame (zero r) 0) (one r) 1)
        (frontier r) (inputLength+1 : ℕ),memory) 4 := by
  let f1 := Function.update frame (zero r) 0
  let f2 := Function.update f1 (frontier r) (inputLength : ℤ)
  let f3 := Function.update f2 (one r) 1
  have lengthFits := nat_fits_le width (show inputLength ≤ inputLength+1 by omega)
  have zeroFits : Fits w 0 := by simpa using nat_fits_le (a := 0) (b := 1) unit (by omega)
  have first : Structured.Exec w (.atom (.constant (zero r) 0)) (frame,memory) (f1,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,zeroFits,f1]
  have load : Structured.Exec w (.atom (.load (frontier r) (zero r))) (f1,memory) (f2,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,f1,f2,header,lengthFits]
  have constant : Structured.Exec w (.atom (.constant (one r) 1)) (f2,memory) (f3,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,unit,f3]
  have source : f3 (frontier r)=inputLength := by simp [f3,f2,frontier,one]
  have increment : Structured.Exec w (.atom (.arithmetic .add (frontier r) (frontier r) (one r)))
      (f3,memory) (Function.update f3 (frontier r) (inputLength+1 : ℕ),memory) 1 := by
    apply Structured.Exec.atom
    have finalFits : Fits w ((inputLength : ℤ)+1) := by simpa using width
    simp [Structured.Primitive.eval,Arithmetic.eval,source,f3,finalFits]
  have reordered : Function.update f3 (frontier r) (inputLength+1 : ℕ)=
      Function.update (Function.update (Function.update frame (zero r) 0) (one r) 1)
        (frontier r) (inputLength+1 : ℕ) := by
    funext i
    simp only [f3,f2,f1,Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [frontier,zero,one]
  simpa only [initializeProgram,reordered] using first.seq (load.seq (constant.seq increment))

/-- The allocation macro is a trace of the original bounded-word RAM, with
exactly the same cost. Code placement is the only additional requirement. -/
theorem compiles {r w pc : ℕ} {code : List (Instruction (r+6))}
    (frame : Fin (r+6) → ℤ) (memory : ℕ → ℤ) (base length : ℕ)
    (front : frame (frontier r)=base) (request : frame (count r)=length)
    (width : Fits w (base+length)) (unit : Fits w 1)
    (contained : Contains code pc ((program r).assemble pc)) (capacity : pc+10<2^w) :
    RunsTo w code (Data.at (frame,memory) pc)
      (Data.at (registers frame (base+length) length base (base+length),clear memory base length)
        (pc+10)) (4*length+7) := by
  simpa only [program_size] using
    (exec frame memory base length front request width unit).compiles contained capacity

end LeanTrominoes.ComplexityAbstract.RAM.Allocation
