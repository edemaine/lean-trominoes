/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.Allocation

/-! # Indexed arrays on the word RAM with memory allocation

Each indexed read or write expands into two primitive instructions. Bounds are
proved using the allocated block's endpoint; a program cannot access an entire
Lean array or function as one instruction. Record fields are constant indices
in fixed-size blocks and use the same operations.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM.Allocation

def Block.write (block : Block) (memory : ℕ → ℤ) (i : Fin block.length) (value : ℤ) : ℕ → ℤ :=
  Function.update memory (block.base+i.val) value

@[simp] theorem Block.read_write_same (block : Block) (memory : ℕ → ℤ)
    (i : Fin block.length) (value : ℤ) : block.read (block.write memory i value) i=value := by
  simp [Block.read,Block.write]

theorem Block.write_frame (block : Block) (memory : ℕ → ℤ)
    (i : Fin block.length) (value : ℤ) {address : ℕ} (outside : ¬block.Owns address) :
    block.write memory i value address=memory address := by
  have different : address≠block.base+i.val := by
    intro eq
    subst address
    apply outside
    simp only [Block.Owns]
    omega
  simp [Block.write,Function.update_of_ne different]

/-- An array's logical contents are separate from its physical addresses.
Solver invariants can refer to these contents without choosing other blocks'
locations. The allocation and frame lemmas establish their independence. -/
def Block.Realizes (block : Block) (memory : ℕ → ℤ) (values : Fin block.length → ℤ) : Prop :=
  ∀ i, block.read memory i=values i

theorem Block.write_realizes (block : Block) (memory : ℕ → ℤ)
    (values : Fin block.length → ℤ) (before : block.Realizes memory values)
    (i : Fin block.length) (value : ℤ) :
    block.Realizes (block.write memory i value) (Function.update values i value) := by
  intro j
  by_cases eq : j=i
  · subst j; simp
  · have different : block.base+j.val≠block.base+i.val := by
      intro same
      exact eq (Fin.ext (by omega))
    simpa [Block.read,Block.write,Function.update_of_ne different,Function.update_of_ne eq]
      using before j

theorem Block.clear_realizes (memory : ℕ → ℤ) (base length : ℕ) :
    (Block.mk base length).Realizes (clear memory base length) (fun _ => 0) := by
  intro i
  change clear memory base length (base+i.val)=0
  have bound : i.val<length := i.isLt
  exact clear_zero ⟨by omega,by omega⟩

theorem Block.clear_preserves (block : Block) (memory : ℕ → ℤ)
    (values : Fin block.length → ℤ) (before : block.Realizes memory values)
    {base length : ℕ} (earlier : block.base+block.length≤base) :
    block.Realizes (clear memory base length) values := by
  intro i
  change clear memory base length (block.base+i.val)=values i
  rw [clear_frame (by omega)]
  exact before i

theorem Block.write_preserves (block other : Block) (memory : ℕ → ℤ)
    (values : Fin block.length → ℤ) (before : block.Realizes memory values)
    (disjoint : ∀ address, block.Owns address → ¬other.Owns address)
    (j : Fin other.length) (value : ℤ) :
    block.Realizes (other.write memory j value) values := by
  intro i
  change other.write memory j value (block.base+i.val)=values i
  have inside : block.Owns (block.base+i.val) := ⟨by omega,by omega⟩
  rw [other.write_frame memory j value (disjoint _ inside)]
  exact before i

def readProgram {r : ℕ} (scratch dst pointer index : Fin r) : Structured.Code r :=
  .seq (.atom (.arithmetic .add scratch pointer index)) (.atom (.load dst scratch))

def writeProgram {r : ℕ} (scratch src pointer index : Fin r) : Structured.Code r :=
  .seq (.atom (.arithmetic .add scratch pointer index)) (.atom (.store scratch src))

@[simp] theorem readProgram_size {r : ℕ} (scratch dst pointer index : Fin r) :
    (readProgram scratch dst pointer index).size=2 := rfl

@[simp] theorem writeProgram_size {r : ℕ} (scratch src pointer index : Fin r) :
    (writeProgram scratch src pointer index).size=2 := rfl

/-- A read preserves memory and changes only its destination and address scratch
register. The value loaded must fit the word, as in the underlying RAM. -/
theorem read_exec {r w : ℕ} (frame : Fin r → ℤ) (memory : ℕ → ℤ)
    (scratch dst pointer index : Fin r) (block : Block) (i : Fin block.length)
    (ptr : frame pointer=block.base) (idx : frame index=i.val)
    (width : Fits w (block.base+block.length)) (valueFits : Fits w (block.read memory i)) :
    Structured.Exec w (readProgram scratch dst pointer index) (frame,memory)
      (Function.update (Function.update frame scratch (block.base+i.val : ℕ)) dst
        (block.read memory i),memory) 2 := by
  have addrFits := nat_fits_le width (show block.base+i.val≤block.base+block.length by omega)
  simp only [Nat.cast_add] at addrFits
  let middle := Function.update frame scratch (block.base+i.val : ℕ)
  have add : Structured.Exec w (.atom (.arithmetic .add scratch pointer index))
      (frame,memory) (middle,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,Arithmetic.eval,ptr,idx,addrFits,middle]
  have load : Structured.Exec w (.atom (.load dst scratch)) (middle,memory)
      (Function.update middle dst (block.read memory i),memory) 1 := by
    apply Structured.Exec.atom
    simp only [Structured.Primitive.eval,middle,Function.update_self]
    have valid : ¬(((block.base+i.val : ℕ) : ℤ)<0 ∨
        ((block.base+i.val : ℕ) : ℤ)≥(2^w : ℕ)) := by
      push Not
      exact ⟨Int.natCast_nonneg _,nat_address (nat_fits_le width (by omega))⟩
    rw [ite_eq_right valid]
    simpa only [Int.toNat_natCast,Block.read] using
      (show (if Fits w (block.read memory i) then
        some (Function.update middle dst (block.read memory i),memory) else none)=
        some (Function.update middle dst (block.read memory i),memory) from ite_eq_left valueFits)
  exact add.seq load

/-- A write preserves registers except for its address scratch register, and
preserves all cells except the selected element. -/
theorem write_exec {r w : ℕ} (frame : Fin r → ℤ) (memory : ℕ → ℤ)
    (scratch src pointer index : Fin r) (block : Block) (i : Fin block.length)
    (different : src≠scratch) (ptr : frame pointer=block.base) (idx : frame index=i.val)
    (width : Fits w (block.base+block.length)) (valueFits : Fits w (frame src)) :
    Structured.Exec w (writeProgram scratch src pointer index) (frame,memory)
      (Function.update frame scratch (block.base+i.val : ℕ),block.write memory i (frame src)) 2 := by
  have addrFits := nat_fits_le width (show block.base+i.val≤block.base+block.length by omega)
  simp only [Nat.cast_add] at addrFits
  let middle := Function.update frame scratch (block.base+i.val : ℕ)
  have add : Structured.Exec w (.atom (.arithmetic .add scratch pointer index))
      (frame,memory) (middle,memory) 1 := by
    apply Structured.Exec.atom
    simp [Structured.Primitive.eval,Arithmetic.eval,ptr,idx,addrFits,middle]
  have store : Structured.Exec w (.atom (.store scratch src)) (middle,memory)
      (middle,block.write memory i (frame src)) 1 := by
    apply Structured.Exec.atom
    simp only [Structured.Primitive.eval,middle,Function.update_self,Function.update_of_ne different]
    have valid : ¬(((block.base+i.val : ℕ) : ℤ)<0 ∨
        ((block.base+i.val : ℕ) : ℤ)≥(2^w : ℕ) ∨ ¬Fits w (frame src)) := by
      push Not
      exact ⟨Int.natCast_nonneg _,nat_address (nat_fits_le width (by omega)),valueFits⟩
    rw [ite_eq_right valid]
    simp only [Int.toNat_natCast,Block.write]
  exact add.seq store

/-- An arena is a specification ledger; the block list is not a runtime lookup
table. The program keeps a frontier and never reuses addresses. This frontier
is the high-water mark, including blocks no longer used. Its bound keeps
pointers within words even without a separate space-complexity claim. -/
structure Arena where
  frontier : ℕ
  blocks : List Block
  below : ∀ block ∈ blocks, block.base+block.length≤frontier

/-- The input and its length header occupy the addresses below the initial
frontier. They are never reused by allocation. -/
def Arena.initial (inputLength : ℕ) : Arena := ⟨inputLength+1,[],by simp⟩

/-- One high-water-mark bound supplies address bounds for every allocated
array. Solvers need no separate physical layout bound for each block. -/
theorem Arena.block_fits {w : ℕ} (arena : Arena) (width : Fits w arena.frontier)
    (block : Block) (member : block∈arena.blocks) : Fits w (block.base+block.length) :=
  nat_fits_le width (arena.below block member)

def Arena.allocate (arena : Arena) (length : ℕ) : Block × Arena :=
  (⟨arena.frontier,length⟩,
   ⟨arena.frontier+length,⟨arena.frontier,length⟩::arena.blocks,by
     intro block member
     rcases List.mem_cons.mp member with eq | old
     · cases eq; exact le_rfl
     · exact (arena.below block old).trans (Nat.le_add_right _ _)⟩)

theorem Arena.allocate_disjoint (arena : Arena) (length : ℕ) (old : Block) (member : old∈arena.blocks) :
    ∀ address, old.Owns address → ¬(arena.allocate length).1.Owns address :=
  fresh_disjoint old (arena.below old member)

end LeanTrominoes.ComplexityAbstract.RAM.Allocation
