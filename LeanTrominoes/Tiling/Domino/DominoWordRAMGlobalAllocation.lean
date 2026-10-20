/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMGlobalLoops
import LeanTrominoes.Computation.RAM.NaturalArithmetic

/-! # Explicit allocation of the two padded endpoint arrays -/
namespace LeanTrominoes.Domino.WordRAM.Driver
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128

abbrev one : Fin 128 := 82
abbrev edgeCountReg : Fin 128 := 83
abbrev nReg : Fin 128 := 66
abbrev frontier : Fin 128 := 74
abbrev left : Fin 128 := 70
abbrev right : Fin 128 := 71
abbrev cursor : Fin 128 := 69

def edgeCount (n d : ℕ) := 1+(2*d*2^d)*n*n

def allocate (d : ℕ) : Structured.Code 128 :=
  .seq (.atom (.constant one 1)) <|
  .seq (.atom (.constant edgeCountReg (2*d*2^d))) <|
  .seq (.atom (.arithmetic .mul edgeCountReg edgeCountReg nReg)) <|
  .seq (.atom (.arithmetic .mul edgeCountReg edgeCountReg nReg)) <|
  .seq (.atom (.arithmetic .add edgeCountReg edgeCountReg one)) <|
  .seq (.atom (.copy left frontier)) <|
  .seq (.atom (.arithmetic .add right frontier edgeCountReg)) <|
  .seq (.atom (.arithmetic .add frontier right edgeCountReg))
    (.atom (.constant cursor 0))

structure Allocated (n d : ℕ) (before after : Data) : Prop where
  unit : after.1 one=1
  count : after.1 edgeCountReg=edgeCount n d
  left : after.1 Driver.left=before.1 frontier
  right : after.1 Driver.right=before.1 frontier+edgeCount n d
  frontier : after.1 Driver.frontier=before.1 Driver.frontier+2*edgeCount n d
  index : after.1 cursor=0
  memory : after.2=before.2
  fixed : ∀ reg : Fin 128, reg≠one → reg≠edgeCountReg → reg≠Driver.left → reg≠Driver.right →
    reg≠Driver.frontier → reg≠cursor → after.1 reg=before.1 reg

/-- All nine allocation and count-computation instructions are executed.
The order of multiplication also covers dimension zero without a large square. -/
theorem allocate_exec {n d H w : ℕ} (data : Data) (positive : 0<n)
    (count : data.1 nReg=n) (space : data.1 frontier+2*edgeCount n d≤H) (word : Fits w H) :
    ∃ result, NaturalData.Exec w (allocate d) data result 9 ∧ Allocated n d data result := by
  let C := 2*d*2^d
  have countBound : edgeCount n d≤H := by omega
  have firstBound : C*n≤H := by
    have grow : C*n≤C*n*n := Nat.le_mul_of_pos_right _ positive
    exact grow.trans (by dsimp [edgeCount,C] at *; omega)
  have factorBound : C≤H := (Nat.le_mul_of_pos_right _ positive).trans firstBound
  have fullBound : C*n*n≤H := by dsimp [edgeCount,C] at *; omega
  have firstAddress : data.1 frontier≤H := by omega
  have rightAddress : data.1 frontier+edgeCount n d≤H := by omega
  have finalAddress : data.1 frontier+edgeCount n d+edgeCount n d≤H := by omega
  let s1 := data.set one 1
  let s2 := s1.set edgeCountReg C
  let s3 := s2.set edgeCountReg (C*n)
  let s4 := s3.set edgeCountReg (C*n*n)
  let s5 := s4.set edgeCountReg (edgeCount n d)
  let s6 := s5.set left (data.1 frontier)
  let s7 := s6.set right (data.1 frontier+edgeCount n d)
  let s8 := s7.set frontier (data.1 frontier+edgeCount n d+edgeCount n d)
  let s9 := s8.set cursor 0
  have run1 := NaturalData.constant_exec data one 1 (Allocation.nat_fits_le (a:=1) word (by unfold edgeCount at countBound; omega))
  have run2 := NaturalData.constant_exec s1 edgeCountReg C (Allocation.nat_fits_le word factorBound)
  have run3 : NaturalData.Exec w (.atom (.arithmetic .mul edgeCountReg edgeCountReg nReg)) s2 s3 1 := by
    simpa [s3,s2,s1,NaturalData.set,one,edgeCountReg,nReg,count] using NaturalData.mul_exec s2 edgeCountReg edgeCountReg nReg
      (by simpa [s2,s1,NaturalData.set,one,edgeCountReg,nReg,count] using Allocation.nat_fits_le word firstBound)
  have run4 : NaturalData.Exec w (.atom (.arithmetic .mul edgeCountReg edgeCountReg nReg)) s3 s4 1 := by
    simpa [s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,nReg,count] using NaturalData.mul_exec s3 edgeCountReg edgeCountReg nReg
      (by simpa [s3,s2,s1,NaturalData.set,one,edgeCountReg,nReg,count] using Allocation.nat_fits_le word fullBound)
  have run5 : NaturalData.Exec w (.atom (.arithmetic .add edgeCountReg edgeCountReg one)) s4 s5 1 := by
    simpa [s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,edgeCount,C,Nat.add_comm] using NaturalData.add_exec s4 edgeCountReg edgeCountReg one
      (by simpa [s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,edgeCount,C,Nat.add_comm] using Allocation.nat_fits_le word countBound)
  have run6 : NaturalData.Exec w (.atom (.copy left frontier)) s5 s6 1 := by
    simpa [s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,frontier] using NaturalData.copy_exec s5 left frontier
      (by simpa [s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,frontier] using Allocation.nat_fits_le word firstAddress)
  have run7 : NaturalData.Exec w (.atom (.arithmetic .add right frontier edgeCountReg)) s6 s7 1 := by
    simpa [s7,s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,right,frontier] using NaturalData.add_exec s6 right frontier edgeCountReg
      (by simpa [s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,frontier] using Allocation.nat_fits_le word rightAddress)
  have run8 : NaturalData.Exec w (.atom (.arithmetic .add frontier right edgeCountReg)) s7 s8 1 := by
    simpa [s8,s7,s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,right,frontier] using NaturalData.add_exec s7 frontier right edgeCountReg
      (by simpa [s7,s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,right,frontier] using Allocation.nat_fits_le word finalAddress)
  have run9 := NaturalData.constant_exec s8 cursor 0 (Allocation.nat_fits_le (a:=0) word (Nat.zero_le _))
  refine ⟨s9,run1.seq (run2.seq (run3.seq (run4.seq (run5.seq (run6.seq (run7.seq (run8.seq run9))))))),?_,?_,?_,?_,?_,?_,rfl,?_⟩
  all_goals first
    | (simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,NaturalData.set,one,edgeCountReg,left,right,frontier,cursor] <;> omega)
    | (intro reg h1 h2 h3 h4 h5 h6; simp only [s9,s8,s7,s6,s5,s4,s3,s2,s1,NaturalData.set,
        Function.update_of_ne h1,Function.update_of_ne h2,Function.update_of_ne h3,
        Function.update_of_ne h4,Function.update_of_ne h5,Function.update_of_ne h6])

end LeanTrominoes.Domino.WordRAM.Driver
