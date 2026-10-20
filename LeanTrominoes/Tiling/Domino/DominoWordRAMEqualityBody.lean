/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMAddition

/-! # A checked binary-array equality scan -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Equality
open ComplexityAbstract.RAM
attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.carry Reg.left Reg.right Reg.one Reg.address
  NaturalData.set add1 add2 add3 add4

def compare : Code := .branch (.eq Reg.left Reg.right)
  (.atom (.copy Reg.carry Reg.carry)) (.atom (.constant Reg.carry 0))

def body : Code :=
  .seq (.atom (.arithmetic .add Reg.address Reg.first Reg.index)) <|
  .seq (.atom (.load Reg.left Reg.address)) <|
  .seq (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) <|
  .seq (.atom (.load Reg.right Reg.address)) <|
  .seq compare (.atom (.arithmetic .add Reg.index Reg.index Reg.one))

def step (data : Data) : Data :=
  let tested := if data.2 (data.1 Reg.first+data.1 Reg.index)=data.2 (data.1 Reg.second+data.1 Reg.index)
    then add4 data else (add4 data).set Reg.carry 0
  tested.set Reg.index (data.1 Reg.index+data.1 Reg.one)

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem body_exec {w : ℕ} (data : Data) (one : data.1 Reg.one=1) (carry : data.1 Reg.carry≤1)
    (left : data.2 (data.1 Reg.first+data.1 Reg.index)≤1)
    (right : data.2 (data.1 Reg.second+data.1 Reg.index)≤1)
    (small : Fits w (1:ℕ))
    (firstAddress : Fits w (data.1 Reg.first+data.1 Reg.index : ℕ))
    (secondAddress : Fits w (data.1 Reg.second+data.1 Reg.index : ℕ))
    (indexFits : Fits w (data.1 Reg.index+1 : ℕ)) :
    ∃ cost, NaturalData.Exec w body data (step data) cost ∧ cost≤8 := by
  have h1 := NaturalData.add_exec data Reg.address Reg.first Reg.index firstAddress
  have h2 : NaturalData.Exec w (.atom (.load Reg.left Reg.address)) (add1 data) (add2 data) 1 := by
    simpa using NaturalData.load_exec (add1 data) Reg.left Reg.address
      (by simpa using firstAddress) (by simpa using fits_le small left)
  have h3 : NaturalData.Exec w (.atom (.arithmetic .add Reg.address Reg.second Reg.index)) (add2 data) (add3 data) 1 := by
    simpa using NaturalData.add_exec (add2 data) Reg.address Reg.second Reg.index (by simpa using secondAddress)
  have h4 : NaturalData.Exec w (.atom (.load Reg.right Reg.address)) (add3 data) (add4 data) 1 := by
    simpa using NaturalData.load_exec (add3 data) Reg.right Reg.address
      (by simpa using secondAddress) (by simpa using fits_le small right)
  by_cases equal : data.2 (data.1 Reg.first+data.1 Reg.index)=data.2 (data.1 Reg.second+data.1 Reg.index)
  · have condition : (Structured.Condition.eq Reg.left Reg.right).Holds (add4 data).word := by
      simp [Structured.Condition.Holds,NaturalData.word,equal]
    have same : (add4 data).set Reg.carry ((add4 data).1 Reg.carry)=add4 data := by
      apply Prod.ext
      · exact Function.update_eq_self _ _
      · rfl
    have copy := NaturalData.copy_exec (add4 data) Reg.carry Reg.carry (by simpa using fits_le small carry)
    rw [same] at copy
    have branch := Structured.Exec.branch_yes (no := .atom (.constant Reg.carry 0)) condition copy
    have last := NaturalData.add_exec (add4 data) Reg.index Reg.index Reg.one (by simpa [one] using indexFits)
    refine ⟨7,?_,by omega⟩
    simpa [NaturalData.Exec,body,compare,step,equal] using
      h1.seq (h2.seq (h3.seq (h4.seq (branch.seq last))))
  · have condition : ¬(Structured.Condition.eq Reg.left Reg.right).Holds (add4 data).word := by
      simpa [Structured.Condition.Holds,NaturalData.word] using equal
    have constant := NaturalData.constant_exec (add4 data) Reg.carry 0 (fits_le small (by omega : 0≤1))
    have branch := Structured.Exec.branch_no (yes := .atom (.copy Reg.carry Reg.carry)) condition constant
    have last := NaturalData.add_exec ((add4 data).set Reg.carry 0) Reg.index Reg.index Reg.one (by simpa [one] using indexFits)
    refine ⟨8,?_,by omega⟩
    simpa [NaturalData.Exec,body,compare,step,equal] using
      h1.seq (h2.seq (h3.seq (h4.seq (branch.seq last))))

end LeanTrominoes.Domino.WordRAM.Binary.Equality
