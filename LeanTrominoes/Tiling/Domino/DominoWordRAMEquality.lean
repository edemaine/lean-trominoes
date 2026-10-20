/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEqualityBody

/-! # Full equality test for arbitrary-precision binary arrays -/
namespace LeanTrominoes.Domino.WordRAM.Binary.Equality
open ComplexityAbstract.RAM

structure Layout where
  first : ℕ
  second : ℕ
  length : ℕ

structure Represents (p : Layout) (source : ℕ → ℕ) (i : ℕ) (data : Data) : Prop where
  index : data.1 Reg.index=i
  length : data.1 Reg.length=p.length
  first : data.1 Reg.first=p.first
  second : data.1 Reg.second=p.second
  one : data.1 Reg.one=1
  carry : data.1 Reg.carry≤1
  memory : data.2=source
  first_bits : ∀ j< p.length, source (p.first+j)≤1
  second_bits : ∀ j< p.length, source (p.second+j)≤1
  agreement : data.1 Reg.carry=1 ↔ ∀ j< i, source (p.first+j)=source (p.second+j)

attribute [local simp] Reg.index Reg.length Reg.first Reg.second Reg.carry Reg.left Reg.right Reg.one Reg.address
  NaturalData.set add1 add2 add3 add4

theorem Represents.step {p : Layout} {source : ℕ → ℕ} {i : ℕ} {data : Data}
    (h : Represents p source i data) (within : i< p.length) : Represents p source (i+1) (Equality.step data) := by
  by_cases equal : data.2 (data.1 Reg.first+data.1 Reg.index)=data.2 (data.1 Reg.second+data.1 Reg.index)
  · have sourceEqual : source (p.first+i)=source (p.second+i) := by
      simpa only [h.first,h.second,h.index,h.memory] using equal
    simp only [Equality.step,equal,ite_true,ite_false]
    constructor
    · simp [Equality.step,equal,h.index,h.one]
    · simp [Equality.step,equal,h.length]
    · simp [Equality.step,equal,h.first]
    · simp [Equality.step,equal,h.second]
    · simp [Equality.step,equal,h.one]
    · simpa [Equality.step,equal] using h.carry
    · simp [Equality.step,equal,h.memory]
    · exact h.first_bits
    · exact h.second_bits
    · change (data.1 Reg.carry=1) ↔ ∀ j< i+1, source (p.first+j)=source (p.second+j)
      rw [h.agreement]
      constructor
      · intro prior j hj
        by_cases earlier : j< i
        · exact prior j earlier
        · have same : j=i := by omega
          simpa only [same] using sourceEqual
      · intro all j hj
        exact all j (by omega)
  · have sourceDifferent : source (p.first+i)≠source (p.second+i) := by
      simpa only [h.first,h.second,h.index,h.memory] using equal
    simp only [Equality.step,equal,ite_true,ite_false]
    constructor
    · simp [Equality.step,equal,h.index,h.one]
    · simp [Equality.step,equal,h.length]
    · simp [Equality.step,equal,h.first]
    · simp [Equality.step,equal,h.second]
    · simp [Equality.step,equal,h.one]
    · simp [Equality.step,equal]
    · simp [Equality.step,equal,h.memory]
    · exact h.first_bits
    · exact h.second_bits
    · change ((0:ℕ)=1) ↔ ∀ j< i+1, source (p.first+j)=source (p.second+j)
      simp only [Nat.zero_ne_one,false_iff]
      intro all
      exact sourceDifferent (all i (by omega))

def loop : Code := .loop (.lt Reg.index Reg.length) body

private theorem fits_le {w n bound : ℕ} (h : Fits w bound) (le : n≤bound) : Fits w n := by
  refine ⟨h.1,?_,lt_of_le_of_lt (by exact_mod_cast le) h.2.2⟩
  exact le_trans (neg_nonpos.mpr (by positivity)) (Int.natCast_nonneg _)

theorem loop_exec {w : ℕ} (p : Layout) (source : ℕ → ℕ) (small : Fits w (1:ℕ))
    (firstFits : Fits w (p.first+p.length : ℕ)) (secondFits : Fits w (p.second+p.length : ℕ))
    (lengthFits : Fits w p.length) (remaining : ℕ) :
    ∀ i data, p.length=i+remaining → Represents p source i data →
    ∃ result cost, NaturalData.Exec w loop data result cost ∧ cost≤10*remaining+2 ∧ Represents p source p.length result := by
  induction remaining with
  | zero =>
    intro i data length h
    have equal : i=p.length := by omega
    subst i
    refine ⟨data,2,?_,by omega,h⟩
    apply Structured.Exec.loop_done
    simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length]
  | succ remaining ih =>
    intro i data length h
    have within : i< p.length := by omega
    obtain ⟨bodyCost,bodyRun,bodyBound⟩ := body_exec data h.one h.carry
      (by rw [h.first,h.index,h.memory]; exact h.first_bits i within)
      (by rw [h.second,h.index,h.memory]; exact h.second_bits i within)
      small (by rw [h.first,h.index]; exact fits_le firstFits (by omega))
      (by rw [h.second,h.index]; exact fits_le secondFits (by omega))
      (by rw [h.index]; exact fits_le lengthFits (by omega))
    obtain ⟨result,restCost,restRun,restBound,correct⟩ := ih (i+1) (Equality.step data) (by omega) (h.step within)
    refine ⟨result,bodyCost+restCost+2,?_,by omega,correct⟩
    apply Structured.Exec.loop_more
    · simp [Structured.Condition.Holds,NaturalData.word,h.index,h.length,within]
    · exact bodyRun
    · exact restRun

def initCode : Code := .seq (.atom (.constant Reg.index 0)) <|
  .seq (.atom (.constant Reg.carry 1)) (.atom (.constant Reg.one 1))
def initialized (data : Data) := ((data.set Reg.index 0).set Reg.carry 1).set Reg.one 1
def program : Code := .seq initCode loop

theorem initialize_exec {w : ℕ} (data : Data) (small : Fits w (1:ℕ)) :
    NaturalData.Exec w initCode data (initialized data) 3 := by
  exact (NaturalData.constant_exec data Reg.index 0 (fits_le small (by omega : 0≤1))).seq
    ((NaturalData.constant_exec (data.set Reg.index 0) Reg.carry 1 small).seq
      (NaturalData.constant_exec ((data.set Reg.index 0).set Reg.carry 1) Reg.one 1 small))

theorem initialized_represents (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (first_bits : ∀ j< p.length, data.2 (p.first+j)≤1) (second_bits : ∀ j< p.length, data.2 (p.second+j)≤1) :
    Represents p data.2 0 (initialized data) := by
  constructor <;> simp_all [initialized]

/-- Full linear-time equality of binary arrays, with all external memory
unchanged and the boolean answer in register `carry`. -/
theorem program_exec {w : ℕ} (p : Layout) (data : Data)
    (length : data.1 Reg.length=p.length) (first : data.1 Reg.first=p.first) (second : data.1 Reg.second=p.second)
    (first_bits : ∀ j< p.length, data.2 (p.first+j)≤1) (second_bits : ∀ j< p.length, data.2 (p.second+j)≤1)
    (small : Fits w (1:ℕ)) (firstFits : Fits w (p.first+p.length : ℕ))
    (secondFits : Fits w (p.second+p.length : ℕ)) (lengthFits : Fits w p.length) :
    ∃ result cost, NaturalData.Exec w program data result cost ∧ cost≤10*p.length+5 ∧ Represents p data.2 p.length result := by
  obtain ⟨result,cost,run,bound,correct⟩ := loop_exec p data.2 small firstFits secondFits lengthFits p.length
    0 (initialized data) (by omega) (initialized_represents p data length first second first_bits second_bits)
  exact ⟨result,3+cost,(initialize_exec data small).seq run,by omega,correct⟩

end LeanTrominoes.Domino.WordRAM.Binary.Equality
