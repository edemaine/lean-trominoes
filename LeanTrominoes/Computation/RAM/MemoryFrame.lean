/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.StructuredCompile
import LeanTrominoes.Computation.RAM.WordBounds

/-! # Preserving caller memory when invoking bounded-word subprograms

An execution at width k accesses memory only below 2^k. Replaying it at any
larger width can therefore preserve arbitrary caller data outside that range.
The proof uses the original load/store address guards and retains exact costs.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM

def Data.frame {r : ℕ} (data : Data r) (limit : ℕ) (external : ℕ → ℤ) : Data r :=
  (data.1,fun address => if address<limit then data.2 address else external address)

theorem Data.frame_registers {r : ℕ} (data : Data r) (limit : ℕ) (external : ℕ → ℤ) :
    (data.frame limit external).1=data.1 := rfl

theorem Data.frame_store {r : ℕ} (data : Data r) (limit address : ℕ) (external : ℕ → ℤ)
    (value : ℤ) (within : address<limit) :
    Data.frame (data.1,Function.update data.2 address value) limit external=
      ((data.frame limit external).1,Function.update (data.frame limit external).2 address value) := by
  apply Prod.ext
  · rfl
  · funext other
    by_cases same : other=address
    · subst other; simp [Data.frame,within]
    · simp [Data.frame,Function.update_of_ne same]

private theorem address_mono {small large : ℕ} (width : small≤large) (address : ℤ)
    (valid : ¬(address<0 ∨ address≥(2^small : ℕ))) :
    ¬(address<0 ∨ address≥(2^large : ℕ)) := by
  have powers : (2 : ℕ)^small≤2^large := pow_le_pow_right₀ (by decide) width
  have cast : ((2^small : ℕ) : ℤ)≤(2^large : ℕ) := by exact_mod_cast powers
  omega

private theorem address_toNat {small : ℕ} (address : ℤ)
    (valid : ¬(address<0 ∨ address≥(2^small : ℕ))) : address.toNat<2^small := by
  have positive : 0≤address := by omega
  have cast : (address.toNat : ℤ)=address := Int.toNat_of_nonneg positive
  have within : (address.toNat : ℤ)<(2^small : ℕ) := by rw [cast]; omega
  exact_mod_cast within

namespace Structured

theorem Primitive.eval_frame_mono {r small large : ℕ} {op : Primitive r} {data result : Data r}
    (width : small≤large) (external : ℕ → ℤ) (execution : op.eval small data=some result) :
    op.eval large (data.frame (2^small) external)=some (result.frame (2^small) external) := by
  cases op with
  | constant dst value =>
    simp only [Primitive.eval] at execution
    split_ifs at execution with fits
    cases execution
    simp [Primitive.eval,Data.frame,WordBounds.fits_mono width fits]
  | copy dst src =>
    simp only [Primitive.eval] at execution
    split_ifs at execution with fits
    cases execution
    simp [Primitive.eval,Data.frame,WordBounds.fits_mono width fits]
  | arithmetic op dst left right =>
    simp only [Primitive.eval] at execution
    split_ifs at execution with fits
    cases execution
    simp [Primitive.eval,Data.frame,WordBounds.fits_mono width fits]
  | load dst address =>
    simp only [Primitive.eval] at execution
    split_ifs at execution with invalid fits
    cases execution
    have larger := address_mono width (data.1 address) invalid
    have within := address_toNat (data.1 address) invalid
    simp [Primitive.eval,Data.frame,within,WordBounds.fits_mono width fits]
    exact_mod_cast (show 0≤data.1 address ∧ data.1 address<(2^large : ℕ) by omega)
  | store address src =>
    simp only [Primitive.eval] at execution
    split_ifs at execution with invalid
    cases execution
    have valid : ¬(data.1 address<0 ∨ data.1 address≥(2^small : ℕ)) := by omega
    have fits : Fits small (data.1 src) := by tauto
    have larger := address_mono width (data.1 address) valid
    have within := address_toNat (data.1 address) valid
    rw [Data.frame_store data (2^small) (data.1 address).toNat external (data.1 src) within]
    simp [Primitive.eval,Data.frame,WordBounds.fits_mono width fits]
    exact_mod_cast (show 0≤data.1 address ∧ data.1 address<(2^large : ℕ) by omega)

theorem Condition.holds_frame {r : ℕ} (condition : Condition r) (data : Data r)
    (limit : ℕ) (external : ℕ → ℤ) :
    condition.Holds (data.frame limit external) ↔ condition.Holds data := by
  cases condition <;> rfl

/-- Every structured program can be called while preserving external memory.
No function evaluation or memory lookup is added to its instruction set. -/
theorem Exec.frame_mono {r small large : ℕ} {code : Code r} {data result : Data r} {cost : ℕ}
    (execution : Exec small code data result cost) (width : small≤large) (external : ℕ → ℤ) :
    Exec large code (data.frame (2^small) external) (result.frame (2^small) external) cost := by
  induction execution with
  | atom evaluation => exact .atom (Primitive.eval_frame_mono width external evaluation)
  | seq first second ihFirst ihSecond => exact ihFirst.seq ihSecond
  | branch_yes holds body ih =>
    apply Exec.branch_yes _ ih
    simpa only [Condition.holds_frame] using holds
  | branch_no absent body ih =>
    apply Exec.branch_no _ ih
    simpa only [Condition.holds_frame] using absent
  | loop_done absent =>
    apply Exec.loop_done
    simpa only [Condition.holds_frame] using absent
  | loop_more holds body rest ihBody ihRest =>
    apply Exec.loop_more _ ihBody ihRest
    simpa only [Condition.holds_frame] using holds

end Structured
end LeanTrominoes.ComplexityAbstract.RAM
