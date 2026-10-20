/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.StructuredCompile

/-! # Embedding a subprogram into a larger finite register file

The old registers retain their indices. Extra registers are preserved exactly,
allowing a caller to retain its loop indices and pointers across the call.
-/
namespace LeanTrominoes.ComplexityAbstract.RAM

def Data.extend {r s : ℕ} (data : Data r) (tail : Fin s → ℤ) : Data (r+s) :=
  (Fin.addCases data.1 tail,data.2)

theorem Data.extend_left {r s : ℕ} (data : Data r) (tail : Fin s → ℤ) (i : Fin r) :
    (data.extend tail).1 (i.castAdd s)=data.1 i := by simp [Data.extend]

theorem Data.extend_right {r s : ℕ} (data : Data r) (tail : Fin s → ℤ) (i : Fin s) :
    (data.extend tail).1 (i.natAdd r)=tail i := by simp [Data.extend]

private theorem extend_update {r s : ℕ} (regs : Fin r → ℤ) (tail : Fin s → ℤ) (dst : Fin r) (value : ℤ) :
    Fin.addCases (motive := fun _ : Fin (r+s) => ℤ) (Function.update regs dst value) tail=
      Function.update (Fin.addCases regs tail) (dst.castAdd s) value := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Function.update_apply]
  · have different : j.natAdd r≠dst.castAdd s := by
      intro same
      have equal := congrArg Fin.val same
      have low := dst.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd] at equal
      omega
    simp [Function.update_of_ne different]

namespace Structured

def Primitive.embed {r : ℕ} (s : ℕ) : Primitive r → Primitive (r+s)
  | .constant dst value => .constant (dst.castAdd s) value
  | .copy dst src => .copy (dst.castAdd s) (src.castAdd s)
  | .arithmetic op dst left right => .arithmetic op (dst.castAdd s) (left.castAdd s) (right.castAdd s)
  | .load dst address => .load (dst.castAdd s) (address.castAdd s)
  | .store address src => .store (address.castAdd s) (src.castAdd s)

def Condition.embed {r : ℕ} (s : ℕ) : Condition r → Condition (r+s)
  | .eq left right => .eq (left.castAdd s) (right.castAdd s)
  | .lt left right => .lt (left.castAdd s) (right.castAdd s)

def Code.embed {r : ℕ} (s : ℕ) : Code r → Code (r+s)
  | .atom op => .atom (op.embed s)
  | .seq first second => .seq (first.embed s) (second.embed s)
  | .branch condition yes no => .branch (condition.embed s) (yes.embed s) (no.embed s)
  | .loop condition body => .loop (condition.embed s) (body.embed s)

theorem Code.size_embed {r : ℕ} (s : ℕ) (code : Code r) : (code.embed s).size=code.size := by
  induction code <;> simp_all [Code.embed,Code.size]

theorem Primitive.eval_embed {r s w : ℕ} (op : Primitive r) (data : Data r) (tail : Fin s → ℤ) :
    (op.embed s).eval w (data.extend tail)=(op.eval w data).map (fun result => result.extend tail) := by
  cases op <;> simp only [Primitive.embed,Primitive.eval,Data.extend,Fin.addCases_left]
  all_goals split_ifs <;> simp [Data.extend,extend_update]

theorem Condition.holds_embed {r s : ℕ} (condition : Condition r) (data : Data r) (tail : Fin s → ℤ) :
    (condition.embed s).Holds (data.extend tail) ↔ condition.Holds data := by
  cases condition <;> simp [Condition.embed,Condition.Holds,Data.extend]

/-- Register embedding preserves exact primitive instruction counts and all
caller-private registers, for every bounded word width. -/
theorem Exec.embed {r s w : ℕ} {code : Code r} {data result : Data r} {cost : ℕ}
    (execution : Exec w code data result cost) (tail : Fin s → ℤ) :
    Exec w (code.embed s) (data.extend tail) (result.extend tail) cost := by
  induction execution with
  | atom evaluation =>
    apply Exec.atom
    rw [Primitive.eval_embed,evaluation]
    rfl
  | seq first second ihFirst ihSecond => exact ihFirst.seq ihSecond
  | branch_yes holds body ih =>
    exact Exec.branch_yes ((Condition.holds_embed _ _ tail).mpr holds) ih
  | branch_no absent body ih =>
    exact Exec.branch_no (fun h => absent ((Condition.holds_embed _ _ tail).mp h)) ih
  | loop_done absent =>
    exact Exec.loop_done (fun h => absent ((Condition.holds_embed _ _ tail).mp h))
  | loop_more holds body rest ihBody ihRest =>
    exact Exec.loop_more ((Condition.holds_embed _ _ tail).mpr holds) ihBody ihRest

end Structured
end LeanTrominoes.ComplexityAbstract.RAM
