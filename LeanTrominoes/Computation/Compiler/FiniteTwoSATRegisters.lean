/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Computation.RAM.RegisterEmbedding

/-! # Running a verified subprogram in any larger fixed register bank -/
namespace LeanTrominoes.ComplexityAbstract.RAM

def Data.castRegisters {r R : ℕ} (equal : r = R) (data : Data r) : Data R := equal ▸ data

theorem Data.castRegisters_memory {r R : ℕ} (equal : r = R) (data : Data r) :
    (data.castRegisters equal).2 = data.2 := by subst R; rfl

theorem Data.castRegisters_register {r R : ℕ} (equal : r = R) (data : Data r) (i : Fin R) :
    (data.castRegisters equal).1 i = data.1 (Fin.cast equal.symm i) := by subst R; rfl

def Data.restrict {r R : ℕ} (large : r ≤ R) (data : Data R) : Data r :=
  (fun i => data.1 (Fin.castLE large i),data.2)

namespace Structured

def Code.castRegisters {r R : ℕ} (equal : r = R) (code : Code r) : Code R := equal ▸ code

@[simp] theorem Code.size_castRegisters {r R : ℕ} (equal : r = R) (code : Code r) :
    (code.castRegisters equal).size = code.size := by subst R; rfl

theorem Exec.castRegisters {r R w : ℕ} (equal : r = R) {code : Code r} {data result : Data r} {steps : ℕ}
    (execution : Exec w code data result steps) :
    Exec w (code.castRegisters equal) (data.castRegisters equal) (result.castRegisters equal) steps := by
  subst R
  exact execution

def Code.widen {r R : ℕ} (large : r ≤ R) (code : Code r) : Code R :=
  (code.embed (R-r)).castRegisters (Nat.add_sub_of_le large)

@[simp] theorem Code.size_widen {r R : ℕ} (large : r ≤ R) (code : Code r) :
    (code.widen large).size = code.size := by simp [Code.widen,Code.size_embed]

theorem Exec.widen {r R w : ℕ} (large : r ≤ R) {code : Code r} {data result : Data r} {steps : ℕ}
    (execution : Exec w code data result steps) (caller : Data R)
    (memory : caller.2 = data.2) (registers : ∀ i, caller.1 (Fin.castLE large i) = data.1 i) :
    ∃ final, Exec w (code.widen large) caller final steps ∧ final.2 = result.2 ∧
      (∀ i, final.1 (Fin.castLE large i)=result.1 i) ∧
      (∀ i : Fin R, r ≤ i.val → final.1 i=caller.1 i) := by
  let equal : r+(R-r)=R := Nat.add_sub_of_le large
  let tail : Fin (R-r) → ℤ := fun i => caller.1 (Fin.cast equal (Fin.natAdd r i))
  have initial : (data.extend tail).castRegisters equal = caller := by
    apply Prod.ext
    · have split : ∀ j : Fin (r+(R-r)), (data.extend tail).1 j = caller.1 (Fin.cast equal j) := by
        intro j
        refine Fin.addCases ?_ ?_ j
        · intro a
          rw [Data.extend_left,← registers a]
          apply congrArg caller.1
          exact Fin.ext rfl
        · intro a
          rw [Data.extend_right]
      funext i
      rw [Data.castRegisters_register]
      have back : Fin.cast equal (Fin.cast equal.symm i)=i := Fin.ext rfl
      simpa only [back] using split (Fin.cast equal.symm i)
    · simpa only [Data.castRegisters_memory,Data.extend] using memory.symm
  let final := (result.extend tail).castRegisters equal
  refine ⟨final,?_,?_,?_,?_⟩
  · simpa only [Code.widen,initial] using (execution.embed tail).castRegisters equal
  · exact (Data.castRegisters_memory equal _).trans rfl
  · intro i
    rw [Data.castRegisters_register]
    have index : Fin.cast equal.symm (Fin.castLE large i)=Fin.castAdd (R-r) i := Fin.ext rfl
    rw [index,Data.extend_left]
  · intro i high
    rw [Data.castRegisters_register]
    let j : Fin (R-r) := ⟨i.val-r,by omega⟩
    have index : Fin.cast equal.symm i=Fin.natAdd r j := by apply Fin.ext; dsimp [j]; omega
    rw [index,Data.extend_right]
    dsimp only [tail]
    apply congrArg caller.1
    apply Fin.ext
    dsimp [j]
    omega

theorem Exec.widen_restrict {r R w : ℕ} (large : r ≤ R) {code : Code r} {caller : Data R}
    {result : Data r} {steps : ℕ} (execution : Exec w code (caller.restrict large) result steps) :
    ∃ final, Exec w (code.widen large) caller final steps ∧ final.2 = result.2 ∧
      (∀ i, final.1 (Fin.castLE large i)=result.1 i) ∧
      (∀ i : Fin R, r ≤ i.val → final.1 i=caller.1 i) :=
  execution.widen large caller rfl (fun _ => rfl)

end Structured
end LeanTrominoes.ComplexityAbstract.RAM
