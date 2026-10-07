/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.Enum
import Mathlib.Tactic

/-! # Shifting the starting index of an enumerated list -/
namespace LeanTrominoes

theorem list_zipIdx_start_eq {α : Type*} (values : List α) (offset : Nat) :
    values.zipIdx offset = values.zipIdx.map (fun tagged => (tagged.1,tagged.2+offset)) := by
  induction values generalizing offset with
  | nil => simp
  | cons value rest ih =>
      simp only [List.zipIdx_cons,List.map_cons,Nat.zero_add]
      congr 1
      rw [ih (offset+1),ih 1,List.map_map]
      congr 1
      funext tagged
      apply Prod.ext <;> simp only [Function.comp_apply,Prod.fst,Prod.snd] <;> omega

end LeanTrominoes
