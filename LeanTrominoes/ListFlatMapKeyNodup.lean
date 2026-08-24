/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Nodup

/-! # Duplicate-free keyed flat-map blocks -/

namespace LeanTrominoes

/-- Flat-mapping duplicate-free blocks preserves duplicate-freedom when
input keys are unique and every output retains its input key. -/
theorem flatMap_nodup_of_map_key_nodup
    {Value Key Output : Type*}
    (values : List Value) (key : Value → Key)
    (outputKey : Output → Key) (blocks : Value → List Output)
    (keyNodup : (values.map key).Nodup)
    (blocksNodup : ∀ value ∈ values, (blocks value).Nodup)
    (blockKey : ∀ value ∈ values, ∀ output ∈ blocks value,
      outputKey output = key value) :
    (values.flatMap blocks).Nodup := by
  induction values with
  | nil => simp
  | cons value values induction =>
      have keyParts := List.nodup_cons.mp keyNodup
      have tailNodup := induction keyParts.2
        (fun later laterMember =>
          blocksNodup later (by simp [laterMember]))
        (fun later laterMember output outputMember =>
          blockKey later (by simp [laterMember]) output outputMember)
      rw [List.flatMap_cons, List.nodup_append]
      refine ⟨blocksNodup value (by simp), tailNodup, ?_⟩
      intro first firstMember second secondMember equal
      rcases List.mem_flatMap.mp secondMember with
        ⟨later, laterMember, secondBlockMember⟩
      have firstKey := blockKey value (by simp) first firstMember
      have secondKey := blockKey later (by simp [laterMember])
        second secondBlockMember
      have keyEq : key value = key later :=
        firstKey.symm.trans
          ((congrArg outputKey equal).trans secondKey)
      exact keyParts.1 (List.mem_map.mpr
        ⟨later, laterMember, keyEq.symm⟩)

end LeanTrominoes
