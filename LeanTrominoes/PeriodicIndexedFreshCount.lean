/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Dedup

/-! # Exact distinct counts for clause-indexed finite blocks -/

namespace LeanTrominoes
namespace IndexedFreshCount

/-- Tag every item in a finite local block by its absolute input position and
the corresponding input item. -/
def blocksFrom {Item Fresh : Type*} (start : Nat) (items : List Item)
    (block : Item → List Fresh) : List ((Nat × Item) × Fresh) :=
  match items with
  | [] => []
  | item :: rest =>
      (block item).map (fun fresh => ((start, item), fresh)) ++
        blocksFrom (start + 1) rest block

@[simp] theorem blocksFrom_nil {Item Fresh : Type*}
    (start : Nat) (block : Item → List Fresh) :
    blocksFrom start [] block = [] := rfl

@[simp] theorem blocksFrom_cons {Item Fresh : Type*}
    (start : Nat) (item : Item) (rest : List Item)
    (block : Item → List Fresh) :
    blocksFrom start (item :: rest) block =
      (block item).map (fun fresh => ((start, item), fresh)) ++
        blocksFrom (start + 1) rest block := rfl

/-- Every tag in a suffix has index at least the suffix's starting index. -/
theorem index_ge_of_mem_blocksFrom {Item Fresh : Type*}
    (start : Nat) (items : List Item) (block : Item → List Fresh)
    {tagged : (Nat × Item) × Fresh}
    (member : tagged ∈ blocksFrom start items block) :
    start ≤ tagged.1.1 := by
  induction items generalizing start with
  | nil => simp at member
  | cons item rest induction =>
      rw [blocksFrom_cons, List.mem_append] at member
      rcases member with current | later
      · simp only [List.mem_map] at current
        rcases current with ⟨fresh, _, rfl⟩
        exact Nat.le_refl start
      · exact Nat.le_trans (Nat.le_succ start)
          (by simpa [Nat.succ_eq_add_one] using
            induction (start + 1) later)

/-- Different absolute input positions make the current block disjoint from
all later blocks. -/
theorem current_disjoint_later {Item Fresh : Type*}
    (start : Nat) (item : Item) (rest : List Item)
    (block : Item → List Fresh) :
    List.Disjoint
      ((block item).map (fun fresh => ((start, item), fresh)))
      (blocksFrom (start + 1) rest block) := by
  rw [List.disjoint_left]
  intro tagged current later
  simp only [List.mem_map] at current
  rcases current with ⟨fresh, _, rfl⟩
  have laterIndex := index_ge_of_mem_blocksFrom
    (start + 1) rest block later
  have impossible : Nat.succ start ≤ start := by
    simpa [Nat.succ_eq_add_one] using laterIndex
  exact (Nat.not_succ_le_self start) impossible

/-- Clause-index tagging makes the number of distinct global fresh values
the sum of the distinct local block sizes, even when a local block repeats a
value to encode several literal occurrences. -/
theorem dedup_length_blocksFrom {Item Fresh : Type*}
    [DecidableEq Item] [DecidableEq Fresh]
    (start : Nat) (items : List Item) (block : Item → List Fresh) :
    (blocksFrom start items block).dedup.length =
      (items.map fun item => (block item).dedup.length).sum := by
  induction items generalizing start with
  | nil => rfl
  | cons item rest induction =>
      rw [blocksFrom_cons,
        (current_disjoint_later start item rest block).dedup_append,
        List.length_append,
        List.dedup_map_of_injective
          (fun _ _ equal => congrArg Prod.snd equal),
        List.length_map,
        induction (start + 1)]
      rfl

end IndexedFreshCount
end LeanTrominoes
