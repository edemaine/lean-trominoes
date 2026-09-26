/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTemplateQueries

/-! # Querying a concatenation selects exactly the requested local fields -/
namespace LeanTrominoes.FiniteTemplateQueries

private theorem getD_middle {V : Type} (leading block trailing : List V) (i : Nat)
    (bound : i < block.length) (fallback : V) :
    (leading ++ block ++ trailing).getD (leading.length + i) fallback = block.getD i fallback := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  have before : ¬ leading.length + i < leading.length := by omega
  simp [before, bound]

/-- Arbitrary leading and trailing data cannot affect valid local template queries. -/
theorem lookup_middle {A V : Type} (blocks : A → List V) (offsets : A → List Nat)
    (valid : ∀ a i, i ∈ offsets a → i < (blocks a).length)
    (source : List A) (leading trailing : List V) (fallback : V) :
    (queriesFrom (fun a => (blocks a).length) offsets leading.length source).map
      (fun i => (leading ++ source.flatMap blocks ++ trailing).getD i fallback) =
      source.flatMap (fun a => (offsets a).map (fun i => (blocks a).getD i fallback)) := by
  induction source generalizing leading with
  | nil => rfl
  | cons a rest ih =>
    rw [queriesFrom, List.map_append, List.map_map, List.flatMap_cons, List.flatMap_cons]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro i hi
      simpa only [Function.comp_def, List.append_assoc] using
        getD_middle leading (blocks a) (rest.flatMap blocks ++ trailing) i (valid a i hi) fallback
    · have result := ih (leading ++ blocks a)
      simpa only [List.length_append, List.append_assoc] using result

theorem lookup {A V : Type} (blocks : A → List V) (offsets : A → List Nat)
    (valid : ∀ a i, i ∈ offsets a → i < (blocks a).length)
    (source : List A) (fallback : V) :
    (queriesFrom (fun a => (blocks a).length) offsets 0 source).map
      (fun i => (source.flatMap blocks).getD i fallback) =
      source.flatMap (fun a => (offsets a).map (fun i => (blocks a).getD i fallback)) := by
  simpa using lookup_middle blocks offsets valid source [] [] fallback


/-- Payloads do not change indices determined solely by template shapes. -/
theorem queriesFrom_map {A B : Type} (size : B → Nat) (offsets : B → List Nat)
    (shape : A → B) (source : List A) (start : Nat) :
    queriesFrom size offsets start (source.map shape) =
      queriesFrom (fun a => size (shape a)) (fun a => offsets (shape a)) start source := by
  induction source generalizing start with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, queriesFrom, ih]

/-- Equal template lengths give identical absolute query indices. -/
theorem queriesFrom_size_congr {A : Type} (first second : A → Nat) (offsets : A → List Nat)
    (source : List A) (equal : ∀ a ∈ source, first a = second a) (start : Nat) :
    queriesFrom first offsets start source = queriesFrom second offsets start source := by
  induction source generalizing start with
  | nil => rfl
  | cons a rest ih =>
    rw [queriesFrom, queriesFrom, equal a (by simp)]
    rw [ih (fun b hb => equal b (by simp [hb]))]

/-- Template-index queries remain valid when each template carries arbitrary data. -/
theorem lookup_payload {A B V : Type} (shape : A → B) (size : B → Nat) (offsets : B → List Nat)
    (blocks : A → List V) (source : List A)
    (lengths : ∀ a ∈ source, (blocks a).length = size (shape a))
    (valid : ∀ a i, i ∈ offsets (shape a) → i < (blocks a).length) (fallback : V) :
    (queriesFrom size offsets 0 (source.map shape)).map
      (fun i => (source.flatMap blocks).getD i fallback) =
      source.flatMap (fun a => (offsets (shape a)).map (fun i => (blocks a).getD i fallback)) := by
  rw [queriesFrom_map, queriesFrom_size_congr _ (fun a => (blocks a).length) _ source
    (fun a ha => (lengths a ha).symm)]
  exact lookup blocks (fun a => offsets (shape a)) valid source fallback

theorem queriesFrom_bound {A : Type} (size : A → Nat) (offsets : A → List Nat)
    (valid : ∀ a i, i ∈ offsets a → i < size a) (source : List A) (start i : Nat)
    (member : i ∈ queriesFrom size offsets start source) :
    start ≤ i ∧ i < start + (source.map size).sum := by
  induction source generalizing start with
  | nil => simp [queriesFrom] at member
  | cons a rest ih =>
    simp only [queriesFrom, List.mem_append, List.mem_map] at member
    simp only [List.map_cons, List.sum_cons]
    rcases member with ⟨j, hj, rfl⟩ | later
    · have h := valid a j hj
      omega
    · have h := ih (start + size a) later
      omega

end LeanTrominoes.FiniteTemplateQueries
