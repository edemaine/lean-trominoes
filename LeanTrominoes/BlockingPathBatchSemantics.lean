/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathBatch

/-! # Disjoint routes and maximality of the blocking phase -/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype V]

structure BatchSpec (buckets : Buckets V T) (roots : List V)
    (s : State V T) (result : BatchResult V T) : Prop where
  extension : Extends s result.state
  valid : Valid result.state
  trap : Trap buckets result.state
  blocked : ∀ v ∈ roots, result.state.blocked v=true
  follows : ∀ p ∈ result.paths, Follows buckets p
  simple : ∀ p ∈ result.paths, p.vertices.Nodup
  root : ∀ p ∈ result.paths, p.first ∈ roots
  fresh : ∀ p ∈ result.paths, ∀ v ∈ p.vertices, s.blocked v=false
  terminalFresh : ∀ p ∈ result.paths, s.reserved p.target=false
  used : ∀ v, result.state.used v=true ↔ s.used v=true ∨ ∃ p ∈ result.paths, v ∈ p.vertices
  reserved : ∀ t, result.state.reserved t=true ↔ s.reserved t=true ∨ ∃ p ∈ result.paths, t=p.target
  disjoint : (result.paths.flatMap Route.vertices).Nodup
  distinctTargets : (result.paths.map Route.target).Nodup

theorem batch_spec (buckets : Buckets V T) (fuel : Nat) (roots : List V) (s : State V T)
    (enough : remaining s ≤ fuel) (valid : Valid s) (trap : Trap buckets s) :
    BatchSpec buckets roots s (batch buckets fuel roots s) := by
  induction roots generalizing s with
  | nil =>
    refine ⟨Extends.refl s,valid,trap,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> simp [batch]
  | cons v vs ih =>
    have first := search_spec buckets fuel v s enough valid trap
    have later := ih (search buckets fuel v s).state ((remaining_mono first.extension).trans enough)
      first.valid first.trap
    cases found : (search buckets fuel v s).route with
    | none =>
      obtain ⟨sameUsed,sameReserved⟩ := first.failure found
      simp only [batch,found]
      refine ⟨first.extension.trans later.extension,later.valid,later.trap,?_,later.follows,later.simple,
        ?_,?_,?_,?_,?_,later.disjoint,later.distinctTargets⟩
      · intro w member
        rcases List.mem_cons.mp member with equal | member
        · subst w; exact later.extension.1 v first.blocked
        · exact later.blocked w member
      · intro p hp
        exact List.mem_cons.mpr (Or.inr (later.root p hp))
      · intro p hp w hw
        have fresh := later.fresh p hp w hw
        cases old : s.blocked w
        · rfl
        · have := first.extension.1 w old; simp_all
      · intro p hp
        have fresh := later.terminalFresh p hp
        simpa [sameReserved] using fresh
      · intro w; simpa [sameUsed] using later.used w
      · intro t; simpa [sameReserved] using later.reserved t
    | some path =>
      obtain ⟨root,follows,simple,fresh,terminalFresh,usedDelta,reservedDelta⟩ := first.success path found
      simp only [batch,found]
      refine ⟨first.extension.trans later.extension,later.valid,later.trap,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · intro w member
        rcases List.mem_cons.mp member with equal | member
        · subst w; exact later.extension.1 v first.blocked
        · exact later.blocked w member
      · intro p hp
        rcases List.mem_cons.mp hp with equal | member
        · subst p; exact follows
        · exact later.follows p member
      · intro p hp
        rcases List.mem_cons.mp hp with equal | member
        · subst p; exact simple
        · exact later.simple p member
      · intro p hp
        rcases List.mem_cons.mp hp with equal | member
        · subst p; simp [root]
        · exact List.mem_cons.mpr (Or.inr (later.root p member))
      · intro p hp w hw
        rcases List.mem_cons.mp hp with equal | member
        · subst p; exact fresh w hw
        · have freshLater := later.fresh p member w hw
          cases old : s.blocked w
          · rfl
          · have := first.extension.1 w old; simp_all
      · intro p hp
        rcases List.mem_cons.mp hp with equal | member
        · subst p; exact terminalFresh
        · have freshLater := later.terminalFresh p member
          cases old : s.reserved p.target
          · rfl
          · have := first.extension.2.2 p.target old; simp_all
      · intro w
        rw [later.used,usedDelta]
        simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
        tauto
      · intro t
        rw [later.reserved,reservedDelta]
        simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]
        tauto
      · simp only [List.flatMap_cons]
        apply List.nodup_append.mpr
        refine ⟨simple,later.disjoint,?_⟩
        intro w one z two equal
        subst z
        obtain ⟨p,hp,hw⟩ := List.mem_flatMap.mp two
        have blocked := first.valid w ((usedDelta w).mpr (Or.inr one))
        have absent := later.fresh p hp w hw
        simp_all
      · simp only [List.map_cons]
        apply List.nodup_cons.mpr
        refine ⟨?_,later.distinctTargets⟩
        intro member
        obtain ⟨p,hp,equal⟩ := List.mem_map.mp member
        have reserved := (reservedDelta path.target).mpr (Or.inr rfl)
        have absent := later.terminalFresh p hp
        rw [equal,reserved] at absent
        cases absent

theorem initial_valid : Valid (initial : State V T) := by simp [Valid,initial]
theorem initial_trap (buckets : Buckets V T) : Trap buckets (initial : State V T) := by
  simp [Trap,initial]

theorem blocking_spec (buckets : Buckets V T) (roots : List V) :
    BatchSpec buckets roots initial (batch buckets (Fintype.card V) roots initial) :=
  batch_spec buckets _ roots _ (by simp [remaining,initial]) initial_valid (initial_trap buckets)

/-- Every remaining route intersects a reserved vertex or ends at a reserved terminal. -/
theorem blocking_cut (buckets : Buckets V T) (roots : List V) (p : Route V T)
    (follows : Follows buckets p) (root : p.first ∈ roots)
    (avoids : ∀ v ∈ p.vertices, (batch buckets (Fintype.card V) roots initial).state.used v=false) :
    (batch buckets (Fintype.card V) roots initial).state.reserved p.target=true := by
  have spec := blocking_spec buckets roots
  exact trap_blocks_route buckets _ spec.trap p follows (spec.blocked p.first root) avoids

end LeanTrominoes.BlockingPath
