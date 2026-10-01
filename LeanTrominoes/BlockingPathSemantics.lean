/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathScan

/-! # Soundness and permanent-blocking invariants for depth-first search -/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype V]

theorem Route.first_mem (p : Route V T) : p.first ∈ p.vertices := by
  cases p <;> simp [Route.first,Route.vertices]

theorem search_spec (buckets : Buckets V T) (fuel : Nat) (v : V) (s : State V T)
    (enough : remaining s ≤ fuel) (valid : Valid s) (trap : Trap buckets s) :
    Spec buckets v s (search buckets fuel v s) := by
  induction fuel generalizing v s with
  | zero =>
    have blocked : s.blocked v=true := by
      cases h : s.blocked v
      · have member : v ∈ Finset.univ.filter (fun w => s.blocked w=false) := by simp [h]
        have positive := Finset.card_pos.mpr ⟨v,member⟩
        unfold remaining at enough
        omega
      · rfl
    refine ⟨Extends.refl s,valid,trap,blocked,?_,?_⟩
    · intro _; exact ⟨rfl,rfl⟩
    · intro p hp; simp [search] at hp
  | succ fuel ih =>
    cases fresh : s.blocked v with
    | true =>
      simp only [search,fresh,if_true]
      refine ⟨Extends.refl s,valid,trap,fresh,?_,?_⟩
      · intro _; exact ⟨rfl,rfl⟩
      · intro p hp; simp at hp
    | false =>
      have unused : s.used v=false := by
        cases h : s.used v
        · rfl
        · have := valid v h
          simp_all
      have fuelBound : remaining (enter s v) ≤ fuel := by
        have drop := remaining_enter s v fresh
        omega
      have later := scan_spec buckets fuel (search buckets fuel)
        (fun w t ht hv hp => ih w t ht hv hp) v (buckets v) (fun _ h => h)
        (enter s v) fuelBound (enter_valid s valid v) (enter_trap buckets s trap v)
        (by simp [enter])
      cases found : (scan (search buckets fuel) v (buckets v) (enter s v)).route with
      | none =>
        obtain ⟨sameUsed,sameReserved,closed⟩ := later.failure found
        simp only [search,fresh,Bool.false_eq_true,if_false,found]
        refine ⟨?_,retire_valid _ later.valid v,retire_trap buckets _ later.trap v closed,?_,?_,?_⟩
        · refine ⟨?_,?_,?_⟩
          · intro w h
            exact later.extension.1 w ((enter_extends s v).1 w h)
          · intro w h
            have ne : w ≠ v := by intro eq; subst w; simp_all
            change Function.update (scan (search buckets fuel) v (buckets v) (enter s v)).state.used v false w=true
            rw [Function.update_of_ne ne]
            exact later.extension.2.1 w ((enter_extends s v).2.1 w h)
          · intro t h
            exact later.extension.2.2 t h
        · exact later.extension.1 v (by simp [enter])
        · intro _
          refine ⟨?_,sameReserved⟩
          funext w
          by_cases eq : w=v
          · subst w; simp [retire,unused]
          · change Function.update (scan (search buckets fuel) v (buckets v) (enter s v)).state.used v false w=s.used w
            rw [Function.update_of_ne eq,sameUsed]
            simp [enter,eq]
        · intro p hp; simp at hp
      | some path =>
        obtain ⟨first,follows,nodup,freshPath,target,usedDelta,reservedDelta⟩ := later.success path found
        have rootMember : v ∈ path.vertices := first ▸ path.first_mem
        simp only [search,fresh,Bool.false_eq_true,if_false,found]
        refine ⟨(enter_extends s v).trans later.extension,later.valid,later.trap,
          later.extension.1 v (by simp [enter]),?_,?_⟩
        · intro absent; simp at absent
        · intro p hp
          cases Option.some.inj hp
          refine ⟨first,follows,nodup,?_,target,?_,reservedDelta⟩
          · intro w member
            by_cases eq : w=v
            · simpa [eq] using fresh
            · have h := freshPath w member eq
              simpa [enter,eq] using h
          · intro w
            rw [usedDelta]
            by_cases eq : w=v
            · subst w; simp [enter,rootMember]
            · simp [enter,eq]

/-- A route avoiding the used vertices cannot escape a failed vertex. -/
theorem trap_blocks_route (buckets : Buckets V T) (s : State V T) (trap : Trap buckets s)
    (p : Route V T) (follows : Follows buckets p) (root : s.blocked p.first=true)
    (avoids : ∀ v ∈ p.vertices, s.used v=false) : s.reserved p.target=true := by
  induction follows with
  | @last v t edge =>
    change s.blocked v=true at root
    change s.reserved t=true
    exact trap v root (avoids v (by simp [Route.vertices])) (t,none) edge
  | @cons v t p edge follows ih =>
    have closed := trap v root (avoids v (by simp [Route.vertices]))
    apply ih (closed _ edge)
    intro w hw
    exact avoids w (List.mem_cons.mpr (Or.inr hw))

end LeanTrominoes.BlockingPath
