/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BlockingPathInvariants

/-! # Correctness of the adjacency-list scan -/
namespace LeanTrominoes.BlockingPath
variable {V T : Type*} [DecidableEq V] [DecidableEq T] [Fintype V]

structure ScanSpec (buckets : Buckets V T) (arcs : List (T × Option V))
    (v : V) (s : State V T) (result : Result V T) : Prop where
  extension : Extends s result.state
  valid : Valid result.state
  trap : Trap buckets result.state
  failure : result.route=none → result.state.used=s.used ∧ result.state.reserved=s.reserved ∧
    ∀ arc ∈ arcs, match arc.2 with
      | none => result.state.reserved arc.1=true
      | some w => result.state.blocked w=true
  success : ∀ p, result.route=some p →
    p.first=v ∧ Follows buckets p ∧ p.vertices.Nodup ∧
    (∀ w ∈ p.vertices, w ≠ v → s.blocked w=false) ∧ s.reserved p.target=false ∧
    (∀ w, result.state.used w=true ↔ s.used w=true ∨ w ∈ p.vertices) ∧
    (∀ t, result.state.reserved t=true ↔ s.reserved t=true ∨ t=p.target)

theorem scan_spec (buckets : Buckets V T) (budget : Nat)
    (descend : V → State V T → Result V T)
    (descend_spec : ∀ w s, remaining s ≤ budget → Valid s → Trap buckets s → Spec buckets w s (descend w s))
    (v : V) (arcs : List (T × Option V)) (subset : ∀ arc ∈ arcs, arc ∈ buckets v)
    (s : State V T) (enough : remaining s ≤ budget) (valid : Valid s)
    (trap : Trap buckets s) (used : s.used v=true) : ScanSpec buckets arcs v s (scan descend v arcs s) := by
  induction arcs generalizing s with
  | nil =>
    refine ⟨Extends.refl s,valid,trap,?_,?_⟩
    · intro _; exact ⟨rfl,rfl,by simp⟩
    · intro p hp; simp [scan] at hp
  | cons arc arcs ih =>
    obtain ⟨t,next⟩ := arc
    have tail : ∀ arc ∈ arcs, arc ∈ buckets v := fun a ha => subset a (List.mem_cons.mpr (Or.inr ha))
    have head := subset (t,next) (List.mem_cons_self ..)
    cases next with
    | none =>
      cases reserved : s.reserved t with
      | true =>
        have later := ih tail s enough valid trap used
        simp only [scan,reserved,if_true]
        refine ⟨later.extension,later.valid,later.trap,?_,?_⟩
        · intro absent
          obtain ⟨sameUsed,sameReserved,closed⟩ := later.failure absent
          refine ⟨sameUsed,sameReserved,?_⟩
          intro a member
          rcases List.mem_cons.mp member with eq | member
          · subst a
            exact later.extension.2.2 t reserved
          · exact closed a member
        · exact later.success
      | false =>
        simp only [scan,reserved,Bool.false_eq_true,if_false]
        refine ⟨reserve_extends s t,reserve_valid s valid t,reserve_trap buckets s trap t,?_,?_⟩
        · intro absent; simp at absent
        · intro p hp
          cases Option.some.inj hp
          refine ⟨rfl,Follows.last head,by simp [Route.vertices],?_,reserved,?_,?_⟩
          · intro w hw ne
            simp [Route.vertices] at hw
            exact (ne hw).elim
          · intro w
            change s.used w=true ↔ s.used w=true ∨ w ∈ [v]
            constructor
            · exact Or.inl
            · rintro (h | h)
              · exact h
              · have equal : w=v := by simpa using h
                simpa [equal] using used
          · intro r
            by_cases equal : r=t
            · simp [reserve,equal,Route.target]
            · simp [reserve,equal,Route.target]
    | some w =>
      have child := descend_spec w s enough valid trap
      cases found : (descend w s).route with
      | none =>
        have later := ih tail (descend w s).state
          ((remaining_mono child.extension).trans enough) child.valid child.trap (child.extension.2.1 v used)
        simp only [scan,found]
        refine ⟨child.extension.trans later.extension,later.valid,later.trap,?_,?_⟩
        · intro absent
          obtain ⟨laterUsed,laterReserved,closed⟩ := later.failure absent
          obtain ⟨childUsed,childReserved⟩ := child.failure found
          refine ⟨laterUsed.trans childUsed,laterReserved.trans childReserved,?_⟩
          intro a member
          rcases List.mem_cons.mp member with equal | member
          · subst a
            exact later.extension.1 w child.blocked
          · exact closed a member
        · intro p hp
          obtain ⟨first,follows,nodup,fresh,target,usedDelta,reservedDelta⟩ := later.success p hp
          obtain ⟨childUsed,childReserved⟩ := child.failure found
          refine ⟨first,follows,nodup,?_,?_,?_,?_⟩
          · intro a ha ne
            have freshLater := fresh a ha ne
            cases old : s.blocked a
            · rfl
            · have := child.extension.1 a old
              simp_all
          · simpa [childReserved] using target
          · intro a; simpa [childUsed] using usedDelta a
          · intro r; simpa [childReserved] using reservedDelta r
      | some path =>
        obtain ⟨first,follows,nodup,fresh,target,usedDelta,reservedDelta⟩ := child.success path found
        have notMem : v ∉ path.vertices := by
          intro member
          have one := fresh v member
          have two := valid v used
          simp_all
        simp only [scan,found]
        refine ⟨child.extension,child.valid,child.trap,?_,?_⟩
        · intro absent; simp at absent
        · intro p hp
          cases Option.some.inj hp
          refine ⟨rfl,Follows.cons (by simpa [first] using head) follows,
            List.nodup_cons.mpr ⟨notMem,nodup⟩,?_,target,?_,?_⟩
          · intro a member ne
            rcases List.mem_cons.mp member with equal | member
            · exact (ne equal).elim
            · exact fresh a member
          · intro a
            change (descend w s).state.used a=true ↔ s.used a=true ∨ a ∈ v::path.vertices
            rw [usedDelta]
            simp only [List.mem_cons]
            constructor
            · rintro (old | member)
              · exact Or.inl old
              · exact Or.inr (Or.inr member)
            · rintro (old | equal | member)
              · exact Or.inl old
              · subst a; exact Or.inl used
              · exact Or.inr member
          · exact reservedDelta

end LeanTrominoes.BlockingPath
