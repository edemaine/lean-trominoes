/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingAugmentSize

/-! # Disjoint alternating families can be augmented together -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

theorem free_label_target (adj : L → R → Prop) (s : State L R) (p : Route L R)
    (alternating : Alternating adj s p) (r : R) (member : r ∈ routeLabels p)
    (free : s.right r=none) : r=p.target := by
  induction alternating with
  | last edge mate => simpa [routeLabels,Route.target] using member
  | @cons l t p edge mate rest ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst r; simp_all
    · exact ih member

theorem family_labels_nodup (adj : L → R → Prop) (s : State L R) (paths : List (Route L R))
    (alternating : ∀ p ∈ paths, Alternating adj s p)
    (vertices : (paths.flatMap Route.vertices).Nodup) (targets : (paths.map Route.target).Nodup) :
    (paths.flatMap routeLabels).Nodup := by
  induction paths with
  | nil => simp
  | cons p ps ih =>
    have verts := List.nodup_append.mp vertices
    have terminal := List.nodup_cons.mp targets
    have first := alternating p (List.mem_cons_self ..)
    have tailAlt := fun q hq => alternating q (List.mem_cons.mpr (Or.inr hq))
    apply List.nodup_append.mpr
    refine ⟨labels_nodup adj s p first verts.1,ih tailAlt verts.2.1 terminal.2,?_⟩
    intro r hr t ht equal
    subst t
    obtain ⟨q,hq,member⟩ := List.mem_flatMap.mp ht
    have next := tailAlt q hq
    cases mate : s.right r with
    | none =>
      have one := free_label_target adj s p first r hr mate
      have two := free_label_target adj s q next r member mate
      apply terminal.1
      exact List.mem_map.mpr ⟨q,hq,two.symm.trans one⟩
    | some w =>
      rcases label_classification adj s p first r hr with impossible | ⟨a,ha,ma⟩
      · simp_all
      · rcases label_classification adj s q next r member with impossible | ⟨b,hb,mb⟩
        · simp_all
        · have eqA : a=w := by simpa [mate] using ma.symm
          have eqB : b=w := by simpa [mate] using mb.symm
          subst a; subst b
          exact verts.2.2 w (List.mem_of_mem_tail ha) w
            (List.mem_flatMap.mpr ⟨q,hq,List.mem_of_mem_tail hb⟩) rfl

def applyRoutes (s : State L R) : List (Route L R) → State L R
  | [] => s
  | p::ps => applyRoutes (applyRoute s p) ps

/-- The disjointness hypotheses retain the original matching on every later route. -/
theorem applyRoutes_correct (adj : L → R → Prop) (s : State L R) (paths : List (Route L R))
    (consistent : Consistent s) (supported : Supported adj s)
    (alternating : ∀ p ∈ paths, Alternating adj s p)
    (rootFree : ∀ p ∈ paths, s.left p.first=none)
    (vertices : (paths.flatMap Route.vertices).Nodup)
    (labels : (paths.flatMap routeLabels).Nodup) :
    Consistent (applyRoutes s paths) ∧ Supported adj (applyRoutes s paths) ∧
      size (applyRoutes s paths)=size s+paths.length := by
  induction paths generalizing s with
  | nil => exact ⟨consistent,supported,by simp [applyRoutes]⟩
  | cons p ps ih =>
    have verts := List.nodup_append.mp vertices
    have label := List.nodup_append.mp labels
    have firstAlt := alternating p (List.mem_cons_self ..)
    have firstFree := rootFree p (List.mem_cons_self ..)
    obtain ⟨firstConsistent,firstSupported⟩ := applyRoute_correct adj s p consistent supported firstAlt verts.1 firstFree
    have firstSize := applyRoute_size adj s consistent p firstAlt verts.1 firstFree
    have tailAlt : ∀ q ∈ ps, Alternating adj (applyRoute s p) q := by
      intro q hq
      apply alternating_right_congr adj s _ q
      · intro r hr
        apply applyRoute_right_outside
        intro one
        exact label.2.2 r one r (List.mem_flatMap.mpr ⟨q,hq,hr⟩) rfl
      · exact alternating q (List.mem_cons.mpr (Or.inr hq))
    have tailFree : ∀ q ∈ ps, (applyRoute s p).left q.first=none := by
      intro q hq
      have outside : q.first ∉ p.vertices := by
        intro member
        exact verts.2.2 q.first member q.first (List.mem_flatMap.mpr ⟨q,hq,q.first_mem⟩) rfl
      rw [applyRoute_left_outside s p q.first outside]
      exact rootFree q (List.mem_cons.mpr (Or.inr hq))
    obtain ⟨resultConsistent,resultSupported,resultSize⟩ :=
      ih (applyRoute s p) firstConsistent firstSupported tailAlt tailFree verts.2.1 label.2.1
    refine ⟨resultConsistent,resultSupported,?_⟩
    simp only [applyRoutes,List.length_cons]
    omega

end LeanTrominoes.BipartiteMatching
