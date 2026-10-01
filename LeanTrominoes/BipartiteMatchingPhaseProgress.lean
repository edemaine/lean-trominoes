/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.BipartiteMatchingPhaseFamily

/-! # Blocking all old shortest routes increases the shortest length -/
namespace LeanTrominoes.BipartiteMatching
open BlockingPath
variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L]

namespace PhaseFamily
variable {buckets : L → List R} {matching : State L R} {height : L → Nat} {depth : Nat}
  {paths : List (Route L R)} (family : PhaseFamily buckets matching height depth paths)
include family

theorem level_transport (labels : Labels buckets matching height depth)
    (consistent : Consistent (applyRoutes matching paths)) (p : Route L R)
    (follows : Follows (levelBuckets buckets (applyRoutes matching paths) height depth) p)
    (outside : p.first ∉ paths.flatMap Route.vertices) :
    Follows (levelBuckets buckets matching height depth) p ∧
      (∀ l ∈ p.vertices, l ∉ paths.flatMap Route.vertices) ∧ p.target ∉ paths.flatMap routeLabels := by
  induction follows with
  | @last l r member =>
    obtain ⟨edge,free,layer⟩ := (mem_levelBuckets ..).mp member
    obtain ⟨notSelected,oldFree⟩ := family.new_free_right r free
    refine ⟨Follows.last ((mem_levelBuckets ..).mpr ⟨edge,oldFree,layer⟩),?_,notSelected⟩
    intro w hw
    have equal : w=l := by simpa [Route.vertices] using hw
    simpa [equal, Route.first] using outside
  | @cons l r p member rest ih =>
    obtain ⟨edge,mate,layer⟩ := (mem_levelBuckets ..).mp member
    have notSelected : r ∉ paths.flatMap routeLabels := by
      intro selected
      obtain ⟨q,hq,inside⟩ := List.mem_flatMap.mp selected
      obtain ⟨w,pair⟩ := pair_at_label q r inside
      have written := applyRoutes_right_write matching paths family.labels_nodup q hq w r pair
      have equal : w=p.first := Option.some.inj (written.symm.trans mate)
      have down := family.pair_down labels q hq w r pair l edge
      rw [equal] at down
      omega
    have nextOutside : p.first ∉ paths.flatMap Route.vertices := by
      intro used
      exact notSelected (family.used_partner consistent p.first used r mate)
    obtain ⟨oldRest,avoid,target⟩ := ih nextOutside
    have oldMate : matching.right r=some p.first := by
      rwa [applyRoutes_right_outside matching paths r notSelected] at mate
    refine ⟨Follows.cons ((mem_levelBuckets ..).mpr ⟨edge,oldMate,layer⟩) oldRest,?_,target⟩
    intro w hw
    rcases List.mem_cons.mp hw with equal | inside
    · simpa [equal, Route.first] using outside
    · exact avoid w inside

end PhaseFamily

theorem route_target_mem (p : Route L R) : p.target ∈ routeLabels p := by
  induction p <;> simp_all [Route.target,routeLabels]

/-- The matching after a blocking phase has no route of the old shortest length. -/
theorem blocking_no_short (buckets : L → List R) (matching : State L R)
    (consistent : Consistent matching) (supported : Supported (fun l r => r ∈ buckets l) matching)
    (height : L → Nat) (depth : Nat) (labels : Labels buckets matching height depth)
    (roots : List L) (free : ∀ l ∈ roots, matching.left l=none)
    (complete : ∀ l, matching.left l=none → l ∈ roots) :
    ¬ ∃ p : Route L R,
      Alternating (fun l r => r ∈ buckets l)
        (applyRoutes matching (batch (levelBuckets buckets matching height depth) (Fintype.card L) roots initial).paths) p ∧
      (applyRoutes matching (batch (levelBuckets buckets matching height depth) (Fintype.card L) roots initial).paths).left p.first=none ∧
      p.vertices.length ≤ depth := by
  let result := batch (levelBuckets buckets matching height depth) (Fintype.card L) roots initial
  have spec := blocking_spec (levelBuckets buckets matching height depth) roots
  have family := blocking_family buckets matching height depth roots free
  obtain ⟨finalConsistent,finalSupported,finalSize⟩ := family.correct consistent supported
  have finalLabels := family.labels_final labels
  rintro ⟨p,alternating,rootFree,short⟩
  have rootHeight := finalLabels.free p.first rootFree
  have lower := route_length_lower buckets (applyRoutes matching result.paths) height depth finalLabels p alternating
  have tight : height p.first+p.vertices.length=depth := by omega
  have follows := tight_route_follows buckets (applyRoutes matching result.paths) height depth finalLabels p alternating tight
  obtain ⟨outside,oldFree⟩ := family.new_free p.first rootFree
  obtain ⟨oldFollows,avoid,target⟩ := family.level_transport labels finalConsistent p follows outside
  have unused : ∀ l ∈ p.vertices, result.state.used l=false := by
    intro l hl
    cases used : result.state.used l with
    | false => rfl
    | true =>
      rcases (spec.used l).mp used with impossible | ⟨q,hq,inside⟩
      · simp [initial] at impossible
      · exact (avoid l hl (List.mem_flatMap.mpr ⟨q,hq,inside⟩)).elim
  have unreserved : result.state.reserved p.target=false := by
    cases reserved : result.state.reserved p.target with
    | false => rfl
    | true =>
      rcases (spec.reserved p.target).mp reserved with impossible | ⟨q,hq,equal⟩
      · simp [initial] at impossible
      · apply False.elim
        apply target
        rw [equal]
        exact List.mem_flatMap.mpr ⟨q,hq,route_target_mem q⟩
  have hit := blocking_cut (levelBuckets buckets matching height depth) roots p oldFollows
    (complete p.first oldFree) unused
  change result.state.reserved p.target=true at hit
  rw [unreserved] at hit
  cases hit

end LeanTrominoes.BipartiteMatching
