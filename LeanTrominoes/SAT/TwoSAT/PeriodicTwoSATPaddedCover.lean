/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATBatch
import LeanTrominoes.SAT.TwoSAT.PeriodicTwoSATDigits

/-! # Cover generation without filtering empty records

For a positive variable count, every clause emits exactly two arcs. Empty
clauses emit self-loops. Thus cover table positions have fixed arithmetic
formulas; the separate Horn marker rules reject empty clauses.
-/
namespace LeanTrominoes.PeriodicTwoSAT.WordRAM
open PeriodicLatticeGraph ImplicationGraph
variable {n d M : ℕ} [NeZero M]

def dummy (positive : 0<n) : Signed (Fin n) := (⟨0,positive⟩,false)
def dummyArc (positive : 0<n) (d : ℕ) : Arc (Signed (Fin n)) d :=
  ⟨dummy positive,dummy positive,0⟩

def paddedClauseArcs (positive : 0<n) : Clause (Fin n) d → List (Arc (Signed (Fin n)) d)
  | none => [dummyArc positive d,dummyArc positive d]
  | some (a,b) => clauseArcs (some (a,b))

def paddedArcs (positive : 0<n) (formula : Formula (Fin n) d) : List (Arc (Signed (Fin n)) d) :=
  formula.flatMap (paddedClauseArcs positive)

theorem paddedArcs_length (positive : 0<n) (formula : Formula (Fin n) d) :
    (paddedArcs positive formula).length=2*formula.length := by
  have clauseLength (c : Clause (Fin n) d) : (paddedClauseArcs positive c).length=2 := by
    cases c with
    | none => rfl
    | some pair => rcases pair with ⟨a,b⟩; rfl
  simp [paddedArcs,List.length_flatMap,clauseLength,Nat.mul_comm]

theorem paddedArcs_mem (positive : 0<n) (formula : Formula (Fin n) d) (e : Arc (Signed (Fin n)) d) :
    e ∈ paddedArcs positive formula ↔ e ∈ arcs formula ∨ (none ∈ formula ∧ e=dummyArc positive d) := by
  simp only [paddedArcs,arcs,List.mem_flatMap]
  constructor
  · rintro ⟨c,hc,he⟩
    cases c with
    | none => exact Or.inr ⟨hc,by simpa [paddedClauseArcs] using he⟩
    | some pair => exact Or.inl ⟨some pair,hc,he⟩
  · rintro (⟨c,hc,he⟩ | ⟨hc,rfl⟩)
    · cases c with
      | none => simp [clauseArcs] at he
      | some pair => exact ⟨some pair,hc,he⟩
    · exact ⟨none,hc,by simp [paddedClauseArcs]⟩

theorem padded_coverAdj (positive : 0<n) (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    CoverAdj (paddedArcs positive formula) M u v →
      Relation.ReflTransGen (CoverAdj (arcs formula) M) u v := by
  rintro ⟨e,he,hs,ht,hz⟩
  rcases (paddedArcs_mem positive formula e).mp he with original | ⟨_,rfl⟩
  · exact .single ⟨e,original,hs,ht,hz⟩
  · have same : u=v := by
      apply Prod.ext
      · exact hs.symm.trans ht
      · simpa [dummyArc,wrap] using hz.symm
    subst v
    exact .refl

theorem padded_coverReach (positive : 0<n) (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    CoverReach (paddedArcs positive formula) M u v ↔ CoverReach (arcs formula) M u v := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih => exact ih.trans (padded_coverAdj positive formula w v edge)
  · intro path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih =>
      obtain ⟨e,he,hs,ht,hz⟩ := edge
      exact ih.tail ⟨e,(paddedArcs_mem positive formula e).mpr (Or.inl he),hs,ht,hz⟩

def paddedCoverEdges (positive : 0<n) (formula : Formula (Fin n) d) (M : ℕ) [NeZero M] :
    List (Fin (n*2*M^d) × Fin (n*2*M^d)) :=
  (List.finRange (M^d)).flatMap fun i => (paddedArcs positive formula).map fun e =>
    (coverIndex n d M (e.source,(coordinateIndex d M).symm i),
      coverIndex n d M (e.target,(coordinateIndex d M).symm i+wrap M e.offset))

theorem paddedCoverEdges_length (positive : 0<n) (formula : Formula (Fin n) d) :
    (paddedCoverEdges positive formula M).length=2*formula.length*M^d := by
  simp [paddedCoverEdges,List.length_flatMap,paddedArcs_length]
  ring

theorem paddedCoverEdges_mem (positive : 0<n) (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    (coverIndex n d M u,coverIndex n d M v) ∈ paddedCoverEdges positive formula M ↔
      CoverAdj (paddedArcs positive formula) M u v := by
  constructor
  · intro member
    obtain ⟨i,hi,edge⟩ := List.mem_flatMap.mp member
    obtain ⟨e,he,equal⟩ := List.mem_map.mp edge
    have left := (coverIndex n d M).injective (Prod.mk.inj equal).1
    have right := (coverIndex n d M).injective (Prod.mk.inj equal).2
    refine ⟨e,he,congrArg Prod.fst left,congrArg Prod.fst right,?_⟩
    have one := congrArg Prod.snd left
    have two := congrArg Prod.snd right
    exact two.symm.trans (congrArg (fun z => z+wrap M e.offset) one)
  · rintro ⟨e,he,source,target,displacement⟩
    apply List.mem_flatMap.mpr
    refine ⟨coordinateIndex d M u.2,List.mem_finRange _,List.mem_map.mpr ⟨e,he,?_⟩⟩
    apply Prod.ext
    · apply congrArg (coverIndex n d M)
      exact Prod.ext source (by simp)
    · apply congrArg (coverIndex n d M)
      exact Prod.ext target (by simpa using displacement.symm)

theorem paddedCoverEdges_reach (positive : 0<n) (formula : Formula (Fin n) d)
    (u v : Signed (Fin n) × CoverLattice d M) :
    Relation.ReflTransGen (EdgeAdj (paddedCoverEdges positive formula M))
      (coverIndex n d M u) (coverIndex n d M v) ↔ CoverReach (arcs formula) M u v := by
  rw [← padded_coverReach positive formula u v]
  have lifted : ∀ s t, Relation.ReflTransGen (EdgeAdj (paddedCoverEdges positive formula M)) s t →
      CoverReach (paddedArcs positive formula) M ((coverIndex n d M).symm s) ((coverIndex n d M).symm t) := by
    intro s t path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih =>
      apply ih.tail
      apply (paddedCoverEdges_mem positive formula _ _).mp
      simpa only [EdgeAdj,Equiv.apply_symm_apply] using edge
  have projected : ∀ s t, CoverReach (paddedArcs positive formula) M s t →
      Relation.ReflTransGen (EdgeAdj (paddedCoverEdges positive formula M))
        (coverIndex n d M s) (coverIndex n d M t) := by
    intro s t path
    induction path with
    | refl => exact .refl
    | @tail w v path edge ih => exact ih.tail ((paddedCoverEdges_mem positive formula w v).mpr edge)
  constructor
  · intro path
    simpa only [Equiv.symm_apply_apply] using lifted _ _ path
  · exact projected u v

end LeanTrominoes.PeriodicTwoSAT.WordRAM
