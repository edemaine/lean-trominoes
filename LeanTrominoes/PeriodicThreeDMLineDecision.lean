/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFEdgeLocalization
import LeanTrominoes.PeriodicThreeDMCNF
import LeanTrominoes.PeriodicThreeDMOneDimensionalContraction
import LeanTrominoes.PeriodicExactOneCNFLocality

/-! # A total decision procedure for local one-dimensional periodic 3DM

The graph locality condition bounds individual incidence edges. Shadow
variables keep the SAT translation local even when an element's incident
triples lie in both neighboring cells. This is semantic cycle-search
correctness; an encoded polynomial-space certificate is a separate step.
-/
namespace LeanTrominoes.PeriodicThreeDM
open Gadget

def IsLocal (p : PeriodicThreeDM) : Prop :=
  ∀ t ∈ p.triples, ∀ c, (t.reference c).offset.1.natAbs + (t.reference c).offset.2.natAbs ≤ 1

instance (p : PeriodicThreeDM) : Decidable p.IsLocal := by
  unfold IsLocal
  infer_instance

instance (p : PeriodicThreeDM) : Decidable p.IsOneDimensional := by
  unfold IsOneDimensional
  infer_instance

def LocalLineProblem (p : PeriodicThreeDM) : Prop :=
  p.IsWellFormed ∧ p.DegreeTwoOrThree ∧ p.IsOneDimensional ∧ p.IsLocal ∧ p.Satisfiable

theorem incidence_offset_local {p : PeriodicThreeDM} (h : p.IsLocal)
    (c : WireColor) (v : Nat) {i : Incidence} (hi : i ∈ p.incidences c v) :
    i.offset.1.natAbs + i.offset.2.natAbs ≤ 1 := by
  simp only [incidences,List.mem_filterMap] at hi
  obtain ⟨j,hj,hi⟩ := hi
  have bound := List.mem_range.mp hj
  split at hi
  · simp only [Option.some.injEq] at hi
    subst i
    apply h _ _ c
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem _
  · contradiction

namespace AsCNF

theorem exactOne_horizontal (p : PeriodicThreeDM) (h : p.IsOneDimensional) :
    (exactOne p).IsOneDimensional := by
  intro cl hcl l hl
  obtain ⟨c,_,hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hcl
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
  have hz := incidence_offset_vertical_eq_zero h c v hi
  simp [literal,Cell.sub,hz]

theorem exactOne_edgeLocal (p : PeriodicThreeDM) (h : p.IsLocal) :
    PeriodicCNF.EdgeLocalization.EdgeLocal (exactOne p) := by
  intro cl hcl l hl
  obtain ⟨c,_,hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hcl
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
  simpa [literal,Cell.sub] using incidence_offset_local h c v hi

theorem exactOne_width (p : PeriodicThreeDM) (h : p.DegreeTwoOrThree) :
    (exactOne p).WidthAtMost 3 := by
  intro cl hcl
  obtain ⟨c,_,hcl⟩ := List.mem_flatMap.mp hcl
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hcl
  have hd := h c v (List.mem_range.mp hv)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hd
  change ((p.incidences c v).map literal).length ≤ 3
  rw [List.length_map]
  change p.degree c v ≤ 3
  omega

private theorem mutex_edgeLocal {V : Type} (cl : PeriodicClause V)
    (h : ∀ l ∈ cl, l.offset.1.natAbs+l.offset.2.natAbs ≤ 1) :
    ∀ d ∈ PeriodicExactOneCNF.mutex cl, ∀ l ∈ d,
      l.offset.1.natAbs+l.offset.2.natAbs ≤ 1 := by
  induction cl with
  | nil => simp [PeriodicExactOneCNF.mutex]
  | cons a rest ih =>
    intro d hd l hl
    simp only [PeriodicExactOneCNF.mutex,List.mem_append,List.mem_map] at hd
    rcases hd with ⟨b,hb,rfl⟩ | hd
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl
      · exact h a (by simp)
      · exact h b (by simp [hb])
    · exact ih (fun l hl => h l (by simp [hl])) d hd l hl

theorem formula_edgeLocal (p : PeriodicThreeDM) (h : p.IsLocal) :
    PeriodicCNF.EdgeLocalization.EdgeLocal (formula p) := by
  intro d hd l hl
  obtain ⟨cl,hcl,hd⟩ := List.mem_flatMap.mp hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact exactOne_edgeLocal p h d hcl l hl
  · exact mutex_edgeLocal cl (exactOne_edgeLocal p h cl hcl) d hd l hl

def localFormula (p : PeriodicThreeDM) : PeriodicCNF (Nat × Cell) :=
  PeriodicCNF.EdgeLocalization.formula (formula p)

theorem localFormula_satisfiable (p : PeriodicThreeDM) :
    (localFormula p).Satisfiable ↔ p.Satisfiable :=
  (PeriodicCNF.EdgeLocalization.satisfiable_iff _).trans (satisfiable_iff p)

theorem localFormula_local (p : PeriodicThreeDM) (h : p.IsLocal) :
    (localFormula p).IsLocal :=
  PeriodicCNF.EdgeLocalization.isLocal _ (formula_edgeLocal p h)

theorem localFormula_horizontal (p : PeriodicThreeDM) (h : p.IsOneDimensional) :
    (localFormula p).IsOneDimensional :=
  PeriodicCNF.EdgeLocalization.isOneDimensional _
    ((PeriodicExactOneCNF.isOneDimensional_iff _).2 (exactOne_horizontal p h))

theorem localFormula_width (p : PeriodicThreeDM) (h : p.DegreeTwoOrThree) :
    (localFormula p).WidthAtMost 3 :=
  PeriodicCNF.EdgeLocalization.width _ (by decide)
    (PeriodicExactOneCNF.width_three _ (exactOne_width p h))
end AsCNF

def lineCheck (p : PeriodicThreeDM) : Bool :=
  decide p.IsWellFormed && decide p.DegreeTwoOrThree && decide p.IsOneDimensional &&
    decide p.IsLocal && PeriodicCNF.LineWindow.check (AsCNF.localFormula p)

theorem lineCheck_correct (p : PeriodicThreeDM) : lineCheck p = true ↔ LocalLineProblem p := by
  simp only [lineCheck,Bool.and_eq_true,decide_eq_true_eq,PeriodicCNF.LineWindow.check_correct,
    LocalLineProblem,AsCNF.localFormula_satisfiable]
  constructor
  · rintro ⟨⟨⟨⟨hw,hd⟩,hh⟩,hl⟩,_,_,hs⟩
    exact ⟨hw,hd,hh,hl,hs⟩
  · rintro ⟨hw,hd,hh,hl,hs⟩
    exact ⟨⟨⟨⟨hw,hd⟩,hh⟩,hl⟩,AsCNF.localFormula_horizontal p hh,
      AsCNF.localFormula_local p hl,hs⟩

end LeanTrominoes.PeriodicThreeDM
