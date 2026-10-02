/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicConstraints

/-! # Finite quotient presentations of periodic subspace tiling

A footprint records each tile cell by its fundamental-domain representative
and lattice displacement. The number of tile kinds and cells is unrestricted;
no connectivity assumption is made. Orientations may be listed as additional
kinds. Solutions are arbitrary infinite selections, not periodic selections.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling
variable (G : Type) [AddCommGroup G]

abbrev Input := List Nat × List ((Nat × Nat) × G)

/-- Indexed tile cells: ((tile kind, representative), lattice offset). -/
def records (input : Input G) : List ((Nat × Nat) × G) :=
  input.2

/-- Ordinary lists of finite footprints give a cell-record presentation.
Empty kinds need no records, and duplicate cells do not affect the semantics. -/
def ofTiles (target : List Nat) (tiles : List (List (Nat × G))) : Input G :=
  (target,(List.range tiles.length).flatMap fun k =>
    (tiles[k]?.getD []).map fun q => ((k,q.1),q.2))


variable {G} [DecidableEq G]
/-- All placements covering representative `q` at lattice offset zero. -/
def candidates (input : Input G) (q : Nat) : List (Nat × G) :=
  (records G input).filterMap fun r => if r.1.2=q then some (r.1.1,-r.2) else none

/-- Containment, coverage, and uniqueness are precisely the tiling conditions. -/
def IsTiling (input : Input G) (selected : Nat → G → Bool) : Prop :=
  (∀ r ∈ records G input, ∀ z, selected r.1.1 z = true → r.1.2 ∈ input.1) ∧
    ∀ q ∈ input.1, ∀ z, ∃! c, c ∈ candidates input q ∧ selected c.1 (z+c.2)=true

def Tileable (input : Input G) : Prop := ∃ selected, IsTiling input selected

/-- Coverage clauses, one for each target representative. -/
def cover (input : Input G) (q : Nat) : List (PeriodicConstraints.Literal G) :=
  (candidates input q).map fun c => (c,true)

/-- Distinct overlapping placements may not both be selected. -/
def exclusions (input : Input G) (q : Nat) : PeriodicConstraints.Formula G :=
  (candidates input q).flatMap fun c => (candidates input q).flatMap fun e =>
    if c=e then [] else [[(c,false),(e,false)]]

/-- A tile extending outside the target is forbidden at every translate. -/
def forbidden (input : Input G) : PeriodicConstraints.Formula G :=
  (records G input).flatMap fun r =>
    if r.1.2 ∈ input.1 then [] else [[((r.1.1,0),false)]]

/-- The complete finite periodic CNF presentation. -/
def formula (input : Input G) : PeriodicConstraints.Formula G :=
  input.1.flatMap (fun q => cover input q :: exclusions input q) ++ forbidden input

theorem cover_holds (input : Input G) (q : Nat) (a : Nat → G → Bool) (z : G) :
    (∃ l ∈ cover input q, a l.1.1 (z+l.1.2)=l.2) ↔
      ∃ c ∈ candidates input q, a c.1 (z+c.2)=true := by
  simp [cover]

theorem exclusions_holds (input : Input G) (q : Nat) (a : Nat → G → Bool) (z : G) :
    (∀ clause ∈ exclusions input q, ∃ l ∈ clause, a l.1.1 (z+l.1.2)=l.2) ↔
      ∀ c ∈ candidates input q, ∀ e ∈ candidates input q,
        a c.1 (z+c.2)=true → a e.1 (z+e.2)=true → c=e := by
  simp only [exclusions,List.forall_mem_flatMap]
  constructor
  · intro h c hc e he one two
    by_contra ne
    have disj := h c hc e he
    simp only [if_neg ne,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp] at disj
    have clause := disj _ rfl
    simp only [List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp] at clause
    simp [one,two] at clause
  · intro unique c hc e he
    by_cases same : c=e
    · simp [same]
    · simp only [if_neg same,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,true_and]
      intro clause equal
      subst clause
      by_cases one : a c.1 (z+c.2)=true
      · have two : a e.1 (z+e.2)=false := by
          cases value : a e.1 (z+e.2) with
          | false => rfl
          | true => exact (same (unique c hc e he one value)).elim
        exact ⟨(e,false),by simp,two⟩
      · have value : a c.1 (z+c.2)=false := by cases h : a c.1 (z+c.2) <;> simp_all
        exact ⟨(c,false),by simp,value⟩

theorem forbidden_holds (input : Input G) (a : Nat → G → Bool) :
    (∀ z clause, clause ∈ forbidden input → ∃ l ∈ clause, a l.1.1 (z+l.1.2)=l.2) ↔
      ∀ r ∈ records G input, ∀ z, a r.1.1 z=true → r.1.2 ∈ input.1 := by
  simp only [forbidden,List.forall_mem_flatMap]
  constructor
  · intro h r hr z one
    by_contra no
    have disj := h z r hr
    simp [no,one] at disj
  · intro contained z r hr
    by_cases inside : r.1.2 ∈ input.1
    · simp [inside]
    · have zero : a r.1.1 z=false := by
        cases value : a r.1.1 z with
        | false => rfl
        | true => exact (inside (contained r hr z value)).elim
      simp [inside,zero]

theorem formula_holds (input : Input G) (a : Nat → G → Bool) :
    PeriodicConstraints.Holds G (formula input) a ↔ IsTiling input a := by
  have split : PeriodicConstraints.Holds G (formula input) a ↔
      (∀ q ∈ input.1, ∀ z,
        (∃ c ∈ candidates input q, a c.1 (z+c.2)=true) ∧
          ∀ c ∈ candidates input q, ∀ e ∈ candidates input q,
            a c.1 (z+c.2)=true → a e.1 (z+e.2)=true → c=e) ∧
      (∀ r ∈ records G input, ∀ z, a r.1.1 z=true → r.1.2 ∈ input.1) := by
    unfold PeriodicConstraints.Holds formula
    simp only [List.forall_mem_append,List.forall_mem_flatMap,List.forall_mem_cons,
      cover_holds,exclusions_holds]
    rw [forall_and,forbidden_holds]
    constructor
    · rintro ⟨h,k⟩; exact ⟨fun q hq z => h z q hq,k⟩
    · rintro ⟨h,k⟩; exact ⟨fun z q hq => h q hq z,k⟩
  rw [split]
  unfold IsTiling
  constructor
  · rintro ⟨h,k⟩
    refine ⟨k,?_⟩
    intro q hq z
    obtain ⟨⟨c,hc,value⟩,unique⟩ := h q hq z
    exact ⟨c,⟨hc,value⟩,fun e he => unique e he.1 c hc he.2 value⟩
  · rintro ⟨k,h⟩
    refine ⟨?_,k⟩
    intro q hq z
    obtain ⟨c,hc,unique⟩ := h q hq z
    refine ⟨⟨c,hc⟩,?_⟩
    intro e he d hd one two
    exact (unique e ⟨he,one⟩).trans (unique d ⟨hd,two⟩).symm

/-- Satisfying assignments are exactly tilings of the periodic target. -/
theorem tileable_iff_formula (input : Input G) :
    Tileable input ↔ PeriodicConstraints.Satisfiable G (formula input) := by
  exact exists_congr fun a => (formula_holds input a).symm

end LeanTrominoes.PeriodicSubspaceTiling
