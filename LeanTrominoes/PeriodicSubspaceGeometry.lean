/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceCompletion
import Mathlib.Tactic.Abel

/-! # Geometric meaning of finite quotient footprint records

A cell is its representative and lattice coordinate. A placement translates
every cell of one footprint by the same lattice vector. This file identifies
the constraint semantics with containment and exact cover by these placements.
In a fundamental-domain chart these are the ordinary geometric tiling axioms.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling
variable {G : Type} [AddCommGroup G] [DecidableEq G]

def placedCells (input : Input G) (placement : Nat × G) : Set (Nat × G) :=
  {x | ∃ r∈input.2, r.1.1=placement.1 ∧ x=(r.1.2,placement.2+r.2)}

def targetRegion (input : Input G) : Set (Nat × G) := {x | x.1∈input.1}

def GeometricIsTiling (input : Input G) (selected : Nat → G → Bool) : Prop :=
  (∀ p, selected p.1 p.2=true → placedCells input p ⊆ targetRegion input) ∧
    ∀ x∈targetRegion input, ∃! p, selected p.1 p.2=true ∧ x∈placedCells input p

theorem placedCells_candidate (input : Input G) (q : Nat) (z : G) (p : Nat × G) :
    (q,z)∈placedCells input p ↔ (p.1,p.2-z)∈candidates input q := by
  constructor
  · rintro ⟨r,hr,hk,equal⟩
    have proto := congrArg Prod.fst equal
    have offset := congrArg Prod.snd equal
    apply List.mem_filterMap.mpr
    refine ⟨r,hr,?_⟩
    change (if r.1.2=q then some (r.1.1,-r.2) else none)=some (p.1,p.2-z)
    rw [if_pos proto.symm,hk]
    congr 2
    dsimp at offset
    rw [offset]
    abel
  · intro hc
    obtain ⟨r,hr,equal⟩ := List.mem_filterMap.mp hc
    change (if r.1.2=q then some (r.1.1,-r.2) else none)=some (p.1,p.2-z) at equal
    split_ifs at equal with hq
    · have eq := Option.some.inj equal
      refine ⟨r,hr,congrArg Prod.fst eq,?_⟩
      apply Prod.ext hq.symm
      have offset := congrArg Prod.snd eq
      dsimp at offset ⊢
      have : p.2+r.2=z := by
        apply sub_eq_zero.mp
        have reorder : p.2+r.2-z=(p.2-z)+r.2 := by abel
        rw [reorder,← offset,neg_add_cancel]
      exact this.symm

theorem geometricIsTiling_iff (input : Input G) (selected : Nat → G → Bool) :
    GeometricIsTiling input selected ↔ IsTiling input selected := by
  constructor
  · rintro ⟨contained,covered⟩
    constructor
    · intro r hr z selectedHere
      exact contained (r.1.1,z) selectedHere ⟨r,hr,rfl,rfl⟩
    · intro q hq z
      obtain ⟨p,hp,unique⟩ := covered (q,z) hq
      refine ⟨(p.1,p.2-z),⟨(placedCells_candidate input q z p).mp hp.2,?_⟩,?_⟩
      · simpa using hp.1
      · intro c hc
        have coveredHere : (q,z)∈placedCells input (c.1,z+c.2) := by
          apply (placedCells_candidate input q z _).mpr
          simpa using hc.1
        have eq := unique (c.1,z+c.2) ⟨hc.2,coveredHere⟩
        have same := congrArg (fun p : Nat × G => (p.1,p.2-z)) eq
        simpa using same
  · rintro ⟨contained,covered⟩
    constructor
    · intro p hp x hx
      obtain ⟨r,hr,hk,rfl⟩ := hx
      exact contained r hr p.2 (hk ▸ hp)
    · rintro ⟨q,z⟩ hq
      obtain ⟨c,hc,unique⟩ := covered q hq z
      refine ⟨(c.1,z+c.2),⟨hc.2,?_⟩,?_⟩
      · apply (placedCells_candidate input q z _).mpr
        simpa using hc.1
      · intro p hp
        have coveredHere := (placedCells_candidate input q z p).mp hp.2
        have selectedHere : selected p.1 (z+(p.2-z))=true := by simpa using hp.1
        have eq := unique (p.1,p.2-z) ⟨coveredHere,selectedHere⟩
        have same := congrArg (fun p : Nat × G => (p.1,z+p.2)) eq
        simpa using same

theorem tileable_iff_geometric (input : Input G) :
    Tileable input ↔ ∃ selected, GeometricIsTiling input selected :=
  exists_congr fun selected => (geometricIsTiling_iff input selected).symm

/-- Representatives used by the target or by any input footprint. -/
def supported (input : Input G) : Set (Nat × G) :=
  {x | x.1∈input.1 ∨ ∃ r∈input.2, r.1.2=x.1}

theorem placedCells_supported (input : Input G) (p : Nat × G) :
    placedCells input p ⊆ supported input := by
  rintro x ⟨r,hr,_,rfl⟩
  exact Or.inr ⟨r,hr,rfl⟩

/-- Ordinary exact cover after realizing representative/lattice coordinates
as physical cells. Injectivity is needed only on the finitely many used
representative orbits, so this also handles full-rank lattices. -/
def RealizedIsTiling {α : Type} (input : Input G) (realize : Nat × G → α)
    (selected : Nat → G → Bool) : Prop :=
  (∀ p, selected p.1 p.2=true →
    realize '' placedCells input p ⊆ realize '' targetRegion input) ∧
    ∀ x∈realize '' targetRegion input, ∃! p,
      selected p.1 p.2=true ∧ x∈realize '' placedCells input p

theorem realizedIsTiling_iff {α : Type} (input : Input G) (realize : Nat × G → α)
    (chart : Set.InjOn realize (supported input)) (selected : Nat → G → Bool) :
    RealizedIsTiling input realize selected ↔ IsTiling input selected := by
  rw [← geometricIsTiling_iff]
  constructor
  · rintro ⟨contained,covered⟩
    constructor
    · intro p hp x hx
      obtain ⟨y,hy,equal⟩ := contained p hp ⟨x,hx,rfl⟩
      have same := chart (Or.inl hy) (placedCells_supported input p hx) equal
      exact same ▸ hy
    · intro x hx
      obtain ⟨p,hp,unique⟩ := covered (realize x) ⟨x,hx,rfl⟩
      obtain ⟨y,hy,equal⟩ := hp.2
      have same := chart (placedCells_supported input p hy) (Or.inl hx) equal
      refine ⟨p,⟨hp.1,same ▸ hy⟩,?_⟩
      intro e he
      exact unique e ⟨he.1,⟨x,he.2,rfl⟩⟩
  · rintro ⟨contained,covered⟩
    constructor
    · intro p hp x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact ⟨y,contained p hp hy,rfl⟩
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := hx
      obtain ⟨p,hp,unique⟩ := covered y hy
      refine ⟨p,⟨hp.1,⟨y,hp.2,rfl⟩⟩,?_⟩
      intro e he
      obtain ⟨z,hz,equal⟩ := he.2
      have same := chart (placedCells_supported input e hz) (Or.inl hy) equal
      exact unique e ⟨he.1,same ▸ hz⟩

theorem tileable_iff_realized {α : Type} (input : Input G) (realize : Nat × G → α)
    (chart : Set.InjOn realize (supported input)) :
    Tileable input ↔ ∃ selected, RealizedIsTiling input realize selected :=
  exists_congr fun selected => (realizedIsTiling_iff input realize chart selected).symm

def RealizedIsCompletion {α : Type} (input : CompletionInput G) (realize : Nat × G → α)
    (selected : Nat → G → Bool) : Prop :=
  RealizedIsTiling input.1 realize selected ∧ ∀ k∈input.2, ∀ z, selected k z=true

theorem completable_iff_realized {α : Type} (input : CompletionInput G) (realize : Nat × G → α)
    (chart : Set.InjOn realize (supported input.1)) :
    Completable input ↔ ∃ selected, RealizedIsCompletion input realize selected := by
  simp only [Completable,IsCompletion,RealizedIsCompletion,realizedIsTiling_iff input.1 realize chart]

end LeanTrominoes.PeriodicSubspaceTiling
