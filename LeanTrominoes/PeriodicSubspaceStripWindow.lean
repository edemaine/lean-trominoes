/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceTiling
import LeanTrominoes.LocalWindowCycle

/-! # Arbitrary bounded footprints on a periodic strip as finite windows -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Strip
abbrev Data := Input Int

def Bounded (input : Data) (bound : Nat) : Prop :=
  ∀ r ∈ input.2, r.2.natAbs ≤ bound

abbrev Column (input : Data) := Fin input.2.length → Bool
abbrev Window (input : Data) (bound : Nat) := LocalWindow.Window (Column input) (2*bound)

def value (input : Data) (kind : Nat) (column : Column input) : Bool :=
  decide (∃ i : Fin input.2.length, input.2[i].1.1=kind ∧ column i=true)

def position (bound : Nat) (c : Nat × Int) : Fin (2*bound+1) :=
  ⟨(bound+c.2).toNat % (2*bound+1),Nat.mod_lt _ (by omega)⟩

def center (bound : Nat) : Fin (2*bound+1) := ⟨bound,by omega⟩

def Valid (input : Data) (bound : Nat) (w : Window input bound) : Prop :=
  (∀ r ∈ input.2, value input r.1.1 (w (center bound))=true → r.1.2 ∈ input.1) ∧
    ∀ q ∈ input.1, ∃! c, c ∈ candidates input q ∧
      value input c.1 (w (position bound c))=true

theorem candidate_record (input : Data) {q : Nat} {c : Nat × Int}
    (member : c ∈ candidates input q) :
    ∃ r ∈ input.2, r.1.2=q ∧ c=(r.1.1,-r.2) := by
  obtain ⟨r,hr,equal⟩ := List.mem_filterMap.mp member
  change (if r.1.2=q then some (r.1.1,-r.2) else none)=some c at equal
  split_ifs at equal with h
  · exact ⟨r,hr,h,Option.some.inj equal |>.symm⟩

theorem position_eq (input : Data) {bound : Nat} (bounded : Bounded input bound)
    {q : Nat} {c : Nat × Int} (member : c ∈ candidates input q) :
    ((position bound c).val : Int) = (bound : Int)+c.2 := by
  obtain ⟨r,hr,_,rfl⟩ := candidate_record input member
  have size := bounded r hr
  have nonneg : 0 ≤ (bound : Int)+ -r.2 := by omega
  have small : ((bound : Int)+ -r.2).toNat < 2*bound+1 := by omega
  simp only [position,Nat.mod_eq_of_lt small,Int.toNat_of_nonneg nonneg]

theorem value_assignment (input : Data) (kind : Nat) (a : Nat → Bool)
    (exists_kind : ∃ r ∈ input.2, r.1.1=kind) :
    value input kind (fun i => a input.2[i].1.1) = a kind := by
  obtain ⟨r,hr,eq⟩ := exists_kind
  obtain ⟨i,hi,record⟩ := List.mem_iff_getElem.mp hr
  cases h : a kind with
  | false =>
    apply decide_eq_false_iff_not.mpr
    rintro ⟨j,hj,selected⟩
    change a input.2[j].1.1=true at selected
    rw [hj,h] at selected; contradiction
  | true =>
    apply decide_eq_true_eq.mpr
    refine ⟨⟨i,hi⟩,?_,?_⟩
    · change input.2[i].1.1=kind
      simpa only [record] using eq
    · change a input.2[i].1.1=true
      simpa only [record,eq] using h

theorem windows_of_tiling (input : Data) (bound : Nat) (bounded : Bounded input bound)
    (selected : Nat → Int → Bool) (tiled : IsTiling input selected) :
    ∀ x, Valid input bound (LocalWindow.windowAt (2*bound)
      (fun x i => selected input.2[i].1.1 x) x) := by
  obtain ⟨contained,covered⟩ := tiled
  intro x
  constructor
  · intro r hr one
    have eq := value_assignment input r.1.1 (fun k => selected k (x+bound)) ⟨r,hr,rfl⟩
    change value input r.1.1 (fun i => selected input.2[i].1.1 (x+bound))=true at one
    rw [eq] at one
    exact contained r hr _ one
  · intro q hq
    obtain ⟨c,hc,unique⟩ := covered q hq (x+bound)
    have truth (e : Nat × Int) (he : e ∈ candidates input q) :
        value input e.1 (LocalWindow.windowAt (2*bound)
          (fun x i => selected input.2[i].1.1 x) x (position bound e)) =
        selected e.1 (x+bound+e.2) := by
      obtain ⟨r,hr,_,equal⟩ := candidate_record input he
      have recordkind : ∃ r ∈ input.2, r.1.1=e.1 := by
        exact ⟨r,hr,by rw [equal]⟩
      change value input e.1 (fun i => selected input.2[i].1.1 (x+(position bound e).val)) = _
      rw [value_assignment input e.1 (fun k => selected k (x+(position bound e).val)) recordkind,
        position_eq input bounded he]
      congr 1; omega
    refine ⟨c,⟨hc.1,?_⟩,?_⟩
    · rw [truth c hc.1]; exact hc.2
    · intro e he
      exact unique e ⟨he.1,by rw [← truth e he.1]; exact he.2⟩

theorem tiling_of_windows (input : Data) (bound : Nat) (bounded : Bounded input bound)
    (configuration : Int → Column input)
    (valid : ∀ x, Valid input bound (LocalWindow.windowAt (2*bound) configuration x)) :
    IsTiling input (fun kind z => value input kind (configuration z)) := by
  constructor
  · intro r hr z one
    have contained := (valid (z-bound)).1
    apply contained r hr
    change value input r.1.1 (configuration ((z-bound)+bound))=true
    simpa using one
  · intro q hq z
    obtain ⟨c,hc,unique⟩ := (valid (z-bound)).2 q hq
    have truth (e : Nat × Int) (he : e ∈ candidates input q) :
        value input e.1 (LocalWindow.windowAt (2*bound) configuration (z-bound) (position bound e)) =
        value input e.1 (configuration (z+e.2)) := by
      change value input e.1 (configuration ((z-bound)+(position bound e).val)) = _
      rw [position_eq input bounded he]
      congr 2; omega
    refine ⟨c,⟨hc.1,?_⟩,?_⟩
    · change value input c.1 (configuration (z+c.2))=true
      rw [← truth c hc.1]; exact hc.2
    · intro e he
      exact unique e ⟨he.1,by rw [truth e he.1]; exact he.2⟩


theorem tileable_iff_windows (input : Data) (bound : Nat) (bounded : Bounded input bound) :
    Tileable input ↔ LocalWindow.Satisfiable (2*bound) (Valid input bound) := by
  constructor
  · rintro ⟨selected,tiled⟩
    exact ⟨_,windows_of_tiling input bound bounded selected tiled⟩
  · rintro ⟨configuration,valid⟩
    exact ⟨_,tiling_of_windows input bound bounded configuration valid⟩

theorem tileable_iff_cycle (input : Data) (bound : Nat) (bounded : Bounded input bound) :
    Tileable input ↔ FiniteState.HasCycle (LocalWindow.Transition (Valid input bound)) := by
  rw [tileable_iff_windows input bound bounded,LocalWindow.satisfiable_iff_cycle]

end LeanTrominoes.PeriodicSubspaceTiling.Strip
