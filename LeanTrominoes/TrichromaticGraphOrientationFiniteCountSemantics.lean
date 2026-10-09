/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteCountColumns
import LeanTrominoes.TrichromaticGraphOrientationFiniteCounts

/-! # The compiled vertex counts have the ordinary finite graph semantics -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget PeriodicOneInThree

private theorem owner_count_filter (indices : List Nat) (owner : Nat → Nat) (vertex : Nat) :
    (indices.map owner).count vertex=(indices.filter fun index => owner index=vertex).length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    by_cases same : owner index=vertex
    · simp [same,ih]
    · simp [same,ih]

theorem degree_count_eq (s : WitnessInput) (vertex : Nat) :
    (ownerValues s).count vertex=(colors s.1 vertex).length := by
  unfold ownerValues colors endsAt
  rw [ends_eq_incidenceIndices]
  simp only [List.filter_map,List.length_map]
  exact owner_count_filter _ _ _

private theorem selected_owner_count (indices : List Nat) (owner : Nat → Nat) (selected : Nat → Bool) (vertex : Nat) :
    ((indices.filter fun index => owner index=vertex).map selected).count true=
      ((indices.filter selected).map owner).count vertex := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    by_cases same : owner index=vertex
    · cases active : selected index <;> simp [same,active,ih]
    · cases active : selected index <;> simp [same,active,ih]

theorem inward_literal_value (s : WitnessInput) (index : Nat) :
    ((s.2.getD (incidenceAt s.1 index).2.1.atom false) == (incidenceAt s.1 index).2.1.value)=inward s.2 index := by
  simp only [incidenceAt_atom,incidenceAt_polarity]
  unfold inward
  by_cases source : index%2=0
  · simp only [source,ne_eq,not_true_eq_false,decide_false,if_true]
    cases s.2.getD (index/2) false <;> rfl
  · simp only [source,ne_eq,not_false_eq_true,decide_true,if_false]
    cases s.2.getD (index/2) false <;> rfl

theorem inward_count_eq (s : WitnessInput) (vertex : Nat) :
    (selectedOwners s).count vertex=finiteInwardCount s.1 (fun edge => s.2.getD edge false) vertex := by
  unfold finiteInwardCount clauseValues incoming endsAt
  rw [ends_eq_incidenceIndices]
  simp only [List.filter_map,List.map_map,Function.comp_def,inward_literal_value]
  exact (selected_owner_count _ (fun index => (incidenceAt s.1 index).1) (inward s.2) vertex).symm

theorem colorField_eq_iff (first second : WireColor) :
    FlatEncoding.colorField first=FlatEncoding.colorField second ↔ first=second := by
  cases first <;> cases second <;> decide

private theorem color_owner_count (indices : List Nat) (owner : Nat → Nat) (color : Nat → WireColor)
    (vertex : Nat) (wanted : WireColor) :
    ((indices.filter fun index => color index=wanted).map owner).count vertex=
      ((indices.filter fun index => owner index=vertex).map color).count wanted := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    by_cases sameOwner : owner index=vertex <;> by_cases sameColor : color index=wanted <;>
      simp_all [eq_comm]

theorem color_count_eq (s : WitnessInput) (vertex : Nat) (color : WireColor) :
    (colorOwners color s).count vertex=(colors s.1 vertex).count color := by
  unfold colorOwners colors endsAt
  rw [ends_eq_incidenceIndices]
  simp only [colorField_eq_iff,List.filter_map,List.map_map,Function.comp_def]
  exact color_owner_count _ (fun index => (incidenceAt s.1 index).1)
    (fun index => (incidenceAt s.1 index).2.2) vertex color

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
