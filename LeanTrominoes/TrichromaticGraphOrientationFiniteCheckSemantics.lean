/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFiniteCountSemantics
import LeanTrominoes.TrichromaticGraphOrientationFiniteCheckColumns

/-! # Vertex checks characterize ordinary finite orientation constraints -/
namespace LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
open Gadget

theorem color_count_length_iff (values : List WireColor) (color : WireColor) :
    values.count color=values.length ↔ ∀ value ∈ values, value=color := by
  constructor
  · intro equal value member
    by_contra different
    have small := List.count_lt_length_iff.mpr ⟨value,member,different⟩
    omega
  · intro same
    induction values with
    | nil => rfl
    | cons value rest ih =>
      have head := same value (by simp)
      have tail : ∀ other ∈ rest, other=color := fun other member => same other (by simp [member])
      simp [head,ih tail]

theorem monochromatic_count_iff (values : List WireColor) (degree : values.length=3) :
    (values.count .red=3 ∨ values.count .green=3 ∨ values.count .blue=3) ↔
      ∃ color : WireColor, ∀ value ∈ values, value=color := by
  rw [← degree,color_count_length_iff,color_count_length_iff,color_count_length_iff]
  constructor
  · rintro (red | green | blue)
    · exact ⟨.red,red⟩
    · exact ⟨.green,green⟩
    · exact ⟨.blue,blue⟩
  · rintro ⟨color,same⟩
    cases color
    · exact Or.inl same
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr same)

theorem colorCheck_correct (s : WitnessInput) (vertex : Nat) (degree : (colors s.1 vertex).length=3) :
    colorCheck s vertex=true ↔
      if s.1.1.getD vertex false then ∀ color : WireColor, (colors s.1 vertex).count color=1
      else ∃ color : WireColor, ∀ value ∈ colors s.1 vertex, value=color := by
  cases kind : s.1.1.getD vertex false with
  | true =>
    simp only [colorCheck,kind,if_true,Bool.and_eq_true,decide_eq_true_eq,color_count_eq]
    constructor
    · rintro ⟨⟨red,green⟩,blue⟩ color
      cases color
      · exact red
      · exact green
      · exact blue
    · intro all
      exact ⟨⟨all .red,all .green⟩,all .blue⟩
  | false =>
    simp only [colorCheck,kind,Bool.false_eq_true,if_false,Bool.or_eq_true,decide_eq_true_eq,color_count_eq]
    rw [or_assoc]
    exact monochromatic_count_iff _ degree

theorem inwardCheck_correct (s : WitnessInput) (vertex : Nat) :
    inwardCheck s vertex=true ↔
      if s.1.1.getD vertex false then
        finiteInwardCount s.1 (fun edge => s.2.getD edge false) vertex=0 ∨
        finiteInwardCount s.1 (fun edge => s.2.getD edge false) vertex=3
      else finiteInwardCount s.1 (fun edge => s.2.getD edge false) vertex=1 := by
  cases kind : s.1.1.getD vertex false <;>
    simp only [inwardCheck,kind,if_true,Bool.false_eq_true,if_false,Bool.or_eq_true,
      decide_eq_true_eq,inward_count_eq]

theorem vertexCheck_correct (s : WitnessInput) :
    (∀ vertex < s.1.1.length, vertexCheck s vertex=true) ↔
      (∀ vertex < s.1.1.length, (colors s.1 vertex).length=3 ∧
        if s.1.1.getD vertex false then ∀ color : WireColor, (colors s.1 vertex).count color=1
        else ∃ color : WireColor, ∀ value ∈ colors s.1 vertex, value=color) ∧
      FiniteCountConstraints s.1 (fun edge => s.2.getD edge false) := by
  simp only [vertexCheck,Bool.and_eq_true,decide_eq_true_eq,degree_count_eq]
  constructor
  · intro checked
    constructor
    · intro vertex bound
      have h := checked vertex bound
      exact ⟨h.1.1,(colorCheck_correct s vertex h.1.1).mp h.1.2⟩
    · intro vertex bound
      exact (inwardCheck_correct s vertex).mp (checked vertex bound).2
  · rintro ⟨formed,oriented⟩ vertex bound
    have h := formed vertex bound
    exact ⟨⟨h.1,(colorCheck_correct s vertex h.1).mpr h.2⟩,
      (inwardCheck_correct s vertex).mpr (oriented vertex bound)⟩

end LeanTrominoes.TrichromaticGraphOrientation.FiniteVerifier
