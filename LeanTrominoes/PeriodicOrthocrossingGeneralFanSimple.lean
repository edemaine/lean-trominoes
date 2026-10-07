/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralFanContacts
import LeanTrominoes.GridPolylineRealSimpleCertificate

/-! # Each fan is simple and reaches the port row only at its port -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem degreeFourFan_translated_simple (center : Int) (rank : Fin 4) :
    GridPolyline.SimpleBoxCertificate (translatePolyline (center,0) (degreeFourFan rank)) := by
  fin_cases rank <;>
    simp [degreeFourFan,translatePolyline,Cell.add,GridPolyline.SimpleBoxCertificate,
      gridPolylineSegments,GridSegment.BoxIntersectionIsPoint] <;> omega

theorem fan_simple_box_certificate {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) : GridPolyline.SimpleBoxCertificate (fan graph orthogonal port) := by
  cases orthogonal
  · simp [fan,GridPolyline.SimpleBoxCertificate,gridPolylineSegments]
  · exact degreeFourFan_translated_simple (vertexX graph port.vertex)
      ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩

theorem fan_isRealSimple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) : GridPolyline.IsRealSimple (fan graph orthogonal port) :=
  GridPolyline.isRealSimple_of_box_certificate (fan_simple_box_certificate graph orthogonal port)

theorem degreeFourFan_reverse_translated_simple (offset : Cell) (center : Int) (rank : Fin 4) :
    GridPolyline.SimpleBoxCertificate
      (translatePolyline offset (translatePolyline (center,0) (degreeFourFan rank)).reverse) := by
  fin_cases rank <;>
    simp [degreeFourFan,translatePolyline,Cell.add,GridPolyline.SimpleBoxCertificate,
      gridPolylineSegments,GridSegment.BoxIntersectionIsPoint] <;> omega

theorem fan_reverse_translated_simple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) (offset : Cell) : GridPolyline.SimpleBoxCertificate
      (translatePolyline offset (fan graph orthogonal port).reverse) := by
  cases orthogonal
  · simp [fan,translatePolyline,Cell.add,GridPolyline.SimpleBoxCertificate,gridPolylineSegments]
  · exact degreeFourFan_reverse_translated_simple offset (vertexX graph port.vertex)
      ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩

theorem degreeFourFan_top_contact (rank : Fin 4) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (degreeFourFan rank) point) (top : point.2 = 3) :
    point = ((rank.val : ℝ)-1,3) := by
  obtain ⟨segment,member,contains⟩ := contains
  fin_cases rank <;> simp [degreeFourFan,gridPolylineSegments] at member
  all_goals repeat' rcases member with rfl | member
  all_goals try subst segment
  all_goals have box := GridSegment.realBoxContains_of_realContains contains
  all_goals simp [GridSegment.RealBoxContains] at box
  all_goals apply Prod.ext <;> simp <;> linarith

theorem fan_top_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) {port : GraphPort Vertex} (member : port ∈ allPorts graph)
    (degree : orthogonal = true → graph.DegreeAtMost 4) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fan graph orthogonal port) point) (top : point.2 = 3) :
    point = realCell (portX graph port,3) := by
  cases orthogonal
  · obtain ⟨segment,segmentMember,contains⟩ := contains
    simp [fan,gridPolylineSegments] at segmentMember
    subst segment
    obtain ⟨t,lo,hi,hx,hy⟩ := contains
    simp only [Int.cast_ofNat] at hy
    have one : t = 1 := by linarith
    apply Prod.ext
    · simp only [realCell,Prod.fst]
      rw [one] at hx
      nlinarith [hx]
    · simpa [realCell] using top
  · have bound : portRank graph port < 4 :=
      lt_of_lt_of_le (port_rank_bound member) (by rw [portsAt_length]; exact degree rfl _)
    let rank : Fin 4 := ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩
    change GridPolyline.RealContains (translatePolyline (vertexX graph port.vertex,0) (degreeFourFan rank)) point at contains
    have localContains := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
    have localTop : (point.1-(vertexX graph port.vertex : ℝ),point.2-(0 : Int)).2 = (3 : ℝ) := by simpa using top
    have contact := degreeFourFan_top_contact rank localContains localTop
    have cx := congrArg Prod.fst contact
    have cy := congrArg Prod.snd contact
    dsimp only [rank] at cx
    rw [Nat.mod_eq_of_lt bound] at cx
    apply Prod.ext
    · simp only [realCell,Prod.fst,vertexX,portX,Int.cast_add,Int.cast_natCast,Int.cast_one] at cx ⊢
      push_cast at cx ⊢
      linarith
    · simpa [realCell] using top

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
