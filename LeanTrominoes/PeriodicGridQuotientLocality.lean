/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-! # Locality of canonical period-cell quotients -/
namespace LeanTrominoes

def periodCell (period : Nat) (point : Cell) : Cell :=
  (point.1/(period : Int),point.2/(period : Int))

theorem PeriodicVariablePlacement.gauged_literal_offset {V : Type*}
    (placement : PeriodicVariablePlacement V) (positive : 0<placement.period)
    (literal : PeriodicLiteral V) :
    (literal.variableGauge placement.canonicalPositionGauge).offset =
      periodCell placement.period (placement.literalPosition literal) := by
  have ne : (placement.period : Int) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have quotient (x k : Int) : (x+placement.period*k)/(placement.period : Int)=
      x/(placement.period : Int)+k := by
    rw [Int.add_ediv_of_dvd_right]
    · rw [Int.mul_ediv_cancel_left]
      exact ne
    · exact dvd_mul_right _ _
  apply Prod.ext
  · change literal.offset.1 + (placement.position literal.atom).1 / (placement.period : Int) =
      ((placement.position literal.atom).1 + (placement.period : Int) * literal.offset.1) /
        (placement.period : Int)
    rw [quotient,add_comm]
  · change literal.offset.2 + (placement.position literal.atom).2 / (placement.period : Int) =
      ((placement.position literal.atom).2 + (placement.period : Int) * literal.offset.2) /
        (placement.period : Int)
    rw [quotient,add_comm]

theorem period_quotients_near (p : Nat) (positive : 0<p) (a b : Int)
    (lower : -(p : Int)<a-b) (upper : a-b<(p : Int)) :
    (a/(p : Int)-b/(p : Int)).natAbs ≤ 1 := by
  have hp : (0 : Int)<p := by exact_mod_cast positive
  have first := Int.ediv_le_ediv hp (show a≤b+p by omega)
  have second := Int.ediv_le_ediv hp (show b≤a+p by omega)
  have ne : (p : Int) ≠ 0 := ne_of_gt hp
  have self : (p : Int)/(p : Int)=1 := Int.ediv_self ne
  simp [Int.add_ediv_of_dvd_right,self] at first second
  omega

theorem aligned_periodCells_local (p : Nat) (positive : 0<p) (a b : Cell)
    (aligned : a.1=b.1 ∨ a.2=b.2)
    (horizontal : -(p : Int)<a.1-b.1 ∧ a.1-b.1<(p : Int))
    (vertical : -(p : Int)<a.2-b.2 ∧ a.2-b.2<(p : Int)) :
    ((periodCell p a).1-(periodCell p b).1).natAbs +
      ((periodCell p a).2-(periodCell p b).2).natAbs ≤ 1 := by
  have hx := period_quotients_near p positive a.1 b.1 horizontal.1 horizontal.2
  have hy := period_quotients_near p positive a.2 b.2 vertical.1 vertical.2
  rcases aligned with h | h <;> simp only [periodCell,h,sub_self,Int.natAbs_zero,zero_add,add_zero] at * <;> assumption

end LeanTrominoes
