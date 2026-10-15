/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentSeparatingAxes

/-! # Bounded integer separators for disjoint nonparallel grid segments -/
namespace LeanTrominoes.GridSegment

theorem StrictlySeparated.negate_swap {normal : Cell} {first second : GridSegment}
    (separated : StrictlySeparated normal first second) :
    StrictlySeparated (-normal.1,-normal.2) second first := by
  have negate (p : Cell) : linearForm (-normal.1,-normal.2) p= -linearForm normal p := by
    unfold linearForm
    ring
  unfold StrictlySeparated at separated ⊢
  simp only [negate]
  omega

theorem positive_cross_integer_separator {bound : Int} {first second : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (positive : 0<cross first.direction second.direction)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    ∃ normal : Cell, (|normal.1|≤bound ∧ |normal.2|≤bound) ∧ StrictlySeparated normal first second := by
  by_contra noSeparator
  have normalBounds (s : GridSegment) (bounds : |s.direction.1|≤bound ∧ |s.direction.2|≤bound) :
      |s.normal.1|≤bound ∧ |s.normal.2|≤bound := by
    simpa only [normal,abs_neg] using And.intro bounds.2 bounds.1
  have negatedBounds (n : Cell) (bounds : |n.1|≤bound ∧ |n.2|≤bound) :
      |(-n.1,-n.2).1|≤bound ∧ |(-n.1,-n.2).2|≤bound := by simpa only [abs_neg] using bounds
  have rejectPositiveFirst : ¬(0<first.side second.start ∧ 0<first.side second.finish) := by
    rintro ⟨start,finish⟩
    exact noSeparator ⟨first.normal,normalBounds first firstBounds,strictlySeparated_of_positive_sides start finish⟩
  have rejectNegativeFirst : ¬(first.side second.start<0 ∧ first.side second.finish<0) := by
    rintro ⟨start,finish⟩
    exact noSeparator ⟨(-first.normal.1,-first.normal.2),negatedBounds _ (normalBounds first firstBounds),
      strictlySeparated_of_negative_sides start finish⟩
  have rejectPositiveSecond : ¬(0<second.side first.start ∧ 0<second.side first.finish) := by
    rintro ⟨start,finish⟩
    exact noSeparator ⟨(-second.normal.1,-second.normal.2),negatedBounds _ (normalBounds second secondBounds),
      (strictlySeparated_of_positive_sides start finish).negate_swap⟩
  have rejectNegativeSecond : ¬(second.side first.start<0 ∧ second.side first.finish<0) := by
    rintro ⟨start,finish⟩
    have separated := (strictlySeparated_of_negative_sides start finish).negate_swap
    have doubleNegate : (-(-second.normal.1),-(-second.normal.2))=second.normal := by simp
    rw [doubleNegate] at separated
    exact noSeparator ⟨second.normal,normalBounds second secondBounds,separated⟩
  have firstDifference := sides_difference first second
  have secondDifference := sides_difference second first
  rw [cross_swap second.direction first.direction] at secondDifference
  obtain ⟨p,firstMember,secondMember⟩ := intersects_of_straddling positive
    (by omega) (by omega) (by omega) (by omega)
  exact disjoint p firstMember secondMember

theorem nonparallel_integer_separator {bound : Int} {first second : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (nonparallel : cross first.direction second.direction≠0)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    ∃ normal : Cell, (|normal.1|≤bound ∧ |normal.2|≤bound) ∧ StrictlySeparated normal first second := by
  by_cases positive : 0<cross first.direction second.direction
  · exact positive_cross_integer_separator firstBounds secondBounds positive disjoint
  · have reverse : 0<cross second.direction first.direction := by
      rw [cross_swap second.direction first.direction]
      omega
    obtain ⟨n,bounds,separated⟩ := positive_cross_integer_separator secondBounds firstBounds reverse
      (fun p secondMember firstMember => disjoint p firstMember secondMember)
    exact ⟨(-n.1,-n.2),by simpa only [abs_neg] using bounds,separated.negate_swap⟩

theorem nonparallel_perturbations_disjoint {bound factor : Int} (nonnegative : 0≤bound) (spacing : 4*bound<factor)
    {first second firstOutput secondOutput : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (nonparallel : cross first.direction second.direction≠0)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p)
    (firstPerturbed : EndpointPerturbation factor first firstOutput)
    (secondPerturbed : EndpointPerturbation factor second secondOutput) :
    ∀ p : ℝ × ℝ, firstOutput.RealContains p → ¬secondOutput.RealContains p := by
  obtain ⟨n,bounds,separated⟩ := nonparallel_integer_separator firstBounds secondBounds nonparallel disjoint
  exact (separated.perturb nonnegative spacing bounds firstPerturbed secondPerturbed).no_common_point

end LeanTrominoes.GridSegment
