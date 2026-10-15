/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentCollinearSeparation
import LeanTrominoes.Common.Geometry.GridSegmentDirectionPerturbation
import LeanTrominoes.Common.Geometry.GridSegmentSharedEndpointCriterion
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple

/-! # Endpoint contacts survive small integer perturbations -/
namespace LeanTrominoes.GridSegment

def oriented (segment : GridSegment) (backwards : Bool) : GridSegment :=
  if backwards then segment.reverse else segment

theorem oriented_contains (segment : GridSegment) (backwards : Bool) (p : ℝ × ℝ) :
    (segment.oriented backwards).RealContains p ↔ segment.RealContains p := by
  cases backwards <;> simp [oriented,realContains_reverse]

theorem oriented_bounds {segment : GridSegment} {bound : Int}
    (bounds : |segment.direction.1|≤bound ∧ |segment.direction.2|≤bound) (backwards : Bool) :
    |(segment.oriented backwards).direction.1|≤bound ∧
      |(segment.oriented backwards).direction.2|≤bound := by
  cases backwards
  · exact bounds
  · simpa [GridSegment.oriented,reverse,direction,abs_sub_comm] using bounds

theorem EndpointPerturbation.oriented {factor : Int} {original output : GridSegment}
    (perturbed : EndpointPerturbation factor original output) (backwards : Bool) :
    EndpointPerturbation factor (original.oriented backwards) (output.oriented backwards) := by
  cases backwards
  · exact perturbed
  · exact ⟨perturbed.2,perturbed.1⟩

def EndpointContacts (first second : GridSegment) : Prop :=
  ∀ p : ℝ × ℝ, first.RealContains p → second.RealContains p →
    (p=realCell first.start ∨ p=realCell first.finish) ∧
      (p=realCell second.start ∨ p=realCell second.finish)

theorem EndpointContacts.oriented {first second : GridSegment}
    (contacts : EndpointContacts first second) (firstBackwards secondBackwards : Bool) :
    EndpointContacts (first.oriented firstBackwards) (second.oriented secondBackwards) := by
  intro p firstMember secondMember
  have endpoints := contacts p ((oriented_contains _ _ _).mp firstMember)
    ((oriented_contains _ _ _).mp secondMember)
  cases firstBackwards <;> cases secondBackwards <;>
    simpa [GridSegment.oriented,reverse,or_comm] using endpoints

theorem endpointPerturbation_nonconstant {factor : Int} (spacing : 2<factor)
    {original output : GridSegment} (nonconstant : original.start≠original.finish)
    (perturbed : EndpointPerturbation factor original output) : output.start≠output.finish := by
  intro equal
  have errors := perturbed.direction
  have coordinateZero (value : Int) (h : |factor*value|≤2) : value=0 := by
    by_contra nonzero
    have gap : 1≤|value| := by have := abs_pos.mpr nonzero; omega
    have scaled : factor*|value|≤2 := by
      simpa [abs_mul,abs_of_pos (show 0<factor by omega)] using h
    nlinarith
  have outputZero : output.direction=(0,0) := by simp [direction,equal]
  rw [outputZero] at errors
  have x := coordinateZero original.direction.1 (by simpa using errors.1)
  have y := coordinateZero original.direction.2 (by simpa using errors.2)
  exact nonconstant (Prod.ext (by simpa [direction] using (sub_eq_zero.mp x).symm)
    (by simpa [direction] using (sub_eq_zero.mp y).symm))

theorem perturbations_contact {factor bound : Int} (boundPositive : 1≤bound)
    (spacing : 8*bound+8<factor) {first second firstOutput secondOutput : GridSegment}
    (firstNonconstant : first.start≠first.finish) (secondNonconstant : second.start≠second.finish)
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (contacts : EndpointContacts first second)
    (firstPerturbed : EndpointPerturbation factor first firstOutput)
    (secondPerturbed : EndpointPerturbation factor second secondOutput)
    (agreement : ∀ a b : Bool, (first.oriented a).start=(second.oriented b).start →
      (firstOutput.oriented a).start=(secondOutput.oriented b).start)
    {p : ℝ × ℝ} (firstMember : firstOutput.RealContains p) (secondMember : secondOutput.RealContains p) :
    ∃ a b : Bool, (first.oriented a).start=(second.oriented b).start ∧
      p=realCell (firstOutput.oriented a).start ∧ p=realCell (secondOutput.oriented b).start := by
  by_cases oldMeet : ∃ q : ℝ × ℝ, first.RealContains q ∧ second.RealContains q
  · obtain ⟨q,firstOld,secondOld⟩ := oldMeet
    have endpoints := contacts q firstOld secondOld
    have orientedEndpoint (segment : GridSegment)
        (endpoint : q=realCell segment.start ∨ q=realCell segment.finish) :
        ∃ backwards : Bool, q=realCell (segment.oriented backwards).start := by
      rcases endpoint with equal | equal
      · exact ⟨false,equal⟩
      · exact ⟨true,equal⟩
    obtain ⟨a,atFirst⟩ := orientedEndpoint first endpoints.1
    obtain ⟨b,atSecond⟩ := orientedEndpoint second endpoints.2
    have sameStart : (first.oriented a).start=(second.oriented b).start :=
      realCell_injective (atFirst.symm.trans atSecond)
    have orientedNonconstant (segment : GridSegment) (h : segment.start≠segment.finish) (backwards : Bool) :
        (segment.oriented backwards).start≠(segment.oriented backwards).finish := by
      cases backwards
      · exact h
      · exact Ne.symm h
    have rays := ray_criterion_of_contacts_at_endpoints sameStart
      (orientedNonconstant first firstNonconstant a) (orientedNonconstant second secondNonconstant b)
      (fun q h k => ((contacts.oriented a b) q h k).1)
    have outputSame := agreement a b sameStart
    have equal := shared_start_perturbations_contact (by omega) spacing
      (oriented_bounds firstBounds a) (oriented_bounds secondBounds b) rays
      (firstPerturbed.oriented a) (secondPerturbed.oriented b) outputSame
      ((oriented_contains _ _ _).mpr firstMember) ((oriented_contains _ _ _).mpr secondMember)
    change p=realCell (firstOutput.oriented a).start at equal
    exact ⟨a,b,sameStart,equal,by simpa only [outputSame] using equal⟩
  · have disjoint : ∀ q : ℝ × ℝ, first.RealContains q → ¬second.RealContains q := by
      intro q h k
      exact oldMeet ⟨q,h,k⟩
    exact (perturbations_disjoint boundPositive (by omega) firstBounds secondBounds disjoint
      firstPerturbed secondPerturbed p firstMember secondMember).elim

end LeanTrominoes.GridSegment
