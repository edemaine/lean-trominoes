/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBoundaryArcSeparation
import LeanTrominoes.FiniteNestedIntervalDepths

/-! # Bounded depths for noninterlacing rectangle boundary chords -/
namespace LeanTrominoes.OrthogonalBoundaryRouting

abbrev Chord := Port × Port

def chordCode (chord : Chord) : (Nat ×ₗ Int) × (Nat ×ₗ Int) :=
  (chord.1.clockwiseCode,chord.2.clockwiseCode)

theorem chordCode_injective : Function.Injective chordCode := by
  intro first second equal
  exact Prod.ext (Port.clockwiseCode_injective (congrArg Prod.fst equal))
    (Port.clockwiseCode_injective (congrArg Prod.snd equal))

def chordIntervals (chords : Finset Chord) : Finset ((Nat ×ₗ Int) × (Nat ×ₗ Int)) :=
  chords.image chordCode

def matchingDepth (chords : Finset Chord) (chord : Chord) : Nat :=
  distinctNestingDepth (chordIntervals chords) (chordCode chord)

theorem matchingDepth_positive (chords : Finset Chord) (chord : Chord) :
    0 < matchingDepth chords chord := distinctNestingDepth_positive _ _

theorem matchingDepth_le_card {chords : Finset Chord} {chord : Chord} (member : chord ∈ chords) :
    matchingDepth chords chord ≤ chords.card :=
  (distinctNestingDepth_le_card (Finset.mem_image.mpr ⟨chord,member,rfl⟩)).trans Finset.card_image_le

theorem matchingDepth_injective (chords : Finset Chord) : Set.InjOn (matchingDepth chords) chords := by
  intro first fm second sm equal
  apply chordCode_injective
  exact distinctNestingDepth_injective (chordIntervals chords)
    (Finset.mem_image.mpr ⟨first,fm,rfl⟩) (Finset.mem_image.mpr ⟨second,sm,rfl⟩) equal

theorem matchingDepth_strict {chords : Finset Chord} {outer inner : Chord}
    (outerMember : outer ∈ chords) (innerMember : inner ∈ chords)
    (firstOrder : outer.1.Before inner.1) (lastOrder : inner.2.Before outer.2) :
    matchingDepth chords inner < matchingDepth chords outer :=
  distinctNestingDepth_strict (Finset.mem_image.mpr ⟨outer,outerMember,rfl⟩)
    (Finset.mem_image.mpr ⟨inner,innerMember,rfl⟩)
    ((Port.before_iff_code_lt _ _).mp firstOrder) ((Port.before_iff_code_lt _ _).mp lastOrder)

def Noninterlacing (first second : Chord) : Prop :=
  first.2.Before second.1 ∨ second.2.Before first.1 ∨
    (first.1.Before second.1 ∧ second.2.Before first.2) ∨
    (second.1.Before first.1 ∧ first.2.Before second.2)

theorem Noninterlacing.symm {first second : Chord} (noninterlacing : Noninterlacing first second) :
    Noninterlacing second first := by
  unfold Noninterlacing at noninterlacing ⊢
  tauto

theorem noninterlacing_endpoints_ne {first second : Chord}
    (firstOrder : first.1.Before first.2) (secondOrder : second.1.Before second.2)
    (noninterlacing : Noninterlacing first second) :
    first.1 ≠ second.1 ∧ first.1 ≠ second.2 ∧ first.2 ≠ second.1 ∧ first.2 ≠ second.2 := by
  have firstCodeOrder := (Port.before_iff_code_lt _ _).mp firstOrder
  have secondCodeOrder := (Port.before_iff_code_lt _ _).mp secondOrder
  unfold Noninterlacing at noninterlacing
  simp only [Port.before_iff_code_lt] at noninterlacing
  rcases noninterlacing with before | before | ⟨left,right⟩ | ⟨left,right⟩
  all_goals
    refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro equal
    have codeEq := congrArg Port.clockwiseCode equal
    order

theorem deeper_endpoints_outside {chords : Finset Chord} {first second : Chord}
    (firstMember : first ∈ chords) (secondMember : second ∈ chords)
    (firstOrder : first.1.Before first.2) (secondOrder : second.1.Before second.2)
    (noninterlacing : Noninterlacing first second) (depthOrder : matchingDepth chords first < matchingDepth chords second) :
    ¬first.1.Between first.2 second.1 ∧ ¬first.1.Between first.2 second.2 := by
  rcases noninterlacing with before | before | nested | nested
  · simp only [Port.between_iff_code_le]
    have beforeCode := (Port.before_iff_code_lt _ _).mp before
    have secondCodeOrder := (Port.before_iff_code_lt _ _).mp secondOrder
    constructor <;> rintro ⟨lo,hi⟩ <;> order
  · simp only [Port.between_iff_code_le]
    have beforeCode := (Port.before_iff_code_lt _ _).mp before
    have secondCodeOrder := (Port.before_iff_code_lt _ _).mp secondOrder
    constructor <;> rintro ⟨lo,hi⟩ <;> order
  · have opposite := matchingDepth_strict firstMember secondMember nested.1 nested.2
    omega
  · simp only [Port.between_iff_code_le]
    have leftCode := (Port.before_iff_code_lt _ _).mp nested.1
    have rightCode := (Port.before_iff_code_lt _ _).mp nested.2
    constructor <;> rintro ⟨lo,hi⟩ <;> order

def matchingRoute (chords : Finset Chord) (width height : Int) (chord : Chord) : List Cell :=
  route width height (matchingDepth chords chord) chord.1 chord.2

end LeanTrominoes.OrthogonalBoundaryRouting
