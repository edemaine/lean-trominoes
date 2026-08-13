/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeDMVariableConnectorBoundary

/-!
# Assembling one-, two-, and three-occurrence variable cycles

The planar exact-one source has at most three occurrences of each variable.
This file closes one, two, or three common connector boundaries into a
variable cycle.  Every glued pair of red continuation ports becomes a
degree-two element, so its two incident triples must be selected exactly
once.

The resulting cycle has exactly two phases.  Consequently all RGB occurrence
terminals carry one common Boolean signal, independently of which fixed-color
connector kind was needed at each occurrence.
-/

namespace LeanTrominoes
namespace PlanarThreeDM

/-- A degree-two element enforces complementation of its two incident triple
selections. -/
theorem exactlyOne_pair_iff_not
    (first second : Bool) :
    PeriodicOneInThree.ExactlyOne [first, second] ↔
      first = !second := by
  cases first <;> cases second <;> native_decide

/-- A one-occurrence cycle closes its two continuation ports together. -/
def OneVariableCycleRealizable
    (kind : VariableConnectorKind) (signal : Bool) : Prop :=
  ∃ boundary : VariableConnectorBoundary,
    boundary.Realizable kind ∧
      boundary.connector = signal ∧
      PeriodicOneInThree.ExactlyOne
        [boundary.second, boundary.first]

/-- Even a one-occurrence variable cycle realizes both truth values. -/
theorem oneVariableCycleRealizable
    (kind : VariableConnectorKind) (signal : Bool) :
    OneVariableCycleRealizable kind signal := by
  refine ⟨VariableConnectorBoundary.canonical signal,
    variableConnectorBoundary_canonical_realizable kind signal,
    rfl, ?_⟩
  cases signal <;> native_decide

/-- Close two occurrence modules into one variable cycle. -/
def TwoVariableCycleRealizable
    (firstKind secondKind : VariableConnectorKind)
    (firstSignal secondSignal : Bool) : Prop :=
  ∃ first second : VariableConnectorBoundary,
    first.Realizable firstKind ∧
      second.Realizable secondKind ∧
      first.connector = firstSignal ∧
      second.connector = secondSignal ∧
      PeriodicOneInThree.ExactlyOne
        [first.second, second.first] ∧
      PeriodicOneInThree.ExactlyOne
        [second.second, first.first]

/-- A two-occurrence cycle exists exactly when its two occurrence signals
agree. -/
theorem twoVariableCycleRealizable_iff
    (firstKind secondKind : VariableConnectorKind)
    (firstSignal secondSignal : Bool) :
    TwoVariableCycleRealizable
        firstKind secondKind firstSignal secondSignal ↔
      firstSignal = secondSignal := by
  constructor
  · rintro ⟨first, second, firstRealizable, secondRealizable,
      firstSignalEq, secondSignalEq, firstLink, _secondLink⟩
    have firstRelation :=
      (variableConnectorBoundary_realizable_iff
        firstKind first).mp firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizable_iff
        secondKind second).mp secondRealizable
    have link := (exactlyOne_pair_iff_not _ _).mp firstLink
    calc
      firstSignal = first.connector := firstSignalEq.symm
      _ = first.first := firstRelation.2
      _ = !first.second := firstRelation.1
      _ = second.first := by rw [link]; simp
      _ = second.connector := secondRelation.2.symm
      _ = secondSignal := secondSignalEq
  · intro equal
    subst secondSignal
    let boundary := VariableConnectorBoundary.canonical firstSignal
    refine ⟨boundary, boundary,
      variableConnectorBoundary_canonical_realizable
        firstKind firstSignal,
      variableConnectorBoundary_canonical_realizable
        secondKind firstSignal,
      rfl, rfl, ?_, ?_⟩
    · cases firstSignal <;> native_decide
    · cases firstSignal <;> native_decide

/-- Close three occurrence modules into one variable cycle. -/
def ThreeVariableCycleRealizable
    (firstKind secondKind thirdKind : VariableConnectorKind)
    (firstSignal secondSignal thirdSignal : Bool) : Prop :=
  ∃ first second third : VariableConnectorBoundary,
    first.Realizable firstKind ∧
      second.Realizable secondKind ∧
      third.Realizable thirdKind ∧
      first.connector = firstSignal ∧
      second.connector = secondSignal ∧
      third.connector = thirdSignal ∧
      PeriodicOneInThree.ExactlyOne
        [first.second, second.first] ∧
      PeriodicOneInThree.ExactlyOne
        [second.second, third.first] ∧
      PeriodicOneInThree.ExactlyOne
        [third.second, first.first]

/-- A three-occurrence cycle exists exactly when all three occurrence
signals agree. -/
theorem threeVariableCycleRealizable_iff
    (firstKind secondKind thirdKind : VariableConnectorKind)
    (firstSignal secondSignal thirdSignal : Bool) :
    ThreeVariableCycleRealizable
        firstKind secondKind thirdKind
        firstSignal secondSignal thirdSignal ↔
      firstSignal = secondSignal ∧ secondSignal = thirdSignal := by
  constructor
  · rintro ⟨first, second, third,
      firstRealizable, secondRealizable, thirdRealizable,
      firstSignalEq, secondSignalEq, thirdSignalEq,
      firstLink, secondLink, _thirdLink⟩
    have firstRelation :=
      (variableConnectorBoundary_realizable_iff
        firstKind first).mp firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizable_iff
        secondKind second).mp secondRealizable
    have thirdRelation :=
      (variableConnectorBoundary_realizable_iff
        thirdKind third).mp thirdRealizable
    have firstLinkRelation :=
      (exactlyOne_pair_iff_not _ _).mp firstLink
    have secondLinkRelation :=
      (exactlyOne_pair_iff_not _ _).mp secondLink
    constructor
    · calc
        firstSignal = first.connector := firstSignalEq.symm
        _ = first.first := firstRelation.2
        _ = !first.second := firstRelation.1
        _ = second.first := by rw [firstLinkRelation]; simp
        _ = second.connector := secondRelation.2.symm
        _ = secondSignal := secondSignalEq
    · calc
        secondSignal = second.connector := secondSignalEq.symm
        _ = second.first := secondRelation.2
        _ = !second.second := secondRelation.1
        _ = third.first := by rw [secondLinkRelation]; simp
        _ = third.connector := thirdRelation.2.symm
        _ = thirdSignal := thirdSignalEq
  · rintro ⟨firstSecond, secondThird⟩
    subst secondSignal
    subst thirdSignal
    let boundary := VariableConnectorBoundary.canonical firstSignal
    refine ⟨boundary, boundary, boundary,
      variableConnectorBoundary_canonical_realizable
        firstKind firstSignal,
      variableConnectorBoundary_canonical_realizable
        secondKind firstSignal,
      variableConnectorBoundary_canonical_realizable
        thirdKind firstSignal,
      rfl, rfl, rfl, ?_, ?_, ?_⟩
    · cases firstSignal <;> native_decide
    · cases firstSignal <;> native_decide
    · cases firstSignal <;> native_decide

/-! ## Signed occurrence cycles -/

/-- A one-occurrence signed variable cycle. -/
def OneSignedVariableCycleRealizable
    (kind : VariableConnectorKind) (polarity signal : Bool) : Prop :=
  ∃ boundary : VariableConnectorBoundary,
    boundary.RealizableFor kind polarity ∧
      boundary.connector = signal ∧
      PeriodicOneInThree.ExactlyOne
        [boundary.second, boundary.first]

/-- A one-occurrence signed cycle realizes either requested literal signal. -/
theorem oneSignedVariableCycleRealizable
    (kind : VariableConnectorKind) (polarity signal : Bool) :
    OneSignedVariableCycleRealizable kind polarity signal := by
  let variableValue := signal == polarity
  refine ⟨VariableConnectorBoundary.canonicalFor
      variableValue polarity,
    variableConnectorBoundary_canonicalFor_realizable
      kind variableValue polarity, ?_, ?_⟩
  · cases signal <;> cases polarity <;> native_decide
  · cases signal <;> cases polarity <;> native_decide

/-- A two-occurrence cycle with independently signed literal ports. -/
def TwoSignedVariableCycleRealizable
    (firstKind secondKind : VariableConnectorKind)
    (firstPolarity secondPolarity : Bool)
    (firstSignal secondSignal : Bool) : Prop :=
  ∃ first second : VariableConnectorBoundary,
    first.RealizableFor firstKind firstPolarity ∧
      second.RealizableFor secondKind secondPolarity ∧
      first.connector = firstSignal ∧
      second.connector = secondSignal ∧
      PeriodicOneInThree.ExactlyOne
        [first.second, second.first] ∧
      PeriodicOneInThree.ExactlyOne
        [second.second, first.first]

/-- Two signed occurrence signals come from one common variable value
precisely when their connector cycle closes. -/
theorem twoSignedVariableCycleRealizable_iff
    (firstKind secondKind : VariableConnectorKind)
    (firstPolarity secondPolarity : Bool)
    (firstSignal secondSignal : Bool) :
    TwoSignedVariableCycleRealizable
        firstKind secondKind firstPolarity secondPolarity
        firstSignal secondSignal ↔
      ∃ variableValue,
        firstSignal =
            variableConnectorLiteralSignal
              variableValue firstPolarity ∧
          secondSignal =
            variableConnectorLiteralSignal
              variableValue secondPolarity := by
  constructor
  · rintro ⟨first, second, firstRealizable, secondRealizable,
      firstSignalEq, secondSignalEq, firstLink, _secondLink⟩
    have firstRelation :=
      (variableConnectorBoundary_realizableFor_iff
        firstKind firstPolarity first).mp firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizableFor_iff
        secondKind secondPolarity second).mp secondRealizable
    have link := (exactlyOne_pair_iff_not _ _).mp firstLink
    have firstEqSecond : first.first = second.first := by
      calc
        first.first = !first.second := firstRelation.1
        _ = second.first := by rw [link]; simp
    refine ⟨first.first, ?_, ?_⟩
    · calc
        firstSignal = first.connector := firstSignalEq.symm
        _ = variableConnectorLiteralSignal
            first.first firstPolarity := firstRelation.2
    · calc
        secondSignal = second.connector := secondSignalEq.symm
        _ = variableConnectorLiteralSignal
            second.first secondPolarity := secondRelation.2
        _ = variableConnectorLiteralSignal
            first.first secondPolarity := by rw [firstEqSecond]
  · rintro ⟨variableValue, firstSignalEq, secondSignalEq⟩
    subst firstSignal
    subst secondSignal
    let first :=
      VariableConnectorBoundary.canonicalFor
        variableValue firstPolarity
    let second :=
      VariableConnectorBoundary.canonicalFor
        variableValue secondPolarity
    refine ⟨first, second,
      variableConnectorBoundary_canonicalFor_realizable
        firstKind variableValue firstPolarity,
      variableConnectorBoundary_canonicalFor_realizable
        secondKind variableValue secondPolarity,
      rfl, rfl, ?_, ?_⟩
    · cases variableValue <;>
        native_decide +revert
    · cases variableValue <;>
        native_decide +revert

/-- A three-occurrence cycle with independently signed literal ports. -/
def ThreeSignedVariableCycleRealizable
    (firstKind secondKind thirdKind : VariableConnectorKind)
    (firstPolarity secondPolarity thirdPolarity : Bool)
    (firstSignal secondSignal thirdSignal : Bool) : Prop :=
  ∃ first second third : VariableConnectorBoundary,
    first.RealizableFor firstKind firstPolarity ∧
      second.RealizableFor secondKind secondPolarity ∧
      third.RealizableFor thirdKind thirdPolarity ∧
      first.connector = firstSignal ∧
      second.connector = secondSignal ∧
      third.connector = thirdSignal ∧
      PeriodicOneInThree.ExactlyOne
        [first.second, second.first] ∧
      PeriodicOneInThree.ExactlyOne
        [second.second, third.first] ∧
      PeriodicOneInThree.ExactlyOne
        [third.second, first.first]

/-- Three signed occurrence signals come from one common variable value
precisely when their connector cycle closes. -/
theorem threeSignedVariableCycleRealizable_iff
    (firstKind secondKind thirdKind : VariableConnectorKind)
    (firstPolarity secondPolarity thirdPolarity : Bool)
    (firstSignal secondSignal thirdSignal : Bool) :
    ThreeSignedVariableCycleRealizable
        firstKind secondKind thirdKind
        firstPolarity secondPolarity thirdPolarity
        firstSignal secondSignal thirdSignal ↔
      ∃ variableValue,
        firstSignal =
            variableConnectorLiteralSignal
              variableValue firstPolarity ∧
          secondSignal =
            variableConnectorLiteralSignal
              variableValue secondPolarity ∧
          thirdSignal =
            variableConnectorLiteralSignal
              variableValue thirdPolarity := by
  constructor
  · rintro ⟨first, second, third,
      firstRealizable, secondRealizable, thirdRealizable,
      firstSignalEq, secondSignalEq, thirdSignalEq,
      firstLink, secondLink, _thirdLink⟩
    have firstRelation :=
      (variableConnectorBoundary_realizableFor_iff
        firstKind firstPolarity first).mp firstRealizable
    have secondRelation :=
      (variableConnectorBoundary_realizableFor_iff
        secondKind secondPolarity second).mp secondRealizable
    have thirdRelation :=
      (variableConnectorBoundary_realizableFor_iff
        thirdKind thirdPolarity third).mp thirdRealizable
    have firstLinkRelation :=
      (exactlyOne_pair_iff_not _ _).mp firstLink
    have secondLinkRelation :=
      (exactlyOne_pair_iff_not _ _).mp secondLink
    have firstEqSecond : first.first = second.first := by
      calc
        first.first = !first.second := firstRelation.1
        _ = second.first := by rw [firstLinkRelation]; simp
    have secondEqThird : second.first = third.first := by
      calc
        second.first = !second.second := secondRelation.1
        _ = third.first := by rw [secondLinkRelation]; simp
    refine ⟨first.first, ?_, ?_, ?_⟩
    · calc
        firstSignal = first.connector := firstSignalEq.symm
        _ = variableConnectorLiteralSignal
            first.first firstPolarity := firstRelation.2
    · calc
        secondSignal = second.connector := secondSignalEq.symm
        _ = variableConnectorLiteralSignal
            second.first secondPolarity := secondRelation.2
        _ = variableConnectorLiteralSignal
            first.first secondPolarity := by rw [firstEqSecond]
    · calc
        thirdSignal = third.connector := thirdSignalEq.symm
        _ = variableConnectorLiteralSignal
            third.first thirdPolarity := thirdRelation.2
        _ = variableConnectorLiteralSignal
            first.first thirdPolarity := by
              rw [← secondEqThird, firstEqSecond]
  · rintro ⟨variableValue, firstSignalEq,
      secondSignalEq, thirdSignalEq⟩
    subst firstSignal
    subst secondSignal
    subst thirdSignal
    let first :=
      VariableConnectorBoundary.canonicalFor
        variableValue firstPolarity
    let second :=
      VariableConnectorBoundary.canonicalFor
        variableValue secondPolarity
    let third :=
      VariableConnectorBoundary.canonicalFor
        variableValue thirdPolarity
    refine ⟨first, second, third,
      variableConnectorBoundary_canonicalFor_realizable
        firstKind variableValue firstPolarity,
      variableConnectorBoundary_canonicalFor_realizable
        secondKind variableValue secondPolarity,
      variableConnectorBoundary_canonicalFor_realizable
        thirdKind variableValue thirdPolarity,
      rfl, rfl, rfl, ?_, ?_, ?_⟩
    · cases variableValue <;>
        native_decide +revert
    · cases variableValue <;>
        native_decide +revert
    · cases variableValue <;>
        native_decide +revert

end PlanarThreeDM
end LeanTrominoes
