/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinate
import LeanTrominoes.RetainedAngularTerminalDataScaling

/-! # Scaling retained angular occurrence coordinates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree

/-- Uniformly scale the radial component of a retained terminal coordinate. -/
def scaleRetainedTerminalCoordinate
    (factor : Nat)
    (coordinate : Nat ×ₗ Nat) : Nat ×ₗ Nat :=
  toLex
    ((ofLex coordinate).1,
      factor * (ofLex coordinate).2)

/-- Positive radial scaling preserves strict lexicographic order. -/
theorem scaleRetainedTerminalCoordinate_lt_iff
    {factor : Nat} (factorPositive : 0 < factor)
    (first second : Nat ×ₗ Nat) :
    scaleRetainedTerminalCoordinate factor first <
        scaleRetainedTerminalCoordinate factor second ↔
      first < second := by
  unfold scaleRetainedTerminalCoordinate
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.lt_iff]
  simp only [Nat.mul_lt_mul_left factorPositive]

/-- Positive radial scaling is injective. -/
theorem scaleRetainedTerminalCoordinate_eq_iff
    {factor : Nat} (factorPositive : 0 < factor)
    (first second : Nat ×ₗ Nat) :
    scaleRetainedTerminalCoordinate factor first =
        scaleRetainedTerminalCoordinate factor second ↔
      first = second := by
  constructor
  · intro equal
    unfold scaleRetainedTerminalCoordinate at equal
    have pairEqual := toLex.injective equal
    simp only [Prod.mk.injEq] at pairEqual
    have firstCoordinateEqual :
        (ofLex first).1 = (ofLex second).1 :=
      pairEqual.1
    have scaledSecondCoordinateEqual :
        factor * (ofLex first).2 =
          factor * (ofLex second).2 :=
      pairEqual.2
    have secondCoordinateEqual :
        (ofLex first).2 = (ofLex second).2 :=
      Nat.mul_left_cancel factorPositive
        scaledSecondCoordinateEqual
    exact ofLex.injective
      (Prod.ext firstCoordinateEqual secondCoordinateEqual)
  · intro equal
    subst second
    rfl

/-- A certified retained occurrence coordinate scales only in its radial
component when every route is uniformly scaled. -/
theorem retainedOccurrenceTerminalCoordinate_scaleIncidenceRoutes
    {Variable : Type*}
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (copy : ThreeOccurrenceVariable Variable)
    (retained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes copy)) :
    retainedOccurrenceTerminalCoordinate
        (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
        copy =
      scaleRetainedTerminalCoordinate factor
        (retainedOccurrenceTerminalCoordinate routes copy) := by
  have classifiedSome :
      (retainedTerminalDirectionClassify
        (occurrenceTerminalVector routes copy)).isSome :=
    (retainedTerminalDirectionClassify_isSome_iff _).2 retained
  rcases Option.isSome_iff_exists.mp classifiedSome with
    ⟨terminal, classified⟩
  unfold retainedOccurrenceTerminalCoordinate
  rw [occurrenceTerminalVector_scaleIncidenceRoutes]
  rw [classifiedRetainedTerminalData_scale_of_classified
    factorPositive classified]
  rw [classifiedRetainedTerminalData_eq_of_classified classified]
  rfl

/-- Positive route scaling preserves strict comparison of two certified
retained occurrence coordinates. -/
theorem retainedOccurrenceTerminalCoordinate_lt_scaleIncidenceRoutes_iff
    {Variable : Type*}
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable)
    (firstRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes first))
    (secondRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes second)) :
    retainedOccurrenceTerminalCoordinate
          (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
          first <
        retainedOccurrenceTerminalCoordinate
          (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
          second ↔
      retainedOccurrenceTerminalCoordinate routes first <
        retainedOccurrenceTerminalCoordinate routes second := by
  rw [retainedOccurrenceTerminalCoordinate_scaleIncidenceRoutes
    factorPositive routes first firstRetained]
  rw [retainedOccurrenceTerminalCoordinate_scaleIncidenceRoutes
    factorPositive routes second secondRetained]
  exact
    scaleRetainedTerminalCoordinate_lt_iff
      factorPositive _ _

/-- Positive route scaling preserves equality of two certified retained
occurrence coordinates. -/
theorem retainedOccurrenceTerminalCoordinate_eq_scaleIncidenceRoutes_iff
    {Variable : Type*}
    {factor : Nat} (factorPositive : 0 < factor)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (first second : ThreeOccurrenceVariable Variable)
    (firstRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes first))
    (secondRetained :
      RetainedTerminalRayVector
        (occurrenceTerminalVector routes second)) :
    retainedOccurrenceTerminalCoordinate
          (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
          first =
        retainedOccurrenceTerminalCoordinate
          (PositionedPeriodicCNF.scaleIncidenceRoutes factor routes)
          second ↔
      retainedOccurrenceTerminalCoordinate routes first =
        retainedOccurrenceTerminalCoordinate routes second := by
  rw [retainedOccurrenceTerminalCoordinate_scaleIncidenceRoutes
    factorPositive routes first firstRetained]
  rw [retainedOccurrenceTerminalCoordinate_scaleIncidenceRoutes
    factorPositive routes second secondRetained]
  exact
    scaleRetainedTerminalCoordinate_eq_iff
      factorPositive _ _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
