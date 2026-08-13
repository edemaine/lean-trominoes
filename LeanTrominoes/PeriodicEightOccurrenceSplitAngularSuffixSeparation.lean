/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OccurrenceSplitAngularFanSpokeSeparation
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes

/-!
# Separation of positioned angular occurrence suffixes

The fixed-eight construction refines every source-grid coordinate by
factor `36`, while each local Figure 7 spoke stays inside a `24 × 24`
macrocell.  Consequently two distinct canonical source occurrence centers
always yield strictly separated spoke macrocells.  This module connects
that arithmetic fact to the clause-indexed angular suffix interface and
preserves it through the final uniform routing refinement.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The occurrence origin used by a clause-indexed suffix is the
factor-36 refinement of its canonical source occurrence center, shifted to
the lower corner of the local Figure 7 macrocell. -/
theorem angularFanOccurrenceOrigin_incidenceRelativeOffset
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    angularFanOccurrenceOrigin sourcePlacement literal.atom
        (incidenceRelativeOffset clause literal) =
      Cell.sub
        (Cell.scale refinementScale
          (PositionedPeriodicCNF.canonicalLiteralPosition
            sourcePlacement clause literal))
        (12, 12) := by
  rcases sourcePlacement.position literal.atom with
    ⟨positionX, positionY⟩
  rcases literal.offset with ⟨offsetX, offsetY⟩
  rcases PeriodicCNF.clauseAnchor clause.literals with
    ⟨anchorX, anchorY⟩
  simp [angularFanOccurrenceOrigin, macroOrigin, placement,
    PeriodicVariablePlacement.translation,
    PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset, refinementScale,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- Distinct integer source centers become Figure 7 macrocells separated
by a strict coordinate gap after the factor-36 refinement. -/
theorem angularFanMacrocellRectanglesSeparated_of_centers_ne
    (firstCenter secondCenter : Cell)
    (centersDifferent : firstCenter ≠ secondCenter) :
    ClosedGridRectanglesSeparated
      (Cell.sub
        (Cell.scale refinementScale firstCenter) (12, 12))
      (Cell.add
        (Cell.sub
          (Cell.scale refinementScale firstCenter) (12, 12))
        (24, 24))
      (Cell.sub
        (Cell.scale refinementScale secondCenter) (12, 12))
      (Cell.add
        (Cell.sub
          (Cell.scale refinementScale secondCenter) (12, 12))
        (24, 24)) := by
  rcases firstCenter with ⟨firstX, firstY⟩
  rcases secondCenter with ⟨secondX, secondY⟩
  have coordinateDifferent :
      firstX ≠ secondX ∨ firstY ≠ secondY := by
    by_cases horizontalDifferent : firstX ≠ secondX
    · exact Or.inl horizontalDifferent
    · apply Or.inr
      intro verticalEqual
      apply centersDifferent
      exact Prod.ext
        (not_ne_iff.mp horizontalDifferent)
        verticalEqual
  simp only [ClosedGridRectanglesSeparated, refinementScale,
    Cell.scale, Cell.sub, Cell.add]
  rcases coordinateDifferent with
      horizontalDifferent | verticalDifferent <;>
    omega

/-- Angular occurrence suffixes at distinct canonical source centers are
contact-free. -/
theorem angularOccurrenceSuffix_strictlyAvoid_of_centers_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (firstClause secondClause :
      PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement firstClause firstLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement secondClause secondLiteral) :
    RoutesStrictlyAvoidEachOther
      (angularOccurrenceSuffix sourcePlacement order
        firstClause firstLiteral
        firstClauseIndex firstLiteralIndex)
      (angularOccurrenceSuffix sourcePlacement order
        secondClause secondLiteral
        secondClauseIndex secondLiteralIndex) := by
  unfold angularOccurrenceSuffix
  apply
    angularFanSpokeRoutesAt_strictlyAvoid_of_originsSeparated
  rw [angularFanOccurrenceOrigin_incidenceRelativeOffset,
    angularFanOccurrenceOrigin_incidenceRelativeOffset]
  exact
    angularFanMacrocellRectanglesSeparated_of_centers_ne
      _ _ centersDifferent

/-- Positive uniform refinement preserves the contact-free separation of
angular occurrence suffixes at distinct canonical centers. -/
theorem scaledAngularOccurrenceSuffix_strictlyAvoid_of_centers_ne
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (firstClause secondClause :
      PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (factor : Int)
    (factorPositive : 0 < factor)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement firstClause firstLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement secondClause secondLiteral) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline factor
        (angularOccurrenceSuffix sourcePlacement order
          firstClause firstLiteral
          firstClauseIndex firstLiteralIndex))
      (scalePolyline factor
        (angularOccurrenceSuffix sourcePlacement order
          secondClause secondLiteral
          secondClauseIndex secondLiteralIndex)) :=
  (angularOccurrenceSuffix_strictlyAvoid_of_centers_ne
    sourcePlacement order
    firstClause secondClause
    firstLiteral secondLiteral
    firstClauseIndex firstLiteralIndex
    secondClauseIndex secondLiteralIndex
    centersDifferent).scalePolyline factorPositive

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
