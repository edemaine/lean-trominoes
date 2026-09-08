/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnitRouteEndpointDisplacement
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily

/-! # Recover retained clause origins through their first-literal routes -/

namespace LeanTrominoes.PeriodicOrthocrossing
open DelimitedDirectionDisplacement PeriodicEightOccurrenceSplit PeriodicThreeSATThree Gadget

private theorem canonicalLiteralPosition_first {Atom : Type}
    (placement : PeriodicVariablePlacement Atom) (clause : PositionedPeriodicClause Atom)
    (literal : PeriodicLiteral Atom) (first : clause.literals.head? = some literal) :
    PositionedPeriodicCNF.canonicalLiteralPosition placement clause literal = placement.position literal.atom := by
  simp only [PositionedPeriodicCNF.canonicalLiteralPosition, PeriodicCNF.clauseAnchor,
    first, Option.map_some, Option.getD_some]
  rcases literal with ⟨atom, ⟨x, y⟩, value⟩
  simp [PeriodicVariablePlacement.translation, Cell.sub, Cell.scale, Cell.add]

/-- The first literal has zero offset relative to its clause's incidence
anchor. Its known ring-copy coordinate and compiled direction displacement
therefore recover the canonical clause origin without a period correction. -/
theorem retainedSplitClauseOrigin_eq_directionRecovery
    {Atom : Type} [DecidableEq Atom] (source : PeriodicCNF Atom)
    (sourceLocal : source.IsLocal) (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (horizontal : Bool)
    (clause : PositionedPeriodicClause (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Atom)))
    (clauseIndex : Nat)
    (clauseMember : (clause, clauseIndex) ∈
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses.zipIdx)
    (literal : PeriodicLiteral (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Atom)))
    (firstLiteral : clause.literals.head? = some literal) :
    component horizontal (PositionedPeriodicCNF.canonicalClausePosition
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source) clause) =
      component horizontal ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source).position literal.atom) -
        component horizontal (AxisDirection.polylineFirstDirection
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source clauseIndex 0)).step -
        displacement horizontal (unitSubdivisionDirections
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source clauseIndex 0).tail) := by
  have literalMember : (literal, 0) ∈ clause.literals.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa only [List.head?_eq_getElem?] using firstLiteral)
  have valid := retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty clauseMember literalMember
  have unitSteps := retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_unitSteps
    source sourceLocal sourceWidth sourceOccurrences sourceNonempty clauseMember literalMember
  rw [canonicalLiteralPosition_first _ clause literal firstLiteral] at valid
  have recovered := start_component_eq_end_sub_displacement horizontal
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source clauseIndex 0)
    _ _ valid.1 valid.2.1 unitSteps
  rw [displacement_eq_first_add_tail _ _ unitSteps] at recovered
  omega

end LeanTrominoes.PeriodicOrthocrossing
