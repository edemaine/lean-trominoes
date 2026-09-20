/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarExactOneEndpoint
import LeanTrominoes.PeriodicPlanarThreeOccurrenceOffsetBounds

/-! # Manhattan locality after the final exact-one coordinate gauge -/
namespace LeanTrominoes.PeriodicOrthocrossing
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 2048
local instance localityRawTargetDecidableEq {V : Type*} [DecidableEq V] :
    DecidableEq (RetainedOrderedFixedEightOneInThreeVariable V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem retainedFinalGauge_inherited_eq_zero {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) (atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable V))
    (member : atom ∈ (retainedFigureNineClearancePositionedFormula source).erase.variableOccurrences) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source (.inl (.inl atom)) = (0,0) := by
  let raw := retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement source
  have inside := retainedFigureNineClearancePlacement_position_inSquare_of_mem source atom member
  have position : raw.position (.inl (.inl atom)) =
      Cell.scale 72 ((retainedFigureNineClearancePlacement source).position atom) := by
    apply Prod.ext <;>
      simp [raw,retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
        PlanarOneInThreeNoUnitsFigureNine.composedPlacement,PeriodicOneInThreeNoUnitsPositioned.placement,
        PeriodicOneInThreePositioned.placement,PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
        PlanarOneInThree.gadgetScale,Cell.scale] <;> ring
  have period : raw.period = 72*(retainedFigureNineClearancePlacement source).period := by
    simp [raw,retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale]
    omega
  change raw.canonicalPositionGauge (.inl (.inl atom)) = (0,0)
  apply Prod.ext
  · change (raw.position (.inl (.inl atom))).1 / (raw.period : Int) = 0
    apply Int.ediv_eq_zero_of_lt
    · rw [position]; dsimp [Cell.scale]; omega
    · rw [position,period]; norm_num [Cell.scale]; exact inside.2.1
  · change (raw.position (.inl (.inl atom))).2 / (raw.period : Int) = 0
    apply Int.ediv_eq_zero_of_lt
    · rw [position]; dsimp [Cell.scale]; omega
    · rw [position,period]; norm_num [Cell.scale]; exact inside.2.2.2

variable {V : Type*} [DecidableEq V] (source : PeriodicCNF V)
    (hl : source.IsLocal) (hw : source.WidthAtMost 3) (ho : source.OccurrencesAtMost 3)
    (hn : ∀ c ∈ source.clauses, c ≠ [])

include hl hw ho hn

theorem retainedFinalGauge_literal_reset
    {clause : PositionedPeriodicClause (RetainedOrderedFixedEightOneInThreeVariable V)} {index : Nat}
    (member : (clause,index) ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source).clauses.zipIdx)
    {literal : PeriodicLiteral (RetainedOrderedFixedEightOneInThreeVariable V)} {literalIndex : Nat}
    (literalMember : (literal,literalIndex) ∈ clause.literals.zipIdx) :
    (literal.variableGauge (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source)).offset = literal.offset ∨
    (literal.variableGauge (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source)).offset = (0,0) := by
  have localReset (notInherited : ∀ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable V),
      literal.atom ≠ .inl (.inl atom)) :
      (literal.variableGauge (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source)).offset = (0,0) := by
    have inside := retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
      source hl hw ho hn member literalMember notInherited
    rw [retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge,
      PeriodicVariablePlacement.gauged_literal_offset _
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement_period_pos source)]
    apply Prod.ext
    · exact Int.ediv_eq_zero_of_lt (le_of_lt inside.1) inside.2.1
    · exact Int.ediv_eq_zero_of_lt (le_of_lt inside.2.2.1) inside.2.2.2
  obtain ⟨base,address,sourceData,_,_⟩ := composedLiteralVariable_inMacrocellOrbit
    (retainedFigureNineClearancePositionedFormula source) (retainedFigureNineClearancePlacement source)
    (by simpa only [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula] using member)
    literalMember
  generalize atomEq : literal.atom = atom at sourceData
  cases sourceData with
  | inherited original originalMember =>
      left
      simp only [PeriodicLiteral.variableGauge_offset,atomEq,
        retainedFinalGauge_inherited_eq_zero source original originalMember,Cell.add]
      simp
  | figureNineAuxiliary =>
      right; apply localReset
      intro original eq
      rw [eq] at atomEq
      simp at atomEq
  | unitEliminationAuxiliary =>
      right; apply localReset
      intro original eq
      rw [eq] at atomEq
      simp at atomEq

theorem retainedFinalGaugedFormula_isLocal :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula source hl hw ho hn).erase.IsLocal := by
  have wf := PeriodicCNF.incidenceGraph_isWellFormed source
  have degree := PeriodicCNF.incidenceGraph_degreeAtMost hw ho
  have graphLocal := PeriodicCNF.incidenceGraph_isLocal hl
  have rawLocal :
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source).erase.IsLocal := by
    rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
    exact PeriodicOneInThreeNoUnits.formula_isLocal (PeriodicOneInThree.formula_isLocal
      (retainedFigureNineClearancePositionedFormula_isLocal wf degree graphLocal))
  have rawBounds :
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source).erase.HasUnitOffsets := by
    rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
    exact PeriodicOneInThreeNoUnits.formula_hasUnitOffsets (PeriodicOneInThree.formula_hasUnitOffsets
      (retainedFigureNineClearancePositionedFormula_hasUnitOffsets wf degree graphLocal))
  rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_variableGauge_isLocal
  apply PositionedPeriodicCNF.variableGauge_isLocal_of_reset _ _ rawLocal rawBounds
  intro clause index member literal literalIndex literalMember
  exact retainedFinalGauge_literal_reset source hl hw ho hn member literalMember

end LeanTrominoes.PeriodicOrthocrossing
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000
variable {V : Type} [Primcodable V] [DecidableEq V]
local instance localityTargetDecidableEq : DecidableEq (Target V) := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
open PeriodicOrthocrossing

omit [Primcodable V] in
theorem isLocal (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ c ∈ f.clauses, c ≠ []) : (input f).1.IsLocal := by
  change (positioned f).erase.IsLocal
  rw [positioned,retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq f hl hw ho hn]
  exact retainedFinalGaugedFormula_isLocal f hl hw ho hn

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
