/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationContinuousPlanarPresentation
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeRouteOrders

/-!
# Logical promises of the routed polarity normalization

The routed construction has the same erased formula as logical polarity
normalization, up to clause-anchor normalization and a variable gauge.  This
module collects the structural promises required at the planar 3DM boundary.
-/

namespace LeanTrominoes

namespace PeriodicOneInThreePolarityNormalization

/-- A variable gauge changes offsets but preserves the value pattern of every
clause, hence preserves polarity normalization. -/
theorem FormulaPolarityNormalized.variableGauge
    {Variable : Type*}
    {source : PeriodicCNF Variable}
    (normalized : FormulaPolarityNormalized source)
    (gauge : Variable → Cell) :
    FormulaPolarityNormalized (source.variableGauge gauge) := by
  intro gaugedClause gaugedClauseMember
  rcases List.mem_map.mp gaugedClauseMember with
    ⟨sourceClause, sourceClauseMember, rfl⟩
  have sourceNormalized := normalized sourceClause sourceClauseMember
  unfold ClausePolarityNormalized at sourceNormalized ⊢
  simpa [PeriodicClause.variableGauge, List.map_map,
    Function.comp_def] using
      sourceNormalized

end PeriodicOneInThreePolarityNormalization

namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The routed polarity-normalized formula obeys the requested terminal
polarity convention after its final variable gauge. -/
theorem formula_polarityNormalized
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) :
    PeriodicOneInThreePolarityNormalization.FormulaPolarityNormalized
      (formula source sourcePlacement routes).erase := by
  rw [erase_formula]
  exact
    (PeriodicOneInThreePolarityNormalization.formula_polarityNormalized
      (refinedSource source sourcePlacement).erase).variableGauge freshGauge

/-- The routed construction preserves the binary-or-ternary clause promise. -/
theorem formula_arityTwoOrThree
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (formula source sourcePlacement routes).erase := by
  have refinedArity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree
        (refinedSource source sourcePlacement).erase := by
    simpa [refinedSource] using
      source.erase.anchorNormalize_arityTwoOrThree arity
  rw [erase_formula]
  exact
    (PeriodicOneInThreePolarityNormalization.formula_arityTwoOrThree
      refinedArity).variableGauge freshGauge

/-- In particular, every routed normalized clause has width at most three. -/
theorem formula_widthAtMostThree
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase) :
    (formula source sourcePlacement routes).erase.WidthAtMost 3 := by
  have normalizedArity :=
    formula_arityTwoOrThree source sourcePlacement routes arity
  intro clause clauseMember
  rcases normalizedArity clause clauseMember with clauseArity | clauseArity <;>
    simp [PeriodicClause.WidthAtMost, clauseArity]

/-- The routed construction preserves the occurrence-three promise. -/
theorem formula_occurrencesAtMostThree
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (occurrences : source.erase.OccurrencesAtMost 3) :
    (formula source sourcePlacement routes).erase.OccurrencesAtMost 3 := by
  have refinedOccurrences :
      (refinedSource source sourcePlacement).erase.OccurrencesAtMost 3 := by
    simpa [refinedSource] using
      source.erase.anchorNormalize_occurrencesAtMost 3 occurrences
  rw [erase_formula]
  exact
    (PeriodicOneInThreePolarityNormalization.formula_occurrencesAtMostThree
      (refinedSource source sourcePlacement).erase
      refinedOccurrences).variableGauge freshGauge

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
