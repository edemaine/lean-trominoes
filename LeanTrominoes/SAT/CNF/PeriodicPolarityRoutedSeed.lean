/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneSeedFactors
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneSeedGauge
import LeanTrominoes.SAT.ExactOne.PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-! # Original-variable pins survive routed polarity normalization -/
namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
open PeriodicCNF.SignedDecoder
variable {V : Type}

theorem seedFactor (source : PeriodicCNF V) :
    LogicalFactor (PeriodicOneInThree.Satisfies source)
      (PeriodicOneInThree.Satisfies
        ((PeriodicOneInThreePolarityNormalization.formula source.anchorNormalize).variableGauge freshGauge))
      inclusionRead Set.univ := by
  have normalized := (PeriodicOneInThreePolarityNormalization.seedFactor source.anchorNormalize)
  have first : LogicalFactor (PeriodicOneInThree.Satisfies source)
      (PeriodicOneInThree.Satisfies (PeriodicOneInThreePolarityNormalization.formula source.anchorNormalize))
      inclusionRead Set.univ := by
    constructor
    · intro a ha
      exact (PeriodicOneInThree.anchorNormalize_satisfies_iff source _).1 (normalized.sound a ha)
    · intro a ha
      exact normalized.complete a ((PeriodicOneInThree.anchorNormalize_satisfies_iff source a).2 ha)
  have result := first.compose
    (exactOneGaugeFactor (PeriodicOneInThreePolarityNormalization.formula source.anchorNormalize) freshGauge)
    (fun _ _ => Set.mem_univ _)
  have same : compose (inclusionRead (V := V)) (gaugeRead freshGauge) = inclusionRead := by
    funext v
    simp [compose,inclusionRead,gaugeRead,freshGauge,Cell.add]
  rw [same] at result
  exact result

theorem seeded_iff (source : PeriodicCNF V) (seed : PeriodicCNF.Seed V) :
    Prescribed (PeriodicOneInThree.Satisfies source) seed ↔
      Prescribed (PeriodicOneInThree.Satisfies
        ((PeriodicOneInThreePolarityNormalization.formula source.anchorNormalize).variableGauge freshGauge))
        (transportSeed inclusionRead seed) :=
  (seedFactor source).seeded_iff seed (fun _ _ => Set.mem_univ _)

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
