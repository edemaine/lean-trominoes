/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedExactOneSeed
import LeanTrominoes.SAT.ExactOne.PeriodicExactOneSeedGauge
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRibbonThreeDMComputability

/-! # Prescriptions at the final gauged planar exact-one endpoint -/
noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def retainedFinalExactOneSeedRead (source : PeriodicCNF V) :
    Read V (RetainedOrderedFixedEightOneInThreeVariable V) :=
  compose (retainedExactOneSeedRead source)
    (gaugeRead (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source))

theorem retainedFinalExactOneSeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) :
    LogicalFactor source.Satisfies
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase)
      (retainedFinalExactOneSeedRead source) Set.univ := by
  have ordered := (retainedExactOneSeedFactor source locality width occurrences).congrTarget
    (fun a =>
      (PositionedPeriodicCNF.orderClausesByRouteDirection_oneInThreeSatisfies_iff
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
          source locality width occurrences nonempty) a).symm)
  have gauged := ordered.compose
    (exactOneGaugeFactor
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source locality width occurrences nonempty).erase
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source))
    (fun _ _ => Set.mem_univ _)
  exact gauged.congrTarget (fun a => by
    rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      source locality width occurrences nonempty,
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
      PositionedPeriodicCNF.erase_variableGauge])

theorem retainedFinalExactOneSeeded_iff (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3)
    (nonempty : ∀ clause ∈ source.clauses, clause ≠ []) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ Prescribed
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed source).erase)
      (transportSeed (retainedFinalExactOneSeedRead source) seed) :=
  (retainedFinalExactOneSeedFactor source locality width occurrences nonempty).seeded_iff
    seed (fun _ _ => Set.mem_univ _)

attribute [local irreducible]
  retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge

theorem retainedFinalExactOneSeedRead_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (retainedFinalExactOneSeedRead source) :=
  compose_primrec (retainedExactOneSeedRead_primrec source)
    (gaugeRead_primrec
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_primrec.comp
        (Primrec.pair (Primrec.const source) Primrec.id)))

end LeanTrominoes.PeriodicOrthocrossing
