/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedGaugedSeed
import LeanTrominoes.SAT.Planar.OccurrenceSplit.PeriodicEightOccurrenceSplitSeed
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance

/-! # Prescribed values at the Figure 9 clearance source -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

attribute [local irreducible] retainedDrawingWrappedPeriodicPlanarSATVariableGauge

def retainedClearanceSeedRead (source : PeriodicCNF V) (v : V) :
    PeriodicLiteral (ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable V)) :=
  let atom : WrappedPeriodicPlanarSATVariable V := ⟨.atom v⟩
  ⟨(atom,8,0),retainedDrawingWrappedPeriodicPlanarSATVariableGauge source atom,true⟩

private theorem clearance_satisfies_iff (source : PeriodicCNF V)
    (a : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable V) → Cell → Bool) :
    (retainedDrawingEightOccurrenceSplitFormula source).Satisfies a ↔
      (retainedFigureNineClearancePositionedFormula source).erase.Satisfies a := by
  rw [retainedFigureNineClearancePositionedFormula,PositionedPeriodicCNF.erase_scale,
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula,
    PositionedPeriodicCNF.orderClausesByRouteDirection_satisfies_iff,
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]

theorem retainedClearanceSeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) :
    Factor source (retainedFigureNineClearancePositionedFormula source).erase
      (retainedClearanceSeedRead source) Set.univ := by
  have combined := (retainedGaugedSeedFactor source locality width occurrences).compose
    (PeriodicEightOccurrenceSplit.seedFactor (retainedPlanarSATFormula source)
      (retainedDrawingAngularOccurrencePorts source))
    (fun _ _ => Set.mem_univ _)
  have same : compose (retainedGaugedSeedRead source) PeriodicEightOccurrenceSplit.seedRead =
      retainedClearanceSeedRead source := by
    funext v
    simp [compose,retainedGaugedSeedRead,PeriodicEightOccurrenceSplit.seedRead,
      retainedClearanceSeedRead,Cell.add]
  rw [same] at combined
  exact combined.congrTarget (clearance_satisfies_iff source)

theorem retainedClearanceSeedRead_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (retainedClearanceSeedRead source) := by
  have atom : Primrec (fun v : V => (⟨PeriodicPlanarSATVariable.atom v⟩ : WrappedPeriodicPlanarSATVariable V)) :=
    WrappedPeriodicVariable.mk_primrec.comp PeriodicPlanarSATVariable.atom_primrec
  have gauge : Primrec (fun v : V =>
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge source ⟨.atom v⟩) :=
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge_primrec.comp
      (Primrec.pair (Primrec.const source) atom)
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.pair atom (Primrec.const (8,0)))
      (Primrec.pair gauge (Primrec.const true)))

end LeanTrominoes.PeriodicOrthocrossing
