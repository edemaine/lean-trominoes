/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedClearanceSeed
import LeanTrominoes.PeriodicExactOneSeedFactors
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics

/-! # Finite prescriptions at the retained unit-free exact-one endpoint -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PeriodicCNF.SignedDecoder
variable {V : Type} [DecidableEq V]

def retainedExactOneSeedRead (source : PeriodicCNF V) (v : V) :
    PeriodicLiteral (RetainedOrderedFixedEightOneInThreeVariable V) :=
  let read := retainedClearanceSeedRead source v
  ⟨Sum.inl (Sum.inl read.atom),read.offset,true⟩

theorem retainedExactOneSeedFactor (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) :
    LogicalFactor source.Satisfies
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source).erase)
      (retainedExactOneSeedRead source) Set.univ := by
  have first := (retainedClearanceSeedFactor source locality width occurrences).logical.compose
    (PeriodicOneInThree.seedFactor (retainedFigureNineClearancePositionedFormula source).erase
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree source width))
    (fun _ _ => Set.mem_univ _)
  have combined := first.compose
    (PeriodicOneInThreeNoUnits.seedFactor
      (PeriodicOneInThree.formula (retainedFigureNineClearancePositionedFormula source).erase))
    (fun _ _ => Set.mem_univ _)
  have same : compose (compose (retainedClearanceSeedRead source) inclusionRead) inclusionRead =
      retainedExactOneSeedRead source := by
    funext v
    simp [compose,inclusionRead,retainedExactOneSeedRead,retainedClearanceSeedRead,Cell.add]
  rw [same] at combined
  exact combined.congrTarget (fun a => by
    rw [retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase])

theorem retainedExactOneSeeded_iff (source : PeriodicCNF V)
    (locality : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (seed : PeriodicCNF.Seed V) :
    source.Seeded seed ↔ Prescribed
      (PeriodicOneInThree.Satisfies
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula source).erase)
      (transportSeed (retainedExactOneSeedRead source) seed) :=
  (retainedExactOneSeedFactor source locality width occurrences).seeded_iff seed
    (fun _ _ => Set.mem_univ _)

theorem retainedExactOneSeedRead_primrec [Primcodable V] (source : PeriodicCNF V) :
    Primrec (retainedExactOneSeedRead source) := by
  have read : Primrec (retainedClearanceSeedRead source) := retainedClearanceSeedRead_primrec source
  have atom := PeriodicThreeCNF.literal_atom_primrec.comp read
  have offset := PeriodicThreeCNF.literal_offset_primrec.comp read
  exact PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.sumInl.comp (Primrec.sumInl.comp atom))
      (Primrec.pair offset (Primrec.const true)))

open Lean Elab Command in
run_cmd do
  let name := ``retainedExactOneSeedFactor
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicOrthocrossing
