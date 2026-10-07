/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarThreeDMSeedDecoder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEncodingComputability

/-! # Effective finite-pin encoding for planar 3DM -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM PeriodicCNF.SignedDecoder
variable {V : Type} [Primcodable V] [DecidableEq V]

theorem seedTriple_primrec (source : PeriodicCNF V) : Primrec (seedTriple source) := by
  have metadata : Primrec (fun v : V => ((source,v),(.first : OccurrenceSlot))) :=
    Primrec.pair (Primrec.pair (Primrec.const source) Primrec.id) (Primrec.const _)
  have polarity := occurrencePolarity_primrec.comp metadata
  have kind := occurrenceConnectorKind_primrec.comp metadata
  have positive : PrimrecPred (fun v : V => occurrencePolarity source v .first = true) :=
    Primrec.eq.comp polarity (Primrec.const true)
  have red : Primrec (fun v : V => Triple.fixedRed v .first
      (if occurrencePolarity source v .first then .bottomLeft else .topLeft)) :=
    triple_fixedRed_primrec.comp
      (Primrec.pair (Primrec.pair Primrec.id (Primrec.const (.first : OccurrenceSlot)))
        (Primrec.ite positive (Primrec.const FixedRedConnectorTriple.bottomLeft)
          (Primrec.const FixedRedConnectorTriple.topLeft)))
  have ordinary (variant : VariableOccurrenceVariant) : Primrec (fun v : V =>
      Triple.ordinary v .first variant
        (if occurrencePolarity source v .first then .first else .second)) :=
    triple_ordinary_primrec.comp
      (Primrec.pair (Primrec.pair (Primrec.pair Primrec.id (Primrec.const (.first : OccurrenceSlot)))
        (Primrec.const variant))
        (Primrec.ite positive (Primrec.const VariableOccurrenceTriple.first)
          (Primrec.const VariableOccurrenceTriple.second)))
  exact (Primrec.ite (Primrec.eq.comp kind (Primrec.const VariableConnectorKind.fixedRed)) red
    (Primrec.ite (Primrec.eq.comp kind (Primrec.const VariableConnectorKind.fixedGreen))
      (ordinary .fixedGreen) (ordinary .fixedBlue))).of_eq (fun v => by
        cases h : occurrenceConnectorKind source v .first <;> simp [seedTriple,h])

theorem encodedSeedRead_primrec (source : PeriodicCNF V) : Primrec (encodedSeedRead source) :=
  PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.list_idxOf.comp (seedTriple_primrec source)
      (Primrec.const (problem source).triples)) (Primrec.const ((0,0),true)))

theorem encodedSeedReduction_primrec (source : PeriodicCNF V) :
    Primrec (transportSeed (encodedSeedRead source)) :=
  transportSeed_primrec (encodedSeedRead_primrec source)

open Lean Elab Command in
run_cmd do
  for name in [``encodedSeedFactor,``encodedSeedReduction_primrec] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.PeriodicPlanarOneInThreeToThreeDM
