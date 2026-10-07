/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedNormalizedOrientationSeedCompleteness
import LeanTrominoes.PeriodicCNFSignedDecoderUniformWindow

/-! # The fixed normalized drawing locally decodes the universal Wang constraints -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedWangNormalizedSeedDecoder
open LeanWang PeriodicCNF.SignedDecoder PeriodicOrthocrossing

abbrev SourceVariable := FixedThreeSATThreeSeed.Variable
abbrev FinalVariable := FixedPlanarThreeDMSeed.FinalVariable
abbrev PolarityVariable := FixedPlanarThreeDMSeed.Variable
abbrev TargetVariable := FixedNormalizedOrientationSeed.Variable
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
local instance : BEq FinalVariable := instBEqOfDecidableEq
local instance : LawfulBEq FinalVariable := by infer_instance
local instance : BEq PolarityVariable := instBEqOfDecidableEq
local instance : LawfulBEq PolarityVariable := by infer_instance

def threeRead : Read WangTile SourceVariable :=
  compose PeriodicThreeCNF.seedRead (PeriodicThreeSATThree.seedRead FixedThreeSATThreeSeed.splitFormula)

theorem threeFactor : Factor WangPeriodicCNF.fixedFormula FixedThreeSATThreeSeed.fixedFormula
    threeRead Set.univ :=
  (PeriodicThreeCNF.seedFactor _).compose (PeriodicThreeSATThree.seedFactor _)
    (fun _ _ => Set.mem_univ _)

def matchingRead : Read SourceVariable Nat :=
  compose (retainedPolaritySeedRead FixedThreeSATThreeSeed.fixedFormula)
    (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead FixedPlanarThreeDMSeed.fixedFormula)

theorem matching_sound (a : Nat → Cell → Bool) (valid : FixedPlanarThreeDMSeed.fixedInstance.Satisfies a) :
    FixedThreeSATThreeSeed.fixedFormula.Satisfies (decode matchingRead a) := by
  rw [matchingRead,decode_compose]
  exact (retainedPolaritySeedFactor FixedThreeSATThreeSeed.fixedFormula
    FixedThreeSATThreeSeed.fixedFormula_isLocal FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree
    FixedPlanarThreeDMSeed.source_occurrences FixedThreeSATThreeSeed.fixedFormula_clausesNonempty).sound _
      ((PeriodicPlanarOneInThreeToThreeDM.encodedSeedFactor FixedPlanarThreeDMSeed.fixedFormula
        FixedPlanarThreeDMSeed.fixedFormula_occurrences FixedPlanarThreeDMSeed.fixedFormula_arity).sound a valid)

def orientationRead : Read SourceVariable TargetVariable :=
  compose matchingRead (PeriodicThreeDM.SeedNormalization.boundedRead
    FixedPlanarThreeDMSeed.fixedPresentation.toPlanarPresentation)

theorem orientation_sound (a : TargetVariable → Cell → Bool)
    (valid : FixedNormalizedOrientationSeed.fixedFormula.Satisfies a) :
    FixedThreeSATThreeSeed.fixedFormula.Satisfies (decode orientationRead a) := by
  rw [orientationRead,decode_compose]
  apply matching_sound
  apply (PeriodicThreeDM.SeedNormalization.formula_satisfies_iff _).1
  exact (PeriodicThreeDM.SeedNormalization.boundedSeedFactor
    FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance_degree
    FixedPlanarThreeDMSeed.fixedPresentation_collisionFree).sound a valid

def read : Read WangTile TargetVariable := compose threeRead orientationRead

theorem sound (a : TargetVariable → Cell → Bool)
    (valid : FixedNormalizedOrientationSeed.fixedFormula.Satisfies a) :
    WangPeriodicCNF.fixedFormula.Satisfies (decode read a) := by
  rw [read,decode_compose]
  exact threeFactor.sound _ (orientation_sound a valid)

theorem read_primrec : Primrec read :=
  compose_primrec
    (compose_primrec PeriodicThreeCNF.seedRead_primrec (PeriodicThreeSATThree.seedRead_primrec _))
    (compose_primrec
      (compose_primrec (retainedPolaritySeedRead_primrec _)
        (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead_primrec _))
      (PeriodicThreeDM.SeedNormalization.boundedRead_primrec _))

theorem clause_finite_radius (clause : PeriodicClause WangTile)
    (member : clause ∈ WangPeriodicCNF.fixedFormula.clauses) :
    ∃ radius, PeriodicCNF.FiniteConsequences.FiniteEntails FixedNormalizedOrientationSeed.fixedFormula
      (groundClause read clause) radius :=
  finite_radius sound clause member

theorem uniform_window : ∃ radius, ∀ a : TargetVariable → Cell → Bool, ∀ translate : Cell,
    (∀ c ∈ TrominoAssignment.boxCellList radius,
      ∀ clause ∈ FixedNormalizedOrientationSeed.fixedFormula.clauses,
        clause.Holds a (Cell.add translate c)) →
    ∀ clause ∈ WangPeriodicCNF.fixedFormula.clauses, clause.Holds (decode read a) translate :=
  uniform_local_window sound

open Lean Elab Command in
run_cmd do
  for name in [``sound,``read_primrec,``clause_finite_radius] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedWangNormalizedSeedDecoder
