/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Wang.FixedWangNormalizedSeedDecoder
import LeanTrominoes.SAT.CNF.PeriodicCNFUnusedVariables

/-! # A local Wang decoder that retains prescriptions on unused variables -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedWangAugmentedSeedDecoder
open LeanWang PeriodicCNF.SignedDecoder PeriodicOrthocrossing

abbrev FinalVariable := FixedPlanarThreeDMSeed.FinalVariable
abbrev PolarityVariable := FixedPlanarThreeDMSeed.Variable
abbrev OrientationVariable := FixedNormalizedOrientationSeed.Variable
abbrev Variable := OrientationVariable ⊕ PolarityVariable
local instance : DecidableEq FinalVariable := PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
local instance : DecidableEq PolarityVariable := inferInstanceAs (DecidableEq (FinalVariable ⊕ _))
local instance : BEq FinalVariable := instBEqOfDecidableEq
local instance : LawfulBEq FinalVariable := by infer_instance
local instance : BEq PolarityVariable := instBEqOfDecidableEq
local instance : LawfulBEq PolarityVariable := by infer_instance

def support : List PolarityVariable :=
  PeriodicPlanarOneInThreeToThreeDM.occurringVariables FixedPlanarThreeDMSeed.fixedFormula

def formula : PeriodicCNF Variable :=
  PeriodicCNF.UnusedVariables.formula FixedNormalizedOrientationSeed.fixedFormula

def supportedRead : Read PolarityVariable OrientationVariable :=
  compose (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead FixedPlanarThreeDMSeed.fixedFormula)
    (PeriodicThreeDM.SeedNormalization.boundedRead
      FixedPlanarThreeDMSeed.fixedPresentation.toPlanarPresentation)

def polarityRead (v : PolarityVariable) : PeriodicLiteral Variable :=
  if v ∈ support then PeriodicCNF.UnusedVariables.literal (supportedRead v)
  else ⟨Sum.inr v,(0,0),true⟩

theorem polarity_decode_supported (a : Variable → Cell → Bool)
    (v : PolarityVariable) (member : v ∈ support) (c : Cell) :
    decode polarityRead a v c =
      decode supportedRead (PeriodicCNF.UnusedVariables.restrict a) v c := by
  simp only [decode,polarityRead,member,ite_true,PeriodicCNF.UnusedVariables.literal,
    PeriodicCNF.UnusedVariables.restrict]

theorem polarity_decode_unused (a : Variable → Cell → Bool)
    (v : PolarityVariable) (unused : v ∉ support) (c : Cell) :
    decode polarityRead a v c = a (.inr v) c := by
  simp [decode,polarityRead,unused,Cell.add]

theorem polarity_sound (a : Variable → Cell → Bool) (valid : formula.Satisfies a) :
    PeriodicOneInThree.Satisfies FixedPlanarThreeDMSeed.fixedFormula (decode polarityRead a) := by
  have orientation := (PeriodicCNF.UnusedVariables.satisfies_iff _ a).1 valid
  have matching := (PeriodicThreeDM.SeedNormalization.formula_satisfies_iff _).1
    ((PeriodicThreeDM.SeedNormalization.boundedSeedFactor
      FixedPlanarThreeDMSeed.fixedPresentation FixedPlanarThreeDMSeed.fixedInstance_degree
      FixedPlanarThreeDMSeed.fixedPresentation_collisionFree).sound _ orientation)
  have exactOne := (PeriodicPlanarOneInThreeToThreeDM.encodedSeedFactor
    FixedPlanarThreeDMSeed.fixedFormula FixedPlanarThreeDMSeed.fixedFormula_occurrences
    FixedPlanarThreeDMSeed.fixedFormula_arity).sound _ matching
  have same : ∀ v ∈ support, ∀ c, decode supportedRead
      (PeriodicCNF.UnusedVariables.restrict a) v c = decode polarityRead a v c := by
    intro v member c
    exact (polarity_decode_supported a v member c).symm
  apply (PeriodicPlanarOneInThreeToThreeDM.exactOne_stable_on_occurringVariables
    FixedPlanarThreeDMSeed.fixedFormula _ _ same).1
  rw [supportedRead,decode_compose]
  exact exactOne

def sourceRead : Read FixedThreeSATThreeSeed.Variable Variable :=
  compose (retainedPolaritySeedRead FixedThreeSATThreeSeed.fixedFormula) polarityRead

theorem source_sound (a : Variable → Cell → Bool) (valid : formula.Satisfies a) :
    FixedThreeSATThreeSeed.fixedFormula.Satisfies (decode sourceRead a) := by
  rw [sourceRead,decode_compose]
  exact (retainedPolaritySeedFactor FixedThreeSATThreeSeed.fixedFormula
    FixedThreeSATThreeSeed.fixedFormula_isLocal FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree
    FixedPlanarThreeDMSeed.source_occurrences FixedThreeSATThreeSeed.fixedFormula_clausesNonempty).sound _
      (polarity_sound a valid)

def read : Read WangTile Variable := compose FixedWangNormalizedSeedDecoder.threeRead sourceRead

theorem sound (a : Variable → Cell → Bool) (valid : formula.Satisfies a) :
    WangPeriodicCNF.fixedFormula.Satisfies (decode read a) := by
  rw [read,decode_compose]
  exact FixedWangNormalizedSeedDecoder.threeFactor.sound _ (source_sound a valid)

theorem supportedRead_primrec : Primrec supportedRead :=
  compose_primrec (PeriodicPlanarOneInThreeToThreeDM.encodedSeedRead_primrec _)
    (PeriodicThreeDM.SeedNormalization.boundedRead_primrec _)

theorem polarityRead_primrec : Primrec polarityRead := by
  have used : PrimrecPred (fun v : PolarityVariable => v ∈ support) :=
    PeriodicCNF.FiniteSearch.mem_primrec.comp Primrec.id (Primrec.const support)
  have free : Primrec (fun v : PolarityVariable =>
      (⟨Sum.inr v,(0,0),true⟩ : PeriodicLiteral Variable)) :=
    PeriodicLiteral.equivData_symm_primrec.comp
      (Primrec.pair Primrec.sumInr (Primrec.const ((0,0),true)))
  exact Primrec.ite used (PeriodicCNF.UnusedVariables.read_primrec supportedRead_primrec) free

theorem read_primrec : Primrec read :=
  compose_primrec
    (compose_primrec PeriodicThreeCNF.seedRead_primrec (PeriodicThreeSATThree.seedRead_primrec _))
    (compose_primrec (retainedPolaritySeedRead_primrec _) polarityRead_primrec)

theorem uniform_window : ∃ radius, ∀ a : Variable → Cell → Bool, ∀ translate : Cell,
    (∀ c ∈ TrominoAssignment.boxCellList radius,
      ∀ clause ∈ formula.clauses, clause.Holds a (Cell.add translate c)) →
    ∀ clause ∈ WangPeriodicCNF.fixedFormula.clauses, clause.Holds (decode read a) translate :=
  uniform_local_window sound

open Lean Elab Command in
run_cmd do
  for name in [``sound,``read_primrec,``uniform_window] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.FixedWangAugmentedSeedDecoder
