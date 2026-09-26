/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicPlanarSATAnchorNormalization
import LeanTrominoes.PeriodicPlanarSATInjectiveRenaming
import LeanTrominoes.OccurrenceIdentityRenaming
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRingVariableSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRingAtomMembership
import LeanTrominoes.PeriodicCNFStripOneDimensional

/-! # The normalized numeric ordinary planar SAT endpoint -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicPlanarSAT
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryInputStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryInputVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

abbrev OrdinaryVariable := ThreeOccurrenceGeometry.Target Variable

def nativeOrdinaryBaseInput (s : List encoding.Γ) : PeriodicPlanarSAT.Input OrdinaryVariable :=
  ThreeOccurrenceGeometry.input (directSourceFormula decider s)

def nativeOrdinaryAtomCodes (s : List encoding.Γ) : List Nat :=
  (nativeOrdinaryBaseInput decider s).1.variableOccurrences.map (directSourceFinalRingVariableCode decider s)

private theorem ordinary_atom_is_ringCopy (s : List encoding.Γ) (atom : OrdinaryVariable)
    (member : atom ∈ (nativeOrdinaryBaseInput decider s).1.variableOccurrences) :
    ∃ original vertex,
      original ∈ (PeriodicOrthocrossing.retainedFinalCoordinatedScaledSource
        (directSourceFormula decider s)).erase.variableOccurrences ∧
      atom = PeriodicEightOccurrenceSplit.ringCopy original vertex := by
  apply PeriodicCNF.FormulaShapeRetainedFigureNineDirection.finalPositionedFormula_atom_is_ringCopy
    (directSourceFormula decider s) atom
  apply (PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm _ _).mem_iff.mp
  simpa only [nativeOrdinaryBaseInput, ThreeOccurrenceGeometry.input, ThreeOccurrenceGeometry.formula,
    PeriodicOrthocrossing.retainedFigureNineClearancePositionedFormula, PositionedPeriodicCNF.erase_scale,
    PeriodicOrthocrossing.retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula] using member

theorem nativeOrdinaryAtomCodes_coherent (s : List encoding.Γ) :
    OccurrenceIdentity.Coherent (nativeOrdinaryBaseInput decider s).1.variableOccurrences (nativeOrdinaryAtomCodes decider s) := by
  refine ⟨List.length_map _, ?_⟩
  intro i hi j hj
  simp only [nativeOrdinaryAtomCodes, List.getElem_map]
  obtain ⟨a, av, ha, ea⟩ := ordinary_atom_is_ringCopy decider s _ (List.getElem_mem hi)
  obtain ⟨b, bv, hb, eb⟩ := ordinary_atom_is_ringCopy decider s _ (List.getElem_mem hj)
  rw [ea, eb]
  exact directSourceFinalRingVariableCode_eq_iff_ringCopy decider s a b ha hb av bv

def nativeOrdinaryRenaming (s : List encoding.Γ) : OrdinaryVariable → Nat :=
  OccurrenceIdentity.rename (nativeOrdinaryBaseInput decider s).1.variableOccurrences (nativeOrdinaryAtomCodes decider s)

theorem nativeOrdinaryRenaming_injective (s : List encoding.Γ) : Function.Injective (nativeOrdinaryRenaming decider s) :=
  OccurrenceIdentity.rename_injective _ _ (nativeOrdinaryAtomCodes_coherent decider s)

theorem nativeOrdinaryRenaming_atoms (s : List encoding.Γ) :
    (nativeOrdinaryBaseInput decider s).1.variableOccurrences.map (nativeOrdinaryRenaming decider s) =
      nativeOrdinaryAtomCodes decider s :=
  OccurrenceIdentity.map_rename _ _ (nativeOrdinaryAtomCodes_coherent decider s)

def nativeOrdinaryInput (s : List encoding.Γ) : PeriodicPlanarSAT.Input Nat :=
  renameInput (nativeOrdinaryRenaming decider s) (anchorInput (nativeOrdinaryBaseInput decider s))

private theorem ordinarySource_occurrences (s : List encoding.Γ) :
    @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable ordinaryInputVariableDecidableEq) (by infer_instance) 3
      (directSourceFormula decider s) :=
  PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
    (sourceFormula_occurrencesAtMostThree_canonicalBEq (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))

private theorem nativeOrdinaryBaseInput_sat (s : List encoding.Γ) :
    (nativeOrdinaryBaseInput decider s).1.Satisfiable ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  exact (PeriodicOrthocrossing.retainedFigureNineClearancePositionedFormula_satisfiable_iff
    (directSourceFormula decider s) (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _)
    (ordinarySource_occurrences decider s)).trans (sourceFormula_correct _).symm

private theorem nativeOrdinaryBaseInput_three (s : List encoding.Γ)
    (h : PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem (nativeOrdinaryBaseInput decider s) := by
  apply (ThreeOccurrenceGeometry.localOneDimensionalThreeOccurrence_correct
    (directSourceFormula decider s) (sourceFormula_isLocal _) (sourceFormula_widthAtMostThree _)
    (ordinarySource_occurrences decider s) (sourceFormula_clausesNonempty _) (sourceFormula_isOneDimensional _)).2
  exact (sourceFormula_correct _).1 h

theorem nativeOrdinaryInput_correct (s : List encoding.Γ) :
    Orbit.LocalOneDimensionalProblem (nativeOrdinaryInput decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  rw [nativeOrdinaryInput, ordinary_rename _ (nativeOrdinaryRenaming_injective decider s)]
  constructor
  · rintro ⟨_, _, _, _, _, satisfiable⟩
    exact (nativeOrdinaryBaseInput_sat decider s).1
      ((PeriodicCNF.anchorNormalize_satisfiable_iff _).1 satisfiable)
  · intro h
    obtain ⟨horizontal, grid, locality, _, problem⟩ := nativeOrdinaryBaseInput_three decider s h
    exact ordinary_anchorInput ⟨horizontal, grid, locality, problem⟩

theorem nativeOrdinaryInput_three_correct (s : List encoding.Γ) :
    Orbit.LocalOneDimensionalThreeOccurrenceProblem (nativeOrdinaryInput decider s) ↔
      PeriodicCNF.LocalPeriodicCNF1DSAT (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) := by
  rw [nativeOrdinaryInput, ordinaryThree_rename _ (nativeOrdinaryRenaming_injective decider s)]
  constructor
  · rintro ⟨_, _, _, _, _, _, satisfiable⟩
    exact (nativeOrdinaryBaseInput_sat decider s).1
      ((PeriodicCNF.anchorNormalize_satisfiable_iff _).1 satisfiable)
  · exact fun h => ordinaryThree_anchorInput (nativeOrdinaryBaseInput_three decider s h)

end LeanTrominoes.PeriodicCNFStripReduction
end
