/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryRouteWords
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryValueColumns
import LeanTrominoes.PositionedIncidenceFormulaFields
import LeanTrominoes.PositionedIncidenceFirstColumns
import LeanTrominoes.UnaryColumnCompiler

/-! # Ordinary incidence columns and clause-start recovery -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing PeriodicCNF PeriodicOrthocrossing UnaryColumn DelimitedDirectionDisplacement
open PeriodicPlanarSAT PeriodicCNF.FormulaShapeDirectionOrdering
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryOffsetStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryOffsetVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

theorem nativeOrdinaryBaseInput_formula (s : List encoding.Γ) :
    (nativeOrdinaryBaseInput decider s).1 = (nativeOrdinaryFormula decider s).erase := by
  rfl

private theorem pointField_double (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) (Cell.scale 2 point) =
      CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point * 2 := by
  rcases point with ⟨x, y⟩
  cases horizontal <;> cases positive <;>
    simp only [CarrierCrossingPointField.pointValue, coordinateFieldOfBools, CarrierCrossingPointField.horizontal,
      CarrierCrossingPointField.keepPositive, Cell.scale, Bool.false_eq_true, ↓reduceIte] <;> omega

def nativeOrdinaryVariableColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (nativeOrdinaryRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (component horizontal ((nativeOrdinaryPlacement decider s).position row.2.1.atom))) := by
  let original : Compiler (nativeOrdinaryRows decider) (fun s row =>
      CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive)
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement (directSourceFormula decider s)).position row.2.1.atom)) :=
    TM2ComputableInPolyTime.of_eq (nativeOrdinaryPositionFieldsCompiler decider horizontal positive)
      (fun s => (PositionedIncidenceRows.map_literals (nativeOrdinaryFormula decider s) _).symm)
  apply TM2ComputableInPolyTime.of_eq (scale original 2)
  intro s
  apply List.map_congr_left
  intro row _
  have doubled := pointField_double horizontal positive
    ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement (directSourceFormula decider s)).position row.2.1.atom)
  cases horizontal <;> cases positive <;> exact doubled.symm

def nativeOrdinaryDisplacementColumn [Inhabited encoding.Γ] (horizontal positive : Bool) :
    Compiler (nativeOrdinaryRows decider) (fun s row => SignedUnaryCoordinateRefinement.field positive
      (displacement horizontal (Gadget.unitSubdivisionDirections (nativeOrdinaryRoutes decider s row.1.2 row.2.2)))) := by
  let physical := DelimitedDirectionDisplacement.valuesComputableInPolyTime
    (nativeOrdinaryDirectionWords decider) horizontal positive (nativeOrdinaryRouteWordsCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [values_eq_displacements]
  simp only [nativeOrdinaryDirectionWords, List.map_map, Function.comp_def]

def nativeOrdinaryFirstColumn [Inhabited encoding.Γ]
    (value : List encoding.Γ → PositionedIncidenceRows.Row OrdinaryVariable → Nat)
    (column : Compiler (nativeOrdinaryRows decider) value) :
    Compiler (nativeOrdinaryRows decider) (fun s => PositionedIncidenceRows.firstValue (value s)) := by
  apply PositionedIncidenceRows.firstColumnCompiler (nativeOrdinaryFormula decider) (nativeOrdinaryProfiles decider)
    (fun profile => profile.orderedProfile.literals.length) _ (nativeOrdinaryProfilesCompiler decider) value column
  intro s
  have h := congrArg (List.map List.length) (nativeOrdinaryProfiles_literals decider s)
  rw [nativeOrdinaryBaseInput_formula] at h
  simpa only [List.map_map, Function.comp_def, PeriodicCNF.ClauseProfileOccurrenceSplit.literalProfiles,
    List.length_map] using h.symm

def nativeOrdinaryRowAtomColumn [Inhabited encoding.Γ] :
    Compiler (nativeOrdinaryRows decider) (fun s row => nativeOrdinaryRenaming decider s row.2.1.atom) := by
  apply TM2ComputableInPolyTime.of_eq (nativeOrdinaryAtomCodesCompiler decider)
  intro s
  rw [← nativeOrdinaryRenaming_atoms, nativeOrdinaryBaseInput_formula]
  have h := congrArg (List.map (nativeOrdinaryRenaming decider s))
    (PositionedIncidenceRows.atoms (nativeOrdinaryFormula decider s))
  simpa only [List.map_map, Function.comp_def] using h.symm

def nativeOrdinaryRowValueColumn [Inhabited encoding.Γ] :
    Compiler (nativeOrdinaryRows decider) (fun _ row => row.2.1.value.toNat) :=
  TM2ComputableInPolyTime.of_eq (nativeOrdinaryLiteralValuesCompiler decider)
    (fun s => (PositionedIncidenceRows.map_literals (nativeOrdinaryFormula decider s) _).symm)

end LeanTrominoes.PeriodicCNFStripReduction
end
