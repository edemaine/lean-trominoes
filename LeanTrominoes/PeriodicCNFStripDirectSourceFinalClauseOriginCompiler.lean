/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFirstParentCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFirstParentRouteSemantics
import LeanTrominoes.RetainedAngularFanClauseOriginFromDirections
import LeanTrominoes.RetainedAngularFanFinalClauseAnchors

/-! # Actual canonical clause origins from compiled first-literal coordinates -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing

private def firstParentPosition {Atom : Type} (placement : PeriodicVariablePlacement Atom)
    (clause : PositionedPeriodicClause Atom) : Cell :=
  (clause.literals.head?.map (fun literal => placement.position literal.atom)).getD (0, 0)

private theorem pointValue_bools (horizontal positive : Bool) (point : Cell) :
    CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.component horizontal point) := by
  cases horizontal <;> cases positive <;> rfl

private theorem firstParentPosition_field {Atom : Type} (placement : PeriodicVariablePlacement Atom)
    (clause : PositionedPeriodicClause Atom) (horizontal positive : Bool) :
    (clause.literals.map fun literal => CarrierCrossingPointField.pointValue
      (coordinateFieldOfBools horizontal positive) (placement.position literal.atom)).getD 0 0 =
      SignedUnaryCoordinateRefinement.field positive
        (DelimitedDirectionDisplacement.component horizontal (firstParentPosition placement clause)) := by
  cases literalsEq : clause.literals with
  | nil => cases horizontal <;> cases positive <;> simp [firstParentPosition, literalsEq,
      SignedUnaryCoordinateRefinement.field, DelimitedDirectionDisplacement.component]
  | cons literal rest =>
    simp only [List.map_cons, List.getD_cons_zero, firstParentPosition, literalsEq,
      List.head?_cons, Option.map_some, Option.getD_some, pointValue_bools]

private theorem field_not (positive : Bool) (value : Int) :
    SignedUnaryCoordinateRefinement.field (!positive) value =
      SignedUnaryCoordinateRefinement.field positive (-value) := by
  cases positive <;> simp [SignedUnaryCoordinateRefinement.field]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance clauseOriginStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- Subtract the selected complete route displacement from its variable endpoint. -/
def directSourceFinalClauseOrigins (horizontal keepPositive : Bool) (symbols : List encoding.Γ) : List Nat :=
  SignedUnaryCoordinateRefinement.values 1 keepPositive
    (fun positive => directSourceFinalFirstParentCoordinates decider horizontal positive symbols)
    (fun positive => directSourceFinalFirstParentRouteDisplacements decider horizontal (!positive) symbols)

/-- Canonical parent origins are compiled uniformly from direct source symbols. -/
noncomputable def directSourceFinalClauseOriginsComputableInPolyTime (horizontal keepPositive : Bool) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalClauseOrigins decider horizontal keepPositive) := by
  unfold directSourceFinalClauseOrigins
  exact SignedUnaryCoordinateRefinement.nativeListComputableInPolyTime 1 keepPositive
    (fun positive => directSourceFinalFirstParentCoordinates decider horizontal positive)
    (fun positive => directSourceFinalFirstParentRouteDisplacements decider horizontal (!positive))
    (fun positive symbols => by rw [directSourceFinalFirstParentCoordinates_length, directSourceFinalFirstParentCoordinates_length])
    (fun positive symbols => by rw [directSourceFinalFirstParentRouteDisplacements_length, directSourceFinalFirstParentCoordinates_length])
    (fun positive => directSourceFinalFirstParentCoordinatesComputableInPolyTime decider horizontal positive)
    (fun positive => directSourceFinalFirstParentRouteDisplacementsComputableInPolyTime decider horizontal (!positive))

private theorem firstParentCoordinates_eq_positions (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalFirstParentCoordinates decider horizontal keepPositive symbols =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.zipIdx.map fun tagged =>
          SignedUnaryCoordinateRefinement.field keepPositive (DelimitedDirectionDisplacement.component horizontal
            (firstParentPosition (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
              (directSourceFormula decider symbols)) tagged.1)) := by
  rw [directSourceFinalFirstParentCoordinates_eq_literals]
  simp only [firstParentPosition_field]
  simpa only [List.map_map, Function.comp_def] using
    (congrArg (List.map (fun clause => SignedUnaryCoordinateRefinement.field keepPositive
      (DelimitedDirectionDisplacement.component horizontal (firstParentPosition
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          (directSourceFormula decider symbols)) clause))))
      (List.zipIdx_map_fst 0 (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses)).symm

/-- Every compiled origin is the actual canonical clause coordinate, in the
original parent order before the Figure 9 clockwise sort. -/
theorem directSourceFinalClauseOrigins_eq_positions (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalClauseOrigins decider horizontal keepPositive symbols =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.map fun clause =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive)
            (PositionedPeriodicCNF.canonicalClausePosition
              (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
                (directSourceFormula decider symbols)) clause) := by
  let source := directSourceFormula decider symbols
  let placement := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  let routes := retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source
  let clauses := (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses
  let endpoint := fun tagged : PositionedPeriodicClause (ThreeOccurrenceVariable
      (WrappedPeriodicPlanarSATVariable Variable)) × Nat =>
    DelimitedDirectionDisplacement.component horizontal (firstParentPosition placement tagged.1)
  let routeDisplacement := fun tagged : PositionedPeriodicClause (ThreeOccurrenceVariable
      (WrappedPeriodicPlanarSATVariable Variable)) × Nat =>
    DelimitedDirectionDisplacement.component horizontal (AxisDirection.polylineFirstDirection (routes tagged.2 0)).step +
      DelimitedDirectionDisplacement.displacement horizontal (Gadget.unitSubdivisionDirections (routes tagged.2 0).tail)
  have endpoints : (fun positive => directSourceFinalFirstParentCoordinates decider horizontal positive symbols) =
      (fun positive => clauses.zipIdx.map fun tagged => SignedUnaryCoordinateRefinement.field positive (endpoint tagged)) :=
    funext (firstParentCoordinates_eq_positions decider horizontal · symbols)
  have offsets : (fun positive => directSourceFinalFirstParentRouteDisplacements decider horizontal (!positive) symbols) =
      (fun positive => clauses.zipIdx.map fun tagged => SignedUnaryCoordinateRefinement.field positive (-routeDisplacement tagged)) := by
    funext positive
    rw [directSourceFinalFirstParentRouteDisplacements_eq_routes]
    simp only [field_not]
    rfl
  unfold directSourceFinalClauseOrigins
  rw [endpoints, offsets, SignedUnaryCoordinateRefinement.values_map]
  simp only [Int.natCast_one, one_mul]
  have sourceOccurrences : @PeriodicCNF.OccurrencesAtMost Variable
      (@instBEqOfDecidableEq Variable directSourceVariableDecidableEqInstance) (by infer_instance) 3 source := by
    exact PeriodicCNF.occurrencesAtMost_congr_beq _ _ (by infer_instance) (by infer_instance) 3 _
      (sourceFormula_occurrencesAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols))
  calc
    _ = clauses.zipIdx.map (fun tagged => SignedUnaryCoordinateRefinement.field keepPositive
        (DelimitedDirectionDisplacement.component horizontal
          (PositionedPeriodicCNF.canonicalClausePosition placement tagged.1))) := by
      apply List.map_congr_left
      intro tagged member
      have nonempty := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty source
        (sourceFormula_clausesNonempty (PolySpaceCompiler.formulaOfSymbols decider symbols))
        tagged.1 (List.fst_mem_of_mem_zipIdx member)
      obtain ⟨literal, rest, literalsEq⟩ := List.exists_cons_of_ne_nil nonempty
      have firstLiteral : tagged.1.literals.head? = some literal := by simp only [literalsEq, List.head?_cons]
      have recovered := @retainedSplitClauseOrigin_eq_directionRecovery Variable
        directSourceVariableDecidableEqInstance source
        (sourceFormula_isLocal (PolySpaceCompiler.formulaOfSymbols decider symbols))
        (sourceFormula_widthAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols))
        sourceOccurrences (sourceFormula_clausesNonempty (PolySpaceCompiler.formulaOfSymbols decider symbols))
        horizontal tagged.1 tagged.2 member literal firstLiteral
      apply congrArg (SignedUnaryCoordinateRefinement.field keepPositive)
      simp only [endpoint, routeDisplacement, firstParentPosition, firstLiteral, Option.map_some, Option.getD_some]
      change DelimitedDirectionDisplacement.component horizontal
        (PositionedPeriodicCNF.canonicalClausePosition placement tagged.1) = _ at recovered
      dsimp only [placement, routes] at recovered ⊢
      omega
    _ = _ := by
      simpa only [List.map_map, Function.comp_def, pointValue_bools] using
        congrArg (List.map (fun clause => CarrierCrossingPointField.pointValue
          (coordinateFieldOfBools horizontal keepPositive)
          (PositionedPeriodicCNF.canonicalClausePosition placement clause))) (List.zipIdx_map_fst 0 clauses)

/-- The original retained parents have zero anchors, so the same compiled
column supplies their stored positions for subsequent geometric refinements. -/
theorem directSourceFinalClauseOrigins_eq_stored_positions (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalClauseOrigins decider horizontal keepPositive symbols =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.map fun clause =>
          CarrierCrossingPointField.pointValue (coordinateFieldOfBools horizontal keepPositive) clause.position := by
  rw [directSourceFinalClauseOrigins_eq_positions]
  apply List.map_congr_left
  intro clause member
  rw [retainedSplitClause_canonicalPosition_eq_position _ clause member]

@[simp] theorem directSourceFinalClauseOrigins_length (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    (directSourceFinalClauseOrigins decider horizontal keepPositive symbols).length =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.length := by
  rw [directSourceFinalClauseOrigins_eq_positions, List.length_map]

end LeanTrominoes.PeriodicCNFStripReduction
end
