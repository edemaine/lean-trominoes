/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FirstParentInheritedRouteDisplacementSemantics
import LeanTrominoes.FirstParentInheritedRouteGeometry
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFirstParentRouteCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceWitness

/-! # Selected parent displacements agree with the actual normalized routes -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineSourceTail

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance parentDisplacementSemanticStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack
attribute [local instance] directSourceVariableDecidableEqInstance

/-- The actual clause list supplies both the finite profile and its ordered tails. -/
def directSourceFinalParentRouteBlocks (symbols : List encoding.Γ) :
    List (DirectedClauseProfile × List (List AxisDirection)) :=
  let source := directSourceFormula decider symbols
  let routes := retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes source
  (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula source).clauses.zipIdx.map fun tagged =>
    (DirectedClauseProfile.ofClause routes tagged.2 tagged.1, orderedTailDirections routes tagged.2 tagged.1)

theorem directSourceFinalParentRouteBlocks_profiles (symbols : List encoding.Γ) :
    (directSourceFinalParentRouteBlocks decider symbols).map (fun block => Token.clause block.1) =
      directSourceFinalClauseDescriptors decider symbols := by
  have equality := directSourceFinalClauseDescriptors_eq_source_prefix decider symbols
  simp only [descriptors, ofFormula] at equality
  have cancelled := List.append_cancel_right equality
  simpa only [directSourceFinalParentRouteBlocks, List.map_map, Function.comp_def] using cancelled

theorem directSourceFinalParentRouteBlocks_tails (symbols : List encoding.Γ) :
    (directSourceFinalParentRouteBlocks decider symbols).map Prod.snd =
      tailTables (directSourceFormula decider symbols) := by
  simp only [directSourceFinalParentRouteBlocks, tailTables, List.map_map, Function.comp_def]

theorem directSourceFinalParentRouteBlocks_pairs (symbols : List encoding.Γ) :
    directFigureNinePolarityRoutePairs decider symbols =
      sourcePairs ((directSourceFinalParentRouteBlocks decider symbols).map (fun block => Token.clause block.1))
        ((directSourceFinalParentRouteBlocks decider symbols).map Prod.snd) := by
  unfold directFigureNinePolarityRoutePairs
  rw [directSourceFinalClauseDescriptors_eq_source_prefix, FirstParentInheritedRoute.sourcePairs_append_variables,
    directSourceFinalParentRouteBlocks_profiles, directSourceFinalParentRouteBlocks_tails]

/-- The compiled displacement selects the same profile/tail block as coordinates. -/
theorem directSourceFinalFirstParentRouteDisplacements_eq_blocks
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalFirstParentRouteDisplacements decider horizontal keepPositive symbols =
      (directSourceFinalParentRouteBlocks decider symbols).map fun block =>
        SignedUnaryCoordinateRefinement.field keepPositive
          (DelimitedDirectionDisplacement.component horizontal (FirstParentInheritedRoute.firstDirection block.1).step +
            DelimitedDirectionDisplacement.displacement horizontal
              (selectedTailDirections block.2 (FirstParentInheritedRoute.selectedHeader block.1))) := by
  unfold directSourceFinalFirstParentRouteDisplacements directSourceFinalFirstParentRouteControls
    directSourceFinalParentRouteDisplacementCandidates directSourceFinalParentFirstSteps
  have tailFields : (fun positive => directSourceFinalTailDisplacements decider horizontal positive symbols) =
      (fun positive => (sourcePairs
        ((directSourceFinalParentRouteBlocks decider symbols).map (fun block => Token.clause block.1))
        ((directSourceFinalParentRouteBlocks decider symbols).map Prod.snd)).map fun pair =>
          SignedUnaryCoordinateRefinement.field positive (DelimitedDirectionDisplacement.displacement horizontal pair.2)) := by
    funext positive
    rw [directSourceFinalTailDisplacements_eq_pairs, directSourceFinalParentRouteBlocks_pairs]
  rw [tailFields, ← directSourceFinalParentRouteBlocks_profiles]
  exact FirstParentInheritedRoute.selectedDisplacements_eq_blocks _ horizontal keepPositive

/-- Every selected field is the first step plus tail displacement of literal
zero in that actual parent's original presentation. -/
theorem directSourceFinalFirstParentRouteDisplacements_eq_routes
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalFirstParentRouteDisplacements decider horizontal keepPositive symbols =
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).clauses.zipIdx.map fun tagged =>
          SignedUnaryCoordinateRefinement.field keepPositive
            (DelimitedDirectionDisplacement.component horizontal
              (AxisDirection.polylineFirstDirection
                (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                  (directSourceFormula decider symbols) tagged.2 0)).step +
              DelimitedDirectionDisplacement.displacement horizontal
                (Gadget.unitSubdivisionDirections
                  (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
                    (directSourceFormula decider symbols) tagged.2 0).tail)) := by
  rw [directSourceFinalFirstParentRouteDisplacements_eq_blocks]
  simp only [directSourceFinalParentRouteBlocks, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro tagged member
  have nonempty := retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
    (directSourceFormula decider symbols)
    (sourceFormula_clausesNonempty (PolySpaceCompiler.formulaOfSymbols decider symbols))
    tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have width : tagged.1.literals.length ≤ 3 := by
    apply retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      (directSourceFormula decider symbols)
      (sourceFormula_widthAtMostThree (PolySpaceCompiler.formulaOfSymbols decider symbols)) tagged.1.literals
    exact PositionedPeriodicCNF.literals_mem_erase_of_mem_zipIdx member
  rw [FirstParentInheritedRoute.firstDirection_ofClause _ _ _ nonempty width,
    FirstParentInheritedRoute.selectedTailDirections_ofClause _ _ _ nonempty width]

end LeanTrominoes.PeriodicCNFStripReduction
end
