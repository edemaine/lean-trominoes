/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FirstParentInheritedRouteSelection
import LeanTrominoes.DelimitedDirectionDisplacementCompiler
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler

/-! # Selected first-parent displacements from aligned profile and tail blocks -/

namespace LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open DelimitedDirectionDisplacement SignedUnaryCoordinateRefinement

/-- Trailing variable markers contribute neither routes nor tail-table reads. -/
theorem sourcePairs_append_variables (descriptors : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (tails : List (List (List AxisDirection))) (count : Nat) :
    sourcePairs (descriptors ++ List.replicate count .variable) tails = sourcePairs descriptors tails := by
  induction descriptors generalizing tails with
  | nil =>
    simp only [List.nil_append, sourcePairs]
    induction count with
    | zero => rfl
    | succ count induction => simpa only [List.replicate_succ, sourcePairs] using induction
  | cons descriptor descriptors induction =>
    cases descriptor <;> simp only [List.cons_append, sourcePairs, induction]

/-- Pair expansion consumes the tail row attached to each parent profile. -/
theorem sourcePairs_blocks (blocks : List (DirectedClauseProfile × List (List AxisDirection))) :
    sourcePairs (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1))
        (blocks.map Prod.snd) =
      blocks.flatMap (fun block => sourceClausePairs block.1 block.2) := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
    simp only [List.map_cons, sourcePairs, List.headD_cons, List.tail_cons, List.flatMap_cons, induction]

/-- Keep the parent profile alongside every selected tail in occurrence order. -/
def routeRows (blocks : List (DirectedClauseProfile × List (List AxisDirection))) :
    List (DirectedClauseProfile × List AxisDirection) :=
  blocks.flatMap fun block => (sourceClauseHeaders block.1).map fun header =>
    (block.1, selectedTailDirections block.2 header)

theorem firstSteps_eq_rows (blocks : List (DirectedClauseProfile × List (List AxisDirection)))
    (horizontal keepPositive : Bool) :
    firstSteps horizontal keepPositive (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1)) =
      (routeRows blocks).map fun row => field keepPositive (DelimitedDirectionDisplacement.component horizontal (firstDirection row.1).step) := by
  simp only [firstSteps, firstStepBlock, routeRows, List.flatMap_map, List.map_flatMap, List.map_map,
    Function.comp_def, List.map_const', DelimitedDirectionDisplacement.component]

theorem tails_eq_rows (blocks : List (DirectedClauseProfile × List (List AxisDirection)))
    (horizontal keepPositive : Bool) :
    (sourcePairs (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1))
      (blocks.map Prod.snd)).map (fun pair => field keepPositive (displacement horizontal pair.2)) =
      (routeRows blocks).map fun row => field keepPositive (displacement horizontal row.2) := by
  simp only [sourcePairs_blocks, routeRows, sourceClausePairs, List.map_flatMap, List.map_map, Function.comp_def]

/-- Adding the repeated first step to each tail and selecting one inherited
row per parent recovers the displacement of that same first-literal route. -/
theorem selectedDisplacements_eq_blocks (blocks : List (DirectedClauseProfile × List (List AxisDirection)))
    (horizontal keepPositive : Bool) :
    UnaryFieldBooleanFilter.selectedValues
      (output (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1)))
      (values 1 keepPositive
        (fun positive => firstSteps horizontal positive
          (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1)))
        (fun positive => (sourcePairs
          (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1))
          (blocks.map Prod.snd)).map fun pair => field positive (displacement horizontal pair.2))) =
      blocks.map fun block => field keepPositive
        (DelimitedDirectionDisplacement.component horizontal (firstDirection block.1).step +
          displacement horizontal (selectedTailDirections block.2 (selectedHeader block.1))) := by
  rw [show (fun positive => firstSteps horizontal positive
      (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1))) =
    (fun positive => (routeRows blocks).map fun row => field positive (DelimitedDirectionDisplacement.component horizontal (firstDirection row.1).step))
    from funext (firstSteps_eq_rows blocks horizontal)]
  rw [show (fun positive => (sourcePairs
      (blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1))
      (blocks.map Prod.snd)).map fun pair => field positive (displacement horizontal pair.2)) =
    (fun positive => (routeRows blocks).map fun row => field positive (displacement horizontal row.2))
    from funext (tails_eq_rows blocks horizontal)]
  rw [values_map]
  simp only [Int.natCast_one, one_mul, output, List.flatMap_map, controlBlock, routeRows,
    List.map_flatMap, List.map_map, Function.comp_def]
  rw [UnaryFieldBooleanFilter.selectedValues_flatMap _ _ _ (by
    intro block _member
    simp only [controls_length, List.length_map])]
  simp only [selectedValues_headerMap, ← List.map_eq_flatMap]

end LeanTrominoes.PeriodicCNFStripReduction.FirstParentInheritedRoute
