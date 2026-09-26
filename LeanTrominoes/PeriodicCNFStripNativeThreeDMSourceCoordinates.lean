/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMElements
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTripleCoordinateCompiler
import LeanTrominoes.PeriodicCNFStripNativePeriodCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMPeriodComputability

/-! # Native source positions and period for planar 3DM incidence routes -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn DelimitedDirectionDisplacement
attribute [local instance] horizontalThreeDMTripleVariableDecidableEq
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeThreeDMCoordinateStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

abbrev nativeThreeDMTriplePositions (s : List encoding.Γ) :=
  horizontalThreeDMTriplePositionsComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

abbrev nativeThreeDMSourcePoint (s : List encoding.Γ) (tag : IncidenceTag) :=
  (nativeThreeDMTriplePositions decider s).getD tag.tripleIndex (0,0)

abbrev nativeThreeDMPeriod (s : List encoding.Γ) :=
  horizontalThreeDMPeriodComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)

theorem nativeThreeDMTriplePositions_length (s : List encoding.Γ) :
    (nativeThreeDMTriplePositions decider s).length = (nativeThreeDMProblem decider s).triples.length := by
  simp [nativeThreeDMTriplePositions,horizontalThreeDMTriplePositionsComputed,nativeThreeDMProblem,
    horizontalThreeDMProblemComputed,PeriodicPlanarOneInThreeToThreeDM.encodedProblem,
    PeriodicPlanarOneInThreeToThreeDM.TypedProblem.encode,PeriodicPlanarOneInThreeToThreeDM.problem]
  exact congrArg (fun deq : DecidableEq RoutedVariable =>
    (@PeriodicPlanarOneInThreeToThreeDM.triples RoutedVariable deq
      (horizontalNormalizedRoutedFormulaComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).erase).length)
    (Subsingleton.elim horizontalThreeDMTripleVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq)

theorem nativeThreeDMSourcePoint_fields (s : List encoding.Γ) (f : Cell → Nat) :
    (nativeThreeDMIncidences decider s).map (fun tag => f (nativeThreeDMSourcePoint decider s tag)) =
      (nativeThreeDMTriplePositions decider s).flatMap (fun p => List.replicate 3 (f p)) := by
  rw [nativeThreeDMIncidences,incidenceTags_eq_range_flatMap,← nativeThreeDMTriplePositions_length]
  simp only [List.map_flatMap,tripleIncidenceTags,incidenceColors,List.map_cons,List.map_nil]
  have h := congrArg (List.flatMap (fun p => List.replicate 3 (f p)))
    (List.map_range_getD (nativeThreeDMTriplePositions decider s) (0,0))
  simpa only [List.flatMap_map,List.map_map,Function.comp_def,List.replicate_succ,List.replicate_zero,
    nativeThreeDMSourcePoint] using h

def nativeThreeDMSourcePointCompiler (horizontal positive : Bool) :
    Compiler (nativeThreeDMIncidences decider) (fun s tag =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal (nativeThreeDMSourcePoint decider s tag))) := by
  apply TM2ComputableInPolyTime.of_eq
    (directSourceFinalIncidenceSourceCoordinatesComputableInPolyTime decider horizontal positive)
  intro s
  dsimp only
  rw [directSourceFinalIncidenceSourceCoordinates_eq_horizontal,
    nativeThreeDMSourcePoint_fields decider s (fun point => SignedUnaryCoordinateRefinement.field positive (component horizontal point))]
  apply List.flatMap_congr
  intro p _
  cases horizontal <;> cases positive <;> rfl

theorem nativeThreeDMPeriod_positive (s : List encoding.Γ) : 0 < nativeThreeDMPeriod decider s := by
  exact Nat.mul_pos (by decide) (Nat.mul_pos (by decide) (nativeRoutedPeriod_positive _))

def nativeThreeDMPeriodCompiler : ScalarCompiler (nativeThreeDMPeriod decider) := by
  let column : Compiler (fun _ : List encoding.Γ => [()]) (fun s _ =>
      (horizontalRoutedPlacementComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s)).period) :=
    nativeRoutedPeriodCompiler decider
  apply TM2ComputableInPolyTime.of_eq (scale column 256)
  intro s
  simp only [List.map_cons,List.map_nil,nativeThreeDMPeriod,horizontalThreeDMPeriodComputed]
  apply congrArg (fun n : Nat => [n])
  omega

end LeanTrominoes.PeriodicCNFStripReduction
end
