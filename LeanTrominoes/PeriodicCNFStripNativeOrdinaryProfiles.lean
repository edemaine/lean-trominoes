/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeOrdinaryInput
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFirstParentRouteSemantics
import LeanTrominoes.FiniteUnaryFieldBlockMapCompiler
import LeanTrominoes.TM2ComputableInPolyTimeCongr

/-! # Compiled clause lengths and literal signs of the ordinary planar source -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeDirectionOrdering PeriodicCNF.ClauseProfileOccurrenceSplit
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance ordinaryProfileStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
local instance ordinaryProfileVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq
set_option maxHeartbeats 800000

def nativeOrdinaryProfiles (s : List encoding.Γ) : List DirectedClauseProfile :=
  (directSourceFinalParentRouteBlocks decider s).map Prod.fst

def nativeOrdinaryProfilesCompiler : TM2ComputableInPolyTime id id (nativeOrdinaryProfiles decider) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseDescriptorsComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime (fun token : Token =>
      match token with | .variable => [] | .clause profile => [profile]))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [← directSourceFinalParentRouteBlocks_profiles]
  simp only [nativeOrdinaryProfiles, List.flatMap_map]
  rw [List.map_eq_flatMap]

theorem nativeOrdinaryProfiles_literals (s : List encoding.Γ) :
    (nativeOrdinaryProfiles decider s).map (fun profile => profile.orderedProfile.literals) =
      (nativeOrdinaryBaseInput decider s).1.clauses.map literalProfiles := by
  change _ = ((PositionedPeriodicCNF.orderClausesByRouteDirection
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula (directSourceFormula decider s))
    (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes (directSourceFormula decider s))).scale
      retainedFigureNineSourceClearanceFactor).erase.clauses.map literalProfiles
  rw [PositionedPeriodicCNF.erase_scale]
  simp only [nativeOrdinaryProfiles, directSourceFinalParentRouteBlocks, List.map_map, Function.comp_def,
    PositionedPeriodicCNF.erase, PositionedPeriodicCNF.orderClausesByRouteDirection]
  apply List.map_congr_left
  intro tagged member
  apply DirectedClauseProfile.orderedProfile_ofClause_literals
  · exact retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_clausesNonempty
      (directSourceFormula decider s) (sourceFormula_clausesNonempty _) tagged.1
      (List.fst_mem_of_mem_zipIdx member)
  · exact retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
      (directSourceFormula decider s) (sourceFormula_widthAtMostThree _) tagged.1.literals
      (PositionedPeriodicCNF.literals_mem_erase_of_mem_zipIdx member)

def nativeOrdinaryClauseLengthsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeOrdinaryBaseInput decider s).1.clauses.map List.length) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryProfilesCompiler decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime (fun profile : DirectedClauseProfile => [profile.orderedProfile.literals.length]))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have h := congrArg (List.map List.length) (nativeOrdinaryProfiles_literals decider s)
  simpa only [FiniteUnaryFieldBlockMap.values, ← List.map_eq_flatMap, List.map_map,
    Function.comp_def, literalProfiles, List.length_map] using h

def nativeOrdinaryLiteralValuesCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeOrdinaryBaseInput decider s).1.clauses.flatMap
      (fun clause => clause.map (fun literal => literal.value.toNat))) := by
  let physical := TM2CompositionMachine.computableInPolyTime (nativeOrdinaryProfilesCompiler decider)
    (FiniteUnaryFieldBlockMap.computableInPolyTime (fun profile : DirectedClauseProfile =>
      profile.orderedProfile.literals.map (fun literal => literal.value.toNat)))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  have h := congrArg (List.flatMap (List.map (fun literal : UnaryProgramClauseProfile.LiteralProfile => literal.value.toNat)))
    (nativeOrdinaryProfiles_literals decider s)
  simpa only [FiniteUnaryFieldBlockMap.values, List.flatMap_map, literalProfiles, List.map_map,
    Function.comp_def] using h

end LeanTrominoes.PeriodicCNFStripReduction
end
