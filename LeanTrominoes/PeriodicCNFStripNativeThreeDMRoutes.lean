/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMElements
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceBodyHorizontalSemantics
import LeanTrominoes.DelimitedDirectionDisplacementCompiler

/-! # Complete native direction words of the planar 3DM incidence routes -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeThreeDMRouteStack (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 2048

abbrev nativeThreeDMRoute (s : List encoding.Γ) (tag : PeriodicThreeDM.IncidenceTag) :=
  horizontalAssembledRouteAtTagComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s,tag)

def nativeThreeDMDirections (s : List encoding.Γ) :=
  (nativeThreeDMIncidences decider s).map (fun tag => unitSubdivisionDirections (nativeThreeDMRoute decider s tag))

private def directionToken : FiniteAlphabetDelimitedBlockJoin.Token AxisDirection → Token
  | .value direction => .direction direction
  | .blockEnd => .routeEnd

private theorem directionToken_blocks (routes : List (List AxisDirection)) :
    (FiniteAlphabetDelimitedBlockJoin.blocks routes).map directionToken = words routes := by
  simp only [FiniteAlphabetDelimitedBlockJoin.blocks,words,List.map_flatMap]
  apply List.flatMap_congr
  intro route _
  simp [FiniteAlphabetDelimitedBlockJoin.block,word,directionToken,List.map_map,Function.comp_def]

def nativeThreeDMDirectionsCompiler : TM2ComputableInPolyTime id id
    (fun s => words (nativeThreeDMDirections decider s)) := by
  let physical := TM2CompositionMachine.computableInPolyTime
    (directSourceFinalCanonicalIncidenceDirectionTokensComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime (fun token => [directionToken token]))
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [← List.map_eq_flatMap,directSourceFinalCanonicalIncidenceDirectionTokens_eq_horizontal,directionToken_blocks]
  apply congrArg words
  unfold nativeThreeDMDirections
  apply List.map_congr_left
  intro tag ht
  exact horizontalCanonicalIncidenceDirectionBlock_directions
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s) tag ht

def nativeThreeDMDisplacementCompiler (horizontal positive : Bool) :
    UnaryColumn.Compiler (nativeThreeDMIncidences decider) (fun s tag =>
      SignedUnaryCoordinateRefinement.field positive
        (displacement horizontal (unitSubdivisionDirections (nativeThreeDMRoute decider s tag)))) := by
  let physical := valuesComputableInPolyTime (nativeThreeDMDirections decider) horizontal positive
    (nativeThreeDMDirectionsCompiler decider)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  rw [values_eq_displacements]
  simp only [nativeThreeDMDirections,List.map_map,Function.comp_def]

end LeanTrominoes.PeriodicCNFStripReduction
end
