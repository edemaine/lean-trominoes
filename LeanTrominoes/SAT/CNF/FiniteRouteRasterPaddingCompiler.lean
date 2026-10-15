/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteRouteRasterPadding
import LeanTrominoes.Tiling.Tromino.Finite.FiniteSparsePaddingColumns
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseRouteRasterRequestAssemblyCompiler
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetSparseRouteRasterRequestTokenCompiler
import LeanTrominoes.Computation.TM2.TM2ComputableInPolyTimeCongr

/-! # Polynomial-time serialization of padded compact raster requests -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
open _root_.Computability Turing
open UnaryFieldEncoderMachine (unaryFields)
open PeriodicThreeDM.NormalizationDirectionRequest

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (requests : List Symbol → List Request) (units : List Symbol → List Unit)
variable (gridCompiler : TM2ComputableInPolyTime id unaryFields
  (fun source => (requests source).map (fun request => request.metadata.gridSize)))
variable (horizontalCompiler : TM2ComputableInPolyTime id unaryFields
  (fun source => (requests source).map (fun request => request.metadata.horizontal)))
variable (verticalCompiler : TM2ComputableInPolyTime id unaryFields
  (fun source => (requests source).map (fun request => request.metadata.verticalComplement)))
variable (colorCompiler : TM2ComputableInPolyTime id id
  (fun source => (requests source).map (fun request => request.metadata.color)))
variable (normalizationCompiler : TM2ComputableInPolyTime id id
  (fun source => Batch.tokens ((requests source).map (fun request => request.normalization))))
variable (unitCompiler : TM2ComputableInPolyTime id id units)

def finitePadRequests (source : List Symbol) : List Request :=
  (requests source).map (finitePadRequest (units source).length)

private def paddedGridCompiler : TM2ComputableInPolyTime id unaryFields
    (fun source => (finitePadRequests requests units source).map (fun request => request.metadata.gridSize)) := by
  let scaled := TM2CompositionMachine.computableInPolyTime gridCompiler
    (UnaryFieldConstantScale.computableInPolyTime 3)
  let offset := TM2CompositionMachine.computableInPolyTime scaled
    (UnaryFieldConstantOffsets.computableInPolyTime 1)
  apply TM2ComputableInPolyTime.of_eq offset
  intro source
  simp only [UnaryFieldConstantOffsets.values,UnaryFieldConstantScale.values,List.map_map,
    Function.comp_def,finitePadRequests,finitePadRequest,Nat.mul_comm]

private def paddedHorizontalCompiler : TM2ComputableInPolyTime id unaryFields
    (fun source => (finitePadRequests requests units source).map (fun request => request.metadata.horizontal)) := by
  let compiler := FiniteSparsePaddingColumns.coordinatesComputableInPolyTime
    (fun source => (requests source).map (fun request => request.metadata.horizontal))
    units horizontalCompiler unitCompiler
  apply TM2ComputableInPolyTime.of_eq compiler
  intro source
  rw [FiniteSparsePaddingColumns.coordinates_eq_map]
  simp only [finitePadRequests,List.map_map,Function.comp_def,finitePadRequest]

private def paddedVerticalCompiler : TM2ComputableInPolyTime id unaryFields
    (fun source => (finitePadRequests requests units source).map (fun request => request.metadata.verticalComplement)) := by
  let compiler := FiniteSparsePaddingColumns.complementsComputableInPolyTime
    (fun source => (requests source).map (fun request => request.metadata.verticalComplement))
    units verticalCompiler unitCompiler
  apply TM2ComputableInPolyTime.of_eq compiler
  intro source
  rw [FiniteSparsePaddingColumns.complements_eq_map]
  simp only [finitePadRequests,List.map_map,Function.comp_def,finitePadRequest]

/-- The original coordinate machines and unchanged finite request fields
produce the exact enlarged-grid request stream. -/
def finitePadRequestsComputableInPolyTime : TM2ComputableInPolyTime id id
    (fun source => GadgetSparseRouteRasterRequestTokens.tokens (finitePadRequests requests units source)) := by
  refine GadgetSparseRouteRasterRequestTokens.RequestAssembly.computableInPolyTimeOf
    id (finitePadRequests requests units)
    (paddedGridCompiler requests units gridCompiler)
    (paddedHorizontalCompiler requests units horizontalCompiler unitCompiler)
    (paddedVerticalCompiler requests units verticalCompiler unitCompiler) ?_ ?_
  · apply TM2ComputableInPolyTime.of_eq colorCompiler
    intro source
    simp only [finitePadRequests,List.map_map,Function.comp_def,finitePadRequest_color]
  · apply TM2ComputableInPolyTime.of_eq normalizationCompiler
    intro source
    simp only [finitePadRequests,List.map_map,Function.comp_def,finitePadRequest_normalization]
end LeanTrominoes.PeriodicCNFStripReduction.RouteRasterRequest
