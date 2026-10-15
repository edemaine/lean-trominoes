/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteProgramNormalizationFacts
import LeanTrominoes.Tiling.Tromino.Finite.FiniteNormalizationVertexPaddingCompiler
import LeanTrominoes.Tiling.Tromino.Finite.FiniteNormalizationRoutePaddingCompiler
import LeanTrominoes.Tiling.Tromino.Finite.FiniteNormalizationRegionCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Vertex.PeriodicCNFStripDirectSourceFinalVertexRecordCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Route.PeriodicCNFStripDirectSourceFinalRouteRasterRequestCompiler
import LeanTrominoes.Computation.TM2.TM2EmptyAlphabetListInputCompiler

/-! # Unconditional original-source polynomial-time finite tromino reduction -/
noncomputable section
namespace LeanTrominoes.FiniteProgramSparseTrominoRegion
open _root_.Computability Turing Gadget PeriodicCNF PeriodicCNFStripReduction
open PeriodicThreeDM.NormalizationCompiler
variable {Source : Type} {encoding : FiniteEncoding Source} {language : Source → Prop}
variable (source : ProgramSource encoding language)
variable (zero : ∀ symbols,FiniteCNF.ZeroOffsets (source.formulaOfSymbols symbols))

private theorem gridUnits_length (symbols : List encoding.Γ) :
    (directDrawingGridUnitsOfSymbols source symbols).length=(inputs source symbols).drawing.gridSize :=
  directDrawingGridUnitsOfSymbols_length source symbols

private def paddedVertexCompiler [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id
    (fun symbols => (paddedInputs source symbols).problem.contractedGraph.vertices.flatMap
      (sparseBoundedInputVertexRequestRecord (paddedInputs source symbols))) :=
  FiniteNormalizationVertexPaddingCompiler.computableInPolyTime (inputs source)
    (directDrawingGridUnitsOfSymbols source) (gridUnits_length source)
    (inputs_zero source zero) (inputs_vertexLength source) (inputs_vertexBounds source)
    (directSparseAffineVertexRequestTokenCompiler source)
    (directDrawingGridUnitsOfSymbolsComputableInPolyTime source)

private def originalNormalizationCompiler : TM2ComputableInPolyTime id id
    (fun symbols => PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens
      ((FiniteNormalizationRoutePaddingCompiler.requests (inputs source) symbols).map
        (fun request => request.normalization))) := by
  apply TM2ComputableInPolyTime.of_eq (directSparseRouteDirectionRequestTokenCompiler source)
  intro symbols
  change directSparseRouteDirectionRequestTokensOfSymbols source symbols=
    PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens
      ((RouteRasterRequest.directSparseRouteRasterRequestsOfSymbols source symbols).map
        (fun request => request.normalization))
  rw [directSparseRasterRequests_normalization_eq]
  rfl

private def paddedRouteCompiler [Inhabited encoding.Γ] : TM2ComputableInPolyTime id id
    (fun symbols => GadgetSparseRouteRasterRequestTokens.tokens
      ((paddedInputs source symbols).problem.contractedEdges.map
        (RouteRasterRequest.ofEdge (paddedInputs source symbols)))) :=
  FiniteNormalizationRoutePaddingCompiler.computableInPolyTime (inputs source)
    (directDrawingGridUnitsOfSymbols source) (gridUnits_length source)
    (inputs_zero source zero) (inputs_vertexLength source) (inputs_vertexBounds source)
    (directSourceFinalRasterGridFieldsComputableInPolyTime source)
    (directSourceFinalRasterHorizontalCoordinatesComputableInPolyTime source)
    (directSourceFinalRasterVerticalFieldsComputableInPolyTime source)
    (directSourceFinalRasterColorFieldsComputableInPolyTime source)
    (originalNormalizationCompiler source)
    (directDrawingGridUnitsOfSymbolsComputableInPolyTime source)

/-- The canonical finite drawing records are emitted directly from source symbols. -/
def assignmentTokensComputableInPolyTime [Inhabited encoding.Γ] :
    TM2ComputableInPolyTime id id (fun symbols =>
      GadgetSparseAssignmentTokens.assignmentsTokens (assignments source symbols)) :=
  FiniteSparseAssignmentSeamCompiler.ofEmitter id
    (fun symbols => finalStripCellAssignments (paddedInputs source symbols))
    (FiniteNormalizationRegionCompiler.assignmentsComputableInPolyTime id (paddedInputs source)
      (paddedInputs_vertexBounds source) (paddedInputs_routeConditions source zero)
      (paddedVertexCompiler source zero) (paddedRouteCompiler source zero))
    (paddedAssignments_positive source zero)

/-- All padding, normalization, sparse records, seam movement, and gadget
pixels are compiled by finite-alphabet machines in polynomial time. -/
def regionOfSymbolsComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime id Tromino.FiniteCoordinateColumns.regionEncoding.encode (regionOfSymbols source t) := by
  classical
  by_cases nonempty : Nonempty encoding.Γ
  · letI : Inhabited encoding.Γ := ⟨Classical.choice nonempty⟩
    exact FiniteNormalizationRegionCompiler.regionComputableInPolyTime id (paddedInputs source)
      (paddedInputs_vertexBounds source) (paddedInputs_routeConditions source zero)
      (paddedVertexCompiler source zero) (paddedRouteCompiler source zero) t
      (paddedAssignments_positive source zero)
  · letI : Inhabited Tromino.FiniteCoordinateColumns.regionEncoding.Γ := ⟨Tromino.FiniteCoordinateColumns.Token.bit false⟩
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonempty ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      Tromino.FiniteCoordinateColumns.regionEncoding.encode (regionOfSymbols source t)

/-- The time bound is measured against the original input encoding. -/
def regionComputableInPolyTime (t : Tromino) :
    TM2ComputableInPolyTime encoding.encode Tromino.FiniteCoordinateColumns.regionEncoding.encode (region source t) :=
  TM2PolyTimeInputEncodingTransport.of_prepare encoding.encode
    (regionOfSymbolsComputableInPolyTime source zero t) (fun _ => rfl) (fun _ => rfl)
end LeanTrominoes.FiniteProgramSparseTrominoRegion
