/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteDirectionRasterCursor
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionData

/-! # Raster-cursor form of direct sparse route records

This removes the last geometric coordinate carried by the finite-direction
route cursor.  Each edge block now depends only on its strip period, finite
color, rasterized source location, and final direction word.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeDM
namespace NormalizationCompiler

open PeriodicCNFStripReduction

/-- One final route record block streamed from its already-rasterized source
location. -/
def finalNormalizationRouteRasterDirectionRecordBlock
    (input : Input) (edge : ContractedEdge) :
    List GadgetSparseAssignmentTokens.Token :=
  let period := finalNormalizationPeriod input
  sparseRouteRecordBlocksFromRasterDirections period edge.color
    (stripRasterLocation period
      (finalNormalizationPosition input edge.toPeriodicEdge.source))
    (finalNormalizationRouteDirections input edge)

/-- Raster-coordinate and geometric-coordinate direction cursors emit the
same canonical block, without any validity hypothesis. -/
theorem finalNormalizationRouteRasterDirectionRecordBlock_eq
    (input : Input) (edge : ContractedEdge) :
    finalNormalizationRouteRasterDirectionRecordBlock input edge =
      finalNormalizationRouteDirectionRecordBlock input edge := by
  unfold finalNormalizationRouteRasterDirectionRecordBlock
    finalNormalizationRouteDirectionRecordBlock
  exact sparseRouteRecordBlocksFromRasterDirections_eq _ _ _ _

end NormalizationCompiler
end PeriodicThreeDM

namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteRasterDirectionDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Edge-major direct route records in executable raster-cursor form. -/
def directSparseComputedRouteRasterDirectionRecordsOfSymbols
    (symbols : List encoding.Γ) :
    List GadgetSparseAssignmentTokens.Token :=
  let input := directSparseComputedNormalizationInputOfSymbols decider symbols
  input.problem.contractedEdges.flatMap fun edge =>
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock
      input edge

/-- The raster-cursor target is definitionally independent per edge and
equals the established finite-direction target. -/
theorem directSparseComputedRouteRasterDirectionRecordsOfSymbols_eq
    (symbols : List encoding.Γ) :
    directSparseComputedRouteRasterDirectionRecordsOfSymbols decider symbols =
      directSparseComputedRouteDirectionRecordsOfSymbols decider symbols := by
  unfold directSparseComputedRouteRasterDirectionRecordsOfSymbols
    directSparseComputedRouteDirectionRecordsOfSymbols
  apply List.flatMap_congr
  intro edge _
  exact
    PeriodicThreeDM.NormalizationCompiler.finalNormalizationRouteRasterDirectionRecordBlock_eq
      _ edge

end PeriodicCNFStripReduction
end LeanTrominoes

end
