/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Computation.Encoding.Binary.BinaryRouteTailRecordBatchFormatterSemantics
import LeanTrominoes.SAT.CNF.PeriodicCNFIncidenceRouteDescriptorBendGeometry
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendFallbackRecordQuerySemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteDirectionSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Bend.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackRouteTailRecordData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.Graphs.Drawings.Orthogonal.Bend.PeriodicOrthocrossingBendNormalizedFallbackRouteTailRecordBlockSemantics

/-! # Direct normalized bend fallback record-route alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalBendNormalizedRecordRouteVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceFinalBendNormalizedFallbackPrefixWords_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackPrefixWords decider symbols =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).flatMap
          BendFallbackRouteTailRecords.Geometry.prefixWords := by
  exact (directSourceFinalBendFallbackRecordGeometry_prefixWords
    decider symbols).symm

private theorem directSourceFinalBendNormalizedFallbackGeometries_different
    (symbols : List encoding.Γ) :
    ∀ geometry ∈ directSourceFinalBendFallbackRecordGeometries
        decider symbols,
      geometry.firstPort ≠ geometry.secondPort := by
  intro geometry geometryMember
  unfold directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries at geometryMember
  rcases List.mem_flatMap.mp geometryMember with
    ⟨descriptor, descriptorMember, geometryMember⟩
  rcases List.mem_map.mp geometryMember with
    ⟨routeBend, routeBendMember, geometryEq⟩
  subst geometry
  exact
    (PeriodicCNF.numericRouteDescriptor_routeBend_cornerGeometry
      (directSourceFormula decider symbols)
      (PeriodicCNF.incidenceGraph_isWellFormed _)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols)
      (by
        unfold directSourceFormula
        exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _))
      descriptorMember (0, 0) routeBendMember).portsDifferent

/-- The complete normalized bend compiler stream is exactly the four-route
projection of the direct normalized declarative blocks. -/
theorem directSourceFinalBendNormalizedFallbackRouteDirections_eq_blockRoutes
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackRouteDirections decider symbols =
      BinaryRouteTailRecordProfileFraming.blockRoutes
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) := by
  rw [directSourceFinalBendNormalizedFallbackRouteDirections_eq_geometric]
  unfold directSourceFinalBendNormalizedFallbackGeometricDirections
    directSourceFinalBendPreCancellationGeometricDirections
  rw [directSourceFinalBendNormalizedFallbackPrefixWords_eq_geometries,
    directSourceFinalBendFallbackSemanticQueries_eq_queryBlocks]
  unfold directSourceFinalBendNormalizedFallbackRecordBlocks
  exact
    (BendNormalizedFallbackRouteTailRecords.blockRoutes_blocks
      (directSourceFinalBendFallbackRecordGeometries decider symbols)
      (directSourceFinalBendOccurrenceSlots decider symbols)
      (directSourceFinalBendNormalizedFallbackGeometries_different
        decider symbols)).symm

/-- Normalization changes only route fields, so the direct bend block profile
stream agrees with the existing raw declarative blocks. -/
theorem directSourceFinalBendNormalizedFallbackRecordBlockProfiles_eq
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalBendNormalizedFallbackRecordBlocks
          decider symbols) =
      BinaryRouteTailRecordProfileFraming.blockProfiles
        (directSourceFinalBendFallbackRecordBlocks decider symbols) := by
  unfold directSourceFinalBendNormalizedFallbackRecordBlocks
    directSourceFinalBendFallbackRecordBlocks
  exact BendNormalizedFallbackRouteTailRecords.blockProfiles_blocks _ _

/-- The fixed batch formatter serializes the named normalized bend blocks. -/
@[simp] theorem directSourceFinalBendNormalizedFallbackRecordFormatter_output
    (symbols : List encoding.Γ) :
    BinaryRouteTailRecordBatchFormatter.output
        (directSourceFinalBendNormalizedFallbackRecordInputTokens
          decider symbols) =
      directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
        decider symbols := by
  unfold directSourceFinalBendNormalizedFallbackRecordInputTokens
    directSourceFinalBendNormalizedFallbackRouteTailRecordTokens
  exact BinaryRouteTailRecordBatchFormatter.output_tokens _

end LeanTrominoes.PeriodicCNFStripReduction

end
