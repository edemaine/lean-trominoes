/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRecordQuerySemantics
import LeanTrominoes.PeriodicOrthocrossingBendFallbackRouteTailRecordBlockRouteSemantics

/-! # Direct bend fallback record-route alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRecordRouteStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendRecordRouteVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceFinalBendFallbackPrefixWords_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackPrefixWords decider symbols =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).flatMap
          BendFallbackRouteTailRecords.Geometry.prefixWords := by
  unfold directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries
    directSourceFinalBendFallbackPrefixWords
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro routeBend _routeBendMember
  rfl

/-- The complete compiled bend route words are exactly the four routes
stored in every declarative bend fallback record block. -/
theorem directSourceFinalBendFallbackRouteDirections_eq_blockRoutes
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackRouteDirections decider symbols =
      BinaryRouteTailRecordProfileFraming.blockRoutes
        (directSourceFinalBendFallbackRecordBlocks decider symbols) := by
  rw [directSourceFinalBendFallbackRouteDirections_eq_geometric]
  unfold directSourceFinalBendFallbackGeometricDirections
  rw [directSourceFinalBendFallbackPrefixWords_eq_geometries,
    directSourceFinalBendFallbackSemanticQueries_eq_queryBlocks]
  unfold directSourceFinalBendFallbackRecordBlocks
  exact
    (BendFallbackRouteTailRecords.blockRoutes_blocks
      (directSourceFinalBendFallbackRecordGeometries decider symbols)
      (directSourceFinalBendOccurrenceSlots decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
