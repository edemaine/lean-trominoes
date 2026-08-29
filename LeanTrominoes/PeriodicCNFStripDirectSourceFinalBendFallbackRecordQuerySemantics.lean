/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackRouteTailRecordData
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnSemantics

/-! # Direct bend fallback record-query alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendRecordQueryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendRecordQueryVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem bend_alignedQueries_terminalBlocks
    (geometries : List BendFallbackRouteTailRecords.Geometry)
    (slots : List RetainedTerminalSlot)
    (lengthEq : slots.length = 4 * geometries.length) :
    let terminals := geometries.flatMap fun geometry =>
      bendRouteTerminalDataBlock geometry.firstPort geometry.secondPort
    FallbackSuffixQueries.alignedQueries
        (List.replicate terminals.length .ordinary)
        terminals slots =
      BendFallbackRouteTailRecords.queryBlocks geometries slots := by
  induction geometries generalizing slots with
  | nil =>
      have slotsNil : slots = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      subst slots
      rfl
  | cons geometry geometries induction =>
      rcases slots with _ | ⟨first, slots⟩
      · simp at lengthEq
      rcases slots with _ | ⟨second, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨third, slots⟩
      · simp at lengthEq
        omega
      rcases slots with _ | ⟨fourth, slots⟩
      · simp at lengthEq
        omega
      have tailLength : slots.length = 4 * geometries.length := by
        simp only [List.length_cons] at lengthEq
        omega
      simp only [List.flatMap_cons, bendRouteTerminalDataBlock,
        List.length_append, List.length_cons, List.length_nil]
      let terminals := geometries.flatMap fun geometry =>
        bendRouteTerminalDataBlock geometry.firstPort geometry.secondPort
      change
        FallbackSuffixQueries.alignedQueries
            (List.replicate (4 + terminals.length) .ordinary)
            ([bendRouteTerminalData
                geometry.firstPort geometry.secondPort 0 0,
              bendRouteTerminalData
                geometry.firstPort geometry.secondPort 0 1,
              bendRouteTerminalData
                geometry.firstPort geometry.secondPort 1 0,
              bendRouteTerminalData
                geometry.firstPort geometry.secondPort 1 1] ++ terminals)
            (first :: second :: third :: fourth :: slots) =
          BendFallbackRouteTailRecords.queryBlocks
            (geometry :: geometries)
            (first :: second :: third :: fourth :: slots)
      rw [List.replicate_add]
      change
        BendFallbackRouteTailRecords.queryBlock geometry
              first second third fourth ++
            FallbackSuffixQueries.alignedQueries
              (List.replicate terminals.length .ordinary)
              terminals
              slots =
          BendFallbackRouteTailRecords.queryBlock geometry
              first second third fourth ++
            BendFallbackRouteTailRecords.queryBlocks geometries slots
      rw [induction slots tailLength]

private theorem directSourceFinalBendFallbackTerminalData_eq_geometries
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackTerminalData decider symbols =
      (directSourceFinalBendFallbackRecordGeometries
        decider symbols).flatMap fun geometry =>
          bendRouteTerminalDataBlock
            geometry.firstPort geometry.secondPort := by
  unfold directSourceFinalBendFallbackTerminalData baseBendTerminalData
    directSourceFinalBendFallbackRecordGeometries
    BendFallbackRouteTailRecords.selectedGeometries
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro descriptor _descriptorMember
  rw [List.flatMap_map]

/-- The ordinary-policy bend query stream consumes the same four final
occurrence slots per bend as the declarative record blocks. -/
theorem directSourceFinalBendFallbackSemanticQueries_eq_queryBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalBendFallbackSemanticQueries decider symbols =
      BendFallbackRouteTailRecords.queryBlocks
        (directSourceFinalBendFallbackRecordGeometries decider symbols)
        (directSourceFinalBendOccurrenceSlots decider symbols) := by
  unfold directSourceFinalBendFallbackSemanticQueries
  rw [directSourceFinalBendFallbackTerminalData_eq_geometries]
  exact bend_alignedQueries_terminalBlocks _ _
    (directSourceFinalBendFallbackRecordSlots_length decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
