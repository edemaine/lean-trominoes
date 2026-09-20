/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFInjectiveRenaming
import LeanTrominoes.PeriodicThreeSATThreeForwardLocal
import LeanTrominoes.PeriodicThreeSATThreeOccurrences
import LeanTrominoes.PeriodicThreeSATThreeCorrectness
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationSemantics

/-! # Compact natural atom names for the three-occurrence reduction -/
namespace LeanTrominoes.PeriodicThreeSATThree.Numeric
open PeriodicCNF

local instance : BEq (ThreeOccurrenceVariable Nat) := instBEqOfDecidableEq

def atomMap (source : PeriodicCNF Nat) : ThreeOccurrenceVariable Nat → Nat :=
  supportedNatCode (PeriodicThreeSATThree.formula source).variableOccurrences.dedup

def formula (source : PeriodicCNF Nat) : PeriodicCNF Nat :=
  (PeriodicThreeSATThree.formula source).rename (atomMap source)

theorem satisfiable_iff (source : PeriodicCNF Nat) : (formula source).Satisfiable ↔ source.Satisfiable := by
  have inj : Function.Injective (atomMap source) := supportedNatCode_injective _
  rw [formula,satisfiable_rename_iff (atomMap source) _ inj]
  exact (PeriodicThreeSATThree.satisfiable_iff source).symm

theorem width_three (source : PeriodicCNF Nat) (width : source.WidthAtMost 3) :
    (formula source).WidthAtMost 3 := by
  rw [formula,width_rename]
  exact formula_widthAtMostThree width

theorem occurrences_three (source : PeriodicCNF Nat) : (formula source).OccurrencesAtMost 3 := by
  apply occurrences_rename (atomMap source) _ (supportedNatCode_injective _) 3
  exact occurrencesAtMost_congr_beq _ _ _ _ _ _ (formula_occurrencesAtMostThree source)

theorem forward (source : PeriodicCNF Nat) (h : source.IsForwardLocal) :
    (formula source).IsForwardLocal := by
  have split := formula_isForwardLocal h
  simpa [formula,rename,renameClause,IsForwardLocal,PeriodicLiteral.IsForwardLocal,
    PeriodicLiteral.rename] using split

theorem target_atoms (source : PeriodicCNF Nat) :
    (splitRouteDescriptors source).map PeriodicOrthocrossing.RouteDescriptor.targetVertexIndex =
      (formula source).variableOccurrences := by
  rw [← numericRouteDescriptors_formula_eq_splitRouteDescriptors]
  simp only [numericRouteDescriptors,List.map_map,Function.comp_def,CNFIncidence.numericRouteDescriptor]
  rw [show (List.map (fun tagged =>
      (PeriodicThreeSATThree.formula source).variableOccurrences.dedup.idxOf tagged.1.literal.atom)
      (incidencesWithMetadata (PeriodicThreeSATThree.formula source)).zipIdx) =
    ((incidencesWithMetadata (PeriodicThreeSATThree.formula source)).zipIdx.map Prod.fst).map
      (fun i => (PeriodicThreeSATThree.formula source).variableOccurrences.dedup.idxOf i.literal.atom) by
        simp only [List.map_map,Function.comp_def]]
  rw [List.zipIdx_map_fst]
  rw [show (incidencesWithMetadata (PeriodicThreeSATThree.formula source)).map
      (fun i => (PeriodicThreeSATThree.formula source).variableOccurrences.dedup.idxOf i.literal.atom) =
      ((incidencesWithMetadata (PeriodicThreeSATThree.formula source)).map (fun i => i.literal.atom)).map
        (fun a => (PeriodicThreeSATThree.formula source).variableOccurrences.dedup.idxOf a) by
      simp only [List.map_map,Function.comp_def]]
  rw [incidencesWithMetadata_atoms,formula,variableOccurrences_rename]
  apply List.map_congr_left
  intro atom ha
  simp [atomMap,supportedNatCode,ha]

end LeanTrominoes.PeriodicThreeSATThree.Numeric
