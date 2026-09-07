/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceMetadata

/-! # Equality of occurrence-local identities and global source coordinates -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeRetainedFigureNineSourceTail

private def prefixCoordinates (routePrefix : Descriptor) : Nat × Nat :=
  let query := routePrefix.localQuery
  let drawing := PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile query.1
  let incidence := drawing.incidenceAt query.2
  let arity := ((drawing.formula[incidence.clauseIndex]?).map
    (fun clause => clause.literals.length)).getD 0
  (incidence.clauseIndex,
    match arity with
    | 2 => if incidence.literalIndex = 0 then 1 else 0
    | 3 => if incidence.literalIndex = 0 then 1 else
        if incidence.literalIndex = 1 then 2 else 0
    | _ => incidence.literalIndex)

private def prefixAtCoordinates (profile : DirectedClauseProfile)
    (coordinates : Nat × Nat) : Descriptor :=
  let ordered := orderedDirectedProfile profile
  let profiles := figureClauseProfiles ordered
  let skipped := ((profiles.take coordinates.1).map (fun clause => clause.literals.length)).sum
  let count := ((profiles[coordinates.1]?).map (fun clause => clause.literals.length)).getD 0
  (FormulaShapeFigureNineFinalClauseOrdering.reorderList
    (((clauseDescriptors ordered).drop skipped).take count)).getD coordinates.2 default

private theorem header_prefix_eq_iff_coordinates
    (profile : DirectedClauseProfile)
    (first second : Header)
    (firstMember : first ∈ sourceClauseHeaders profile)
    (secondMember : second ∈ sourceClauseHeaders profile) :
    first.figurePrefix = second.figurePrefix ↔
      (headerTemplateCoordinate first).clauseIndex =
        (headerTemplateCoordinate second).clauseIndex ∧
      first.polarity.indexed.sourceLiteralIndex =
        second.polarity.indexed.sourceLiteralIndex := by
  have checked : ∀ profile : DirectedClauseProfile,
      (sourceClauseHeaders profile).all (fun header => decide (
        let coordinates := ((headerTemplateCoordinate header).clauseIndex,
          header.polarity.indexed.sourceLiteralIndex)
        prefixCoordinates header.figurePrefix = coordinates ∧
          prefixAtCoordinates profile coordinates = header.figurePrefix)) = true := by
    native_decide
  have firstFields := of_decide_eq_true
    (List.all_eq_true.mp (checked profile) first firstMember)
  have secondFields := of_decide_eq_true
    (List.all_eq_true.mp (checked profile) second secondMember)
  constructor
  · intro equal
    exact Prod.mk.inj (firstFields.1.symm.trans
      ((congrArg prefixCoordinates equal).trans secondFields.1))
  · intro equal
    exact firstFields.2.symm.trans
      ((congrArg (prefixAtCoordinates profile) (Prod.ext equal.1 equal.2)).trans secondFields.2)

private theorem sourceOccurrencesFrom_parent_le
    (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection))) (occurrence : SourceOccurrence)
    (member : occurrence ∈ sourceOccurrencesFrom parent start source tails) :
    parent ≤ occurrence.parentClauseIndex := by
  induction source generalizing parent start tails with
  | nil => simp [sourceOccurrencesFrom] at member
  | cons token rest ih =>
      cases token with
      | «variable» => exact ih parent start tails member
      | clause profile =>
          rcases List.mem_append.mp member with head | tail
          · obtain ⟨header, _, rfl⟩ := List.mem_map.mp head
            exact Nat.le_refl _
          · exact Nat.le_trans (Nat.le_succ parent) (ih _ _ _ tail)

/-- A parent index determines the generated-clause start and complete profile
within the common occurrence stream. Equal-looking profiles in different
parents do not merge their identities. -/
theorem sourceOccurrencesFrom_parent_data
    (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection)))
    (first second : SourceOccurrence)
    (firstMember : first ∈ sourceOccurrencesFrom parent start source tails)
    (secondMember : second ∈ sourceOccurrencesFrom parent start source tails)
    (parentEq : first.parentClauseIndex = second.parentClauseIndex) :
    first.generatedClauseStart = second.generatedClauseStart ∧ first.profile = second.profile := by
  induction source generalizing parent start tails with
  | nil => simp [sourceOccurrencesFrom] at firstMember
  | cons token rest ih =>
      cases token with
      | «variable» => exact ih parent start tails firstMember secondMember
      | clause profile =>
          rcases List.mem_append.mp firstMember with firstHead | firstTail <;>
            rcases List.mem_append.mp secondMember with secondHead | secondTail
          · obtain ⟨firstHeader, _, rfl⟩ := List.mem_map.mp firstHead
            obtain ⟨secondHeader, _, rfl⟩ := List.mem_map.mp secondHead
            exact ⟨rfl, rfl⟩
          · obtain ⟨header, _, rfl⟩ := List.mem_map.mp firstHead
            have lower := sourceOccurrencesFrom_parent_le _ _ _ _ _ secondTail
            simp only at parentEq
            omega
          · obtain ⟨header, _, rfl⟩ := List.mem_map.mp secondHead
            have lower := sourceOccurrencesFrom_parent_le _ _ _ _ _ firstTail
            simp only at parentEq
            omega
          · exact ih _ _ _ firstTail secondTail

private theorem sourceOccurrencesFrom_header_mem
    (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection))) (occurrence : SourceOccurrence)
    (member : occurrence ∈ sourceOccurrencesFrom parent start source tails) :
    occurrence.header ∈ sourceClauseHeaders occurrence.profile := by
  induction source generalizing parent start tails with
  | nil => simp [sourceOccurrencesFrom] at member
  | cons token rest ih =>
      cases token with
      | «variable» => exact ih parent start tails member
      | clause profile =>
          rcases List.mem_append.mp member with head | tail
          · obtain ⟨header, headerMember, rfl⟩ := List.mem_map.mp head
            exact headerMember
          · exact ih _ _ _ tail

/-- The local fresh-variable key (parent, finite prefix) is equal precisely
when the two records select the same global source occurrence. -/
theorem sourceOccurrencesFrom_freshKey_eq_iff_sourceIndex
    (parent start : Nat) (source : List Token)
    (tails : List (List (List AxisDirection)))
    (first second : SourceOccurrence)
    (firstMember : first ∈ sourceOccurrencesFrom parent start source tails)
    (secondMember : second ∈ sourceOccurrencesFrom parent start source tails) :
    (first.parentClauseIndex, first.header.figurePrefix) =
        (second.parentClauseIndex, second.header.figurePrefix) ↔
      first.sourceIndex = second.sourceIndex := by
  have firstHeader := sourceOccurrencesFrom_header_mem _ _ _ _ _ firstMember
  have secondHeader := sourceOccurrencesFrom_header_mem _ _ _ _ _ secondMember
  constructor
  · intro keyEq
    have parentEq := congrArg Prod.fst keyEq
    have prefixEq := congrArg Prod.snd keyEq
    obtain ⟨startEq, profileEq⟩ := sourceOccurrencesFrom_parent_data
      parent start source tails first second firstMember secondMember parentEq
    rw [← profileEq] at secondHeader
    obtain ⟨clauseEq, literalEq⟩ := (header_prefix_eq_iff_coordinates
      first.profile first.header second.header firstHeader secondHeader).mp prefixEq
    apply Prod.ext
    · simp only [SourceOccurrence.sourceIndex, SourceOccurrence.generatedClauseIndex,
        SourceOccurrence.metadataKey, startEq, clauseEq]
    · exact literalEq
  · intro indexEq
    have clauseEq := congrArg Prod.fst indexEq
    have literalEq := congrArg Prod.snd indexEq
    have firstKey := (List.mem_zipIdx_iff_le_and_getElem?_sub.mp
      (sourceOccurrencesFrom_metadataKey_mem parent start source tails first firstMember)).2
    have secondKey := (List.mem_zipIdx_iff_le_and_getElem?_sub.mp
      (sourceOccurrencesFrom_metadataKey_mem parent start source tails second secondMember)).2
    have metadataEq : first.metadataKey = second.metadataKey := by
      change first.generatedClauseIndex = second.generatedClauseIndex at clauseEq
      rw [clauseEq] at firstKey
      exact Option.some.inj (firstKey.symm.trans secondKey)
    have parentEq := congrArg Prod.fst metadataEq
    have localClauseEq := congrArg Prod.snd metadataEq
    have profileEq := (sourceOccurrencesFrom_parent_data
      parent start source tails first second firstMember secondMember parentEq).2
    rw [← profileEq] at secondHeader
    exact Prod.ext parentEq ((header_prefix_eq_iff_coordinates
      first.profile first.header second.header firstHeader secondHeader).mpr
        ⟨localClauseEq, literalEq⟩)

end LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
