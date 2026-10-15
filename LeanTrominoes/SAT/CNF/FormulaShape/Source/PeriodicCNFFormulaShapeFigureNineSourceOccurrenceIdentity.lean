/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case0
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case1
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case2
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case3
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case4
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case5
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case6
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case7
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case8
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case9
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case10
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case11
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case12
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case13
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case14
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case15
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case16
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case17
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case18
import LeanTrominoes.SAT.CNF.FormulaShape.Source.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentityCertificates.Case19

/-! # Equality of occurrence-local identities and global source coordinates -/

namespace LeanTrominoes.PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail

open FormulaShapeDirectionOrdering
open FormulaShapeFigureNinePolarityRouteHeader
open FormulaShapeFigureNineRoutePrefix
open FormulaShapeRetainedFigureNineSourceTail

private theorem sourcePrefixRoundtripCheck_first_correct
    (first : UnaryProgramClauseProfile.LiteralProfile) (direction : AxisDirection) :
    firstDirectedProfileCheck sourcePrefixRoundtripCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact sourcePrefixRoundtripCheck_case0
  · exact sourcePrefixRoundtripCheck_case1
  · exact sourcePrefixRoundtripCheck_case2
  · exact sourcePrefixRoundtripCheck_case3
  · exact sourcePrefixRoundtripCheck_case4
  · exact sourcePrefixRoundtripCheck_case5
  · exact sourcePrefixRoundtripCheck_case6
  · exact sourcePrefixRoundtripCheck_case7
  · exact sourcePrefixRoundtripCheck_case8
  · exact sourcePrefixRoundtripCheck_case9
  · exact sourcePrefixRoundtripCheck_case10
  · exact sourcePrefixRoundtripCheck_case11
  · exact sourcePrefixRoundtripCheck_case12
  · exact sourcePrefixRoundtripCheck_case13
  · exact sourcePrefixRoundtripCheck_case14
  · exact sourcePrefixRoundtripCheck_case15
  · exact sourcePrefixRoundtripCheck_case16
  · exact sourcePrefixRoundtripCheck_case17
  · exact sourcePrefixRoundtripCheck_case18
  · exact sourcePrefixRoundtripCheck_case19

private theorem sourcePrefixRoundtripCheck_correct (profile : DirectedClauseProfile) :
    sourcePrefixRoundtripCheck profile = true :=
  firstDirectedProfileCheck_sound sourcePrefixRoundtripCheck
    sourcePrefixRoundtripCheck_first_correct profile

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
  have checked := sourcePrefixRoundtripCheck_correct profile
  unfold sourcePrefixRoundtripCheck at checked
  have firstFields := of_decide_eq_true
    (List.all_eq_true.mp checked first firstMember)
  have secondFields := of_decide_eq_true
    (List.all_eq_true.mp checked second secondMember)
  constructor
  · intro equal
    exact Prod.mk.inj (firstFields.1.symm.trans
      ((congrArg sourceOccurrencePrefixCoordinates equal).trans secondFields.1))
  · intro equal
    exact firstFields.2.symm.trans
      ((congrArg (sourceOccurrencePrefixAtCoordinates profile) (Prod.ext equal.1 equal.2)).trans secondFields.2)

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
