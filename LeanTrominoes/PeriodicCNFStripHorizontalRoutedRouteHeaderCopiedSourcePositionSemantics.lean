/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionCompiler
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Semantics of copied-clause compact-source positions -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderCopiedSourcePosition

open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader

abbrev sourceWordCount :=
  HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount

def totalSourceWordCount : List Token → Nat
  | [] => 0
  | .variable :: source => totalSourceWordCount source
  | .clause profile :: source =>
      sourceWordCount profile + totalSourceWordCount source

def expectedStartsAux : Nat → List Token → List Nat
  | _, [] => []
  | start, .variable :: source => expectedStartsAux start source
  | start, .clause profile :: source =>
      let count :=
        (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
          (.clause profile)).length
      List.replicate count start ++
        expectedStartsAux (start + sourceWordCount profile) source

def expectedStarts (source : List Token) : List Nat :=
  expectedStartsAux 0 source

/-- Direct clause-wise semantics of every compact-source query. -/
def expectedAux : Nat → List Token → List Nat
  | _, [] => []
  | start, .variable :: source => expectedAux start source
  | start, .clause profile :: source =>
      ((HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
        profile).map fun control => start + scopeOffset control) ++
          expectedAux (start + sourceWordCount profile) source

def expected (source : List Token) : List Nat :=
  expectedAux 0 source

@[simp] theorem sourceWordCount_pos (profile : DirectedClauseProfile) :
    0 < sourceWordCount profile := by
  cases profile <;>
    simp [sourceWordCount,
      HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount,
      PeriodicCNF.FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals]

/-- The total fallback in presentation-slot lookup is always a genuine slot
of the nonempty source clause. -/
private theorem presentationTaggedLiteral_slot_lt
    (profile : DirectedClauseProfile)
    (tagged : HorizontalRoutedRouteHeaderPresentationAtomScope.TaggedLiteral)
    (member : tagged ∈
      HorizontalRoutedRouteHeaderPresentationAtomScope.presentationTaggedLiterals
        profile) :
    sourceSlotNat tagged.2 < sourceWordCount profile := by
  rcases tagged with ⟨literal, slot⟩
  cases profile <;> cases slot <;>
    simp_all
      [HorizontalRoutedRouteHeaderPresentationAtomScope.presentationTaggedLiterals,
        sourceWordCount,
        HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount,
        PeriodicCNF.FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
        sourceSlotNat]

private theorem orderedPresentationSlot_lt
    (profile : DirectedClauseProfile) (slot : SourceLiteralSlot)
    (member : slot ∈
      HorizontalRoutedRouteHeaderPresentationAtomScope.orderedPresentationSlots
        profile) :
    sourceSlotNat slot < sourceWordCount profile := by
  unfold HorizontalRoutedRouteHeaderPresentationAtomScope.orderedPresentationSlots
    HorizontalRoutedRouteHeaderPresentationAtomScope.orderedTaggedLiterals at member
  obtain ⟨tagged, taggedMember, rfl⟩ := List.mem_map.mp member
  apply presentationTaggedLiteral_slot_lt profile tagged
  exact (List.mem_insertionSort
    (r := HorizontalRoutedRouteHeaderPresentationAtomScope.taggedDirectionLE)).mp
      taggedMember

theorem presentationSlotAt_lt
    (profile : DirectedClauseProfile) (slot : SourceLiteralSlot) :
    sourceSlotNat
        (HorizontalRoutedRouteHeaderPresentationAtomScope.presentationSlotAt
          profile slot) <
      sourceWordCount profile := by
  unfold HorizontalRoutedRouteHeaderPresentationAtomScope.presentationSlotAt
  by_cases indexLt : sourceSlotNat slot <
      (HorizontalRoutedRouteHeaderPresentationAtomScope.orderedPresentationSlots
        profile).length
  · rw [List.getD_eq_getElem _ _ indexLt]
    exact orderedPresentationSlot_lt profile _ (List.getElem_mem indexLt)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt indexLt)]
    cases profile <;>
      simp [sourceWordCount,
        HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount,
        PeriodicCNF.FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
        sourceSlotNat]

/-- Every copied source clause expands to at least one final occurrence, so
its ending source advance is always represented in the aligned stream. -/
private theorem polarityDescriptors_ne_nil
    (profile : PeriodicCNF.UnaryProgramClauseProfile.ClauseProfile) :
    PeriodicCNF.ClauseProfilePolarityRouteOperation.descriptors profile ≠
      [] := by
  cases profile <;>
    simp [PeriodicCNF.ClauseProfilePolarityRouteOperation.descriptors,
      PeriodicCNF.ClauseProfilePolarityRouteOperation.clauseRouteBlocks]

private theorem figureClauseProfiles_ne_nil
    (profile : DirectedClauseProfile) :
    figureClauseProfiles profile ≠ [] := by
  cases profile <;>
    simp [figureClauseProfiles,
      PeriodicCNF.FormulaShapeFigureNineRoutePrefix.clauseProfile,
      PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile,
      PlanarOneInThreeNoUnitsFigureNine.oneDrawingFor,
      PlanarOneInThreeNoUnitsFigureNine.twoDrawingFor,
      PlanarOneInThreeNoUnitsFigureNine.fullDrawingFor,
      PlanarOneInThreeNoUnitsFigureNine.oneFormulaFor,
      PlanarOneInThreeNoUnitsFigureNine.twoFormulaFor,
      PlanarOneInThreeNoUnitsFigureNine.fullFormulaFor]

private theorem headers_ne_nil
    (profiles : List PeriodicCNF.UnaryProgramClauseProfile.ClauseProfile)
    (profilesNe : profiles ≠ [])
    (prefixes : List
      PeriodicCNF.FormulaShapeFigureNineRoutePrefix.Descriptor) :
    headers profiles prefixes ≠ [] := by
  cases profiles with
  | nil => contradiction
  | cons profile profiles =>
      simp only [headers]
      apply List.append_ne_nil_of_left_ne_nil
      unfold clauseHeaders
      apply List.ne_nil_of_length_pos
      rw [List.length_map]
      exact List.length_pos_iff_ne_nil.mpr
        (polarityDescriptors_ne_nil profile)

theorem clauseOccurrenceCount_pos (profile : DirectedClauseProfile) :
    0 < (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
      (.clause profile)).length := by
  rw [HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock_clause,
    List.length_map]
  apply List.length_pos_iff_ne_nil.mpr
  unfold sourceClauseHeaders
  apply headers_ne_nil
  exact figureClauseProfiles_ne_nil
    (PeriodicCNF.FormulaShapeFigureNineRoutePrefix.orderedDirectedProfile
      profile)

private theorem startsAux_replicate_zero_append
    (start count : Nat) (remaining : List Nat) :
    PrefixSums.startsAux start
        (List.replicate count 0 ++ remaining) =
      List.replicate count start ++
        PrefixSums.startsAux start remaining := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [List.replicate_succ, List.cons_append,
        PrefixSums.startsAux_cons]
      simp only [Nat.add_zero]
      rw [induction, List.replicate_succ]
      simp

private theorem startsAux_endingAdvances_append
    (start count : Nat) (advance : SourceAdvance)
    (remaining : List Nat) :
    PrefixSums.startsAux start
        ((endingAdvances (count + 1) advance).map SourceAdvance.toNat ++
          remaining) =
      List.replicate (count + 1) start ++
        PrefixSums.startsAux (start + advance.toNat) remaining := by
  rw [show (endingAdvances (count + 1) advance).map
        SourceAdvance.toNat =
      List.replicate count 0 ++ [advance.toNat] by
    simp [endingAdvances, List.map_append, SourceAdvance.toNat,
      SourceAdvance.zero]]
  rw [List.append_assoc, startsAux_replicate_zero_append]
  rw [show List.replicate (count + 1) start =
      List.replicate count start ++ [start] by
    simp [List.replicate_add]]
  simp [List.append_assoc]

private theorem startsAux_advances (start : Nat) (source : List Token) :
    PrefixSums.startsAux start (increments source) =
      expectedStartsAux start source := by
  induction source generalizing start with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [increments, advances, tokenAdvances,
            expectedStartsAux, FiniteUnaryFieldMap.values] using
            induction start
      | clause profile =>
          have countPos :
              0 < (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                (.clause profile)).length :=
            clauseOccurrenceCount_pos profile
          obtain ⟨countPred, countEq⟩ := Nat.exists_eq_succ_of_ne_zero
            (Nat.ne_of_gt countPos)
          rw [show increments (.clause profile :: source) =
              (endingAdvances
                    (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                      (.clause profile)).length
                    (profileAdvance profile)).map SourceAdvance.toNat ++
                increments source by
            simp [increments, advances, tokenAdvances,
              FiniteUnaryFieldMap.values, List.map_append]]
          rw [show expectedStartsAux start (.clause profile :: source) =
              List.replicate
                (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                  (.clause profile)).length start ++
              expectedStartsAux
                (start + sourceWordCount profile) source by
            rfl]
          rw [countEq, startsAux_endingAdvances_append,
            induction, profileAdvance_toNat]

/-- Prefix summation repeats the start of each clause's presentation block
at every final occurrence generated from that clause. -/
theorem sourceStarts_eq_expectedStarts (source : List Token) :
    sourceStarts source = expectedStarts source := by
  exact startsAux_advances 0 source

private theorem sums_replicate_map_append
    (start : Nat) (controls : List AtomScopeControl)
    (firsts seconds : List Nat) :
    UnaryAlignedAddMachine.sums
        (List.replicate controls.length start ++ firsts)
        (controls.map scopeOffset ++ seconds) =
      controls.map (fun control => start + scopeOffset control) ++
        UnaryAlignedAddMachine.sums firsts seconds := by
  induction controls with
  | nil => rfl
  | cons control controls induction =>
      simp only [List.length_cons, List.replicate_succ, List.cons_append,
        List.map_cons, UnaryAlignedAddMachine.sums]
      rw [induction]

private theorem sums_expectedStarts_scopeOffsets
    (start : Nat) (source : List Token) :
    UnaryAlignedAddMachine.sums
        (expectedStartsAux start source) (scopeOffsets source) =
      expectedAux start source := by
  induction source generalizing start with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [expectedStartsAux, expectedAux, scopeOffsets,
            FiniteUnaryFieldMap.values,
            HorizontalRoutedRouteHeaderPresentationAtomScope.output,
            HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock]
            using induction start
      | clause profile =>
          let controls :=
            HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
              profile
          rw [show expectedStartsAux start (.clause profile :: source) =
              List.replicate
                  (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                    (.clause profile)).length start ++
                expectedStartsAux
                  (start + sourceWordCount profile) source by
            rfl]
          rw [show scopeOffsets (.clause profile :: source) =
              controls.map scopeOffset ++ scopeOffsets source by
            simp [scopeOffsets, FiniteUnaryFieldMap.values,
              HorizontalRoutedRouteHeaderPresentationAtomScope.output,
              HorizontalRoutedRouteHeaderPresentationAtomScope.tokenBlock,
              controls, List.map_append]]
          rw [show expectedAux start (.clause profile :: source) =
              controls.map (fun control => start + scopeOffset control) ++
                expectedAux (start + sourceWordCount profile) source by
            rfl]
          change UnaryAlignedAddMachine.sums
              (List.replicate
                  (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                    (.clause profile)).length start ++
                expectedStartsAux (start + sourceWordCount profile) source)
              (controls.map scopeOffset ++ scopeOffsets source) = _
          rw [show
              (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
                (.clause profile)).length = controls.length by
            exact (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock_length
              profile).symm]
          rw [sums_replicate_map_append, induction]

/-- The compiled arithmetic column is exactly the direct clause-wise
presentation-position specification. -/
theorem positions_eq_expected (source : List Token) :
    positions source = expected source := by
  unfold positions AlignedUnaryListClosure.added expected
  rw [sourceStarts_eq_expectedStarts]
  exact sums_expectedStarts_scopeOffsets 0 source

theorem scopeOffset_lt (profile : DirectedClauseProfile)
    (control : AtomScopeControl)
    (member : control ∈
      HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile) :
    scopeOffset control < sourceWordCount profile := by
  unfold HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock at member
  obtain ⟨header, _headerMember, rfl⟩ := List.mem_map.mp member
  unfold HorizontalRoutedRouteHeaderPresentationAtomScope.remapScopeControl
  cases scopeEq : outputAtomScopeControl header with
  | inherited sourceSlot =>
      simp [scopeOffset, presentationSlotAt_lt]
  | parentLocal localControl =>
      simp [scopeOffset, sourceWordCount_pos]

theorem expectedAux_forall_lt (start : Nat) (source : List Token) :
    (expectedAux start source).Forall fun position =>
      position < start + totalSourceWordCount source := by
  induction source generalizing start with
  | nil => simp [expectedAux, totalSourceWordCount]
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [expectedAux, totalSourceWordCount] using induction start
      | clause profile =>
          rw [expectedAux]
          rw [List.forall_append]
          constructor
          · rw [List.forall_iff_forall_mem]
            intro position positionMember
            obtain ⟨control, controlMember, rfl⟩ :=
              List.mem_map.mp positionMember
            have offsetLt := scopeOffset_lt profile control controlMember
            have withinClause :
                start + scopeOffset control <
                  start + sourceWordCount profile :=
              Nat.add_lt_add_left offsetLt start
            simpa [totalSourceWordCount, Nat.add_assoc] using
              withinClause.trans_le
                (Nat.le_add_right
                  (start + sourceWordCount profile)
                  (totalSourceWordCount source))
          · simpa [totalSourceWordCount, Nat.add_assoc] using
              induction (start + sourceWordCount profile)

/-- Every compiled query is in range of the compact presentation stream. -/
theorem positions_forall_lt (source : List Token) :
    (positions source).Forall fun position =>
      position < totalSourceWordCount source := by
  rw [positions_eq_expected]
  simpa [expected] using expectedAux_forall_lt 0 source

/-- Select a candidate identity at every compiled source position. -/
def selectedValues (source : List Token)
    (candidateValues : List Nat) : List Nat :=
  UnaryIndexedValueLookup.values (positions source) candidateValues

@[simp] theorem selectedValues_length (source : List Token)
    (candidateValues : List Nat) :
    (selectedValues source candidateValues).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  rw [selectedValues, UnaryIndexedValueLookup.values_length,
    positions_length]

/-- A correctly sized candidate column turns every compiled source-position
query into ordinary zero-based lookup, preserving duplicates and order. -/
theorem selectedValues_eq_map_getD (source : List Token)
    (candidateValues : List Nat)
    (candidateLength : candidateValues.length =
      totalSourceWordCount source) :
    selectedValues source candidateValues =
      (positions source).map fun position =>
        candidateValues.getD position 0 := by
  unfold selectedValues
  apply UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt
  intro position positionMember
  have positionLt := (List.forall_iff_forall_mem.mp
    (positions_forall_lt source)) position positionMember
  simpa [candidateLength] using positionLt

end HorizontalRoutedRouteHeaderCopiedSourcePosition
end PeriodicCNFStripReduction
end LeanTrominoes
