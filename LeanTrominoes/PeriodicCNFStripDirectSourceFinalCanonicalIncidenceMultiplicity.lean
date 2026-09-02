/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFlatMapAligned
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceOccurrenceKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceElementCodeCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseIncidenceMultiplicity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceVariableElementMultiplicity

/-! # Complete canonical incidence multiplicities -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PlanarThreeDM PeriodicPlanarOneInThreeToThreeDM

/-- Pointwise degree expansion of aligned element-code and degree columns. -/
def degreeExpandedElementCodes
    (codes degrees : List Nat) : List Nat :=
  (List.zipWith (fun code degree => List.replicate degree code)
    codes degrees).flatten

theorem countedExpandedElementCodes_zip_eq_degreeExpanded
    (codes degrees : List Nat) :
    CountedContractedIncidence.expandedElementCodes (codes.zip degrees) =
      degreeExpandedElementCodes codes degrees := by
  unfold CountedContractedIncidence.expandedElementCodes
    degreeExpandedElementCodes
  exact (List.zipWith_flatten_eq_pair_flatMap
    (fun code degree => List.replicate degree code)
    codes degrees).symm

theorem degreeExpandedElementCodes_append
    (firstCodes secondCodes firstDegrees secondDegrees : List Nat)
    (aligned : firstCodes.length = firstDegrees.length) :
    degreeExpandedElementCodes
        (firstCodes ++ secondCodes) (firstDegrees ++ secondDegrees) =
      degreeExpandedElementCodes firstCodes firstDegrees ++
        degreeExpandedElementCodes secondCodes secondDegrees := by
  unfold degreeExpandedElementCodes
  rw [List.zipWith_append_of_length_eq
    (fun code degree => List.replicate degree code)
    firstCodes secondCodes firstDegrees secondDegrees aligned,
    List.flatten_append]

private theorem degreeExpandedElementCodes_eq_duplicate_of_all_two
    (codes degrees : List Nat)
    (aligned : codes.length = degrees.length)
    (allTwo : ∀ degree ∈ degrees, degree = 2) :
    degreeExpandedElementCodes codes degrees =
      duplicateElementCodes codes := by
  induction codes generalizing degrees with
  | nil =>
      have degreesNil : degrees = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using aligned.symm)
      subst degrees
      rfl
  | cons code codes induction =>
      cases degrees with
      | nil => simp at aligned
      | cons degree degrees =>
          have degreeEq : degree = 2 := allTwo degree (by simp)
          have tailAligned : codes.length = degrees.length := by
            simpa using Nat.succ.inj aligned
          have tailTwo : ∀ other ∈ degrees, other = 2 := by
            intro other member
            exact allTwo other (by simp [member])
          subst degree
          change [code, code] ++
              degreeExpandedElementCodes codes degrees =
            [code, code] ++ duplicateElementCodes codes
          rw [induction degrees tailAligned tailTwo]

private theorem directSourceFinalVariableElementDegrees_all_two
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (symbols : List encoding.Γ) :
    ∀ degree ∈ directSourceFinalVariableElementDegrees decider symbols,
      degree = 2 := by
  intro degree member
  unfold directSourceFinalVariableElementDegrees
    FiniteUnaryFieldBlockMap.values at member
  simp only [List.mem_flatMap] at member
  obtain ⟨pair, _pairMember, localMember⟩ := member
  cases kindEq : pair.1.kind (groupedVariableFanSiteSlot pair.2) <;>
    simp [directSourceFinalVariableElementDegreeBlock, kindEq] at localMember <;>
    exact localMember

private theorem directSourceFinalVariableDegreeExpanded_eq_duplicate
    {Input : Type} {encoding : _root_.Computability.FinEncoding Input}
    {language : Input → Prop}
    (decider : Complexity.DeciderInPolySpace encoding language)
    (color : WireColor) (symbols : List encoding.Γ) :
    degreeExpandedElementCodes
        (directSourceFinalCanonicalVariableElementCodes
          decider color symbols)
        (directSourceFinalVariableElementDegrees decider symbols) =
      duplicateElementCodes
        (directSourceFinalCanonicalVariableElementCodes
          decider color symbols) := by
  exact degreeExpandedElementCodes_eq_duplicate_of_all_two _ _
    (directSourceFinalCanonicalVariableElementCodes_length
      decider color symbols)
    (directSourceFinalVariableElementDegrees_all_two decider symbols)

private theorem degreeExpandedElementCodes_flatMap
    {First Second : Type*}
    (firstBlock : First → List Nat)
    (secondBlock : Second → List Nat)
    (blockLengths : ∀ first second,
      (firstBlock first).length = (secondBlock second).length) :
    ∀ (firsts : List First) (seconds : List Second),
      degreeExpandedElementCodes
          (firsts.flatMap firstBlock) (seconds.flatMap secondBlock) =
        (List.zipWith
          (fun first second => degreeExpandedElementCodes
            (firstBlock first) (secondBlock second))
          firsts seconds).flatten
  | [], _ => rfl
  | _ :: _, [] => by simp [degreeExpandedElementCodes]
  | first :: firsts, second :: seconds => by
      simp only [List.flatMap_cons, List.zipWith_cons_cons,
        List.flatten_cons]
      rw [degreeExpandedElementCodes_append _ _ _ _
        (blockLengths first second),
        degreeExpandedElementCodes_flatMap firstBlock secondBlock
          blockLengths firsts seconds]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

private theorem directSourceFinalClauseIndexPlaceholders_length_eq_fans
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIndexPlaceholders decider symbols).length =
      (directSourceFinalClauseFans decider symbols).length := by
  simp [directSourceFinalClauseIndexPlaceholders,
    FiniteUnaryFieldBlockMap.values,
    directSourceFinalClauseIndexPlaceholderBlock]

private theorem directSourceFinalClauseColorDegreeExpanded_eq_blocks
    (color : WireColor) (symbols : List encoding.Γ) :
    degreeExpandedElementCodes
        (directSourceFinalClauseElementCodes decider color symbols)
        (directSourceFinalClauseElementDegrees decider symbols) =
      (List.zipWith
        (finalClauseCanonicalExpandedElementCodeColorBlock color)
        (List.range (directSourceFinalClauseFans decider symbols).length)
        (directSourceFinalClauseFans decider symbols)).flatten := by
  rw [directSourceFinalClauseElementCodes_eq_flatMap]
  rw [directSourceFinalClauseIndexPlaceholders_length_eq_fans]
  unfold directSourceFinalClauseElementDegrees
    FiniteUnaryFieldBlockMap.values
  exact degreeExpandedElementCodes_flatMap
    (directSourceFinalClauseElementCodeBlock color)
    directSourceFinalClauseElementDegreeBlock
    (fun index fan => by
      simp [directSourceFinalClauseElementCodeBlock])
    (List.range (directSourceFinalClauseFans decider symbols).length)
    (directSourceFinalClauseFans decider symbols)

/-- The clause-major RGB block presentation is a permutation of the three
color-major canonical clause degree expansions. -/
theorem directSourceFinalClauseExpandedElementCodes_perm_colorMajor
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseExpandedElementCodes decider symbols).Perm
      (degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .red symbols)
          (directSourceFinalClauseElementDegrees decider symbols) ++
        degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .green symbols)
          (directSourceFinalClauseElementDegrees decider symbols) ++
        degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .blue symbols)
          (directSourceFinalClauseElementDegrees decider symbols)) := by
  let indices :=
    List.range (directSourceFinalClauseFans decider symbols).length
  let fans := directSourceFinalClauseFans decider symbols
  unfold directSourceFinalClauseExpandedElementCodes
    finalClauseCanonicalExpandedElementCodeBlock
  apply (List.zipWith_flatten_append3_perm
    (finalClauseCanonicalExpandedElementCodeColorBlock .red)
    (finalClauseCanonicalExpandedElementCodeColorBlock .green)
    (finalClauseCanonicalExpandedElementCodeColorBlock .blue)
    indices fans).trans
  rw [← directSourceFinalClauseColorDegreeExpanded_eq_blocks,
    ← directSourceFinalClauseColorDegreeExpanded_eq_blocks,
    ← directSourceFinalClauseColorDegreeExpanded_eq_blocks]

private theorem sixBlockVariableClause_perm_colorMajor
    (variableRed variableGreen variableBlue
      clauseRed clauseGreen clauseBlue : List Nat) :
    ((variableRed ++ variableGreen ++ variableBlue) ++
        (clauseRed ++ clauseGreen ++ clauseBlue)).Perm
      ((variableRed ++ clauseRed) ++
        (variableGreen ++ clauseGreen) ++
        (variableBlue ++ clauseBlue)) := by
  have moveClauseRed :
      ((variableGreen ++ variableBlue) ++ clauseRed).Perm
        (clauseRed ++ variableGreen ++ variableBlue) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm :
        ((variableGreen ++ variableBlue) ++ clauseRed).Perm
          (clauseRed ++ (variableGreen ++ variableBlue)))
  have first :
      ((variableRed ++ variableGreen ++ variableBlue) ++
          (clauseRed ++ clauseGreen ++ clauseBlue)).Perm
        (variableRed ++ clauseRed ++ variableGreen ++ variableBlue ++
          clauseGreen ++ clauseBlue) := by
    simpa only [List.append_assoc] using
      (moveClauseRed.append_right (clauseGreen ++ clauseBlue)
        |>.append_left variableRed)
  have moveClauseGreen :
      (variableBlue ++ clauseGreen).Perm
        (clauseGreen ++ variableBlue) := List.perm_append_comm
  have second :
      (variableRed ++ clauseRed ++ variableGreen ++ variableBlue ++
          clauseGreen ++ clauseBlue).Perm
        ((variableRed ++ clauseRed) ++
          (variableGreen ++ clauseGreen) ++
          (variableBlue ++ clauseBlue)) := by
    simpa only [List.append_assoc] using
      (moveClauseGreen.append_right clauseBlue
        |>.append_left (variableRed ++ clauseRed ++ variableGreen))
  exact first.trans second

private theorem degreeExpandedElementCodes_threeColors
    (redVariable redClause greenVariable greenClause
      blueVariable blueClause variableDegrees clauseDegrees : List Nat)
    (redVariableLength : redVariable.length = variableDegrees.length)
    (greenVariableLength : greenVariable.length = variableDegrees.length)
    (blueVariableLength : blueVariable.length = variableDegrees.length)
    (redClauseLength : redClause.length = clauseDegrees.length)
    (greenClauseLength : greenClause.length = clauseDegrees.length)
    (_blueClauseLength : blueClause.length = clauseDegrees.length) :
    degreeExpandedElementCodes
        ((redVariable ++ redClause) ++
          (greenVariable ++ greenClause) ++
          (blueVariable ++ blueClause))
        ((variableDegrees ++ clauseDegrees) ++
          (variableDegrees ++ clauseDegrees) ++
          (variableDegrees ++ clauseDegrees)) =
      (degreeExpandedElementCodes redVariable variableDegrees ++
          degreeExpandedElementCodes redClause clauseDegrees) ++
        (degreeExpandedElementCodes greenVariable variableDegrees ++
          degreeExpandedElementCodes greenClause clauseDegrees) ++
        (degreeExpandedElementCodes blueVariable variableDegrees ++
          degreeExpandedElementCodes blueClause clauseDegrees) := by
  rw [degreeExpandedElementCodes_append _ _ _ _ (by
      simp only [List.length_append]
      omega),
    degreeExpandedElementCodes_append _ _ _ _ (by
      simp only [List.length_append]
      omega),
    degreeExpandedElementCodes_append _ _ _ _ redVariableLength,
    degreeExpandedElementCodes_append _ _ _ _ greenVariableLength,
    degreeExpandedElementCodes_append _ _ _ _ blueVariableLength]

private theorem directSourceFinalCanonicalElementCodes_eq_sixBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementCodes decider symbols =
      (directSourceFinalCanonicalVariableElementCodes
          decider .red symbols ++
        directSourceFinalClauseElementCodes decider .red symbols) ++
      (directSourceFinalCanonicalVariableElementCodes
          decider .green symbols ++
        directSourceFinalClauseElementCodes decider .green symbols) ++
      (directSourceFinalCanonicalVariableElementCodes
          decider .blue symbols ++
        directSourceFinalClauseElementCodes decider .blue symbols) := by
  simp [directSourceFinalCanonicalElementCodes,
    directSourceFinalGreenBlueElementCodes,
    directSourceFinalOneColorElementCodes, List.append_assoc]

private theorem directSourceFinalCanonicalElementDegrees_eq_sixBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalElementDegrees decider symbols =
      (directSourceFinalVariableElementDegrees decider symbols ++
        directSourceFinalClauseElementDegrees decider symbols) ++
      (directSourceFinalVariableElementDegrees decider symbols ++
        directSourceFinalClauseElementDegrees decider symbols) ++
      (directSourceFinalVariableElementDegrees decider symbols ++
        directSourceFinalClauseElementDegrees decider symbols) := by
  rw [directSourceFinalCanonicalElementDegrees_eq_three_colors]
  simp [directSourceFinalOneColorElementDegrees, List.append_assoc]

private theorem directSourceFinalCanonicalDegreeExpansion_eq_colorBlocks
    (symbols : List encoding.Γ) :
    CountedContractedIncidence.expandedElementCodes
        ((directSourceFinalCanonicalElementCodes decider symbols).zip
          (directSourceFinalCanonicalElementDegrees decider symbols)) =
      (degreeExpandedElementCodes
          (directSourceFinalCanonicalVariableElementCodes
            decider .red symbols)
          (directSourceFinalVariableElementDegrees decider symbols) ++
        degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .red symbols)
          (directSourceFinalClauseElementDegrees decider symbols)) ++
      (degreeExpandedElementCodes
          (directSourceFinalCanonicalVariableElementCodes
            decider .green symbols)
          (directSourceFinalVariableElementDegrees decider symbols) ++
        degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .green symbols)
          (directSourceFinalClauseElementDegrees decider symbols)) ++
      (degreeExpandedElementCodes
          (directSourceFinalCanonicalVariableElementCodes
            decider .blue symbols)
          (directSourceFinalVariableElementDegrees decider symbols) ++
        degreeExpandedElementCodes
          (directSourceFinalClauseElementCodes decider .blue symbols)
          (directSourceFinalClauseElementDegrees decider symbols)) := by
  rw [countedExpandedElementCodes_zip_eq_degreeExpanded,
    directSourceFinalCanonicalElementCodes_eq_sixBlocks,
    directSourceFinalCanonicalElementDegrees_eq_sixBlocks]
  exact degreeExpandedElementCodes_threeColors _ _ _ _ _ _ _ _
    (directSourceFinalCanonicalVariableElementCodes_length
      decider .red symbols)
    (directSourceFinalCanonicalVariableElementCodes_length
      decider .green symbols)
    (directSourceFinalCanonicalVariableElementCodes_length
      decider .blue symbols)
    (directSourceFinalClauseElementCodes_length decider .red symbols)
    (directSourceFinalClauseElementCodes_length decider .green symbols)
    (directSourceFinalClauseElementCodes_length decider .blue symbols)

/-- The complete independently compiled incidence identity column is a
permutation of the canonical element-code column expanded by its aligned
degree column. -/
theorem directSourceFinalCanonicalIncidenceElementCodes_perm_expanded
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceElementCodes
        decider symbols).Perm
      (CountedContractedIncidence.expandedElementCodes
        ((directSourceFinalCanonicalElementCodes decider symbols).zip
          (directSourceFinalCanonicalElementDegrees decider symbols))) := by
  let variableRed :=
    directSourceFinalCanonicalVariableElementCodes decider .red symbols
  let variableGreen :=
    directSourceFinalCanonicalVariableElementCodes decider .green symbols
  let variableBlue :=
    directSourceFinalCanonicalVariableElementCodes decider .blue symbols
  let variableDegrees :=
    directSourceFinalVariableElementDegrees decider symbols
  let clauseRed := degreeExpandedElementCodes
    (directSourceFinalClauseElementCodes decider .red symbols)
    (directSourceFinalClauseElementDegrees decider symbols)
  let clauseGreen := degreeExpandedElementCodes
    (directSourceFinalClauseElementCodes decider .green symbols)
    (directSourceFinalClauseElementDegrees decider symbols)
  let clauseBlue := degreeExpandedElementCodes
    (directSourceFinalClauseElementCodes decider .blue symbols)
    (directSourceFinalClauseElementDegrees decider symbols)
  have variablePerm :
      (directSourceFinalExpectedVariableIncidenceElementCodes
          decider symbols).Perm
        (degreeExpandedElementCodes variableRed variableDegrees ++
          degreeExpandedElementCodes variableGreen variableDegrees ++
          degreeExpandedElementCodes variableBlue variableDegrees) := by
    apply (directSourceFinalExpectedVariableIncidenceElementCodes_perm_canonical
      decider symbols).trans
    unfold variableRed variableGreen variableBlue variableDegrees
    rw [show duplicateElementCodes
          (directSourceFinalCanonicalVariableElementCodes
              decider .red symbols ++
            directSourceFinalCanonicalVariableElementCodes
              decider .green symbols ++
            directSourceFinalCanonicalVariableElementCodes
              decider .blue symbols) =
          duplicateElementCodes
              (directSourceFinalCanonicalVariableElementCodes
                decider .red symbols) ++
            duplicateElementCodes
              (directSourceFinalCanonicalVariableElementCodes
                decider .green symbols) ++
            duplicateElementCodes
              (directSourceFinalCanonicalVariableElementCodes
                decider .blue symbols) by
        unfold duplicateElementCodes
        rw [List.flatMap_append, List.flatMap_append],
      ← directSourceFinalVariableDegreeExpanded_eq_duplicate,
      ← directSourceFinalVariableDegreeExpanded_eq_duplicate,
      ← directSourceFinalVariableDegreeExpanded_eq_duplicate]
  have sourceParts :
      (directSourceFinalCanonicalIncidenceElementCodes
          decider symbols).Perm
        (directSourceFinalExpectedVariableIncidenceElementCodes
            decider symbols ++
          (directSourceFinalClauseIncidenceElementCodes decider symbols ++
            directSourceFinalExpectedParentIncidenceElementCodes
              decider symbols)) := by
    unfold directSourceFinalCanonicalIncidenceElementCodes
    apply ((directSourceFinalVariableIncidenceElementCodes_perm_components
      decider symbols).append_right
        (directSourceFinalClauseIncidenceElementCodes
          decider symbols)).trans
    have swapped :
        (directSourceFinalExpectedParentIncidenceElementCodes
            decider symbols ++
          directSourceFinalClauseIncidenceElementCodes
            decider symbols).Perm
          (directSourceFinalClauseIncidenceElementCodes
              decider symbols ++
            directSourceFinalExpectedParentIncidenceElementCodes
              decider symbols) := List.perm_append_comm
    simpa only [List.append_assoc] using
      (swapped.append_left
          (directSourceFinalExpectedVariableIncidenceElementCodes
            decider symbols))
  apply sourceParts.trans
  apply (List.Perm.append variablePerm
    (directSourceFinalClauseAndParentIncidenceElementCodes_perm_canonical
      decider symbols)).trans
  apply (List.Perm.append (List.Perm.refl _)
    (directSourceFinalClauseExpandedElementCodes_perm_colorMajor
      decider symbols)).trans
  apply (sixBlockVariableClause_perm_colorMajor
    (degreeExpandedElementCodes variableRed variableDegrees)
    (degreeExpandedElementCodes variableGreen variableDegrees)
    (degreeExpandedElementCodes variableBlue variableDegrees)
    clauseRed clauseGreen clauseBlue).trans
  rw [directSourceFinalCanonicalDegreeExpansion_eq_colorBlocks]

end LeanTrominoes.PeriodicCNFStripReduction

end
