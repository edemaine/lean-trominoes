/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case0
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case1
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case2
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case3
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case4
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case5
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case6
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case7
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case8
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case9
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case10
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case11
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case12
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case13
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case14
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case15
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case16
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case17
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case18
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalRoutedRouteHeaderLocalOccurrenceBoundCertificates.Case19

/-! # Local final-atom occurrence bounds in one routed parent block -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderPresentationAtomScope

open PeriodicCNF.FormulaShapeDirectionOrdering
open HorizontalRoutedRouteHeader

private theorem localOccurrenceBoundsCheck_first_correct
    (first : LeanTrominoes.PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile)
    (direction : AxisDirection) : firstDirectedProfileCheck localOccurrenceBoundsCheck first direction = true := by
  rcases first with ⟨nextSlice, value⟩
  cases nextSlice <;> cases value <;> cases direction
  · exact localOccurrenceBoundsCheck_case0
  · exact localOccurrenceBoundsCheck_case1
  · exact localOccurrenceBoundsCheck_case2
  · exact localOccurrenceBoundsCheck_case3
  · exact localOccurrenceBoundsCheck_case4
  · exact localOccurrenceBoundsCheck_case5
  · exact localOccurrenceBoundsCheck_case6
  · exact localOccurrenceBoundsCheck_case7
  · exact localOccurrenceBoundsCheck_case8
  · exact localOccurrenceBoundsCheck_case9
  · exact localOccurrenceBoundsCheck_case10
  · exact localOccurrenceBoundsCheck_case11
  · exact localOccurrenceBoundsCheck_case12
  · exact localOccurrenceBoundsCheck_case13
  · exact localOccurrenceBoundsCheck_case14
  · exact localOccurrenceBoundsCheck_case15
  · exact localOccurrenceBoundsCheck_case16
  · exact localOccurrenceBoundsCheck_case17
  · exact localOccurrenceBoundsCheck_case18
  · exact localOccurrenceBoundsCheck_case19

private theorem localOccurrenceBoundsCheck_correct (profile : DirectedClauseProfile) :
    localOccurrenceBoundsCheck profile = true :=
  firstDirectedProfileCheck_sound localOccurrenceBoundsCheck localOccurrenceBoundsCheck_first_correct profile

/-- Every genuine clause descriptor expands to a nonempty final occurrence
block, so the parent-index prefix sum advances exactly once per clause. -/
theorem clauseBlock_length_pos (profile : DirectedClauseProfile) :
    0 < (clauseBlock profile).length := by
  have checked := localOccurrenceBoundsCheck_correct profile
  simp only [localOccurrenceBoundsCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.1

/-- As above, the checker scans only atoms that occur in its finite block. -/
private theorem parentLocalAtoms_count_check
    (profile : DirectedClauseProfile) :
    (parentLocalAtoms profile).all fun atom =>
      decide ((parentLocalAtoms profile).count atom <= 3) := by
  have checked := localOccurrenceBoundsCheck_correct profile
  simp only [localOccurrenceBoundsCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.1.2

/-- Quotienting the several descriptors that can represent the same local
atom still leaves multiplicity at most three. -/
theorem parentLocalAtoms_count_le_three
    (profile : DirectedClauseProfile) (atom : ParentRelativeAtom) :
    (parentLocalAtoms profile).count atom <= 3 := by
  by_cases member : atom ∈ parentLocalAtoms profile
  · have checked :=
      (List.all_eq_true.mp (parentLocalAtoms_count_check profile))
        atom member
    simpa only [decide_eq_true_eq] using checked
  · rw [List.count_eq_zero_of_not_mem member]
    omega

/-- Canonical quotient codes at the same parent-local positions. -/
noncomputable def parentLocalCodes (profile : DirectedClauseProfile) :
    List ParentLocalAtomCode :=
  (clauseBlock profile).filterMap fun scope =>
    match scope with
    | .inherited _ => none
    | .parentLocal control => some (parentLocalAtomCode control)

private theorem parentLocalCodes_count_mk
    (profile : DirectedClauseProfile) (control : AtomControl) :
    (parentLocalCodes profile).count (parentLocalAtomCode control) =
      (parentLocalAtoms profile).count control.representedAtom := by
  unfold parentLocalCodes parentLocalAtoms
  generalize clauseBlock profile = scopes
  induction scopes with
  | nil => rfl
  | cons scope scopes induction =>
      cases scope with
      | inherited sourceSlot =>
          simpa using induction
      | parentLocal current =>
          by_cases representedEq :
              current.representedAtom = control.representedAtom
          · have codeEq :
                parentLocalAtomCode current =
                  parentLocalAtomCode control :=
              (parentLocalAtomCode_eq_iff current control).mpr representedEq
            simp [codeEq, representedEq, induction]
          · have codeNe :
                parentLocalAtomCode current ≠
                  parentLocalAtomCode control := by
              exact fun equality => representedEq
                ((parentLocalAtomCode_eq_iff current control).mp equality)
            simp [codeNe, representedEq, induction]

/-- The canonical local quotient used by the numeric compiler preserves the
same at-most-three bound. -/
theorem parentLocalCodes_count_le_three
    (profile : DirectedClauseProfile) (code : ParentLocalAtomCode) :
    (parentLocalCodes profile).count code <= 3 := by
  refine Quotient.inductionOn code (fun control => ?_)
  change
    (parentLocalCodes profile).count (parentLocalAtomCode control) <= 3
  rw [parentLocalCodes_count_mk]
  exact parentLocalAtoms_count_le_three profile control.representedAtom

/-- The finite checker only scans controls that actually occur in the
selected block.  This avoids enumerating the much larger ambient descriptor
alphabet. -/
private theorem clauseBlock_local_count_check
    (profile : DirectedClauseProfile) :
    (clauseBlock profile).all fun scope =>
      match scope with
      | .inherited _ => true
      | .parentLocal control =>
          decide
            ((clauseBlock profile).count (.parentLocal control) <= 3) := by
  have checked := localOccurrenceBoundsCheck_correct profile
  simp only [localOccurrenceBoundsCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact checked.2

/-- Every parent-local Figure 9 or polarity-normalization atom occurs at most
three times in the final routed block generated by one source clause. -/
theorem clauseBlock_count_parentLocal_le_three
    (profile : DirectedClauseProfile) (control : AtomControl) :
    (clauseBlock profile).count (.parentLocal control) <= 3 := by
  by_cases member :
      AtomScopeControl.parentLocal control ∈ clauseBlock profile
  · have checked :=
      (List.all_eq_true.mp (clauseBlock_local_count_check profile))
        (.parentLocal control) member
    simpa only [decide_eq_true_eq] using checked
  · rw [List.count_eq_zero_of_not_mem member]
    omega

end HorizontalRoutedRouteHeaderPresentationAtomScope
end PeriodicCNFStripReduction
end LeanTrominoes
