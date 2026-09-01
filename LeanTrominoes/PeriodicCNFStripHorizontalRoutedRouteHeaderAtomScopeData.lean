/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderOccurrenceSemantics

/-! # Global-scope controls for finite routed-header atoms -/

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeader

open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix

/-- A final atom either inherits one of the parent clause's source variables,
or is scoped to the parent clause itself.  The latter branch retains the
finite control needed to compare two atoms within that parent. -/
inductive AtomScopeControl
  | inherited (sourceSlot : SourceLiteralSlot)
  | parentLocal (control : AtomControl)
  deriving DecidableEq, Fintype, Inhabited

/-- Explicit parent-relative atom represented by a finite atom control. -/
def AtomControl.representedAtom : AtomControl → ParentRelativeAtom
  | .original sourceOccurrence => .inl (prefixAtom sourceOccurrence)
  | .fresh sourceOccurrence => .inr sourceOccurrence

/-- Genuine inherited source atoms expose their source-literal slot; all
Figure 9 auxiliaries and polarity fresh variables remain parent-local. -/
def ParentRelativeAtom.inheritedSourceSlot? :
    ParentRelativeAtom → Option SourceLiteralSlot
  | .inl atom => sourceSlot? atom
  | .inr _ => none

def AtomControl.inheritedSourceSlot?
    (control : AtomControl) : Option SourceLiteralSlot :=
  control.representedAtom.inheritedSourceSlot?

/-- Finite global-scope classification of one atom control. -/
def AtomControl.scopeControl (control : AtomControl) : AtomScopeControl :=
  match control.inheritedSourceSlot? with
  | some sourceSlot => .inherited sourceSlot
  | none => .parentLocal control

/-- Scope classification carried by one final routed header. -/
def outputAtomScopeControl (header : Header) : AtomScopeControl :=
  (outputAtomControl header).scopeControl

/-- Scope classification carried by an already projected occurrence record. -/
def OccurrenceData.atomScopeControl
    (occurrence : OccurrenceData) : AtomScopeControl :=
  occurrence.atomControl.scopeControl

/-- The finite control represents exactly the explicit parent-relative atom
previously assigned to the header. -/
@[simp] theorem outputAtomControl_representedAtom (header : Header) :
    (outputAtomControl header).representedAtom =
      outputParentRelativeAtom header := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  cases operation <;> rfl

/-- Thus the scope control selects precisely the genuine inherited source
slot, using the complete finite atom control for every parent-local case. -/
theorem outputAtomScopeControl_eq (header : Header) :
    outputAtomScopeControl header =
      match (outputParentRelativeAtom header).inheritedSourceSlot? with
      | some sourceSlot => .inherited sourceSlot
      | none => .parentLocal (outputAtomControl header) := by
  rcases header with ⟨⟨sourceSlot, operation⟩, figurePrefix⟩
  cases operation <;> rfl

@[simp] theorem occurrenceData_atomScopeControl (header : Header) :
    (occurrenceData header).atomScopeControl =
      outputAtomScopeControl header :=
  rfl

end HorizontalRoutedRouteHeader
end PeriodicCNFStripReduction
end LeanTrominoes
