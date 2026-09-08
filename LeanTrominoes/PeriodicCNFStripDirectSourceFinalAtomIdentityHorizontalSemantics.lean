/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalInheritedAtomHorizontalSemantics

/-! # Complete numeric identities agree with actual horizontal atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open HorizontalRoutedRouteHeader

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance identityHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance identityHorizontalVariableDecidableEq : DecidableEq Variable := directSourceVariableDecidableEq

/-- The complete identity compiler induces exactly the actual horizontal atom
partition, across both parent phases and all fresh, auxiliary, and inherited roles. -/
theorem directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstAtom secondAtom : RoutedVariable)
    (firstLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]? = some firstAtom)
    (secondLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]? = some secondAtom) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      firstAtom = secondAtom := by
  by_cases firstFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[firstIndex]
  · exact directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_fresh
      decider symbols firstIndex secondIndex firstLt secondLt firstFresh
      firstAtom secondAtom firstLookup secondLookup
  by_cases secondFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex]
  · have swapped := directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_fresh
      decider symbols secondIndex firstIndex secondLt firstLt secondFresh
      secondAtom firstAtom secondLookup firstLookup
    exact eq_comm.trans (swapped.trans eq_comm)
  cases firstSelected : sourceSlot?
      (prefixAtom (directSourceFinalOccurrences decider symbols)[firstIndex].header.figurePrefix) with
  | none =>
      exact directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_auxiliary
        decider symbols firstIndex secondIndex firstLt secondLt ⟨firstFresh, firstSelected⟩
        firstAtom secondAtom firstLookup secondLookup
  | some firstSlot =>
      cases secondSelected : sourceSlot?
          (prefixAtom (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix) with
      | none =>
          have swapped := directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_auxiliary
            decider symbols secondIndex firstIndex secondLt firstLt ⟨secondFresh, secondSelected⟩
            secondAtom firstAtom secondLookup firstLookup
          exact eq_comm.trans (swapped.trans eq_comm)
      | some secondSlot =>
          exact directSourceFinalAtomIdentityCodes_inherited_eq_iff_horizontalAtoms
            decider symbols firstIndex secondIndex _ _
            (List.getElem?_eq_getElem firstLt) (List.getElem?_eq_getElem secondLt)
            firstFresh secondFresh firstSlot secondSlot firstSelected secondSelected
            firstAtom secondAtom firstLookup secondLookup

end LeanTrominoes.PeriodicCNFStripReduction

end
