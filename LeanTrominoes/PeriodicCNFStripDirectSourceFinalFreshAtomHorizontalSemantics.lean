/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFreshAtomIdentity
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSourceIndexedAtomsHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData

/-! # Fresh numeric identities agree with actual horizontal atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The global polarity descriptor projected from one coherent occurrence. -/
def sourceOccurrencePolarityDescriptor (occurrence : SourceOccurrence) : SourceIndexedDescriptor :=
  sourceIndexedDescriptorOf occurrence.generatedClauseIndex occurrence.header.polarity.indexed

private theorem sourceOccurrencePolarityDescriptor_fresh
    (occurrence : SourceOccurrence) (fresh : sourceOccurrenceIsFresh occurrence) :
    (sourceOccurrencePolarityDescriptor occurrence).operation = .incompatible ∨
      (sourceOccurrencePolarityDescriptor occurrence).operation = .complementFresh := by
  simpa only [sourceOccurrencePolarityDescriptor, sourceIndexedDescriptorOf,
    PeriodicCNF.ClauseProfilePolarityRouteOperation.Descriptor.indexed,
    sourceOccurrenceIsFresh] using fresh

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance freshHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance freshHorizontalVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The same coherent records now supply both compiled identities and the
entire actual horizontal atom column, with no missing source lookups. -/
theorem directSourceFinalOccurrences_map_atom_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).map
        (fun occurrence => (sourceOccurrencePolarityDescriptor occurrence).atom?
          (refinedSource (directSourceFinalGaugedFormula decider symbols)
            (directSourceFinalGaugedPlacement decider symbols)).erase) =
      (horizontalRoutedFormulaComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map some := by
  have identified := directFigureNinePolarityRoutePairs_sourceIndexedAtoms_eq_horizontal decider symbols
  rw [← directSourceFinalOccurrences_map_generatedClauseIndex,
    ← directSourceFinalOccurrences_map_pair, List.zipWith_map, List.zipWith_self,
    List.map_map] at identified
  simpa only [sourceOccurrencePolarityDescriptor, SourceOccurrence.pair,
    PeriodicCNF.variableOccurrences, List.map_flatMap, List.map_map, Function.comp_def] using identified

/-- At each genuine incidence, decoding its coherent record retrieves the
actual horizontal atom at that same presentation index. -/
theorem directSourceFinalOccurrence_atom_eq_of_horizontal_lookup
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (atom : RoutedVariable)
    (atomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    (sourceOccurrencePolarityDescriptor (directSourceFinalOccurrences decider symbols)[index]).atom?
        (refinedSource (directSourceFinalGaugedFormula decider symbols)
          (directSourceFinalGaugedPlacement decider symbols)).erase = some atom := by
  have lookup := congrArg (fun values => values[index]?)
    (directSourceFinalOccurrences_map_atom_eq_horizontal decider symbols)
  simp only [List.getElem?_map, List.getElem?_eq_getElem indexLt,
    Option.map_some, atomLookup] at lookup
  exact Option.some.inj lookup

/-- On genuine fresh incidences, equality of complete compiled atom codes
is precisely equality of the actual horizontal source variables. -/
theorem directSourceFinalAtomIdentityCodes_fresh_eq_iff_horizontalAtoms
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[firstIndex])
    (secondFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex])
    (firstAtom secondAtom : RoutedVariable)
    (firstLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]? = some firstAtom)
    (secondLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]? = some secondAtom) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      firstAtom = secondAtom := by
  rw [directSourceFinalAtomIdentityCodes_fresh_eq_iff_sourceIndex
    decider symbols firstIndex secondIndex firstLt secondLt firstFresh secondFresh]
  have semantic := SourceIndexedDescriptor.fresh_atom_eq_iff
    (refinedSource (directSourceFinalGaugedFormula decider symbols)
      (directSourceFinalGaugedPlacement decider symbols)).erase
    (sourceOccurrencePolarityDescriptor (directSourceFinalOccurrences decider symbols)[firstIndex])
    (sourceOccurrencePolarityDescriptor (directSourceFinalOccurrences decider symbols)[secondIndex])
    (sourceOccurrencePolarityDescriptor_fresh _ firstFresh)
    (sourceOccurrencePolarityDescriptor_fresh _ secondFresh) firstAtom secondAtom
    (directSourceFinalOccurrence_atom_eq_of_horizontal_lookup decider symbols firstIndex firstLt firstAtom firstLookup)
    (directSourceFinalOccurrence_atom_eq_of_horizontal_lookup decider symbols secondIndex secondLt secondAtom secondLookup)
  simpa only [sourceOccurrencePolarityDescriptor, sourceIndexedDescriptorOf,
    SourceOccurrence.sourceIndex] using semantic.symm

end LeanTrominoes.PeriodicCNFStripReduction

end
