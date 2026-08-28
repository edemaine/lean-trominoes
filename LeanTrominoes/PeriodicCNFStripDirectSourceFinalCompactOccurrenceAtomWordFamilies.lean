/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeBaseBendAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeCarrierAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRoutedClauseAtomWordSemantics
import LeanTrominoes.PeriodicCNFRouteDescriptorSourceTerminalCompactAtomWordPresentation
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCompactOccurrenceAtomWordData
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableAtomWordSemantics

/-! # Five compact blocks of direct final occurrence atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCompactAtomWordFamiliesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCompactAtomWordFamiliesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Fixed crossover-role compact atom words, one Figure 8(b) block per
canonical crossing in the exact last-occurrence halo order. -/
def directSourceFinalCompactCrossoverAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := directSourceFinalCompactAtomWord formula
  (canonicalizedCrossingHalo formula.incidenceGraph).flatMap fun crossing =>
    crossoverFormula.flatMap fun clause =>
      clause.literals.map fun literal =>
        word ⟨normalizedCrossoverAtom crossing literal.1⟩

/-- Repeated compact normalized endpoint words of every retained carrier
link. -/
def directSourceFinalCompactCarrierAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := directSourceFinalCompactAtomWord formula
  ((retainedDrawingCompleteCarrierLinks formula.incidenceGraph).map
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization formula))).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- Repeated compact normalized endpoint words of every canonical base
bend. -/
def directSourceFinalCompactBendAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := directSourceFinalCompactAtomWord formula
  (baseBendNormalizedLinks formula).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- Compact source-terminal atom rows projected directly from the
presentation-ordered route descriptors. -/
def directSourceFinalCompactRoutedClauseAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  (RouteDescriptorSourceTerminalCompactWords.words
    (PeriodicCNF.numericRouteDescriptors formula)).words

/-- Repeated compact normalized endpoint words of every canonical final-site
routed-variable link. -/
def directSourceFinalCompactRoutedVariableAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := directSourceFinalCompactAtomWord formula
  (PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableLinks
      source).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- The exact five-family compact atom-word target, retaining the append tree
of the duplicate-free final clause presentation. -/
def directSourceFinalFiveFamilyCompactAtomWordBlocks
    (symbols : List encoding.Γ) : List (List Bool) :=
  (directSourceFinalCompactCrossoverAtomWordBlock decider symbols ++
    directSourceFinalCompactCarrierAtomWordBlock decider symbols) ++
  ((directSourceFinalCompactBendAtomWordBlock decider symbols ++
    directSourceFinalCompactRoutedClauseAtomWordBlock decider symbols) ++
    directSourceFinalCompactRoutedVariableAtomWordBlock decider symbols)

/-- The complete final compact occurrence word column is exactly the
concatenation of the five explicit physical blocks above. -/
theorem directSourceFinalCompactOccurrenceAtomWords_eq_blocks
    (symbols : List encoding.Γ) :
    (directSourceFinalCompactOccurrenceAtomWords decider symbols).words =
      directSourceFinalFiveFamilyCompactAtomWordBlocks decider symbols := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  let formula := PeriodicThreeSATThree.formula source
  have sourceLocal : source.IsLocal := by
    apply PeriodicThreeCNF.formula_isLocal
    exact (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have sourceWidth : source.WidthAtMost 3 :=
    PeriodicThreeCNF.formula_widthAtMostThree original
  have occurrenceDecidableEqEq :
      directFinalCompactAtomWordFamiliesVariableDecidableEq =
        (PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq :
          DecidableEq Variable) :=
    Subsingleton.elim _ _
  rw [directSourceFinalCompactOccurrenceAtomWords_eq_fiveFamilies,
    directSourceFormula_eq_threeSATThree]
  unfold directSourceFinalFiveFamilyClauses
    directThreeCNFSourceFormula
    directSourceFinalFiveFamilyCompactAtomWordBlocks
    directSourceFinalCompactCrossoverAtomWordBlock
    directSourceFinalCompactCarrierAtomWordBlock
    directSourceFinalCompactBendAtomWordBlock
    directSourceFinalCompactRoutedClauseAtomWordBlock
    directSourceFinalCompactRoutedVariableAtomWordBlock
  change
    (((crossoverMetadataNormalizedClausesDedup formula ++
        PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses source) ++
      ((PeriodicThreeSATThree.formulaBaseBendNormalizedClauses source ++
        PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses source) ++
        PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
          source)).flatMap _) = _
  rw [List.flatMap_append, List.flatMap_append,
    List.flatMap_append, List.flatMap_append]
  unfold crossoverMetadataNormalizedClausesDedup
    PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
    PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
    PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
    PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
  rw [occurrenceDecidableEqEq]
  rw [@crossoverMetadataNormalizedClauses_dedup_atomWords
      Variable
      PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      formula
      (PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source)
      (PeriodicThreeSATThree.formula_incidenceGraph_degreeAtMostThree
        sourceWidth)
      (PeriodicThreeSATThree.formula_incidenceGraph_isLocal sourceLocal),
    @carrierMetadataNormalizedClauses_atomWords
      Variable
      PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      formula,
    @baseBendNormalizedClauses_atomWords
      Variable
      PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      formula,
    @baseRoutedClauseNormalizedClauses_atomWords
      Variable
      PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
      formula,
    PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableClauses_atomWords]
  unfold directSourceFinalCompactAtomWord
  rw [← @PeriodicCNF.numericRouteDescriptors_sourceTerminalCompactWords_eq
    Variable
    PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq
    formula
    (PeriodicThreeSATThree.formula_incidenceGraph_isWellFormed source)
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord formula)]
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
