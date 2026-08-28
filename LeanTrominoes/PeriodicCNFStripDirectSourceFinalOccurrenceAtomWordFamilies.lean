/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeBaseBendAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeCarrierAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRoutedClauseAtomWordSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomWordData
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableAtomWordSemantics

/-! # Five structural blocks of direct final occurrence atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalAtomWordFamiliesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalAtomWordFamiliesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Fixed crossover-role atom words, one Figure 8(b) block per canonical
crossing in the exact last-occurrence halo order. -/
def directSourceFinalCrossoverAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := DirectSourceFinalIndexedAtomWords.word formula
  (canonicalizedCrossingHalo formula.incidenceGraph).flatMap fun crossing =>
    crossoverFormula.flatMap fun clause =>
      clause.literals.map fun literal =>
        word ⟨normalizedCrossoverAtom crossing literal.1⟩

/-- Repeated normalized endpoint words of every retained carrier link. -/
def directSourceFinalCarrierAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := DirectSourceFinalIndexedAtomWords.word formula
  ((retainedDrawingCompleteCarrierLinks formula.incidenceGraph).map
      (PeriodicEquality.normalizeLink
        (carrierWrappedVariableNormalization formula))).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- Repeated normalized endpoint words of every canonical base bend. -/
def directSourceFinalBendAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := DirectSourceFinalIndexedAtomWords.word formula
  (baseBendNormalizedLinks formula).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- Source-terminal atom rows of the presentation-ordered routed clauses. -/
def directSourceFinalRoutedClauseAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := DirectSourceFinalIndexedAtomWords.word formula
  formula.clauses.zipIdx.flatMap fun taggedClause =>
    (clauseRouteOccurrencesAt formula
      (taggedClause.2, (0, 0))).map fun occurrence =>
        word (externalWrappedVariableNormalization formula
          (.carrier (.terminal
            (occurrence.sourceTerminal formula)))).1

/-- Repeated normalized endpoint words of every canonical final-site routed
variable link. -/
def directSourceFinalRoutedVariableAtomWordBlock
    (symbols : List encoding.Γ) : List (List Bool) :=
  let source := directThreeCNFSourceFormula decider symbols
  let formula := PeriodicThreeSATThree.formula source
  let word := DirectSourceFinalIndexedAtomWords.word formula
  (PeriodicThreeSATThree.canonicalWrappedNormalizedRoutedVariableLinks
      source).flatMap fun link =>
    [word link.first, word link.second,
      word link.first, word link.second]

/-- The exact five-family atom-word target, retaining the same append tree as
the duplicate-free final clause presentation. -/
def directSourceFinalFiveFamilyAtomWordBlocks
    (symbols : List encoding.Γ) : List (List Bool) :=
  (directSourceFinalCrossoverAtomWordBlock decider symbols ++
    directSourceFinalCarrierAtomWordBlock decider symbols) ++
  ((directSourceFinalBendAtomWordBlock decider symbols ++
    directSourceFinalRoutedClauseAtomWordBlock decider symbols) ++
    directSourceFinalRoutedVariableAtomWordBlock decider symbols)

/-- The complete final occurrence word column is exactly the concatenation of
the five explicit structural blocks above. -/
theorem directSourceFinalOccurrenceAtomWords_eq_structuralBlocks
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrenceAtomWords decider symbols).words =
      directSourceFinalFiveFamilyAtomWordBlocks decider symbols := by
  let original := PolySpaceCompiler.formulaOfSymbols decider symbols
  let source := PeriodicThreeCNF.formula original
  let formula := PeriodicThreeSATThree.formula source
  have sourceLocal : source.IsLocal := by
    apply PeriodicThreeCNF.formula_isLocal
    exact (formulaOfSymbols_sourceAdmissible decider symbols).2.1
  have sourceWidth : source.WidthAtMost 3 :=
    PeriodicThreeCNF.formula_widthAtMostThree original
  have occurrenceDecidableEqEq :
      directFinalAtomWordFamiliesVariableDecidableEq =
        (PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq :
          DecidableEq Variable) :=
    Subsingleton.elim _ _
  rw [directSourceFinalOccurrenceAtomWords_eq_fiveFamilies,
    directSourceFormula_eq_threeSATThree]
  unfold directSourceFinalFiveFamilyClauses
    directThreeCNFSourceFormula directSourceFinalFiveFamilyAtomWordBlocks
    directSourceFinalCrossoverAtomWordBlock
    directSourceFinalCarrierAtomWordBlock
    directSourceFinalBendAtomWordBlock
    directSourceFinalRoutedClauseAtomWordBlock
    directSourceFinalRoutedVariableAtomWordBlock
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
  rfl

end PeriodicCNFStripReduction
end LeanTrominoes

end
