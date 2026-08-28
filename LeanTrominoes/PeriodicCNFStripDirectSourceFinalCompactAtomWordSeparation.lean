/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomWordData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaForwardLocalNamed
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedCompactAtomWord
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions
import LeanTrominoes.RetainedAngularOccurrenceGlobalSeparatedAtomWordSemantics

/-! # Compact atom words separate direct final occurrences -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicEightOccurrenceSplit PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCompactAtomWordSeparationStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directCompactAtomWordSeparationVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The indexed source-variable word is injective for every fixed source. -/
theorem directSourceFinalIndexedSourceVariableWord_injective
    (source : PeriodicCNF Variable) :
    Function.Injective
      (DirectSourceFinalIndexedAtomWords.sourceVariableWord source) := by
  intro first second wordsEq
  have decodedEq := congrArg
    (DirectSourceFinalIndexedAtomWords.decodeSourceVariable source) wordsEq
  have firstDecoded :
      DirectSourceFinalIndexedAtomWords.decodeSourceVariable source
          (DirectSourceFinalIndexedAtomWords.sourceVariableWord source first) =
        some (first, []) := by
    simpa using
      DirectSourceFinalIndexedAtomWords.decodeSourceVariable_word_append
        source first []
  have secondDecoded :
      DirectSourceFinalIndexedAtomWords.decodeSourceVariable source
          (DirectSourceFinalIndexedAtomWords.sourceVariableWord source second) =
        some (second, []) := by
    simpa using
      DirectSourceFinalIndexedAtomWords.decodeSourceVariable_word_append
        source second []
  rw [firstDecoded, secondDecoded] at decodedEq
  exact congrArg Prod.fst (Option.some.inj decodedEq)

/-- Direct-source specialization of the compact retained-atom word. -/
def directSourceFinalCompactAtomWord
    (source : PeriodicCNF Variable) :
    WrappedPeriodicPlanarSATVariable Variable → List Bool :=
  PeriodicOrthocrossing.RetainedCompactAtomWords.word
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord source)

/-- Presentation-ordered compact words for the exact source-scaled final
formula used by stable terminal ranking. -/
def directSourceFinalCompactOccurrenceAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  retainedOccurrenceGlobalAtomWords
    (retainedFinalCoordinatedScaledSource
      (directSourceFormula decider symbols)).erase
    (directSourceFinalCompactAtomWord
      (directSourceFormula decider symbols))

/-- Compact descriptor-key words separate every represented atom in the
direct source's final occurrence presentation. -/
theorem directSourceFinalCompactOccurrenceAtomWords_separate
    (symbols : List encoding.Γ) :
    OccurrenceAtomWordsSeparate
      (retainedFinalCoordinatedScaledSource
        (directSourceFormula decider symbols)).erase
      (directSourceFinalCompactAtomWord
        (directSourceFormula decider symbols)) := by
  let source := directSourceFormula decider symbols
  intro first firstMember second secondMember wordsEq
  have wellFormed : source.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source
  have degree : source.incidenceGraph.DegreeAtMost 3 := by
    exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  have isLocal : source.incidenceGraph.IsLocal := by
    unfold source directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        source first.original := by
    apply
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        source wellFormed degree isLocal
    simpa [source, retainedFinalCoordinatedScaledSource,
      finalCoordinatedSource, PositionedPeriodicCNF.erase_scale] using
        firstMember
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        source second.original := by
    apply
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        source wellFormed degree isLocal
    simpa [source, retainedFinalCoordinatedScaledSource,
      finalCoordinatedSource, PositionedPeriodicCNF.erase_scale] using
        secondMember
  exact RetainedCompactAtomWords.word_injective_on_valid
    source
    (DirectSourceFinalIndexedAtomWords.sourceVariableWord source)
    (directSourceFinalIndexedSourceVariableWord_injective source)
    first firstValid second secondValid wordsEq

/-- Consequently the compact-word equality square is exactly the semantic
same-atom square used by the stable-rank compiler. -/
theorem directSourceFinalGlobalAtomEqualityBits_eq_compactWords
    (symbols : List encoding.Γ) :
    retainedOccurrenceGlobalAtomEqualityBits
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase =
      DelimitedBinaryWordEqualitySquare.equalityBits
        (directSourceFinalCompactOccurrenceAtomWords decider symbols) := by
  apply retainedOccurrenceGlobalAtomEqualityBits_eq_separatingWords
  exact directSourceFinalCompactOccurrenceAtomWords_separate decider symbols

end PeriodicCNFStripReduction
end LeanTrominoes

end
