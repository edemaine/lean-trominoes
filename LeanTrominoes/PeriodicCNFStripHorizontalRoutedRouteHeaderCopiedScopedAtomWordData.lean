/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderParentLocalAtomCode
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderPresentationAtomScopeCompiler

/-! # Copied-clause scoped final atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction
namespace HorizontalRoutedRouteHeaderCopiedScopedAtomWords

open PeriodicCNF.ClauseProfilePolarityRouteOperation
open PeriodicCNF.FormulaShapeDirectionOrdering
open PeriodicCNF.FormulaShapeFigureNinePolarityRouteHeader
open HorizontalRoutedRouteHeader

/-- Number of presentation-ordered pre-Figure9 atom words consumed by one
directed copied clause. -/
def sourceWordCount (profile : DirectedClauseProfile) : Nat :=
  profile.taggedLiterals.length

/-- Interpret one presentation-relative finite scope using its parent clause
index and the presentation-ordered source words of that clause. -/
def scopedSource (parentIndex : Nat) (sourceWords : List (List Bool)) :
    AtomScopeControl → ScopedAtomWordSource
  | .inherited presentationSlot =>
      .inherited
        (sourceWords.getD (sourceSlotNat presentationSlot) [])
  | .parentLocal control =>
      .parentLocal parentIndex (parentLocalAtomCode control)

/-- Scoped sources of every final occurrence generated from one copied
clause. -/
def clauseSources (parentIndex : Nat) (profile : DirectedClauseProfile)
    (sourceWords : List (List Bool)) : List ScopedAtomWordSource :=
  (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock profile).map
    (scopedSource parentIndex sourceWords)

/-- Binary final-atom words generated from one copied clause. -/
def clauseWords (parentIndex : Nat) (profile : DirectedClauseProfile)
    (sourceWords : List (List Bool)) : List (List Bool) :=
  (clauseSources parentIndex profile sourceWords).map
    ScopedAtomWordSource.word

/-- Consume the presentation atom-word column clause by clause while
retaining a globally unique parent index for every copied descriptor. -/
def sourcesAux : Nat →
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token →
      List (List Bool) → List ScopedAtomWordSource
  | _, [], _ => []
  | parentIndex, .variable :: source, sourceWords =>
      sourcesAux parentIndex source sourceWords
  | parentIndex, .clause profile :: source, sourceWords =>
      let count := sourceWordCount profile
      clauseSources parentIndex profile (sourceWords.take count) ++
        sourcesAux (parentIndex + 1) source (sourceWords.drop count)

def sources
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (sourceWords : DelimitedBinaryWords.Input) :
    List ScopedAtomWordSource :=
  sourcesAux 0 source sourceWords.words

/-- Complete scoped final words for a copied descriptor stream and its
aligned pre-Figure9 compact atom-word column. -/
def words
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (sourceWords : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨(sources source sourceWords).map ScopedAtomWordSource.word⟩

@[simp] theorem clauseSources_length (parentIndex : Nat)
    (profile : DirectedClauseProfile) (sourceWords : List (List Bool)) :
    (clauseSources parentIndex profile sourceWords).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock
        (.clause profile)).length := by
  simp [clauseSources,
    HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock,
    HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock]

/-- The merger emits exactly one scoped source per final copied occurrence,
independently of the harmless total-lookup fallback on malformed inputs. -/
theorem sourcesAux_length (parentIndex : Nat)
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (sourceWords : List (List Bool)) :
    (sourcesAux parentIndex source sourceWords).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  induction source generalizing parentIndex sourceWords with
  | nil => rfl
  | cons token source induction =>
      cases token with
      | «variable» =>
          simpa [sourcesAux,
            HorizontalRoutedRouteHeaderOccurrenceBlock.output,
            HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock] using
            induction parentIndex sourceWords
      | clause profile =>
          simp only [sourcesAux, List.length_append,
            clauseSources_length]
          rw [induction]
          simp [HorizontalRoutedRouteHeaderOccurrenceBlock.output,
            HorizontalRoutedRouteHeaderOccurrenceBlock.tokenBlock]

theorem sources_length
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (sourceWords : DelimitedBinaryWords.Input) :
    (sources source sourceWords).length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  exact sourcesAux_length 0 source sourceWords.words

theorem words_length
    (source : List PeriodicCNF.FormulaShapeDirectionOrdering.Token)
    (sourceWords : DelimitedBinaryWords.Input) :
    (words source sourceWords).words.length =
      (HorizontalRoutedRouteHeaderOccurrenceBlock.output source).length := by
  simp [words, sources_length]

end HorizontalRoutedRouteHeaderCopiedScopedAtomWords
end PeriodicCNFStripReduction
end LeanTrominoes

end
