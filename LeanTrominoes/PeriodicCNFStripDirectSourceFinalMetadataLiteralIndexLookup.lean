/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalMetadataProfileCoordinateLookup
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineMetadataClauseArity

/-! # Exact direct Figure 9 metadata literal-index lookup -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.ClauseProfileOccurrenceSplit
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeOfFormula
open PeriodicCNF.UnaryProgramClauseProfile
open PeriodicOrthocrossing
open PlanarOneInThreeNoUnitsFigureNine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalMetadataLiteralIndexLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalMetadataLiteralIndexLookupVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem directSourceWidthAtMostThree
    (symbols : List encoding.Γ) :
    (directSourceFormula decider symbols).WidthAtMost 3 := by
  simpa only [directSourceFormula] using
    sourceFormula_widthAtMostThree
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

private theorem directSourceClausesNonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ (directSourceFormula decider symbols).clauses,
      clause ≠ [] := by
  simpa only [directSourceFormula] using
    sourceFormula_clausesNonempty
      (PolySpaceCompiler.formulaOfSymbols decider symbols)

/-- Every direct occurrence retrieves concrete metadata whose composed-clause
arity yields the exact original literal index selected by the header. -/
theorem exists_metadata_of_directFigureNinePolarityRoutePair_exactLiteralIndex
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index <
      (directFigureNinePolarityRoutePairs decider symbols).length) :
    ∃ metadata,
      (formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula
          (directSourceFormula decider symbols)))[
            (directFigureNinePolarityRoutePairSourceClauseIndices
              decider symbols).getD index 0]? = some metadata ∧
      (headerTemplateProfileCoordinate
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1).profile =
        clauseProfile (literalProfiles metadata.sourceClause.literals) ∧
      (headerTemplateProfileCoordinate
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1).coordinate.clauseIndex =
        metadata.localClauseIndex ∧
      (headerTemplateProfileCoordinate
        ((directFigureNinePolarityRoutePairs
          decider symbols).getD index default).1).coordinate.literalIndex =
        (PeriodicCNF.FormulaShapeFigureNineFinalClauseOrdering.reorderList
          (List.range metadata.clause.literals.length)).getD
            ((headerTemplateProfileCoordinate
              ((directFigureNinePolarityRoutePairs
                decider symbols).getD index default).1).coordinate.polarity.sourceLiteralIndex)
            0 := by
  rcases exists_metadata_of_directFigureNinePolarityRoutePair
      decider symbols index indexLt with
    ⟨metadata, metadataLookup, profileEq, clauseIndexEq, literalIndexEq⟩
  have metadataIndexLt :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember : metadata ∈
      formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula
          (directSourceFormula decider symbols)) := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have arityEq :=
    metadata_clause_length_eq_parentProfileCoordinate_literalCount
      (retainedFigureNineClearancePositionedFormula
        (directSourceFormula decider symbols))
      (retainedFigureNineClearancePositionedFormula_clausesNonempty
        (directSourceFormula decider symbols)
        (directSourceClausesNonempty decider symbols))
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        (directSourceFormula decider symbols)
        (directSourceWidthAtMostThree decider symbols))
      metadataMember
  rw [← arityEq] at literalIndexEq
  exact ⟨metadata, metadataLookup, profileEq,
    clauseIndexEq, literalIndexEq⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
