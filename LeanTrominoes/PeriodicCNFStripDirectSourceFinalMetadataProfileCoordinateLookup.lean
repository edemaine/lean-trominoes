/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineIndexedProfileCoordinateMetadataLookup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalMetadataProfileCoordinateSemantics

/-! # Pointwise direct Figure 9 metadata profile-coordinate lookup -/

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

noncomputable local instance directFinalMetadataProfileCoordinateLookupStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalMetadataProfileCoordinateLookupVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Every direct occurrence's broadcast generated-clause index looks up
concrete Figure 9 metadata with the same parent profile and local clause
coordinate as its finite header query. -/
theorem exists_metadata_of_directFigureNinePolarityRoutePair
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
          (List.range metadata.parentProfileCoordinate.literalCount)).getD
            ((headerTemplateProfileCoordinate
              ((directFigureNinePolarityRoutePairs
                decider symbols).getD index default).1).coordinate.polarity.sourceLiteralIndex)
            0 := by
  apply exists_metadata_of_indexedProfileCoordinateStream
    (fun pair => headerTemplateProfileCoordinate pair.1)
    (directFigureNinePolarityRoutePairSourceClauseIndices decider symbols)
    (directFigureNinePolarityRoutePairs decider symbols)
    ((PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
      (directSourceFormula decider symbols)).flatMap
        expectedIndexedProfileCoordinateBlocks)
    (formulaClauseMetadata
      (retainedFigureNineClearancePositionedFormula
        (directSourceFormula decider symbols)))
    ClauseMetadata.parentProfileCoordinate
  · simp
  · exact directFigureNinePolarityRoutePairs_zipWith_indexedProfileCoordinate
      decider symbols
  · exact directSourceIndexedProfileCoordinateBlocks_map_parent_eq_metadata
      decider symbols
  · intro block blockMember coordinate coordinateMember
    exact
      coordinate_parent_of_mem_source_expectedIndexedProfileCoordinateBlocks
        (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
          (directSourceFormula decider symbols))
        blockMember coordinateMember
  · intro block blockMember coordinate coordinateMember
    exact
      coordinate_literalIndex_of_mem_source_expectedIndexedProfileCoordinateBlocks
        (PeriodicCNF.FormulaShapeRetainedFigureNineDirection.descriptors
          (directSourceFormula decider symbols))
        blockMember coordinateMember
  · exact indexLt

end LeanTrominoes.PeriodicCNFStripReduction

end
