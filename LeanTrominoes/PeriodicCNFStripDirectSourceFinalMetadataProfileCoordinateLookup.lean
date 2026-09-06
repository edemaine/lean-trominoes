/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceWitness

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
  obtain ⟨occurrence, pairEq, generatedEq, ⟨witness⟩⟩ :=
    exists_directSourceFinalOccurrence decider symbols index indexLt
  obtain ⟨profileEq, clauseEq, literalEq, _literalLt⟩ :=
    witness.metadataCoordinates
  rw [← pairEq, ← generatedEq]
  exact ⟨witness.metadata, witness.metadataLookup, profileEq, clauseEq, literalEq⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
