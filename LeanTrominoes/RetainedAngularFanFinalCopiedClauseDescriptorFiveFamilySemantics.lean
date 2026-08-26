/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedBendClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedCarrierClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFiveFamilyPresentation
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryListSemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedCrossoverClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedClauseQuerySemantics
import LeanTrominoes.RetainedAngularFanFinalCopiedRoutedVariableClauseQueryCorrectness

/-! # Evaluated five-family semantics of final copied clauses -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

local instance finalDescriptorFiveFamilyThreeOccurrenceDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (ThreeOccurrenceVariable Variable) :=
  PeriodicThreeSATThree.fiveFamilyNormalizedThreeOccurrenceDecidableEq

/-- Evaluating the exact final query stream gives the five semantic families:
stable direct crossover queries, final carrier and bend descriptors, stable
direct routed-clause queries, and stable routed-variable site queries. -/
theorem retainedFinalCopiedClauseDescriptors_formula_eq_fiveFamilies
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈
      PeriodicThreeSATThree.occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    let formula := PeriodicThreeSATThree.formula source
    retainedFinalCopiedClauseDescriptors
        (retainedFinalIndexedClauseQueries formula) =
      retainedFinalCopiedClauseDescriptors
          ((List.replicate
            (orientedCrossings formula.incidenceGraph).length
            retainedFinalDirectCrossoverClauseQueries).flatten) ++
        carrierMetadataClauseDescriptors formula ++
          baseBendClauseDescriptors formula ++
            retainedFinalCopiedClauseDescriptors
                (formula.clauses.map fun clause =>
                  retainedFinalDirectRoutedClauseQuery
                    (clause.map fun literal =>
                      (⟨false, literal.value⟩ :
                        UnaryProgramClauseProfile.LiteralProfile))) ++
              retainedFinalCopiedClauseDescriptors
                ((List.range
                  (PeriodicCNF.presentationLiteralCount source)).flatMap
                    (fun _targetIndex =>
                      retainedFinalDirectRoutedVariableFullSiteQueries)) := by
  dsimp only
  have formulaLocal :
      (PeriodicThreeSATThree.formula source).IsLocal :=
    PeriodicThreeSATThree.formula_isLocal sourceLocal
  have formulaWidth :
      (PeriodicThreeSATThree.formula source).WidthAtMost 3 :=
    PeriodicThreeSATThree.formula_widthAtMostThree sourceWidth
  have formulaClausesNonempty :
      ∀ clause ∈ (PeriodicThreeSATThree.formula source).clauses,
        clause ≠ [] :=
    PeriodicThreeSATThree.formula_clausesNonempty
      source sourceClausesNonempty
  rw [retainedFinalIndexedClauseQueries_formula_eq_fiveFamilies
    source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]
  simp only [retainedFinalCopiedClauseDescriptors_append]
  rw [retainedFinalCrossoverClauseQueries_formula_eq,
    retainedFinalCarrierClauseQueryDescriptors_formula_eq,
    retainedFinalBendClauseQueryDescriptors_formula_eq,
    retainedFinalRoutedClauseQueries_formula_eq,
    retainedFinalRoutedVariableClauseQueries_formula_eq_fullSites]
  all_goals first
    | exact formulaLocal
    | exact formulaWidth
    | exact
        PeriodicThreeSATThree.formula_occurrencesAtMostThree_decidableEq source
    | exact formulaClausesNonempty
    | assumption

end PeriodicEightOccurrenceSplit
end LeanTrominoes
