/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListSubfamilyLookup
import LeanTrominoes.PeriodicThreeSATThreeFiveFamilyNormalizedClauses

/-! # Indexed carrier lookup in the retained clause presentation -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

/-- Every carrier tagged from the end of the crossover prefix occupies its
declared global index in the duplicate-free retained clause list. -/
theorem formulaCarrierMetadataNormalizedClauses_getElem?_of_mem_zipIdx
    {Variable : Type} [DecidableEq Variable]
    [occurrenceDecEq : DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0))
    (taggedClause :
      PeriodicClause
          (WrappedPeriodicPlanarSATVariable
            (ThreeOccurrenceVariable Variable)) × Nat)
    (taggedClauseMember : taggedClause ∈
      (formulaCarrierMetadataNormalizedClauses source).zipIdx
        (crossoverMetadataNormalizedClausesDedup
          (formula source)).length) :
    (deduplicatedClauses (formula source))[taggedClause.2]? =
      some taggedClause.1 := by
  have occurrenceDecEqEq : occurrenceDecEq =
      fiveFamilyNormalizedThreeOccurrenceDecidableEq :=
    Subsingleton.elim _ _
  subst occurrenceDecEq
  have clausesEq :=
    deduplicatedClauses_formula_eq_fiveFamilies
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets
  exact IndexedListScan.getElem?_of_eq_append_middle_of_mem_zipIdx
    (deduplicatedClauses (formula source))
    (crossoverMetadataNormalizedClausesDedup (formula source))
    (formulaCarrierMetadataNormalizedClauses source)
    (formulaBaseBendNormalizedClauses source ++
      formulaBaseRoutedClauseNormalizedClauses source ++
        formulaCanonicalWrappedNormalizedRoutedVariableClauses source)
    clausesEq taggedClause taggedClauseMember

end LeanTrominoes.PeriodicThreeSATThree
