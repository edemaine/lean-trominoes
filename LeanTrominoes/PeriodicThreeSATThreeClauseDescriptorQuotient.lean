/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverPublicDescriptorPrefix
import LeanTrominoes.PeriodicThreeSATThreeNonCrossoverDescriptorQuotient

/-! # Public descriptor quotient of an occurrence-split formula -/

noncomputable section

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

local instance clauseDescriptorQuotientWrappedDecidableEq
    {Variable : Type} [DecidableEq Variable] :
    DecidableEq (WrappedPeriodicPlanarSATVariable
      (ThreeOccurrenceVariable Variable)) :=
  inferInstance

/-- Complete canonical descriptor stream under an explicit equality
implementation for occurrence-split variables. -/
def clauseDescriptorQuotientWith
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (outputDecidableEq : DecidableEq
      (ThreeOccurrenceVariable Variable)) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  letI := outputDecidableEq
  (List.replicate
      (orientedCrossings (formula source).incidenceGraph).length
      PeriodicCNF.FormulaShapeCrossoverDirection.descriptors).flatten ++
    nonCrossoverDescriptorQuotient source

/-- Complete canonical descriptor stream of the occurrence-split retained
drawing: fixed crossover blocks followed by the four non-crossover
quotients. -/
def clauseDescriptorQuotient
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List PeriodicCNF.FormulaShapeDirectionOrdering.Token :=
  clauseDescriptorQuotientWith source inferInstance

/-- The canonical quotient is independent of the chosen decidable equality
implementation for occurrence-split variables. -/
theorem clauseDescriptorQuotientWith_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (first second : DecidableEq
      (ThreeOccurrenceVariable Variable)) :
    clauseDescriptorQuotientWith source first =
      clauseDescriptorQuotientWith source second := by
  have instanceEq : first = second := Subsingleton.elim _ _
  subst second
  rfl

/-- The public retained clause descriptors of the occurrence-split formula
are exactly the complete canonical quotient stream. -/
theorem clauseDescriptors_formula_eq_quotient
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    clauseDescriptors (formula source) =
      clauseDescriptorQuotient source := by
  unfold clauseDescriptorQuotient clauseDescriptorQuotientWith
  rw [clauseDescriptors_eq_fixedCrossover_append_nonCrossover
      (formula source)
      (formula_incidenceGraph_isWellFormed source)
      (formula_incidenceGraph_degreeAtMostThree sourceWidth)
      (formula_incidenceGraph_isLocal sourceLocal),
    nonCrossoverMetadataNormalizedClauses_formula_dedup_map_representative
      source sourceLocal sourceWidth sourceClausesNonempty positiveOffsets]

end LeanTrominoes.PeriodicThreeSATThree

end
