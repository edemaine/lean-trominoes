/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomCoordinateCompiler
import LeanTrominoes.PeriodicCNFPlanarZeroVariableRouteSites

/-! # Exact geometric cases for final original-atom coordinate columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing PeriodicEightOccurrenceSplit

local instance finalOriginalGeometryVariableDecidableEq : DecidableEq Variable :=
  originalAtomWordVariableDecidableEq

/-- For a valid query, the coordinate contribution is determined solely by
its constructor, without a remaining dictionary-membership test. -/
theorem originalAtomCoordinateContribution_eq_constructor
    (source : PeriodicCNF Variable) (horizontal keepPositive : Bool)
    (isLocal : source.incidenceGraph.IsLocal)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (valid : RetainedDrawingPeriodicPlanarSATVariableValid source query.original) :
    originalAtomCoordinateContribution source horizontal keepPositive query =
      match query.original with
      | .atom _ => originalAtomCoordinateField source horizontal keepPositive query
      | _ => 0 := by
  rcases query with ⟨query⟩
  cases query with
  | atom atom =>
      apply originalAtomCoordinateContribution_atom
      apply List.mem_dedup.mpr
      exact (mem_variableOccurrences_iff_zeroSite_mem source isLocal atom).mpr valid
  | terminal indexed endpoint =>
      apply originalAtomCoordinateContribution_of_not_original
      intro atom equal
      cases equal
  | boundary boundary =>
      apply originalAtomCoordinateContribution_of_not_original
      intro atom equal
      cases equal
  | crossoverInternal internal =>
      apply originalAtomCoordinateContribution_of_not_original
      intro atom equal
      cases equal

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance finalOriginalGeometryStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

section NamedSource

local instance finalCoordinateNamedDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The five-family query presentation is the exact variable-occurrence list
of the actual retained source used by the final construction. -/
theorem directSourceFinalCoordinateAtoms_eq_variableOccurrences
    (symbols : List encoding.Γ) :
    directSourceFinalCoordinateAtoms decider symbols =
      (@retainedFinalCoordinatedScaledSource Variable directSourceVariableDecidableEq
        (directSourceFormula decider symbols)).erase.variableOccurrences := by
  unfold directSourceFinalCoordinateAtoms retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]
  unfold PeriodicCNF.variableOccurrences
  rw [finalCoordinatedSource_erase_clauses_eq,
    directSource_deduplicatedClauses_eq_fiveFamilies]

/-- Every query atom satisfies the source geometry's validity predicate. -/
private theorem directSourceFinalCoordinateAtoms_valid_named (symbols : List encoding.Γ)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (member : query ∈ directSourceFinalCoordinateAtoms decider symbols) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      (directSourceFormula decider symbols) query.original := by
  have sourceMember := member
  rw [directSourceFinalCoordinateAtoms_eq_variableOccurrences] at sourceMember
  have namedValid : @RetainedDrawingPeriodicPlanarSATVariableValid Variable
      directSourceVariableDecidableEq (directSourceFormula decider symbols) query.original := by
    letI : DecidableEq Variable := directSourceVariableDecidableEq
    let source := directSourceFormula decider symbols
    have isLocal : source.incidenceGraph.IsLocal := by
      unfold source directSourceFormula
      exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
    apply retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      source (PeriodicCNF.incidenceGraph_isWellFormed source)
      (directSourceFormula_incidenceGraph_degreeAtMost decider symbols) isLocal
    simpa only [source, retainedFinalCoordinatedScaledSource,
      finalCoordinatedSource, PositionedPeriodicCNF.erase_scale] using sourceMember
  exact namedValid

end NamedSource

/-- The validity predicate is independent of the chosen equality implementation. -/
theorem directSourceFinalCoordinateAtoms_valid (symbols : List encoding.Γ)
    (query : WrappedPeriodicPlanarSATVariable Variable)
    (member : query ∈ directSourceFinalCoordinateAtoms decider symbols) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      (directSourceFormula decider symbols) query.original := by
  have namedValid := directSourceFinalCoordinateAtoms_valid_named decider symbols query member
  have instanceEq : directSourceVariableDecidableEq = originalAtomWordVariableDecidableEq :=
    Subsingleton.elim _ _
  change @RetainedDrawingPeriodicPlanarSATVariableValid Variable directSourceVariableDecidableEq
    (directSourceFormula decider symbols) query.original at namedValid
  rw [instanceEq] at namedValid
  exact namedValid

/-- Each final occurrence receives its actual canonical original-atom field;
terminal, boundary, and crossover occurrences receive zero in this contribution. -/
theorem directSourceFinalOriginalAtomCoordinates_eq_geometricCases
    (horizontal keepPositive : Bool) (symbols : List encoding.Γ) :
    directSourceFinalOriginalAtomCoordinates decider horizontal keepPositive symbols =
      (directSourceFinalCoordinateAtoms decider symbols).map fun query =>
        match query.original with
        | .atom _ => originalAtomCoordinateField (directSourceFormula decider symbols)
            horizontal keepPositive query
        | _ => 0 := by
  rw [directSourceFinalOriginalAtomCoordinates_eq_contributions]
  apply List.map_congr_left
  intro query member
  have isLocal : (directSourceFormula decider symbols).incidenceGraph.IsLocal := by
    unfold directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  exact originalAtomCoordinateContribution_eq_constructor (directSourceFormula decider symbols)
    horizontal keepPositive isLocal query (directSourceFinalCoordinateAtoms_valid decider symbols
      query member)

end LeanTrominoes.PeriodicCNFStripReduction

end
