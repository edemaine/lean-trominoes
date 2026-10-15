/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Stable.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockFamilyData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectThreeCNFSourceFacts
import LeanTrominoes.SAT.ThreeSAT.PeriodicThreeSATThreeRoutedClauseLookup

/-! # Indexed membership of final routed clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalRoutedClauseMembershipVariableDecidableEq :
    DecidableEq Variable := directSourceVariableDecidableEq

def directSourceFinalRoutedClauseTaggedClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (directSourceFinalRoutedClauseClauses decider symbols).zipIdx
    (directSourceFinalRoutedClauseStart decider symbols)

def directSourceFinalRoutedClauseTaggedSourceClauses
    (symbols : List encoding.Γ) :
    List (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat) :=
  (deduplicatedClauses (directSourceFormula decider symbols)).zipIdx

theorem directSourceFinalRoutedClauseClauses_indexedMember
    (symbols : List encoding.Γ) :
    ∀ taggedClause ∈
        directSourceFinalRoutedClauseTaggedClauses decider symbols,
      taggedClause ∈
        directSourceFinalRoutedClauseTaggedSourceClauses decider symbols := by
  intro taggedClause taggedMember
  unfold directSourceFinalRoutedClauseTaggedClauses at taggedMember
  unfold directSourceFinalRoutedClauseTaggedSourceClauses
  apply List.mem_zipIdx_iff_getElem?.mpr
  have lookup :=
    PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses_getElem?_of_mem_zipIdx
      (directThreeCNFSourceFormula decider symbols)
      (directThreeCNFSource_isLocal decider symbols)
      (directThreeCNFSource_widthAtMostThree decider symbols)
      (directThreeCNFSource_clausesNonempty decider symbols)
      (directThreeCNFSource_positiveOffsets decider symbols)
      taggedClause
      (by
        simpa only [directSourceFinalRoutedClauseClauses,
          directSourceFinalRoutedClauseStart,
          directSourceFinalBendStart,
          directSourceFinalCarrierStart,
          directSourceFinalCrossoverClauses,
          directSourceFinalCarrierClauses,
          directSourceFinalBendClauses]
          using taggedMember)
  rw [directSourceFormula_eq_finalNormalized decider symbols]
  simpa only [directSourceFinalNormalizedFormula] using lookup

end LeanTrominoes.PeriodicCNFStripReduction

end
