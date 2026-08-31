/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendClauseIndexedMembership
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalCertificate
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotBlockData
import LeanTrominoes.RetainedAngularFanFinalCoordinatedOccurrenceSlotBlockSemantics

/-! # Semantic occurrence slots of direct final-bend clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendOccurrenceSlotStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendOccurrenceSlotVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The semantic occurrence slots of any indexed direct final-bend clause
are its global stable-rank slot block. -/
theorem directSourceFinalBendClauseOccurrenceSlots_eq_stableRankBlock
    (symbols : List encoding.Γ)
    (taggedClause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable) × Nat)
    (taggedMember : taggedClause ∈
      (directSourceFinalBendClauses decider symbols).zipIdx
        (directSourceFinalBendStart decider symbols)) :
    taggedClause.1.zipIdx.map (fun taggedLiteral =>
        retainedFinalCoordinatedOccurrenceSlot
          (directSourceFormula decider symbols)
          taggedLiteral.1 taggedClause.2 taggedLiteral.2) =
      retainedOccurrenceGlobalStableTerminalSlotBlock
        (retainedFinalCoordinatedScaledSource
          (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes
          (directSourceFormula decider symbols))
        taggedClause := by
  apply retainedFinalCoordinatedOccurrenceSlots_eq_globalStableRankBlock
    (directSourceFormula decider symbols)
    taggedClause
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
  rw [directSourceFinalScaledClauses_eq decider symbols]
  exact directSourceFinalBendClauses_indexedMember
    decider symbols taggedClause taggedMember

end LeanTrominoes.PeriodicCNFStripReduction

end
