/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaIncidenceDegree
import LeanTrominoes.RetainedAngularFanFinalCoordinatedGlobalTerminalComparisonScaling
import LeanTrominoes.RetainedAngularFanSourceScaledVariableRouteOrder

/-! # Terminal certificate for the direct final source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalTerminalCertificateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalTerminalCertificateVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The final coordinated routes for a direct source have the classified
terminal data needed by occurrence ranking. -/
theorem directSourceFinalOccurrenceTerminalCertificate
    (symbols : List encoding.Γ) :
    RetainedOccurrenceTerminalCertificate
      (finalCoordinatedSource
        (directSourceFormula decider symbols)).erase
      (finalCoordinatedSourceRoutes
        (directSourceFormula decider symbols)) := by
  let source := directSourceFormula decider symbols
  have wellFormed : source.incidenceGraph.IsWellFormed :=
    PeriodicCNF.incidenceGraph_isWellFormed source
  have degree : source.incidenceGraph.DegreeAtMost 3 := by
    exact directSourceFormula_incidenceGraph_degreeAtMost decider symbols
  have isLocal : source.incidenceGraph.IsLocal := by
    unfold source directSourceFormula
    exact PeriodicCNF.incidenceGraph_isLocal (sourceFormula_isLocal _)
  have clausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [] := by
    unfold source directSourceFormula
    exact sourceFormula_clausesNonempty _
  have retainedClausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula source,
        clause.literals ≠ [] :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      source clausesNonempty
  simpa only [source, finalCoordinatedSource,
    finalCoordinatedSourceRoutes] using
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
      source wellFormed degree isLocal retainedClausesNonempty

end LeanTrominoes.PeriodicCNFStripReduction

end
