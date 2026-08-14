/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityCrossover
import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputabilityVariableInput

/-! # Primitive-recursive retained clause and variable routes -/

noncomputable section

namespace LeanTrominoes

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PeriodicOrthocrossing

theorem routedClausePortLiterals_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × ClauseRouteSite =>
      routedClausePortLiterals input.1 input.2 := by
  have occurrences : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      clauseRouteOccurrencesAt input.1 input.2 :=
    clauseRouteOccurrencesAt_primrec
  have one : Primrec₂ fun
      (input : PeriodicCNF Variable × ClauseRouteSite)
      (occurrence : CNFRouteOccurrence Variable) =>
      (sourceOccurrenceArm input.1 occurrence,
        occurrence.incidence.literal.value) := by
    have terminal : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        combined.2.sourceTerminal combined.1.1 :=
      CNFRouteOccurrence.sourceTerminal_primrec.comp
        (Primrec.fst.comp Primrec.fst) Primrec.snd
    have arm : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        sourceOccurrenceArm combined.1.1 combined.2 :=
      (SegmentTerminal.duplicatorArm_primrec.comp terminal).of_eq
        fun combined => (sourceOccurrenceArm_eq
          combined.1.1 combined.2).symm
    have value : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          CNFRouteOccurrence Variable =>
        combined.2.incidence.literal.value :=
      PeriodicThreeCNF.literal_value_primrec.comp
        (CNFIncidence.literal_primrec.comp
          (CNFRouteOccurrence.incidence_primrec.comp Primrec.snd))
    exact Primrec.pair arm value
  exact (Primrec.list_map occurrences one).of_eq fun _ => rfl

theorem routedClauseOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable × ClauseRouteSite =>
      routedClauseOrigin input.1 input.2 := by
  have vertex : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (CNFVertex.clause input.2.1 : CNFVertex Variable) :=
    CNFVertex.clause_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (liftedIncidenceVertexMacroOrigin_primrec.comp
    (Primrec.pair
      (Primrec.pair Primrec.fst vertex)
      (Primrec.snd.comp Primrec.snd))).of_eq fun _ => rfl

abbrev RoutedClauseRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat

def routedClauseRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : RoutedClauseRouteInput Variable) : List Cell :=
  (drawingPlanarSATRoutedClauseIncidenceDrawing
    input.1.1.1 input.1.1.2).routes input.1.2 input.2

theorem routedClauseRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseRoute (Variable := Variable)) := by
  change Primrec fun input : RoutedClauseRouteInput Variable =>
    (drawingPlanarSATRoutedClauseIncidenceDrawing
      input.1.1.1 input.1.1.2).routes input.1.2 input.2
  have formula : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      routedClausePortFormula
        (routedClausePortLiterals input.1 input.2) :=
    routedClausePortFormula_primrec.comp
      routedClausePortLiterals_primrec
  have position : Primrec fun input :
      (PeriodicCNF Variable × ClauseRouteSite) × DuplicatorArm =>
      DuplicatorArm.portPosition input.2 :=
    duplicatorArmPortPosition_primrec.comp Primrec.snd
  have base : Primrec fun input :
      ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat =>
      (routedClausePortStraightIncidenceDrawing
        (routedClausePortLiterals input.1.1.1 input.1.1.2)).routes
          input.1.2 input.2 :=
    (straightIncidenceRoutes_primrec
      (fun input : PeriodicCNF Variable × ClauseRouteSite =>
        routedClausePortFormula
          (routedClausePortLiterals input.1 input.2))
      (fun (_input : PeriodicCNF Variable × ClauseRouteSite) arm =>
        DuplicatorArm.portPosition arm)
      formula position).of_eq fun _ => rfl
  have origin : Primrec fun input :
      ((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat =>
      routedClauseOrigin input.1.1.1 input.1.1.2 :=
    routedClauseOrigin_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have transform : Primrec fun input :
      (((PeriodicCNF Variable × ClauseRouteSite) × Nat) × Nat) ×
        Cell =>
      Cell.add
        (routedClauseOrigin input.1.1.1.1 input.1.1.1.2) input.2 :=
    Computability.cell_add_primrec.comp
      (origin.comp Primrec.fst) Primrec.snd
  exact Primrec.list_map base transform.to₂

end PeriodicOrthocrossing
end LeanTrominoes
