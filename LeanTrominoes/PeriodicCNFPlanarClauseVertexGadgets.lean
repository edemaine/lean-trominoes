/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVertexGadgetCore

/-! # Clause gadgets at routed SAT vertices -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- All routed endpoints incident to clause vertices. -/
def drawingClauseRouteEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (CNFRouteEndpoint Variable) :=
  (drawingCNFRouteEndpoints formula).filter
    CNFRouteEndpoint.isClauseEnd

/-- All routed endpoints incident to variable vertices. -/
def drawingVariableRouteEndpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (CNFRouteEndpoint Variable) :=
  (drawingCNFRouteEndpoints formula).filter
    CNFRouteEndpoint.isVariableEnd

/-- The finite lifted clause sites represented in the neighboring block. -/
def drawingClauseRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : List ClauseRouteSite :=
  formula.clauses.zipIdx.flatMap fun taggedClause =>
    neighborTranslations.map fun translate =>
      (taggedClause.2, translate)

/-- Incidence-route occurrences at one lifted clause vertex, in original
literal order. -/
def clauseRouteOccurrencesAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    List (CNFRouteOccurrence Variable) :=
  ((PeriodicCNF.incidencesWithMetadata formula).zipIdx.filter
      fun taggedIncidence =>
        taggedIncidence.1.clauseIndex = site.1).map
    fun taggedIncidence =>
      ⟨taggedIncidence.1, taggedIncidence.2, site.2⟩

/-- Clause endpoints at one lifted clause vertex, in original literal order. -/
def clauseRouteEndpointsAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    List (CNFRouteEndpoint Variable) :=
  ((drawingClauseRouteEndpoints formula).filter fun endpoint =>
    endpoint.clauseSite = site).insertionSort fun first second =>
      first.occurrence.incidence.literalIndex ≤
        second.occurrence.incidence.literalIndex

/-- Variable endpoints at one lifted variable vertex, in global edge order. -/
def variableRouteEndpointsAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (CNFRouteEndpoint Variable) :=
  ((drawingVariableRouteEndpoints formula).filter fun endpoint =>
    endpoint.variableSite = site).insertionSort fun first second =>
      first.occurrence.edgeIndex ≤ second.occurrence.edgeIndex

/-- The original signed clause, attached to the carrier node of each
incoming incidence route. -/
def routedClauseAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (site : ClauseRouteSite) :
    EmbeddedClause (PlanarSATNode Variable) where
  position :=
    Cell.add
      (liftedIncidenceVertexMacroOrigin formula
        (.clause site.1) site.2) (10, 10)
  literals :=
    (clauseRouteOccurrencesAt formula site).map fun occurrence =>
      (.carrier (.terminal (occurrence.sourceTerminal formula)),
        occurrence.incidence.literal.value)

/-- All routed original clauses in the neighboring block. -/
def drawingRoutedClauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATNode Variable)) :=
  (drawingClauseRouteSites formula).map
    (routedClauseAt formula)

/-- Satisfaction of the routed clause family is exactly satisfaction of
every listed routed clause. -/
theorem drawingRoutedClauseFormula_holds_iff
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment : PlanarSATNode Variable → Bool) :
    FormulaHolds assignment (drawingRoutedClauseFormula formula) ↔
      ∀ site ∈ drawingClauseRouteSites formula,
        ClauseHolds assignment (routedClauseAt formula site) := by
  unfold FormulaHolds drawingRoutedClauseFormula
  constructor
  · intro holds site siteMem
    exact holds (routedClauseAt formula site)
      (List.mem_map.mpr ⟨site, siteMem, rfl⟩)
  · intro holds clause clauseMem
    rcases List.mem_map.mp clauseMem with
      ⟨site, siteMem, clauseEq⟩
    subst clause
    exact holds site siteMem

end PeriodicOrthocrossing
end LeanTrominoes
