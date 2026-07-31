import LeanTrominoes.RetainedFinalFlatNormalizedDirectComponents

/-!
# Route occurrences represented by normalized terminal components

The retained terminal-component proximity theorems ask for one represented
CNF route occurrence at the routed clause or variable site.  Anchor
normalization can change the finite presentation of a source, so this file
recovers those occurrences after translation.

For a routed variable, retained source membership already contains an active
arm link and hence its endpoint occurrence.  For a routed clause, the
original final-route literal proves that its source occurrence list is
nonempty; translating that occurrence follows the source into the normalized
finite frame.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- A normalized routed-variable source retains an occurrence represented at
its variable site, together with the active arm link's first endpoint. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.exists_variableRouteOccurrence_of_source_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    {site : VariableRouteSite Variable}
    {armIndex : Nat}
    {arm : DuplicatorArm}
    {link : EqualityLink (PlanarSATNode Variable)}
    {localClauseIndex : Nat}
    (sourceEq :
      normalized.source =
        .routedVariable
          site armIndex arm link localClauseIndex) :
    ∃ occurrence ∈ variableRouteOccurrencesAt formula site,
      link.first =
        .carrier (.terminal
          (occurrence.targetTerminal formula)) := by
  have sourceMember := normalized.sourceMember
  rw [sourceEq] at sourceMember
  exact
    exists_routeOccurrence_of_routedVariableLinkMember
      formula site sourceMember.2.1

/-- A normalized routed-clause source represents at least one occurrence at
its translated clause site. -/
theorem
    FinalGaugedFlatNormalizedMacrocellSource.exists_clauseRouteOccurrence_of_source_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    {taggedRoute : List Cell × Nat}
    {macrocell :
      FinalGaugedFlatRouteMacrocellWitness
        formula taggedRoute}
    (normalized :
      FinalGaugedFlatNormalizedMacrocellSource
        formula macrocell)
    {site : ClauseRouteSite}
    (sourceEq :
      normalized.source = .routedClause site) :
    ∃ occurrence,
      occurrence ∈ clauseRouteOccurrencesAt formula site := by
  have componentEq := normalized.componentEq
  rw [sourceEq] at componentEq
  cases originalSourceEq :
      macrocell.routeWitness.metadata.source with
  | crossover crossing localClauseIndex =>
      simp [originalSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component] at componentEq
  | carrier link localClauseIndex =>
      simp [originalSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component] at componentEq
  | bend routeBend localClauseIndex =>
      simp [originalSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component] at componentEq
  | routedClause originalSite =>
      have siteEq :
          site =
            clauseRouteSitePeriodTranslate originalSite
              macrocell.routeWitness.physicalShift := by
        simpa [originalSourceEq,
          DrawingPlanarSATClauseSource.periodTranslate,
          DrawingPlanarSATClauseSource.component] using
            componentEq
      have clauseMember :=
        macrocell.routeWitness.metadata.retainedLocalClauseMember
          wellFormed degree isLocal
          macrocell.routeWitness.metadata_retainedValid
      have clauseEq :
          macrocell.routeWitness.metadata.clause =
            (routedClauseAt formula originalSite).rename
              planarSATExternalVariableMap := by
        simpa [originalSourceEq,
          DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex] using
            clauseMember
      have literalMember := macrocell.routeWitness.literalMember
      rw [clauseEq] at literalMember
      rcases
          exists_clauseRouteOccurrence_of_routedClauseLiteralMember
            formula originalSite literalMember with
        ⟨occurrence, occurrenceMember⟩
      refine
        ⟨occurrence.periodTranslate
            macrocell.routeWitness.physicalShift, ?_⟩
      rw [siteEq, clauseRouteOccurrencesAt_periodTranslate]
      exact List.mem_map.mpr
        ⟨occurrence, occurrenceMember, rfl⟩
  | routedVariable
      originalSite originalArmIndex originalArm
      originalLink localClauseIndex =>
      simp [originalSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component] at componentEq

end PeriodicOrthocrossing
end LeanTrominoes
