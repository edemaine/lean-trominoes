import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingPlanarSATCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierCrossoverGeometry
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendProximity
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierTerminalComponentAllSeparation

/-!
# Complete component separation for the retained planar SAT formula

The selected retained carrier family now has all five pairwise geometric
interfaces: another carrier, a crossover, a bend, a routed source clause, or
a routed variable arm.  This file packages those theorems at the metadata
level and combines them with the existing non-carrier macrocell theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- A clause source whose component is a carrier is itself a carrier source,
with only its local clause index forgotten by the component projection. -/
theorem DrawingPlanarSATClauseSource.exists_eq_carrier_of_component_eq
    {Variable : Type*}
    (source : DrawingPlanarSATClauseSource Variable)
    (link : EqualityLink CarrierNode)
    (componentEq : source.component = .carrier link) :
    ∃ localClauseIndex, source = .carrier link localClauseIndex := by
  cases source <;>
    simp_all [DrawingPlanarSATClauseSource.component]

/-- A literal of a represented routed source clause witnesses at least one
route occurrence at that clause site. -/
theorem exists_clauseRouteOccurrence_of_routedClauseLiteralMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        ((routedClauseAt formula site).rename
          planarSATExternalVariableMap).literals.zipIdx) :
    ∃ occurrence,
      occurrence ∈ clauseRouteOccurrencesAt formula site := by
  have indexLt :=
    List.snd_lt_of_mem_zipIdx literalMember
  have occurrenceLengthPositive :
      0 < (clauseRouteOccurrencesAt formula site).length := by
    simpa [routedClauseAt, EmbeddedClause.rename,
      EmbeddedClause.map] using Nat.zero_lt_of_lt indexLt
  let occurrence :=
    (clauseRouteOccurrencesAt formula site).get
      ⟨0, occurrenceLengthPositive⟩
  exact
    ⟨occurrence,
      List.get_mem
        (clauseRouteOccurrencesAt formula site)
        ⟨0, occurrenceLengthPositive⟩⟩

/-- Retained validity agrees with the original validity predicate for every
non-carrier source. -/
theorem DrawingPlanarSATClauseMetadata.valid_of_retainedValid_of_not_carrier
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (notCarrier :
      ¬∃ link, metadata.source.component = .carrier link) :
    metadata.Valid formula := by
  rcases metadata with ⟨clause, source⟩
  cases source <;>
    simp_all [DrawingPlanarSATClauseMetadata.RetainedValid,
      DrawingPlanarSATClauseMetadata.Valid,
      DrawingPlanarSATClauseSource.component]

/-- A retained carrier component avoids every distinct retained-valid
component when it is listed first. -/
theorem
    retainedDrawingPlanarSATMetadata_routesAvoidEachOther_of_first_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (differentComponents :
      first.source.component ≠ second.source.component)
    (link : EqualityLink CarrierNode)
    (firstCarrier :
      first.source.component = .carrier link) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((first.source.incidenceDrawing formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  rcases first with ⟨firstClause, firstSource⟩
  rcases firstSource.exists_eq_carrier_of_component_eq
      link firstCarrier with
    ⟨firstClauseIndex, firstSourceEq⟩
  subst firstSource
  have firstClauseMember :=
    (⟨firstClause, .carrier link firstClauseIndex⟩ :
      DrawingPlanarSATClauseMetadata Variable)
      |>.retainedLocalClauseMember
        wellFormed degree isLocal firstValid
  rcases second with ⟨secondClause, secondSource⟩
  cases secondSource with
  | crossover crossing secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause, .crossover crossing secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      exact
        retainedDrawingPlanarSATCarrierCrossoverRoutesAvoidEachOther
          wellFormed degree isLocal firstValid.1 secondValid.1
          firstClauseMember firstLiteralMember
          secondClauseMember secondLiteralMember
  | carrier secondLink secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause, .carrier secondLink secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      have linksDifferent : link ≠ secondLink := by
        intro linksEqual
        subst secondLink
        exact differentComponents rfl
      exact
        retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther
          wellFormed degree isLocal firstValid.1 secondValid.1
          linksDifferent firstClauseMember firstLiteralMember
          secondClauseMember secondLiteralMember
  | bend routeBend secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause, .bend routeBend secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      exact
        retainedDrawingPlanarSATCarrierBendRoutesAvoidEachOther
          wellFormed degree isLocal firstValid.1 secondValid.1
          firstClauseMember firstLiteralMember
          secondClauseMember secondLiteralMember
  | routedClause site =>
      have secondClauseMember :=
        (⟨secondClause, .routedClause site⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      have literalAtSite :
          (secondLiteral, secondLiteralIndex) ∈
            ((routedClauseAt formula site).rename
              planarSATExternalVariableMap).literals.zipIdx := by
        rw [secondValid.2] at secondLiteralMember
        exact secondLiteralMember
      rcases
          exists_clauseRouteOccurrence_of_routedClauseLiteralMember
            formula site literalAtSite with
        ⟨occurrence, occurrenceMember⟩
      exact
        retainedDrawingPlanarSATCarrierRoutedClauseRoutesAvoidEachOther
          wellFormed degree isLocal firstValid.1 occurrenceMember
          firstClauseMember firstLiteralMember
          secondClauseMember secondLiteralMember
  | routedVariable site armIndex arm routedLink secondClauseIndex =>
      have secondClauseMember :=
        (⟨secondClause,
            .routedVariable site armIndex arm
              routedLink secondClauseIndex⟩ :
          DrawingPlanarSATClauseMetadata Variable)
          |>.retainedLocalClauseMember
            wellFormed degree isLocal secondValid
      exact
        retainedDrawingPlanarSATCarrierRoutedVariableRoutesAvoidEachOther
          wellFormed degree isLocal firstValid.1
          (List.fst_mem_of_mem_zipIdx secondValid.2.1)
          firstClauseMember firstLiteralMember
          secondClauseMember secondLiteralMember

/-- Every distinct pair involving at least one retained carrier component
has continuously separated routes. -/
theorem retainedDrawingPlanarSATMetadata_carrierRoutesAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx)
    (differentComponents :
      first.source.component ≠ second.source.component)
    (carrier :
      (∃ link, first.source.component = .carrier link) ∨
        ∃ link, second.source.component = .carrier link) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      ((first.source.incidenceDrawing formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  rcases carrier with firstCarrier | secondCarrier
  · rcases firstCarrier with ⟨link, firstCarrier⟩
    exact
      retainedDrawingPlanarSATMetadata_routesAvoidEachOther_of_first_carrier
        formula wellFormed degree isLocal
        first second firstValid secondValid
        firstLiteralMember secondLiteralMember
        differentComponents link firstCarrier
  · rcases secondCarrier with ⟨link, secondCarrier⟩
    exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
      (retainedDrawingPlanarSATMetadata_routesAvoidEachOther_of_first_carrier
        formula wellFormed degree isLocal
        second first secondValid firstValid
        secondLiteralMember firstLiteralMember
        (Ne.symm differentComponents) link secondCarrier)

/-- Complete component-level separation predicate for the retained
presentation. -/
def RetainedDrawingPlanarSATComponentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ (first second : DrawingPlanarSATClauseMetadata Variable),
    first.RetainedValid formula →
      second.RetainedValid formula →
        ∀ {firstLiteral secondLiteral :
            PlanarSATVariable Variable × Bool}
          {firstLiteralIndex secondLiteralIndex : Nat},
          (firstLiteral, firstLiteralIndex) ∈
              first.clause.literals.zipIdx →
            (secondLiteral, secondLiteralIndex) ∈
                second.clause.literals.zipIdx →
              first.source.component ≠ second.source.component →
                EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
                  ((first.source.incidenceDrawing formula).routes
                    first.source.localClauseIndex firstLiteralIndex)
                  ((second.source.incidenceDrawing formula).routes
                    second.source.localClauseIndex secondLiteralIndex)

/-- All distinct retained-valid component pairs are continuously separated. -/
theorem retainedDrawingPlanarSAT_componentRoutesSeparated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal) :
    RetainedDrawingPlanarSATComponentRoutesSeparated formula := by
  intro first second firstValid secondValid
    firstLiteral secondLiteral
    firstLiteralIndex secondLiteralIndex
    firstLiteralMember secondLiteralMember differentComponents
  by_cases firstCarrier :
      ∃ link, first.source.component = .carrier link
  · exact
      retainedDrawingPlanarSATMetadata_carrierRoutesAvoidEachOther
        formula wellFormed degree isLocal
        first second firstValid secondValid
        firstLiteralMember secondLiteralMember differentComponents
        (Or.inl firstCarrier)
  by_cases secondCarrier :
      ∃ link, second.source.component = .carrier link
  · exact
      retainedDrawingPlanarSATMetadata_carrierRoutesAvoidEachOther
        formula wellFormed degree isLocal
        first second firstValid secondValid
        firstLiteralMember secondLiteralMember differentComponents
        (Or.inr secondCarrier)
  rcases
      first.source.component.exists_macrocellCenter_of_not_carrier
        formula firstCarrier with
    ⟨firstCenter, firstCenterEq⟩
  rcases
      second.source.component.exists_macrocellCenter_of_not_carrier
        formula secondCarrier with
    ⟨secondCenter, secondCenterEq⟩
  exact
    drawingPlanarSATMetadata_noncarrierRoutesAvoidEachOther
      formula wellFormed degree isLocal
      first second
      (first.valid_of_retainedValid_of_not_carrier
        firstValid firstCarrier)
      (second.valid_of_retainedValid_of_not_carrier
        secondValid secondCarrier)
      firstCenter secondCenter firstCenterEq secondCenterEq
      differentComponents firstLiteralMember secondLiteralMember

end PeriodicOrthocrossing
end LeanTrominoes
