/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitTerminalPorts
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes

/-!
# Terminal ports through positioned clause deduplication

The physical planar-SAT construction names routes in its original finite
presentation.  Clause-orbit deduplication retains one positioned
representative and subtracts its periodic anchor from every route point.
That common translation does not change the terminal vector.

This file isolates the geometric obligation before reindexing: the raw route
selected by every retained representative must use a valid compass ray, and
equal atoms must use different rays.  The obligation then transports to the
canonical periodic occurrence source consumed by fixed-eight splitting.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

open PeriodicThreeSATThree
open PeriodicEightOccurrenceSplit

/-- Anchor normalization preserves the terminal vector of every route
selected by a retained clause. -/
theorem deduplicatedIncidenceRoutes_routeTerminalVector
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        source.deduplicateByLiterals.clauses.zipIdx)
    (literalIndex : Nat) :
    routeTerminalVector
        (source.deduplicatedIncidenceRoutes placement routes
          clauseIndex literalIndex) =
      routeTerminalVector
        (routes
          (source.representativeClauseIndex clause.literals)
          literalIndex) := by
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp clauseMember
  rw [deduplicatedIncidenceRoutes, clauseLookup]
  exact routeTerminalVector_map_sub _ _

/-- Consequently anchor normalization also preserves the selected compass
port. -/
theorem deduplicatedIncidenceRoutes_routeTerminalPort
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        source.deduplicateByLiterals.clauses.zipIdx)
    (literalIndex : Nat) :
    routeTerminalPort
        (source.deduplicatedIncidenceRoutes placement routes)
        clauseIndex literalIndex =
      routeTerminalPort routes
        (source.representativeClauseIndex clause.literals)
        literalIndex := by
  simp only [routeTerminalPort,
    deduplicatedIncidenceRoutes_routeTerminalVector
      source placement routes clauseMember literalIndex]

/-- Every tagged literal of a positioned erasure comes from the positioned
clause and literal at the same two presentation indices. -/
theorem exists_positionedOccurrence_of_tagged
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {tagged : PeriodicLiteral Variable × Nat × Nat}
    (taggedMember : tagged ∈ taggedLiterals source.erase) :
    ∃ clause : PositionedPeriodicClause Variable,
      (clause, tagged.2.1) ∈ source.clauses.zipIdx ∧
        (tagged.1, tagged.2.2) ∈ clause.literals.zipIdx := by
  simp only [taggedLiterals, List.mem_flatMap,
    List.mem_map] at taggedMember
  rcases taggedMember with
    ⟨taggedClause, taggedClauseMember,
      taggedLiteral, taggedLiteralMember, taggedEqual⟩
  have clauseMember :
      (taggedClause.1, taggedClause.2) ∈
        source.erase.clauses.zipIdx :=
    taggedClauseMember
  change
    (taggedClause.1, taggedClause.2) ∈
      (source.clauses.map
        PositionedPeriodicClause.literals).zipIdx
    at clauseMember
  rw [List.zipIdx_map] at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨positionedTagged, positionedTaggedMember,
      positionedTaggedEqual⟩
  have clauseIndexEqual :
      positionedTagged.2 = taggedClause.2 :=
    congrArg Prod.snd positionedTaggedEqual
  have literalsEqual :
      positionedTagged.1.literals = taggedClause.1 := by
    simpa using congrArg Prod.fst positionedTaggedEqual
  subst tagged
  refine ⟨positionedTagged.1, ?_, ?_⟩
  · simpa only [← clauseIndexEqual] using positionedTaggedMember
  · rw [literalsEqual]
    exact taggedLiteralMember

/-- Raw terminal-ray obligation restricted to the representatives actually
retained by clause-orbit deduplication. -/
structure RepresentativeTerminalPortCertificate
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (routes : IncidenceRoutes) : Prop where
  valid :
    ∀ clause clauseIndex,
      (clause, clauseIndex) ∈
          source.deduplicateByLiterals.clauses.zipIdx →
        ∀ literal literalIndex,
          (literal, literalIndex) ∈ clause.literals.zipIdx →
            (terminalPort
              (routeTerminalVector
                (routes
                  (source.representativeClauseIndex clause.literals)
                  literalIndex))).isSome
  separate :
    ∀ firstClause firstClauseIndex,
      (firstClause, firstClauseIndex) ∈
          source.deduplicateByLiterals.clauses.zipIdx →
        ∀ firstLiteral firstLiteralIndex,
          (firstLiteral, firstLiteralIndex) ∈
              firstClause.literals.zipIdx →
          ∀ secondClause secondClauseIndex,
            (secondClause, secondClauseIndex) ∈
                source.deduplicateByLiterals.clauses.zipIdx →
              ∀ secondLiteral secondLiteralIndex,
                (secondLiteral, secondLiteralIndex) ∈
                    secondClause.literals.zipIdx →
                  firstLiteral.atom = secondLiteral.atom →
                  routeTerminalPort routes
                      (source.representativeClauseIndex
                        firstClause.literals)
                      firstLiteralIndex =
                    routeTerminalPort routes
                      (source.representativeClauseIndex
                        secondClause.literals)
                      secondLiteralIndex →
                  (firstLiteral, firstClauseIndex, firstLiteralIndex) =
                    (secondLiteral, secondClauseIndex, secondLiteralIndex)

/-- A certificate on raw representative routes induces the terminal
certificate on the canonical deduplicated route family. -/
theorem terminalPortCertificate_deduplicatedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : IncidenceRoutes)
    (certificate :
      RepresentativeTerminalPortCertificate source routes) :
    TerminalPortCertificate
      source.deduplicateByLiterals.erase
      (source.deduplicatedIncidenceRoutes placement routes) := by
  constructor
  · intro tagged taggedMember
    rcases exists_positionedOccurrence_of_tagged
        source.deduplicateByLiterals taggedMember with
      ⟨clause, clauseMember, literalMember⟩
    rw [deduplicatedIncidenceRoutes_routeTerminalVector
      source placement routes clauseMember tagged.2.2]
    exact certificate.valid
      clause tagged.2.1 clauseMember
      tagged.1 tagged.2.2 literalMember
  · intro first firstMember second secondMember
      atomsEqual portsEqual
    rcases exists_positionedOccurrence_of_tagged
        source.deduplicateByLiterals firstMember with
      ⟨firstClause, firstClauseMember, firstLiteralMember⟩
    rcases exists_positionedOccurrence_of_tagged
        source.deduplicateByLiterals secondMember with
      ⟨secondClause, secondClauseMember, secondLiteralMember⟩
    rw [deduplicatedIncidenceRoutes_routeTerminalPort
      source placement routes firstClauseMember first.2.2,
      deduplicatedIncidenceRoutes_routeTerminalPort
        source placement routes secondClauseMember second.2.2]
      at portsEqual
    exact certificate.separate
      firstClause first.2.1 firstClauseMember
      first.1 first.2.2 firstLiteralMember
      secondClause second.2.1 secondClauseMember
      second.1 second.2.2 secondLiteralMember
      atomsEqual portsEqual

end PositionedPeriodicCNF
end LeanTrominoes
