/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitAngularSuffixSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutePairs
import LeanTrominoes.RetainedFinalSourceIncidenceDistinctness

/-!
# Spoke separation in the final coordinated fixed-eight source

Within one final retained source clause, different literal indices name
different physical periodic incidence keys.  Canonical gauging places every
variable representative strictly inside one fundamental square, so a
representative plus a period translate is unique.  Thus different literal
indices also have different canonical source centers.  The generic
factor-36 Figure 7 macrocell theorem then gives strict separation of their
scaled occurrence suffixes.
-/

namespace LeanTrominoes

/-- A representative in one half-open period together with its integer
period translate is unique. -/
theorem periodicRepresentativeAndOffset_eq
    (period : Nat)
    (periodPositive : 0 < period)
    (firstPosition secondPosition firstOffset secondOffset : Int)
    (firstNonnegative : 0 ≤ firstPosition)
    (firstLt : firstPosition < period)
    (secondNonnegative : 0 ≤ secondPosition)
    (secondLt : secondPosition < period)
    (equal :
      firstPosition + period * firstOffset =
        secondPosition + period * secondOffset) :
    firstPosition = secondPosition ∧
      firstOffset = secondOffset := by
  have moduloEqual :=
    congrArg (fun value : Int => value % period) equal
  have positionsEqual : firstPosition = secondPosition := by
    simpa [Int.add_emod, Int.mul_emod,
      Int.emod_eq_of_lt firstNonnegative firstLt,
      Int.emod_eq_of_lt secondNonnegative secondLt] using
      moduloEqual
  constructor
  · exact positionsEqual
  · rw [positionsEqual] at equal
    have productsEqual :
        (period : Int) * firstOffset =
          period * secondOffset := by
      omega
    exact mul_left_cancel₀
      (show (period : Int) ≠ 0 by
        exact_mod_cast ne_of_gt periodPositive)
      productsEqual

namespace PositionedPeriodicCNF

/-- For one clause, equality of canonical lifted literal positions
identifies both the fundamental-square representatives and the literal
offsets. -/
theorem canonicalLiteralPosition_eq_sameClause_imp
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (clause : PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (firstInSquare :
      0 ≤ (placement.position firstLiteral.atom).1 ∧
        (placement.position firstLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position firstLiteral.atom).2 ∧
        (placement.position firstLiteral.atom).2 < placement.period)
    (secondInSquare :
      0 ≤ (placement.position secondLiteral.atom).1 ∧
        (placement.position secondLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position secondLiteral.atom).2 ∧
        (placement.position secondLiteral.atom).2 < placement.period)
    (positionsEqual :
      canonicalLiteralPosition placement clause firstLiteral =
        canonicalLiteralPosition placement clause secondLiteral) :
    placement.position firstLiteral.atom =
        placement.position secondLiteral.atom ∧
      firstLiteral.offset = secondLiteral.offset := by
  rcases firstPositionEq :
      placement.position firstLiteral.atom with
    ⟨firstPositionX, firstPositionY⟩
  rcases secondPositionEq :
      placement.position secondLiteral.atom with
    ⟨secondPositionX, secondPositionY⟩
  rcases firstOffsetEq : firstLiteral.offset with
    ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffsetEq : secondLiteral.offset with
    ⟨secondOffsetX, secondOffsetY⟩
  simp only [canonicalLiteralPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale,
    firstPositionEq, secondPositionEq,
    firstOffsetEq, secondOffsetEq,
    Prod.mk.injEq]
    at positionsEqual
  simp only [firstPositionEq, secondPositionEq]
    at firstInSquare secondInSquare
  have horizontal :=
    periodicRepresentativeAndOffset_eq
      placement.period periodPositive
      firstPositionX secondPositionX
      (firstOffsetX -
        (PeriodicCNF.clauseAnchor clause.literals).1)
      (secondOffsetX -
        (PeriodicCNF.clauseAnchor clause.literals).1)
      firstInSquare.1 firstInSquare.2.1
      secondInSquare.1 secondInSquare.2.1
      positionsEqual.1
  have vertical :=
    periodicRepresentativeAndOffset_eq
      placement.period periodPositive
      firstPositionY secondPositionY
      (firstOffsetY -
        (PeriodicCNF.clauseAnchor clause.literals).2)
      (secondOffsetY -
        (PeriodicCNF.clauseAnchor clause.literals).2)
      firstInSquare.2.2.1 firstInSquare.2.2.2
      secondInSquare.2.2.1 secondInSquare.2.2.2
      positionsEqual.2
  constructor
  · exact Prod.ext horizontal.1 vertical.1
  · exact Prod.ext (by omega) (by omega)

end PositionedPeriodicCNF

namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- The atom of a genuine positioned incidence occurs in the erased
formula's variable-occurrence list. -/
theorem atom_mem_variableOccurrences_of_positioned_members
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    literal.atom ∈ source.erase.variableOccurrences := by
  unfold PeriodicCNF.variableOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨clause.literals, ?_, ?_⟩
  · exact
      PeriodicEightOccurrenceSplitPositioned.erasedClause_mem_of_positioned_mem
        source clauseMember
      |> List.fst_mem_of_mem_zipIdx
  · exact List.mem_map.mpr
      ⟨literal, List.fst_mem_of_mem_zipIdx literalMember, rfl⟩

/-- Different literal indices in one final retained clause have different
canonical source occurrence centers after source-clearance scaling. -/
theorem
    retainedFinalSameClauseCanonicalLiteralPositions_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    let placement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor
    PositionedPeriodicCNF.canonicalLiteralPosition
        placement
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral ≠
      PositionedPeriodicCNF.canonicalLiteralPosition
        placement
        (clause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral := by
  dsimp only
  let source :=
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula
  let placement :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have firstAtomMember :
      firstLiteral.atom ∈ source.erase.variableOccurrences := by
    exact atom_mem_variableOccurrences_of_positioned_members
      source clauseMember firstLiteralMember
  have secondAtomMember :
      secondLiteral.atom ∈ source.erase.variableOccurrences := by
    exact atom_mem_variableOccurrences_of_positioned_members
      source clauseMember secondLiteralMember
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula firstLiteral.atom.original := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        (by simpa [source] using firstAtomMember)
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula secondLiteral.atom.original := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        (by simpa [source] using secondAtomMember)
  have firstStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula firstLiteral.atom
  have secondStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula secondLiteral.atom
  have firstBounds :
      0 ≤ (placement.position firstLiteral.atom).1 ∧
        (placement.position firstLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position firstLiteral.atom).2 ∧
        (placement.position firstLiteral.atom).2 < placement.period := by
    exact
      ⟨firstStrictBounds.1.le, firstStrictBounds.2.1,
        firstStrictBounds.2.2.1.le, firstStrictBounds.2.2.2⟩
  have secondBounds :
      0 ≤ (placement.position secondLiteral.atom).1 ∧
        (placement.position secondLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position secondLiteral.atom).2 ∧
        (placement.position secondLiteral.atom).2 < placement.period := by
    exact
      ⟨secondStrictBounds.1.le, secondStrictBounds.2.1,
        secondStrictBounds.2.2.1.le, secondStrictBounds.2.2.2⟩
  have incidenceKeysNodup :
      source.AllIncidenceKeysNodup := by
    exact
      retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_allIncidenceKeysNodup
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
  have clauseIncidenceKeysNodup :
      clause.IncidenceKeysNodup := by
    rw [PositionedPeriodicCNF.AllIncidenceKeysNodup]
      at incidenceKeysNodup
    exact incidenceKeysNodup clause
      (List.fst_mem_of_mem_zipIdx clauseMember)
  rw [PositionedPeriodicClause.IncidenceKeysNodup]
    at clauseIncidenceKeysNodup
  intro scaledCentersEqual
  have centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause secondLiteral := by
    apply Cell.scale_injective
      (show
        (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
        simp [retainedAngularFanSourceClearanceFactor])
    simpa [placement] using scaledCentersEqual
  have positionAndOffsetEqual :=
    PositionedPeriodicCNF.canonicalLiteralPosition_eq_sameClause_imp
      placement
      (by
        simpa [placement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement]
          using drawingPeriodicPlanarSATPlacement_period_pos formula)
      clause firstLiteral secondLiteral
      firstBounds secondBounds centersEqual
  have atomsEqual :
      firstLiteral.atom = secondLiteral.atom := by
    exact
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
        formula
        sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal
        firstValid secondValid
        (by simpa [placement] using positionAndOffsetEqual.1)
  have keysEqual :
      (firstLiteral.atom, firstLiteral.offset) =
        (secondLiteral.atom, secondLiteral.offset) :=
    Prod.ext atomsEqual positionAndOffsetEqual.2
  have firstIndexLt :
      firstLiteralIndex < clause.literals.length :=
    List.snd_lt_of_mem_zipIdx firstLiteralMember
  have secondIndexLt :
      secondLiteralIndex < clause.literals.length :=
    List.snd_lt_of_mem_zipIdx secondLiteralMember
  have keysEqualAtIndices :
      (clause.literals.map fun literal =>
        (literal.atom, literal.offset))[
          firstLiteralIndex]'(by simpa using firstIndexLt) =
        (clause.literals.map fun literal =>
          (literal.atom, literal.offset))[
            secondLiteralIndex]'(by simpa using secondIndexLt) := by
    simp only [List.getElem_map]
    have firstAt :
        clause.literals[firstLiteralIndex] = firstLiteral :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          firstLiteralMember)).2
    have secondAt :
        clause.literals[secondLiteralIndex] = secondLiteral :=
      (List.getElem?_eq_some_iff.mp
        ((List.mem_zipIdx_iff_getElem?).mp
          secondLiteralMember)).2
    rw [firstAt, secondAt]
    exact keysEqual
  exact literalIndicesDifferent
    (clauseIncidenceKeysNodup.getElem_inj_iff.mp
      keysEqualAtIndices)

/-- The two scaled Figure 7 suffixes selected by distinct literal entries
of one final retained clause are contact-free. -/
theorem
    retainedFinalCoordinatedOccurrenceSuffixes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    let source :=
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).scale retainedAngularFanSourceClearanceFactor
    let placement :=
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
        formula).scale retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula)
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex))
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex)) := by
  dsimp only
  apply scaledAngularOccurrenceSuffix_strictlyAvoid_of_centers_ne
  · simp [retainedTerminalFanRoutingRefinement]
  · exact
      retainedFinalSameClauseCanonicalLiteralPositions_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        clauseMember firstLiteralMember secondLiteralMember
        literalIndicesDifferent

end PeriodicOrthocrossing
end LeanTrominoes
