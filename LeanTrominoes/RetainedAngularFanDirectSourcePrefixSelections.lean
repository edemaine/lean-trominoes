import LeanTrominoes.RetainedAngularFanDirectSourcePrefixProfiles
import LeanTrominoes.RetainedAngularFanOuterCoordinatedSeparation
import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings
import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex

/-!
# Selecting direct source-prefix certificates from clause metadata

The finite direct-source atlas is indexed by fixed local component data.
This file bridges that finite indexing to genuine retained planar-SAT clause
metadata and presentation-indexed literals.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicThreeSATThree
open PeriodicOrthocrossing

/-- The atlas entry selected for one literal of a positioned direct local
component, together with its exact route-direction match. -/
structure RetainedDirectSourcePrefixSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat) where
  kind : RetainedDirectClauseKind
  index : Fin (retainedDirectSourcePrefixChoices kind).length
  direction_eq :
    (retainedDirectSourcePrefixChoiceAt kind index).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((source.incidenceDrawing formula).routes
            source.localClauseIndex literalIndex))

/-- Two literals of one direct clause select two different entries of the
same finite atlas profile. -/
structure RetainedDirectSourcePrefixPairSelection
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (firstLiteralIndex secondLiteralIndex : Nat) where
  kind : RetainedDirectClauseKind
  firstIndex :
    Fin (retainedDirectSourcePrefixChoices kind).length
  secondIndex :
    Fin (retainedDirectSourcePrefixChoices kind).length
  indicesDifferent : firstIndex ≠ secondIndex
  firstDirection_eq :
    (retainedDirectSourcePrefixChoiceAt
      kind firstIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((source.incidenceDrawing formula).routes
            source.localClauseIndex firstLiteralIndex))
  secondDirection_eq :
    (retainedDirectSourcePrefixChoiceAt
      kind secondIndex).direction =
      classifiedRetainedTerminalDirection
        (routeTerminalVector
          ((source.incidenceDrawing formula).routes
            source.localClauseIndex secondLiteralIndex))

/-- A pair selected from genuine direct metadata imports the atlas's
ordinary separation and head-only-contact certificate at any common gate. -/
theorem RetainedDirectSourcePrefixPairSelection.positionedEscapes_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (gate : Cell) :
    RoutesAvoidEachOther
        (retainedDirectPositionedSourceEscapeRoute
          gate selection.kind selection.firstIndex)
        (retainedDirectPositionedSourceEscapeRoute
          gate selection.kind selection.secondIndex) ∧
      RoutesMeetOnlyAtHeads
        (retainedDirectPositionedSourceEscapeRoute
          gate selection.kind selection.firstIndex)
        (retainedDirectPositionedSourceEscapeRoute
          gate selection.kind selection.secondIndex) :=
  retainedDirectPositionedSourceEscapeRoutes_separated
    gate selection.kind selection.firstIndex selection.secondIndex
    selection.indicesDifferent

/-- The first selected atlas entry packaged at its actual center, length,
and occurrence slot. -/
def RetainedDirectSourcePrefixPairSelection.firstEscapeCertificate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (center : Cell)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalFanOuterSourceEscapeCertificate
      center
      ((retainedDirectSourcePrefixChoiceAt
        selection.kind selection.firstIndex).direction, length)
      slot :=
  retainedDirectSourceEscapeCertificateAt
    selection.kind selection.firstIndex center length slot

/-- The second selected atlas entry packaged at its actual center, length,
and occurrence slot. -/
def RetainedDirectSourcePrefixPairSelection.secondEscapeCertificate
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (center : Cell)
    (length : Nat)
    (slot : RetainedTerminalSlot) :
    RetainedTerminalFanOuterSourceEscapeCertificate
      center
      ((retainedDirectSourcePrefixChoiceAt
        selection.kind selection.secondIndex).direction, length)
      slot :=
  retainedDirectSourceEscapeCertificateAt
    selection.kind selection.secondIndex center length slot

/-- When the two actual demands have the common source-clause gate, their
packaged 64-block escape certificates inherit the atlas's ordinary
separation and head-only contact property. -/
theorem
    RetainedDirectSourcePrefixPairSelection.escapeCertificates_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (firstCenter secondCenter : Cell)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (gatesEqual :
      (retainedAngularFanOuterDemand
        firstCenter
        ((retainedDirectSourcePrefixChoiceAt
          selection.kind selection.firstIndex).direction,
          firstLength)
        firstSlot).gate =
      (retainedAngularFanOuterDemand
        secondCenter
        ((retainedDirectSourcePrefixChoiceAt
          selection.kind selection.secondIndex).direction,
          secondLength)
        secondSlot).gate) :
    RoutesAvoidEachOther
        (selection.firstEscapeCertificate
          firstCenter firstLength firstSlot).route
        (selection.secondEscapeCertificate
          secondCenter secondLength secondSlot).route ∧
      RoutesMeetOnlyAtHeads
        (selection.firstEscapeCertificate
          firstCenter firstLength firstSlot).route
        (selection.secondEscapeCertificate
          secondCenter secondLength secondSlot).route := by
  unfold RetainedDirectSourcePrefixPairSelection.firstEscapeCertificate
    RetainedDirectSourcePrefixPairSelection.secondEscapeCertificate
  rw [
    retainedDirectSourceEscapeCertificateAt_route_eq_positioned,
    retainedDirectSourceEscapeCertificateAt_route_eq_positioned,
    gatesEqual]
  exact
    retainedDirectPositionedSourceEscapeRoutes_separated
      (retainedAngularFanOuterDemand
        secondCenter
        ((retainedDirectSourcePrefixChoiceAt
          selection.kind selection.secondIndex).direction,
          secondLength)
        secondSlot).gate
      selection.kind selection.firstIndex selection.secondIndex
      selection.indicesDifferent

/-- Once the three contact-free pairs involving complete tails are supplied,
the selected atlas escapes assemble into separated complete outer routes
whose common clause gate is their only possible contact. -/
theorem
    RetainedDirectSourcePrefixPairSelection.coordinatedCompleteRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    {source : DrawingPlanarSATClauseSource Variable}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (selection :
      RetainedDirectSourcePrefixPairSelection
        formula source firstLiteralIndex secondLiteralIndex)
    (firstCenter secondCenter : Cell)
    (firstLength secondLength : Nat)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (gatesEqual :
      (retainedAngularFanOuterDemand
        firstCenter
        ((retainedDirectSourcePrefixChoiceAt
          selection.kind selection.firstIndex).direction,
          firstLength)
        firstSlot).gate =
      (retainedAngularFanOuterDemand
        secondCenter
        ((retainedDirectSourcePrefixChoiceAt
          selection.kind selection.secondIndex).direction,
          secondLength)
        secondSlot).gate)
    (firstEscapeAvoidSecondTail :
      RoutesStrictlyAvoidEachOther
        (selection.firstEscapeCertificate
          firstCenter firstLength firstSlot).route
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          secondCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.secondIndex).direction,
            secondLength)
          secondSlot))
    (firstTailAvoidSecondEscape :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          firstCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.firstIndex).direction,
            firstLength)
          firstSlot)
        (selection.secondEscapeCertificate
          secondCenter secondLength secondSlot).route)
    (tailsAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          firstCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.firstIndex).direction,
            firstLength)
          firstSlot)
        (retainedTerminalFanOuterCoordinatedEscapedCompleteTail
          secondCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.secondIndex).direction,
            secondLength)
          secondSlot)) :
    RoutesAvoidEachOther
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          firstCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.firstIndex).direction,
            firstLength)
          firstSlot
          (selection.firstEscapeCertificate
            firstCenter firstLength firstSlot))
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          secondCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.secondIndex).direction,
            secondLength)
          secondSlot
          (selection.secondEscapeCertificate
            secondCenter secondLength secondSlot)) ∧
      RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          firstCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.firstIndex).direction,
            firstLength)
          firstSlot
          (selection.firstEscapeCertificate
            firstCenter firstLength firstSlot))
        (retainedTerminalFanOuterCoordinatedEscapedCompleteRoute
          secondCenter
          ((retainedDirectSourcePrefixChoiceAt
            selection.kind selection.secondIndex).direction,
            secondLength)
          secondSlot
          (selection.secondEscapeCertificate
            secondCenter secondLength secondSlot)) := by
  have escapesSeparated :=
    selection.escapeCertificates_separated
      firstCenter secondCenter firstLength secondLength
      firstSlot secondSlot gatesEqual
  exact
    retainedTerminalFanOuterCoordinatedEscapedCompleteRoutes_separated
      firstCenter secondCenter
      ((retainedDirectSourcePrefixChoiceAt
        selection.kind selection.firstIndex).direction,
        firstLength)
      ((retainedDirectSourcePrefixChoiceAt
        selection.kind selection.secondIndex).direction,
        secondLength)
      firstSlot secondSlot
      (selection.firstEscapeCertificate
        firstCenter firstLength firstSlot)
      (selection.secondEscapeCertificate
        secondCenter secondLength secondSlot)
      escapesSeparated.1 escapesSeparated.2
      firstEscapeAvoidSecondTail
      firstTailAvoidSecondEscape tailsAvoid

/-- A genuine crossover-clause literal selects the atlas entry with its
fixed local clause and literal indices. -/
theorem exists_retainedDirectSourcePrefixSelection_crossover
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause, .crossover crossing localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    Nonempty
      (RetainedDirectSourcePrefixSelection
        formula (.crossover crossing localClauseIndex) literalIndex) := by
  have localClauseIndexLt :
      localClauseIndex < 26 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2
    simpa [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      crossoverFormula] using indexLt
  let clauseIndex : Fin 26 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).length :=
    List.snd_lt_of_mem_zipIdx valid.2
  have localClauseEq :
      (drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have literalIndexLt :
      literalIndex <
        (retainedDirectSourcePrefixChoices
          (.crossover clauseIndex)).length := by
    rw [retainedDirectCrossoverPrefixChoices_length]
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseLiteralsLength :
        clause.literals.length =
          (retainedDirectCrossoverClauseAt
            clauseIndex).literals.length := by
      rw [← localClauseEq]
      simp [drawingPlanarSATCrossoverFormulaAt,
        scopedCrossoverInstance, instantiateFormula,
        retainedDirectCrossoverClauseAt,
        EmbeddedClause.place, EmbeddedClause.rename,
        EmbeddedClause.map, clauseIndex]
    simpa [clauseLiteralsLength] using literalLt
  let atlasIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length :=
    ⟨literalIndex, literalIndexLt⟩
  exact
    ⟨{
      kind := .crossover clauseIndex
      index := atlasIndex
      direction_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, atlasIndex] using
          retainedDirectCrossoverPrefixChoice_positionedDirection
            formula crossing clauseIndex atlasIndex
    }⟩

/-- Distinct literals of one genuine crossover clause select distinct
entries of its common local atlas profile. -/
theorem exists_retainedDirectSourcePrefixPairSelection_crossover
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (crossing : CrossingRecord)
    (localClauseIndex : Nat)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (valid :
      (⟨clause, .crossover crossing localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    Nonempty
      (RetainedDirectSourcePrefixPairSelection
        formula (.crossover crossing localClauseIndex)
        firstLiteralIndex secondLiteralIndex) := by
  have localClauseIndexLt :
      localClauseIndex < 26 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2
    simpa [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      crossoverFormula] using indexLt
  let clauseIndex : Fin 26 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).length :=
    List.snd_lt_of_mem_zipIdx valid.2
  have localClauseEq :
      (drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have clauseLiteralsLength :
      clause.literals.length =
        (retainedDirectCrossoverClauseAt
          clauseIndex).literals.length := by
    rw [← localClauseEq]
    simp [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      retainedDirectCrossoverClauseAt,
      EmbeddedClause.place, EmbeddedClause.rename,
      EmbeddedClause.map, clauseIndex]
  have firstLiteralIndexLt :
      firstLiteralIndex <
        (retainedDirectSourcePrefixChoices
          (.crossover clauseIndex)).length := by
    rw [retainedDirectCrossoverPrefixChoices_length]
    simpa [clauseLiteralsLength] using
      List.snd_lt_of_mem_zipIdx firstLiteralMember
  have secondLiteralIndexLt :
      secondLiteralIndex <
        (retainedDirectSourcePrefixChoices
          (.crossover clauseIndex)).length := by
    rw [retainedDirectCrossoverPrefixChoices_length]
    simpa [clauseLiteralsLength] using
      List.snd_lt_of_mem_zipIdx secondLiteralMember
  let firstIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length :=
    ⟨firstLiteralIndex, firstLiteralIndexLt⟩
  let secondIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.crossover clauseIndex)).length :=
    ⟨secondLiteralIndex, secondLiteralIndexLt⟩
  exact
    ⟨{
      kind := .crossover clauseIndex
      firstIndex := firstIndex
      secondIndex := secondIndex
      indicesDifferent := by
        intro equal
        exact literalIndicesDifferent
          (congrArg Fin.val equal)
      firstDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, firstIndex] using
          retainedDirectCrossoverPrefixChoice_positionedDirection
            formula crossing clauseIndex firstIndex
      secondDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, secondIndex] using
          retainedDirectCrossoverPrefixChoice_positionedDirection
            formula crossing clauseIndex secondIndex
    }⟩

/-- A genuine routed-variable implication literal selects the atlas entry
for its physical arm, local clause, and literal indices. -/
theorem exists_retainedDirectSourcePrefixSelection_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause,
        .routedVariable site armIndex arm link localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    Nonempty
      (RetainedDirectSourcePrefixSelection
        formula
        (.routedVariable
          site armIndex arm link localClauseIndex)
        literalIndex) := by
  have localClauseIndexLt :
      localClauseIndex < 2 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2.2.2
    simpa [drawingPlanarSATRoutedVariableFormulaAt,
      equalityInstance] using indexLt
  let clauseIndex : Fin 2 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2.2.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATRoutedVariableFormulaAt
          link).length :=
    List.snd_lt_of_mem_zipIdx valid.2.2.2
  have localClauseEq :
      (drawingPlanarSATRoutedVariableFormulaAt
        link).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have literalIndexLt :
      literalIndex <
        (retainedDirectSourcePrefixChoices
          (.duplicator arm clauseIndex)).length := by
    rw [retainedDirectDuplicatorPrefixChoices_length]
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseLiteralsLength :
        clause.literals.length =
          (retainedDirectDuplicatorClauseAt
            arm clauseIndex).literals.length := by
      rw [← localClauseEq]
      simp [drawingPlanarSATRoutedVariableFormulaAt,
        retainedDirectDuplicatorClauseAt,
        duplicatorArmFormula, equalityInstance,
        EmbeddedClause.rename, EmbeddedClause.map,
        clauseIndex]
      interval_cases localClauseIndex <;> rfl
    simpa [clauseLiteralsLength] using literalLt
  let atlasIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length :=
    ⟨literalIndex, literalIndexLt⟩
  exact
    ⟨{
      kind := .duplicator arm clauseIndex
      index := atlasIndex
      direction_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, atlasIndex] using
          retainedDirectDuplicatorPrefixChoice_positionedDirection
            formula site arm link clauseIndex atlasIndex
    }⟩

/-- Distinct literals of one routed-variable implication clause select
distinct entries of its common arm-and-clause atlas profile. -/
theorem exists_retainedDirectSourcePrefixPairSelection_routedVariable
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : VariableRouteSite Variable)
    (armIndex : Nat)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (localClauseIndex : Nat)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (valid :
      (⟨clause,
        .routedVariable site armIndex arm link localClauseIndex⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    Nonempty
      (RetainedDirectSourcePrefixPairSelection
        formula
        (.routedVariable
          site armIndex arm link localClauseIndex)
        firstLiteralIndex secondLiteralIndex) := by
  have localClauseIndexLt :
      localClauseIndex < 2 := by
    have indexLt :=
      List.snd_lt_of_mem_zipIdx valid.2.2.2
    simpa [drawingPlanarSATRoutedVariableFormulaAt,
      equalityInstance] using indexLt
  let clauseIndex : Fin 2 :=
    ⟨localClauseIndex, localClauseIndexLt⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp valid.2.2.2
  have localFormulaIndexLt :
      localClauseIndex <
        (drawingPlanarSATRoutedVariableFormulaAt
          link).length :=
    List.snd_lt_of_mem_zipIdx valid.2.2.2
  have localClauseEq :
      (drawingPlanarSATRoutedVariableFormulaAt
        link).get
          ⟨localClauseIndex, localFormulaIndexLt⟩ =
        clause := by
    apply Option.some.inj
    simpa [List.getElem?_eq_getElem,
      localFormulaIndexLt] using clauseLookup
  have clauseLiteralsLength :
      clause.literals.length =
        (retainedDirectDuplicatorClauseAt
          arm clauseIndex).literals.length := by
    rw [← localClauseEq]
    simp [drawingPlanarSATRoutedVariableFormulaAt,
      retainedDirectDuplicatorClauseAt,
      duplicatorArmFormula, equalityInstance,
      EmbeddedClause.rename, EmbeddedClause.map,
      clauseIndex]
    interval_cases localClauseIndex <;> rfl
  have firstLiteralIndexLt :
      firstLiteralIndex <
        (retainedDirectSourcePrefixChoices
          (.duplicator arm clauseIndex)).length := by
    rw [retainedDirectDuplicatorPrefixChoices_length]
    simpa [clauseLiteralsLength] using
      List.snd_lt_of_mem_zipIdx firstLiteralMember
  have secondLiteralIndexLt :
      secondLiteralIndex <
        (retainedDirectSourcePrefixChoices
          (.duplicator arm clauseIndex)).length := by
    rw [retainedDirectDuplicatorPrefixChoices_length]
    simpa [clauseLiteralsLength] using
      List.snd_lt_of_mem_zipIdx secondLiteralMember
  let firstIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length :=
    ⟨firstLiteralIndex, firstLiteralIndexLt⟩
  let secondIndex :
      Fin (retainedDirectSourcePrefixChoices
        (.duplicator arm clauseIndex)).length :=
    ⟨secondLiteralIndex, secondLiteralIndexLt⟩
  exact
    ⟨{
      kind := .duplicator arm clauseIndex
      firstIndex := firstIndex
      secondIndex := secondIndex
      indicesDifferent := by
        intro equal
        exact literalIndicesDifferent
          (congrArg Fin.val equal)
      firstDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, firstIndex] using
          retainedDirectDuplicatorPrefixChoice_positionedDirection
            formula site arm link clauseIndex firstIndex
      secondDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          clauseIndex, secondIndex] using
          retainedDirectDuplicatorPrefixChoice_positionedDirection
            formula site arm link clauseIndex secondIndex
    }⟩

/-- A genuine routed source-clause literal selects the atlas entry named by
its physical arm, even when the source clause presents only a subset of the
three possible arms or lists them in another order. -/
theorem exists_retainedDirectSourcePrefixSelection_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : ClauseRouteSite)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (valid :
      (⟨clause, .routedClause site⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    Nonempty
      (RetainedDirectSourcePrefixSelection
        formula (.routedClause site) literalIndex) := by
  have literalIndexLt :
      literalIndex <
        (routedClausePortLiterals formula site).length := by
    have literalLt :=
      List.snd_lt_of_mem_zipIdx literalMember
    have clauseEq :
        clause =
          (routedClauseAt formula site).rename
            planarSATExternalVariableMap := by
      simpa using valid.2
    rw [clauseEq] at literalLt
    simpa [routedClausePortLiterals, routedClauseAt,
      EmbeddedClause.rename, EmbeddedClause.map] using literalLt
  let portIndex :
      Fin (routedClausePortLiterals formula site).length :=
    ⟨literalIndex, literalIndexLt⟩
  exact
    ⟨{
      kind := .routedClause
      index :=
        retainedDirectRoutedClauseArmIndex
          ((routedClausePortLiterals formula site).get
            portIndex).1
      direction_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          portIndex] using
          retainedDirectRoutedClauseArmChoice_positionedDirection
            formula site portIndex
    }⟩

/-- Distinct literals of one routed source clause have distinct physical
arms and therefore select distinct entries of the common routed atlas. -/
theorem exists_retainedDirectSourcePrefixPairSelection_routedClause
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (site : ClauseRouteSite)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (valid :
      (⟨clause, .routedClause site⟩ :
        DrawingPlanarSATClauseMetadata Variable).RetainedValid formula)
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    Nonempty
      (RetainedDirectSourcePrefixPairSelection
        formula (.routedClause site)
        firstLiteralIndex secondLiteralIndex) := by
  have clauseEq :
      clause =
        (routedClauseAt formula site).rename
          planarSATExternalVariableMap := by
    simpa using valid.2
  have firstLiteralIndexLt :
      firstLiteralIndex <
        (routedClausePortLiterals formula site).length := by
    have literalLt :=
      List.snd_lt_of_mem_zipIdx firstLiteralMember
    rw [clauseEq] at literalLt
    simpa [routedClausePortLiterals, routedClauseAt,
      EmbeddedClause.rename, EmbeddedClause.map] using literalLt
  have secondLiteralIndexLt :
      secondLiteralIndex <
        (routedClausePortLiterals formula site).length := by
    have literalLt :=
      List.snd_lt_of_mem_zipIdx secondLiteralMember
    rw [clauseEq] at literalLt
    simpa [routedClausePortLiterals, routedClauseAt,
      EmbeddedClause.rename, EmbeddedClause.map] using literalLt
  let firstPortIndex :
      Fin (routedClausePortLiterals formula site).length :=
    ⟨firstLiteralIndex, firstLiteralIndexLt⟩
  let secondPortIndex :
      Fin (routedClausePortLiterals formula site).length :=
    ⟨secondLiteralIndex, secondLiteralIndexLt⟩
  let firstArm :=
    ((routedClausePortLiterals formula site).get
      firstPortIndex).1
  let secondArm :=
    ((routedClausePortLiterals formula site).get
      secondPortIndex).1
  have armsDifferent : firstArm ≠ secondArm := by
    intro armsEqual
    let firstMappedIndex :
        Fin ((routedClausePortLiterals
          formula site).map Prod.fst).length :=
      ⟨firstLiteralIndex, by
        simpa using firstLiteralIndexLt⟩
    let secondMappedIndex :
        Fin ((routedClausePortLiterals
          formula site).map Prod.fst).length :=
      ⟨secondLiteralIndex, by
        simpa using secondLiteralIndexLt⟩
    have mappedValuesEqual :
        ((routedClausePortLiterals
          formula site).map Prod.fst).get firstMappedIndex =
        ((routedClausePortLiterals
          formula site).map Prod.fst).get secondMappedIndex := by
      simpa [firstMappedIndex, secondMappedIndex,
        firstArm, secondArm, firstPortIndex,
        secondPortIndex] using armsEqual
    have mappedIndicesEqual :
        firstMappedIndex = secondMappedIndex :=
      (routedClausePortLiterals_ports_nodup
        formula degree site).injective_get
          mappedValuesEqual
    exact literalIndicesDifferent
      (congrArg Fin.val mappedIndicesEqual)
  let firstIndex :=
    retainedDirectRoutedClauseArmIndex firstArm
  let secondIndex :=
    retainedDirectRoutedClauseArmIndex secondArm
  exact
    ⟨{
      kind := .routedClause
      firstIndex := firstIndex
      secondIndex := secondIndex
      indicesDifferent := by
        intro equal
        exact armsDifferent
          (retainedDirectRoutedClauseArmIndex_injective equal)
      firstDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          firstArm, firstPortIndex, firstIndex] using
          retainedDirectRoutedClauseArmChoice_positionedDirection
            formula site firstPortIndex
      secondDirection_eq := by
        simpa [DrawingPlanarSATClauseSource.incidenceDrawing,
          DrawingPlanarSATClauseSource.localClauseIndex,
          secondArm, secondPortIndex, secondIndex] using
          retainedDirectRoutedClauseArmChoice_positionedDirection
            formula site secondPortIndex
    }⟩

/-- The direct-source trichotomy emitted by normalized component analysis is
enough to select a checked atlas entry for every genuine clause literal. -/
theorem
    DrawingPlanarSATClauseMetadata.exists_retainedDirectSourcePrefixSelection_of_directCases
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    {literal : PlanarSATVariable Variable × Bool}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex)) :
    Nonempty
      (RetainedDirectSourcePrefixSelection
        formula metadata.source literalIndex) := by
  rcases metadata with ⟨clause, source⟩
  rcases directCases with
      ⟨crossing, localClauseIndex, rfl⟩ |
      ⟨⟨site, rfl⟩ |
        ⟨site, armIndex, arm, link,
          localClauseIndex, rfl⟩⟩
  · exact
      exists_retainedDirectSourcePrefixSelection_crossover
        formula clause crossing localClauseIndex
        valid literalMember
  · exact
      exists_retainedDirectSourcePrefixSelection_routedClause
        formula clause site valid literalMember
  · exact
      exists_retainedDirectSourcePrefixSelection_routedVariable
        formula clause site armIndex arm link localClauseIndex
        valid literalMember

/-- The same direct-source trichotomy selects a separated pair of atlas
entries for two distinct literals of one retained clause. -/
theorem
    DrawingPlanarSATClauseMetadata.exists_retainedDirectSourcePrefixPairSelection_of_directCases
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        metadata.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        metadata.clause.literals.zipIdx)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (directCases :
      (∃ crossing localClauseIndex,
          metadata.source =
            .crossover crossing localClauseIndex) ∨
        (∃ site,
          metadata.source = .routedClause site) ∨
        (∃ site armIndex arm link localClauseIndex,
          metadata.source =
            .routedVariable
              site armIndex arm link localClauseIndex)) :
    Nonempty
      (RetainedDirectSourcePrefixPairSelection
        formula metadata.source
        firstLiteralIndex secondLiteralIndex) := by
  rcases metadata with ⟨clause, source⟩
  rcases directCases with
      ⟨crossing, localClauseIndex, rfl⟩ |
      ⟨⟨site, rfl⟩ |
        ⟨site, armIndex, arm, link,
          localClauseIndex, rfl⟩⟩
  · exact
      exists_retainedDirectSourcePrefixPairSelection_crossover
        formula clause crossing localClauseIndex
        valid firstLiteralMember secondLiteralMember
        literalIndicesDifferent
  · exact
      exists_retainedDirectSourcePrefixPairSelection_routedClause
        formula degree clause site valid
        firstLiteralMember secondLiteralMember
        literalIndicesDifferent
  · exact
      exists_retainedDirectSourcePrefixPairSelection_routedVariable
        formula clause site armIndex arm link localClauseIndex
        valid firstLiteralMember secondLiteralMember
        literalIndicesDifferent

end PeriodicEightOccurrenceSplit
end LeanTrominoes
