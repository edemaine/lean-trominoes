import LeanTrominoes.RetainedAngularFanDirectSourcePrefixProfiles
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

end PeriodicEightOccurrenceSplit
end LeanTrominoes
