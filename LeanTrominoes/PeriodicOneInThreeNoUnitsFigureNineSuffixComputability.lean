/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineSuffixCoreComputability

/-!
# Computability of composed Figure 9 route suffix lookup

This module combines the executable connector core with flattened clause
metadata to compute the complete presentation-indexed suffix dispatcher.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

set_option maxHeartbeats 500000
set_option linter.overlappingInstances false

open PeriodicOrthocrossing

private abbrev ComposedVariable (Variable : Type*) :=
  OneInThreeNoUnitVariable (OneInThreeVariable Variable)

private abbrev GeneratedClause (Variable : Type*) :=
  PositionedPeriodicClause (ComposedVariable Variable)

private abbrev InheritedRouteData (Variable : Type*) :=
  (ClauseIndexData Variable × GeneratedClause Variable) ×
    PeriodicLiteral (ComposedVariable Variable)

/-- All proof-free presentation data needed to classify one final
incidence. -/
private def inheritedRouteData?
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    Option (InheritedRouteData Variable) :=
  (formulaClauseIndexData source)[clauseIndex]?.bind fun metadata =>
    ((PeriodicOneInThreeNoUnitsPositioned.formula
      (PeriodicOneInThreePositioned.formula source)).clauses[clauseIndex]?
        |>.map fun generatedClause => (metadata, generatedClause)).bind fun pair =>
      pair.2.literals[literalIndex]?.map fun generatedLiteral =>
        (pair, generatedLiteral)

private theorem inheritedRouteData?_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input : (Input × Nat) × Nat =>
      inheritedRouteData? (source input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  let metadataFn : Query → Option (ClauseIndexData Variable) := fun input =>
    (formulaClauseIndexData (source input.1.1))[input.1.2]?
  have metadata : Primrec metadataFn :=
    Primrec.list_getElem?.comp
      (formulaClauseIndexData_primrec.comp
        (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp Primrec.fst)
  let targetFn : Query → PositionedPeriodicCNF (ComposedVariable Variable) :=
    fun input => PeriodicOneInThreeNoUnitsPositioned.formula
      (PeriodicOneInThreePositioned.formula (source input.1.1))
  have target : Primrec targetFn :=
    (PeriodicOneInThreeNoUnitsPositioned.formula_primrec.comp
      (PeriodicOneInThreePositioned.formula_primrec.comp
        sourcePrimrec)).comp (Primrec.fst.comp Primrec.fst)
  let generatedClauseFn : Query → Option (GeneratedClause Variable) :=
    fun input => (PeriodicOneInThreeNoUnitsPositioned.formula
      (PeriodicOneInThreePositioned.formula
        (source input.1.1))).clauses[input.1.2]?
  have generatedClause : Primrec generatedClauseFn :=
    Primrec.list_getElem?.comp
      (PositionedPeriodicCNF.clauses_primrec.comp target)
      (Primrec.snd.comp Primrec.fst)
  let selectedPairFn : Query →
      Option (ClauseIndexData Variable × GeneratedClause Variable) :=
    fun input => (metadataFn input).bind fun selectedMetadata =>
      (generatedClauseFn input).map fun selectedClause =>
        (selectedMetadata, selectedClause)
  have selectedPair : Primrec selectedPairFn := by
    exact Primrec.option_bind metadata
      (Primrec.option_map
        (generatedClause.comp Primrec.fst)
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  let selectedFn : Query → Option (InheritedRouteData Variable) :=
    fun input => (selectedPairFn input).bind fun pair =>
      pair.2.literals[input.2]?.map fun literal => (pair, literal)
  have selected : Primrec selectedFn := by
    have literal : Primrec₂ fun (input : Query)
        (pair : ClauseIndexData Variable × GeneratedClause Variable) =>
        pair.2.literals[input.2]? := by
      exact Primrec.list_getElem?.comp
        (PositionedPeriodicClause.literals_primrec.comp
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst) |>.to₂
    exact Primrec.option_bind selectedPair
      (Primrec.option_map literal
        (Primrec.pair
          (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  exact selected.of_eq fun input => by
    unfold selectedFn selectedPairFn metadataFn generatedClauseFn
      inheritedRouteData?
    cases metadataLookup :
        (formulaClauseIndexData (source input.1.1))[input.1.2]? with
    | none => simp
    | some metadata =>
        cases clauseLookup :
            (PeriodicOneInThreeNoUnitsPositioned.formula
              (PeriodicOneInThreePositioned.formula
                (source input.1.1))).clauses[input.1.2]? <;>
          simp

/-- The proof-free selector is exactly a metadata lookup followed by a
literal lookup in the metadata's generated clause. -/
private theorem inheritedRouteData?_eq_metadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (clauseIndex literalIndex : Nat) :
    inheritedRouteData? source clauseIndex literalIndex =
      (formulaClauseMetadata source)[clauseIndex]?.bind fun metadata =>
        metadata.clause.literals[literalIndex]?.map fun literal =>
          ((metadata.indexData, metadata.clause), literal) := by
  unfold inheritedRouteData?
  rw [formulaClauseIndexData_eq, List.getElem?_map,
    ← formulaClauseMetadata_clauses, List.getElem?_map]
  cases (formulaClauseMetadata source)[clauseIndex]? <;> rfl

/-- Executable direct suffix lookup.  Invalid or auxiliary incidences use
the empty fallback; the complete dispatcher adds auxiliary singletons. -/
def orderedInheritedRouteSuffixesComputed
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) : List Cell :=
  Option.casesOn (inheritedRouteData? source clauseIndex literalIndex) []
    fun data => Sum.casesOn data.2.atom
      (fun figureAtom => Sum.casesOn figureAtom
        (fun sourceAtom =>
          let sourceLiteralIndex :=
            sourceLiteralIndexForAtom data.1.1.1.1 sourceAtom
          fanInheritedRouteSuffixAtIndex
            (composedPlacement source sourcePlacement).period
            sourcePlacement.period data.1.1.1.1 data.1.2
            sourceLiteralIndex
            (sourceRoutes data.1.1.1.2 sourceLiteralIndex))
        (fun _ => []))
      (fun _ => [])

/-- Dispatch through two nested auxiliary sums, retaining only the original
source branch. -/
private def nestedSourceOrEmpty
    {Context Source FirstAux SecondAux Output : Type*}
    (sourceBranch : Context → Source → Output)
    (default : Output) (context : Context) :
    (Source ⊕ FirstAux) ⊕ SecondAux → Output
  | .inl (.inl sourceValue) => sourceBranch context sourceValue
  | _ => default

/-- Primitive-recursive dispatch through the two nested auxiliary sums used
by the composed Figure 9 variable type.  Keeping this combinator abstract
prevents elaboration from normalizing the concrete geometric branch. -/
private theorem nestedSourceOrEmpty_primrec
    {Context Source FirstAux SecondAux Output : Type*}
    [Primcodable Context] [Primcodable Source]
    [Primcodable FirstAux] [Primcodable SecondAux] [Primcodable Output]
    (sourceBranch : Context → Source → Output)
    (default : Output)
    (sourceBranchPrimrec : Primrec₂ sourceBranch) :
    Primrec₂ (nestedSourceOrEmpty
      (FirstAux := FirstAux) (SecondAux := SecondAux)
      sourceBranch default) := by
  let Inner := Source ⊕ FirstAux
  let Outer := Inner ⊕ SecondAux
  have liftedSource : Primrec₂ fun (input : Context × Inner)
      (value : Source) => sourceBranch input.1 value :=
    sourceBranchPrimrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  let figureBranch : Context → Inner → Output := fun context atom =>
    match atom with
    | .inl sourceValue => sourceBranch context sourceValue
    | .inr _ => default
  have figureBranchPrimrec : Primrec₂ figureBranch := by
    change Primrec fun input : Context × Inner =>
      figureBranch input.1 input.2
    exact (Primrec.sumCasesOn Primrec.snd liftedSource
      (Primrec.const default).to₂).of_eq fun input => by
        cases input.2 <;> rfl
  have liftedFigure : Primrec₂ fun (input : Context × Outer)
      (value : Inner) => figureBranch input.1 value :=
    figureBranchPrimrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  change Primrec fun input : Context × Outer =>
    nestedSourceOrEmpty sourceBranch default input.1 input.2
  exact (Primrec.sumCasesOn Primrec.snd liftedFigure
    (Primrec.const default).to₂).of_eq fun input => by
      cases input.2 with
      | inl inner => cases inner <;> rfl
      | inr _ => rfl

/-- The proof-free inherited suffix lookup is primitive recursive from the
source formula, its period, and its route lookup. -/
theorem orderedInheritedRouteSuffixesComputed_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (sourcePlacement : Input → PeriodicVariablePlacement Variable)
    (sourceRoutes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec fun input =>
      (sourcePlacement input).period)
    (sourceRoutesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      sourceRoutes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      orderedInheritedRouteSuffixesComputed
        (source input.1.1) (sourcePlacement input.1.1)
        (sourceRoutes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have selected : Primrec fun input : Query =>
      inheritedRouteData? (source input.1.1) input.1.2 input.2 :=
    inheritedRouteData?_primrec source sourcePrimrec
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  let someFn : Query → InheritedRouteData Variable → List Cell :=
    fun input data => nestedSourceOrEmpty
      (fun input sourceAtom =>
          let sourceLiteralIndex :=
            sourceLiteralIndexForAtom data.1.1.1.1 sourceAtom
          fanInheritedRouteSuffixAtIndex
            (composedPlacement
              (source input.1.1) (sourcePlacement input.1.1)).period
            (sourcePlacement input.1.1).period
            data.1.1.1.1 data.1.2 sourceLiteralIndex
            (sourceRoutes input.1.1
              data.1.1.1.2 sourceLiteralIndex))
        [] input data.2.atom
  have some : Primrec₂ someFn := by
    let Combined := Query × InheritedRouteData Variable
    have atom : Primrec fun input : Combined => input.2.2.atom :=
      PeriodicThreeCNF.literal_atom_primrec.comp
        (Primrec.snd.comp Primrec.snd)
    let sourceBranchFn : Combined → Variable → List Cell :=
      fun input sourceAtom =>
        let sourceLiteralIndex :=
          sourceLiteralIndexForAtom input.2.1.1.1.1 sourceAtom
        fanInheritedRouteSuffixAtIndex
          (composedPlacement
            (source input.1.1.1) (sourcePlacement input.1.1.1)).period
          (sourcePlacement input.1.1.1).period
          input.2.1.1.1.1 input.2.1.2 sourceLiteralIndex
          (sourceRoutes input.1.1.1
            input.2.1.1.1.2 sourceLiteralIndex)
    have sourceBranch : Primrec₂ sourceBranchFn := by
      let WithAtom := Combined × Variable
      have sourceInput : Primrec fun input : WithAtom => input.1.1.1.1 :=
        Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst))
      have sourceClause : Primrec fun input : WithAtom =>
          input.1.2.1.1.1.1 :=
        Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst))))
      have sourceClauseIndex : Primrec fun input : WithAtom =>
          input.1.2.1.1.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp (Primrec.fst.comp
            (Primrec.snd.comp Primrec.fst))))
      have generatedClause : Primrec fun input : WithAtom =>
          input.1.2.1.2 :=
        Primrec.snd.comp (Primrec.fst.comp
          (Primrec.snd.comp Primrec.fst))
      let sourceIndexFn : WithAtom → Nat := fun input =>
        sourceLiteralIndexForAtom input.1.2.1.1.1.1 input.2
      have sourceIndex : Primrec sourceIndexFn :=
        sourceLiteralIndexForAtom_primrec.comp
          (Primrec.pair sourceClause Primrec.snd)
      have sourceRoute : Primrec fun input : WithAtom =>
          sourceRoutes input.1.1.1.1
            input.1.2.1.1.1.2 (sourceIndexFn input) :=
        sourceRoutesPrimrec.comp
          (Primrec.pair (Primrec.pair sourceInput sourceClauseIndex)
            sourceIndex)
      have outputPeriod : Primrec fun input =>
          (composedPlacement (source input) (sourcePlacement input)).period :=
        composedPlacement_period_primrec source sourcePlacement periodPrimrec
      have outputPeriodAt : Primrec fun input : WithAtom =>
          (composedPlacement (source input.1.1.1.1)
            (sourcePlacement input.1.1.1.1)).period :=
        outputPeriod.comp sourceInput
      have sourcePeriodAt : Primrec fun input : WithAtom =>
          (sourcePlacement input.1.1.1.1).period :=
        periodPrimrec.comp sourceInput
      let RouteInput :=
        (((Nat × Nat) × PositionedPeriodicClause Variable) ×
          GeneratedClause Variable) × (Nat × List Cell)
      let periodsFn : WithAtom → Nat × Nat := fun input =>
        ((composedPlacement (source input.1.1.1.1)
          (sourcePlacement input.1.1.1.1)).period,
        (sourcePlacement input.1.1.1.1).period)
      have periods : Primrec periodsFn :=
        Primrec.pair outputPeriodAt sourcePeriodAt
      let sourceDataFn : WithAtom →
          (Nat × Nat) × PositionedPeriodicClause Variable := fun input =>
        (periodsFn input, input.1.2.1.1.1.1)
      have sourceData : Primrec sourceDataFn :=
        Primrec.pair periods sourceClause
      let clauseDataFn : WithAtom →
          ((Nat × Nat) × PositionedPeriodicClause Variable) ×
            GeneratedClause Variable := fun input =>
        (sourceDataFn input, input.1.2.1.2)
      have clauseData : Primrec clauseDataFn :=
        Primrec.pair sourceData generatedClause
      let routeDataFn : WithAtom → Nat × List Cell := fun input =>
        (sourceIndexFn input,
          sourceRoutes input.1.1.1.1 input.1.2.1.1.1.2
            (sourceIndexFn input))
      have routeData : Primrec routeDataFn :=
        Primrec.pair sourceIndex sourceRoute
      let routeInputFn : WithAtom → RouteInput := fun input =>
        (clauseDataFn input, routeDataFn input)
      have routeInput : Primrec routeInputFn :=
        Primrec.pair clauseData routeData
      exact (fanInheritedRouteSuffixAtIndex_primrec.comp routeInput).to₂.of_eq
        fun _ _ => rfl
    let classifierFn : Combined → ComposedVariable Variable → List Cell :=
      nestedSourceOrEmpty sourceBranchFn []
    have classifier : Primrec₂ classifierFn :=
      nestedSourceOrEmpty_primrec sourceBranchFn [] sourceBranch
    let classifiedFn : Combined → List Cell := fun input =>
      classifierFn input input.2.2.atom
    have classified : Primrec classifiedFn :=
      classifier.comp Primrec.id atom
    exact classified.of_eq fun input => by
      rcases input with ⟨query, data⟩
      rfl
  exact (Primrec.option_casesOn selected none some).of_eq fun input => by
    unfold orderedInheritedRouteSuffixesComputed
    cases selectedData : inheritedRouteData?
        (source input.1.1) input.1.2 input.2 with
    | none => rfl
    | some data =>
        change someFn input data = _
        dsimp only [someFn, nestedSourceOrEmpty]
        cases data.2.atom with
        | inl figureAtom => cases figureAtom <;> rfl
        | inr _ => rfl

/-- Distinct source-clause atoms make the executable atom lookup recover the
provenance certificate's exact literal index. -/
private theorem sourceLiteralIndexForAtom_eq_of_provenance
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (sourceDistinct : source.AllAtomsNodup)
    (data : InheritedIncidenceData
      source sourcePlacement clauseIndex literalIndex) :
    sourceLiteralIndexForAtom data.sourceClause data.sourceLiteral.atom =
      data.sourceLiteralIndex := by
  have atomsNodup :
      (data.sourceClause.literals.map PeriodicLiteral.atom).Nodup :=
    sourceDistinct data.sourceClause
      (List.fst_mem_of_mem_zipIdx data.sourceClauseMember)
  have literalLookup :=
    (List.mem_zipIdx_iff_getElem?).mp data.sourceLiteralMember
  have literalIndexLt := (List.getElem?_eq_some_iff.mp literalLookup).1
  have literalEq := (List.getElem?_eq_some_iff.mp literalLookup).2
  have atomEq :
      (data.sourceClause.literals[data.sourceLiteralIndex]).atom =
        data.sourceLiteral.atom :=
    congrArg PeriodicLiteral.atom literalEq
  unfold sourceLiteralIndexForAtom
  rw [← atomEq]
  rw [← List.getElem_map PeriodicLiteral.atom]
  exact atomsNodup.idxOf_getElem data.sourceLiteralIndex
    (by simpa using literalIndexLt)

/-- Every proof-oriented provenance witness determines the same proof-free
metadata/literal lookup result. -/
private theorem inheritedRouteData?_of_provenance
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    {clauseIndex literalIndex : Nat}
    (data : InheritedIncidenceData
      source sourcePlacement clauseIndex literalIndex) :
    inheritedRouteData? source clauseIndex literalIndex =
      some ((data.metadata.indexData, data.generatedClause),
        data.generatedLiteral) := by
  rw [inheritedRouteData?_eq_metadata, data.metadataLookup]
  simp only [Option.bind_some]
  rw [data.metadataClause]
  rw [(List.mem_zipIdx_iff_getElem?).mp data.generatedLiteralMember]
  rfl

/-- The executable inherited-suffix lookup agrees pointwise with the
proof-backed ordered suffix family used by the Figure 9 geometry. -/
theorem orderedInheritedRouteSuffixesComputed_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (clauseIndex literalIndex : Nat) :
    orderedInheritedRouteSuffixesComputed
        source sourcePlacement sourceRoutes clauseIndex literalIndex =
      orderedInheritedRouteSuffixesRoutes
        source sourcePlacement sourceWidth sourceRoutes
        clauseIndex literalIndex := by
  cases provenanceLookup : inheritedIncidenceData?
      source sourcePlacement clauseIndex literalIndex with
  | none =>
      have orderedEq :
          orderedInheritedRouteSuffixesRoutes
              source sourcePlacement sourceWidth sourceRoutes
              clauseIndex literalIndex = [] := by
        simp [orderedInheritedRouteSuffixesRoutes, provenanceLookup]
      rw [orderedEq]
      unfold orderedInheritedRouteSuffixesComputed
      rw [inheritedRouteData?_eq_metadata]
      cases metadataLookup :
          (formulaClauseMetadata source)[clauseIndex]? with
      | none => simp
      | some metadata =>
          simp only [Option.bind_some]
          cases literalLookup : metadata.clause.literals[literalIndex]? with
          | none => simp
          | some literal =>
              simp only [Option.map_some]
              cases atomLookup : literal.atom with
              | inr _ => rfl
              | inl figureAtom =>
                  cases figureAtom with
                  | inr _ => rfl
                  | inl sourceAtom =>
                      have clauseLookup :
                          (PeriodicOneInThreeNoUnitsPositioned.formula
                            (PeriodicOneInThreePositioned.formula source)).clauses[
                              clauseIndex]? = some metadata.clause := by
                        rw [← formulaClauseMetadata_clauses,
                          List.getElem?_map, metadataLookup]
                        rfl
                      have clauseMember :
                          (metadata.clause, clauseIndex) ∈
                            (PeriodicOneInThreeNoUnitsPositioned.formula
                              (PeriodicOneInThreePositioned.formula
                                source)).clauses.zipIdx :=
                        (List.mem_zipIdx_iff_getElem?).mpr clauseLookup
                      have literalMember :
                          (literal, literalIndex) ∈
                            metadata.clause.literals.zipIdx :=
                        (List.mem_zipIdx_iff_getElem?).mpr literalLookup
                      have literalSource :
                          literal.atom = .inl (.inl sourceAtom) := atomLookup
                      rcases inheritedIncidenceData?_of_members
                          source sourcePlacement sourceWidth sourceDistinct
                          clauseMember literalMember sourceAtom literalSource with
                        ⟨data, dataLookup⟩
                      rw [provenanceLookup] at dataLookup
                      contradiction
  | some data =>
      have sourceIndexEq :=
        sourceLiteralIndexForAtom_eq_of_provenance sourceDistinct data
      have sourceIndexLtThree : data.sourceLiteralIndex < 3 := by
        have indexLt := data.sourceLiteralIndex_lt
        have width := data.sourceClause_width sourceWidth
        omega
      have slotEq :
          boundedSourceSlot data.sourceLiteralIndex =
            data.sourceSlot sourceWidth := by
        apply Fin.ext
        rw [boundedSourceSlot_val_of_lt_three sourceIndexLtThree,
          data.sourceSlot_val]
      calc
        orderedInheritedRouteSuffixesComputed
            source sourcePlacement sourceRoutes clauseIndex literalIndex =
          fanInheritedRouteSuffixAtIndex
            (composedPlacement source sourcePlacement).period
            sourcePlacement.period data.sourceClause data.generatedClause
            data.sourceLiteralIndex
            (sourceRoutes data.sourceClauseIndex
              data.sourceLiteralIndex) := by
                unfold orderedInheritedRouteSuffixesComputed
                rw [inheritedRouteData?_of_provenance data]
                simp [data.literalAtom, ClauseMetadata.indexData,
                  data.metadataSourceClause,
                  data.metadataSourceClauseIndex, sourceIndexEq]
        _ = fanInheritedRouteSuffix
            (composedPlacement source sourcePlacement) sourcePlacement
            data.sourceClause data.generatedClause
            (PositionedPeriodicCNF.clauseExitFanData
              data.sourceClause data.sourceClauseIndex sourceRoutes)
            (boundedSourceSlot data.sourceLiteralIndex)
            (sourceRoutes data.sourceClauseIndex
              data.sourceLiteralIndex) :=
          fanInheritedRouteSuffixAtIndex_eq
            (composedPlacement source sourcePlacement) sourcePlacement
            data.sourceClause data.generatedClause
            data.sourceClauseIndex data.sourceLiteralIndex sourceRoutes
            sourceIndexLtThree
        _ = fanInheritedRouteSuffix
            (composedPlacement source sourcePlacement) sourcePlacement
            data.sourceClause data.generatedClause
            (PositionedPeriodicCNF.clauseExitFanData
              data.sourceClause data.sourceClauseIndex sourceRoutes)
            (data.sourceSlot sourceWidth)
            (sourceRoutes data.sourceClauseIndex
              data.sourceLiteralIndex) := by rw [slotEq]
        _ = orderedInheritedRouteSuffixesRoutes
            source sourcePlacement sourceWidth sourceRoutes
            clauseIndex literalIndex :=
          (orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
            source sourcePlacement sourceWidth sourceRoutes
            clauseIndex literalIndex data provenanceLookup).symm

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
