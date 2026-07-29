import LeanTrominoes.PeriodicOrthocrossingRetainedRawSameCarrierSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedNoncarrierPeriodicSeparation

/-!
# Periodic separation on one physical carrier

After aligning two final carrier occurrences by their physical gauge shifts,
equality of their physical carrier keys puts both links into one raw retained
carrier chain.  Distinct aligned links are separated by raw carrier order.
Equal aligned links are handled by the existing component-alignment transfer
and finite planarity.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1200000

/-- Every valid list index has a tagged member at that exact index. -/
private theorem exists_mem_zipIdx_of_lt
    {Value : Type*} (values : List Value) (index : Nat)
    (indexLt : index < values.length) :
    ∃ value, (value, index) ∈ values.zipIdx := by
  let finiteIndex : Fin values.length := ⟨index, indexLt⟩
  refine ⟨values.get finiteIndex, ?_⟩
  rw [List.mem_zipIdx_iff_getElem?]
  exact List.getElem?_eq_getElem indexLt

/-- Every clause in a carrier equality block has two literals. -/
theorem drawingPlanarSATCarrierFormulaAt_clause_literals_length
    {Variable : Type*}
    (link : EqualityLink CarrierNode)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    (clauseMem :
      clause ∈ drawingPlanarSATCarrierFormulaAt
        (Variable := Variable) link) :
    clause.literals.length = 2 := by
  simp [drawingPlanarSATCarrierFormulaAt, equalityInstance,
    EmbeddedClause.rename, EmbeddedClause.map] at clauseMem
  rcases clauseMem with clauseEq | clauseEq
  · subst clause
    simp
  · subst clause
    simp

/-- Translating a selected link to the physical carrier key of another
selected link leaves it in the raw retained carrier window. -/
theorem
    retainedDrawingCompleteCarrierLink_periodTranslate_mem_raw_of_first_key_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (shift : Cell)
    (keyEq :
      (carrierLinkPeriodTranslate graph first shift).first.carrierKey =
        second.first.carrierKey) :
    carrierLinkPeriodTranslate graph first shift ∈
      retainedDrawingCompleteCarrierLinksRaw graph := by
  apply retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph first).mp firstMem).1
  · exact
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph firstMem
  · have translateEq :
        (carrierLinkPeriodTranslate graph first shift).first.translate =
          second.first.translate := by
      simpa [CarrierNode.carrierKey_eq_indexed_translate,
        PeriodicGridDrawing.SegmentOccurrenceKey] using
        congrArg (fun key : Nat × Nat × Cell => key.2.2) keyEq
    change
      IsNeighborTranslation
        (carrierLinkPeriodTranslate graph first shift).first.translate
    rw [translateEq]
    exact
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph secondMem

/-- At one physical carrier key, distinct aligned carrier metadata routes
avoid each other even when the first aligned link is not the selected orbit
owner. -/
theorem
    DrawingPlanarSATClauseMetadata.periodTranslate_localRoutes_avoidEachOther_of_carrier_same_key
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (shift : Cell)
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstClauseIndex secondClauseIndex : Nat)
    (firstSourceEq :
      first.source = .carrier firstLink firstClauseIndex)
    (secondSourceEq :
      second.source = .carrier secondLink secondClauseIndex)
    (sameKey :
      (carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift).first.carrierKey =
        secondLink.first.carrierKey)
    (different :
      carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink shift ≠
        secondLink)
    {firstLiteral secondLiteral :
      PlanarSATVariable Variable × Bool}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        first.clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        second.clause.literals.zipIdx) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (((first.source.periodTranslate formula shift).incidenceDrawing
          formula).routes
        first.source.localClauseIndex firstLiteralIndex)
      ((second.source.incidenceDrawing formula).routes
        second.source.localClauseIndex secondLiteralIndex) := by
  let translatedFirst :=
    carrierLinkPeriodTranslate formula.incidenceGraph firstLink shift
  have firstValid' := firstValid
  have secondValid' := secondValid
  unfold DrawingPlanarSATClauseMetadata.RetainedValid
    at firstValid' secondValid'
  rw [firstSourceEq] at firstValid'
  rw [secondSourceEq] at secondValid'
  have translatedFirstMem :
      translatedFirst ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    retainedDrawingCompleteCarrierLink_periodTranslate_mem_raw_of_first_key_eq
      wellFormed degree isLocal firstValid'.1 secondValid'.1 shift
      (by simpa only [translatedFirst] using sameKey)
  have secondRawMem :
      secondLink ∈
        retainedDrawingCompleteCarrierLinksRaw
          formula.incidenceGraph :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      formula.incidenceGraph secondLink).mp secondValid'.1).1
  have firstClauseIndexLt : firstClauseIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx firstValid'.2
    simpa [drawingPlanarSATCarrierFormulaAt,
      equalityInstance] using indexLt
  have secondClauseIndexLt : secondClauseIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx secondValid'.2
    simpa [drawingPlanarSATCarrierFormulaAt,
      equalityInstance] using indexLt
  have firstLiteralIndexLt : firstLiteralIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx firstLiteralMember
    have clauseLength :=
      drawingPlanarSATCarrierFormulaAt_clause_literals_length
        firstLink
        (List.fst_mem_of_mem_zipIdx firstValid'.2)
    rw [clauseLength] at indexLt
    exact indexLt
  have secondLiteralIndexLt : secondLiteralIndex < 2 := by
    have indexLt := List.snd_lt_of_mem_zipIdx secondLiteralMember
    have clauseLength :=
      drawingPlanarSATCarrierFormulaAt_clause_literals_length
        secondLink
        (List.fst_mem_of_mem_zipIdx secondValid'.2)
    rw [clauseLength] at indexLt
    exact indexLt
  have translatedFormulaLength :
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula translatedFirst).formula.length = 2 := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal translatedFirstMem]
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance]
  have secondFormulaLength :
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).formula.length = 2 := by
    rw [
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal secondRawMem]
    simp [drawingPlanarSATCarrierFormulaAt, equalityInstance]
  rcases exists_mem_zipIdx_of_lt
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula translatedFirst).formula
      firstClauseIndex
      (by omega) with
    ⟨translatedFirstClause, translatedFirstClauseMem⟩
  rcases exists_mem_zipIdx_of_lt
      (drawingPlanarSATCarrierLensIncidenceDrawing
        formula secondLink).formula
      secondClauseIndex
      (by omega) with
    ⟨secondPhysicalClause, secondPhysicalClauseMem⟩
  have translatedFirstClauseLength :
      translatedFirstClause.literals.length = 2 := by
    apply drawingPlanarSATCarrierFormulaAt_clause_literals_length
      translatedFirst
    rw [←
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal translatedFirstMem]
    exact List.fst_mem_of_mem_zipIdx translatedFirstClauseMem
  have secondPhysicalClauseLength :
      secondPhysicalClause.literals.length = 2 := by
    apply drawingPlanarSATCarrierFormulaAt_clause_literals_length
      secondLink
    rw [←
      retainedDrawingPlanarSATCarrierLensIncidenceDrawing_formula_of_raw
        wellFormed degree isLocal secondRawMem]
    exact List.fst_mem_of_mem_zipIdx secondPhysicalClauseMem
  rcases exists_mem_zipIdx_of_lt
      translatedFirstClause.literals firstLiteralIndex
      (by omega) with
    ⟨translatedFirstLiteral, translatedFirstLiteralMem⟩
  rcases exists_mem_zipIdx_of_lt
      secondPhysicalClause.literals secondLiteralIndex
      (by omega) with
    ⟨secondPhysicalLiteral, secondPhysicalLiteralMem⟩
  have routeAvoid :=
    retainedDrawingPlanarSATCarrierCarrierRoutesAvoidEachOther_of_raw_same_key
      wellFormed degree isLocal translatedFirstMem secondRawMem
      (by simpa only [translatedFirst] using different)
      (by simpa only [translatedFirst] using sameKey)
      translatedFirstClauseMem translatedFirstLiteralMem
      secondPhysicalClauseMem secondPhysicalLiteralMem
  simpa [translatedFirst, firstSourceEq, secondSourceEq,
    DrawingPlanarSATClauseSource.periodTranslate,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using routeAvoid

/-- Distinct final carrier occurrences on the same aligned physical carrier
have disjoint continuous segment interiors. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_carriers_same_physical_key
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier firstLink)
    (secondComponentEq :
      second.routeWitness.metadata.source.component = .carrier secondLink)
    (samePhysicalKey :
      (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
        (Cell.sub first.physicalShift
          second.physicalShift)).first.carrierKey =
        secondLink.first.carrierKey)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift) :
    ¬GridSegment.InteriorsMeet
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift))
      (secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)) := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  by_cases alignedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink reindexShift =
        secondLink
  · apply
      retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_first_component_aligns_second
        formula wellFormed degree isLocal clausesNonempty
        first second
    · simpa [reindexShift, firstSourceEq, secondSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component,
        alignedLinkEq]
    · exact different
  · have routeAvoid :=
      first.routeWitness.metadata
        |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_same_key
          wellFormed degree isLocal second.routeWitness.metadata
          first.metadata_retainedValid second.metadata_retainedValid
          reindexShift firstLink secondLink
          firstClauseIndex secondClauseIndex
          firstSourceEq secondSourceEq
          (by simpa only [reindexShift] using samePhysicalKey)
          alignedLinkEq
          first.routeWitness.literalMember
          second.routeWitness.literalMember
    apply
      retainedDeduplicatedGaugedWrappedDrawing_interiorsDisjoint_of_periodTranslate_localRoutesAvoidEachOther
        formula first second
    simpa only [reindexShift] using routeAvoid

/-- Distinct final carrier occurrences on the same aligned physical
carrier also satisfy asymmetric interior-versus-closed avoidance. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_carriers_same_physical_key
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈ retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    {firstIndexed secondIndexed : IndexedGridSegment}
    {firstShift secondShift : Cell}
    (first :
      FinalGaugedSegmentOccurrenceWitness
        formula firstIndexed firstShift)
    (second :
      FinalGaugedSegmentOccurrenceWitness
        formula secondIndexed secondShift)
    (firstLink secondLink : EqualityLink CarrierNode)
    (firstComponentEq :
      first.routeWitness.metadata.source.component = .carrier firstLink)
    (secondComponentEq :
      second.routeWitness.metadata.source.component = .carrier secondLink)
    (samePhysicalKey :
      (carrierLinkPeriodTranslate formula.incidenceGraph firstLink
        (Cell.sub first.physicalShift
          second.physicalShift)).first.carrierKey =
        secondLink.first.carrierKey)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          firstIndexed firstShift ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          secondIndexed secondShift)
    (point : Cell)
    (firstContains :
      (firstIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation firstShift)).InteriorContains point) :
    ¬(secondIndexed.segment.translate
        ((retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).periodTranslation secondShift)).Contains point := by
  let reindexShift :=
    Cell.sub first.physicalShift second.physicalShift
  rcases
      first.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq firstLink firstComponentEq with
    ⟨firstClauseIndex, firstSourceEq⟩
  rcases
      second.routeWitness.metadata.source
        |>.exists_eq_carrier_of_component_eq secondLink secondComponentEq with
    ⟨secondClauseIndex, secondSourceEq⟩
  by_cases alignedLinkEq :
      carrierLinkPeriodTranslate formula.incidenceGraph
          firstLink reindexShift =
        secondLink
  · apply
      retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_first_component_aligns_second
        formula wellFormed degree isLocal clausesNonempty
        first second
    · simpa [reindexShift, firstSourceEq, secondSourceEq,
        DrawingPlanarSATClauseSource.periodTranslate,
        DrawingPlanarSATClauseSource.component,
        alignedLinkEq]
    · exact different
    · exact firstContains
  · have routeAvoid :=
      first.routeWitness.metadata
        |>.periodTranslate_localRoutes_avoidEachOther_of_carrier_same_key
          wellFormed degree isLocal second.routeWitness.metadata
          first.metadata_retainedValid second.metadata_retainedValid
          reindexShift firstLink secondLink
          firstClauseIndex secondClauseIndex
          firstSourceEq secondSourceEq
          (by simpa only [reindexShift] using samePhysicalKey)
          alignedLinkEq
          first.routeWitness.literalMember
          second.routeWitness.literalMember
    apply
      retainedDeduplicatedGaugedWrappedDrawing_avoidsInterior_of_periodTranslate_localRoutesAvoidEachOther
        formula first second
    · simpa only [reindexShift] using routeAvoid
    · exact firstContains

end PeriodicOrthocrossing
end LeanTrominoes
