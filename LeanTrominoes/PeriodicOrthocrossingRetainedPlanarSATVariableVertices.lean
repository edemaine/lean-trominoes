import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATLocalIncidenceDrawing
import LeanTrominoes.PeriodicOrthocrossingRouteEndpointNormalizationDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPerpendicularCarrierCore
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBendProximity

/-!
# Variables in the retained planar SAT drawing

Every variable occurring in the assembled retained formula comes from one
of three geometric families: a retained carrier node, a represented routed
variable site, or an internal variable scoped by a retained halo crossing.
This file proves that classification locally for each component drawing and
then lifts it through the retained clause metadata.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A planar-SAT variable belongs to the geometric family advertised by
its constructor. -/
def RetainedDrawingPlanarSATVariableValid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    PlanarSATVariable Variable → Prop
  | .inl (.carrier node) =>
      node ∈ retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula)
  | .inl (.atom site) =>
      site ∈ drawingVariableRouteSites formula
  | .inr (crossing, _) =>
      crossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula)

theorem retainedDrawingPlanarSATBoundary_mem_carrierNodes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {crossing : CrossingRecord}
    (crossingMem :
      crossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula))
    (side : CrossingSide) :
    CarrierNode.boundary ⟨crossing, side⟩ ∈
      retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula) := by
  unfold retainedDrawingCarrierNodes
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨⟨crossing, side⟩, ?_, rfl⟩
  apply List.mem_flatMap.mpr
  refine
    ⟨crossing,
      orientedCrossingHalo_subset_retainedCrossings
        wellFormed degree isLocal crossingMem, ?_⟩
  cases side <;> simp

theorem routedClauseSourceTerminal_mem_retainedDrawingCarrierNodes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : ClauseRouteSite}
    (siteMem : site ∈ drawingClauseRouteSites formula)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ clauseRouteOccurrencesAt formula site) :
    CarrierNode.terminal (occurrence.sourceTerminal formula) ∈
      retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula) := by
  have occurrenceGlobal :
      occurrence ∈ drawingCNFRouteOccurrences formula :=
    clauseRouteOccurrencesAt_mem_drawing
      formula siteMem occurrenceMem
  have terminalMem :
      occurrence.sourceTerminal formula ∈
        drawingSegmentTerminals
          (PeriodicCNF.incidenceGraph formula) := by
    apply
      mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
    · exact occurrence.sourceTerminal_indexed_mem occurrenceGlobal
    · simpa [CNFRouteOccurrence.sourceTerminal] using
        occurrence.translate_neighbor formula occurrenceGlobal
  unfold retainedDrawingCarrierNodes
  simp [terminalMem]

theorem routedVariableLink_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {link : EqualityLink (PlanarSATNode Variable)}
    (linkMem : link ∈ routedVariableLinksAt formula site) :
    (∃ occurrence ∈ variableRouteOccurrencesAt formula site,
      link.first =
        .carrier (.terminal (occurrence.targetTerminal formula))) ∧
      link.second = .atom site := by
  constructor
  · apply
      (mem_routedVariableNodes_iff
        formula site link.first).mp
    rcases List.mem_map.mp linkMem with
      ⟨taggedNode, taggedNodeMem, linkEq⟩
    subst link
    exact List.mem_of_mem_take
      (List.fst_mem_of_mem_zipIdx taggedNodeMem)
  · exact routedVariableLinksAt_second formula site linkMem

theorem routedVariableTargetTerminal_mem_retainedDrawingCarrierNodes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ variableRouteOccurrencesAt formula site) :
    CarrierNode.terminal (occurrence.targetTerminal formula) ∈
      retainedDrawingCarrierNodes
        (PeriodicCNF.incidenceGraph formula) := by
  have occurrenceGlobal :
      occurrence ∈ drawingCNFRouteOccurrences formula :=
    (variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site occurrenceMem).1
  have terminalMem :
      occurrence.targetTerminal formula ∈
        drawingSegmentTerminals
          (PeriodicCNF.incidenceGraph formula) := by
    apply
      mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
    · exact occurrence.targetTerminal_indexed_mem occurrenceGlobal
    · simpa [CNFRouteOccurrence.targetTerminal] using
        occurrence.translate_neighbor formula occurrenceGlobal
  unfold retainedDrawingCarrierNodes
  simp [terminalMem]

theorem mem_drawingPlanarSATCrossover_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (crossing : CrossingRecord)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (drawingPlanarSATCrossoverIncidenceDrawing
          formula crossing).variableVertices) :
    (∃ side, atom = .inl (.carrier (.boundary ⟨crossing, side⟩))) ∨
      ∃ internal, atom = .inr (crossing, internal) := by
  unfold drawingPlanarSATCrossoverIncidenceDrawing at member
  rw [EmbeddedCNFIncidenceDrawing.variableVertices_rename
    _ _ _
    (fun first _ second _ equal =>
      planarSATCrossoverVariableMap_injective crossing equal)]
    at member
  rcases List.mem_map.mp member with ⟨role, roleMember, atomEq⟩
  subst atom
  cases role <;>
    simp_all [planarSATCrossoverVariableMap,
      planarSATCoreVariableMap,
      scopedCrossoverVariableMap,
      carrierNodeCrossingPorts]

theorem mem_retainedDrawingPlanarSATCarrier_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).variableVertices) :
    atom = .inl (.carrier link.first) ∨
      atom = .inl (.carrier link.second) := by
  unfold drawingPlanarSATCarrierLensIncidenceDrawing at member
  rw [EmbeddedCNFIncidenceDrawing.variableVertices_rename
    _ _ _
    (fun first _ second _ equal =>
      planarSATCarrierVariableMap_injective equal)]
    at member
  rcases List.mem_map.mp member with ⟨node, nodeMember, atomEq⟩
  subst atom
  have nodeCases : node = link.first ∨ node = link.second := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      retainedDrawingCompleteCarrierLink_lensDrawing_formula
        wellFormed degree isLocal linkMem] at nodeMember
    simpa [equalityInstance] using nodeMember
  rcases nodeCases with rfl | rfl <;>
    simp [planarSATCarrierVariableMap]

theorem mem_drawingPlanarSATBend_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (drawingPlanarSATBendCornerIncidenceDrawing
          formula routeBend).variableVertices) :
    atom =
        .inl (.carrier
          (routeBend.equalityLink
            (PeriodicCNF.incidenceGraph formula)).first) ∨
      atom =
        .inl (.carrier
          (routeBend.equalityLink
            (PeriodicCNF.incidenceGraph formula)).second) := by
  unfold drawingPlanarSATBendCornerIncidenceDrawing at member
  rw [EmbeddedCNFIncidenceDrawing.variableVertices_rename
    _ _ _
    (fun first _ second _ equal =>
      planarSATCarrierVariableMap_injective equal)]
    at member
  rcases List.mem_map.mp member with ⟨node, nodeMember, atomEq⟩
  subst atom
  have nodeCases :
      node =
          (routeBend.equalityLink
            (PeriodicCNF.incidenceGraph formula)).first ∨
        node =
          (routeBend.equalityLink
            (PeriodicCNF.incidenceGraph formula)).second := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      RouteBend.cornerDrawing_formula] at nodeMember
    simpa [equalityInstance] using nodeMember
  rcases nodeCases with rfl | rfl <;>
    simp [planarSATCarrierVariableMap]

theorem mem_drawingPlanarSATRoutedVariable_variableVertices
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (drawingPlanarSATRoutedVariableIncidenceDrawing
          formula site arm link).variableVertices) :
    atom = .inl link.first ∨ atom = .inl link.second := by
  unfold drawingPlanarSATRoutedVariableIncidenceDrawing at member
  rw [EmbeddedCNFIncidenceDrawing.variableVertices_rename
    _ _ _
    (fun first _ second _ equal =>
      planarSATRoutedVariableMap_injective
        formula site linkMem equal)]
    at member
  rcases List.mem_map.mp member with ⟨role, roleMember, atomEq⟩
  subst atom
  cases role <;>
    simp [planarSATRoutedVariableMap]

namespace DrawingPlanarSATClauseMetadata

theorem retainedValid_variableValid
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (metadata.source.incidenceDrawing
          formula).variableVertices) :
    RetainedDrawingPlanarSATVariableValid formula atom := by
  cases metadata with
  | mk clause source =>
      cases source with
      | crossover crossing localClauseIndex =>
          simp only [DrawingPlanarSATClauseMetadata.RetainedValid]
            at valid
          rcases mem_drawingPlanarSATCrossover_variableVertices
              formula crossing atom member with
            ⟨side, rfl⟩ | ⟨internal, rfl⟩
          · exact retainedDrawingPlanarSATBoundary_mem_carrierNodes
              formula wellFormed degree isLocal valid.1 side
          · exact valid.1
      | carrier link localClauseIndex =>
          simp only [DrawingPlanarSATClauseMetadata.RetainedValid]
            at valid
          rcases mem_retainedDrawingPlanarSATCarrier_variableVertices
              formula wellFormed degree isLocal link valid.1 atom
              member with
            rfl | rfl
          · exact
              (retainedDrawingCompleteCarrierLink_endpoints_mem
                (PeriodicCNF.incidenceGraph formula) valid.1).1
          · exact
              (retainedDrawingCompleteCarrierLink_endpoints_mem
                (PeriodicCNF.incidenceGraph formula) valid.1).2
      | bend routeBend localClauseIndex =>
          simp only [DrawingPlanarSATClauseMetadata.RetainedValid]
            at valid
          rcases mem_drawingPlanarSATBend_variableVertices
              formula routeBend atom member with
            rfl | rfl
          · have terminalMem :=
              (drawingRouteBend_terminals_mem_drawingSegmentTerminals
                (PeriodicCNF.incidenceGraph formula) valid.1).1
            change
              CarrierNode.terminal routeBend.incomingTerminal ∈
                retainedDrawingCarrierNodes
                  (PeriodicCNF.incidenceGraph formula)
            unfold retainedDrawingCarrierNodes
            simp [terminalMem]
          · have terminalMem :=
              (drawingRouteBend_terminals_mem_drawingSegmentTerminals
                (PeriodicCNF.incidenceGraph formula) valid.1).2
            change
              CarrierNode.terminal routeBend.outgoingTerminal ∈
                retainedDrawingCarrierNodes
                  (PeriodicCNF.incidenceGraph formula)
            unfold retainedDrawingCarrierNodes
            simp [terminalMem]
      | routedClause site =>
          simp only [DrawingPlanarSATClauseMetadata.RetainedValid]
            at valid
          rcases
              (mem_drawingPlanarSATRoutedClause_variableVertices_iff
                formula site atom).mp member with
            ⟨occurrence, occurrenceMem, rfl⟩
          exact
            routedClauseSourceTerminal_mem_retainedDrawingCarrierNodes
            formula valid.1 occurrenceMem
      | routedVariable site armIndex arm link localClauseIndex =>
          simp only [DrawingPlanarSATClauseMetadata.RetainedValid]
            at valid
          have linkMem :
              link ∈ routedVariableLinksAt formula site :=
            List.fst_mem_of_mem_zipIdx valid.2.1
          rcases
              mem_drawingPlanarSATRoutedVariable_variableVertices
              formula site arm link linkMem atom member with
            rfl | rfl
          · rcases routedVariableLink_endpoints
                formula site linkMem with
              ⟨⟨occurrence, occurrenceMem, firstEq⟩, secondEq⟩
            rw [firstEq]
            exact
              routedVariableTargetTerminal_mem_retainedDrawingCarrierNodes
              formula site occurrenceMem
          · rw [routedVariableLinksAt_second
              formula site linkMem]
            exact valid.1

end DrawingPlanarSATClauseMetadata

/-- Every variable occurring in the assembled retained formula belongs to
its advertised retained geometric family. -/
theorem
    retainedDrawingPlanarSATLocalIncidenceDrawing_variableVertices_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (member :
      atom ∈
        (retainedDrawingPlanarSATLocalIncidenceDrawing
          formula).variableVertices) :
    RetainedDrawingPlanarSATVariableValid formula atom := by
  rw [EmbeddedCNFIncidenceDrawing.variableVertices,
    retainedDrawingPlanarSATLocalIncidenceDrawing_formula,
    List.mem_dedup] at member
  rcases List.mem_flatMap.mp member with
    ⟨clause, clauseMember, atomMember⟩
  rcases List.mem_map.mp atomMember with
    ⟨literal, literalMember, atomEqual⟩
  rw [← retainedDrawingPlanarSATClauseMetadata_clauses]
    at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨metadata, metadataMember, metadataClauseEqual⟩
  subst clause
  have valid :=
    retainedDrawingPlanarSATClauseMetadata_valid
      formula metadataMember
  have localClauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have localAtomMember :
      atom ∈
        (metadata.source.incidenceDrawing
          formula).variableVertices := by
    rw [EmbeddedCNFIncidenceDrawing.variableVertices,
      List.mem_dedup]
    apply List.mem_flatMap.mpr
    refine
      ⟨metadata.clause,
        List.fst_mem_of_mem_zipIdx localClauseMember, ?_⟩
    · exact List.mem_map.mpr
        ⟨literal, literalMember, atomEqual⟩
  exact metadata.retainedValid_variableValid
    wellFormed degree isLocal valid atom localAtomMember

end LeanTrominoes.PeriodicOrthocrossing
