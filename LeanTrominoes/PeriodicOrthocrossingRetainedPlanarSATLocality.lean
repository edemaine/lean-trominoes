/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedClausePositions
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierRouteBounds
import LeanTrominoes.PeriodicGridQuotientLocality

/-! # Manhattan locality of the retained planar SAT presentation -/
namespace LeanTrominoes.PeriodicOrthocrossing
open PlanarThreeSAT
set_option maxHeartbeats 1500000

theorem noncarrier_clause_literal_in_macrocell
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
    (center : Cell)
    (centerEq :
      metadata.source.component.macrocellCenter formula = some center)
    (first : PlanarSATVariable Variable × Bool)
    (literalIndex : Nat)
    (firstMember :
      (first, literalIndex) ∈ metadata.clause.literals.zipIdx) :
    InPlanarSATMacrocell center
      (drawingPlanarSATVariablePosition formula first.1) := by
  have notCarrier :
      ¬∃ link, metadata.source.component = .carrier link := by
    rintro ⟨link, componentEq⟩
    rw [componentEq] at centerEq
    simp [DrawingPlanarSATComponent.macrocellCenter] at centerEq
  have originalValid : metadata.Valid formula :=
    metadata.valid_of_retainedValid_of_not_carrier valid notCarrier
  have clauseMember :=
    metadata.retainedLocalClauseMember
      wellFormed degree isLocal valid
  have routesMatch :=
    metadata.retainedLocalDrawingRoutesMatch
      wellFormed degree isLocal valid
  have endpoints :=
    (metadata.source.incidenceDrawing formula).physicalRoutesMatch
      routesMatch metadata.clause
      metadata.source.localClauseIndex clauseMember
      first literalIndex firstMember
  rw [DrawingPlanarSATClauseSource.incidenceDrawing_variablePosition]
    at endpoints
  have positionMember :
      drawingPlanarSATVariablePosition formula first.1 ∈
        (metadata.source.incidenceDrawing formula).routes
          metadata.source.localClauseIndex literalIndex :=
    mem_of_getLast?_eq_some endpoints.2
  exact
    metadata.localRoutePoints_inPlanarSATMacrocell
      wellFormed degree isLocal originalValid
      center centerEq firstMember positionMember


def localGaugedLiteral {V : Type*} [DecidableEq V] (f : PeriodicCNF V)
    (literal : PlanarSATVariable V × Bool) : PeriodicLiteral (WrappedPeriodicPlanarSATVariable V) :=
  (wrapPeriodicPlanarSATLiteral (periodicizePlanarSATLiteral f literal)).variableGauge
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge f)

theorem localGaugedLiteral_offset {V : Type*} [DecidableEq V] (f : PeriodicCNF V)
    (literal : PlanarSATVariable V × Bool) :
    (localGaugedLiteral f literal).offset =
      periodCell (drawingPeriodicPlanarSATPlacement f).period (drawingPlanarSATVariablePosition f literal.1) := by
  rw [← periodicizePlanarSATLiteral_position]
  exact (drawingPeriodicPlanarSATPlacement f).gauged_literal_offset
    (drawingPeriodicPlanarSATPlacement_period_pos f) (periodicizePlanarSATLiteral f literal)

theorem noncarrier_gauged_clause_local {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) (metadata : DrawingPlanarSATClauseMetadata V)
    (valid : metadata.RetainedValid f) (center : Cell)
    (centerEq : metadata.source.component.macrocellCenter f=some center) :
    PeriodicClause.IsLocal (metadata.clause.literals.map (localGaugedLiteral f)) := by
  intro first hf second hs
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp ha
  obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
  have ba := noncarrier_clause_literal_in_macrocell wf degree locality metadata valid center centerEq
    a i (List.mem_zipIdx_iff_getElem?.mpr hi)
  have bb := noncarrier_clause_literal_in_macrocell wf degree locality metadata valid center centerEq
    b j (List.mem_zipIdx_iff_getElem?.mpr hj)
  have quot := macrocellQuotient_eq (periodFactor := drawingGridSize f.incidenceGraph) ba bb
  have equal : (localGaugedLiteral f a).offset=(localGaugedLiteral f b).offset := by
    rw [localGaugedLiteral_offset,localGaugedLiteral_offset]
    apply Prod.ext
    · simpa [periodCell,drawingPeriodicPlanarSATPlacement,planarMacroScale] using quot.1
    · simpa [periodCell,drawingPeriodicPlanarSATPlacement,planarMacroScale] using quot.2
  simp [PeriodicClause.offsetDistance,equal]

theorem carrier_periodCells_local {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) {link : EqualityLink CarrierNode}
    (member : link ∈ retainedDrawingCompleteCarrierLinks f.incidenceGraph) :
    let a := periodCell (drawingPeriodicPlanarSATPlacement f).period (link.first.position f.incidenceGraph)
    let b := periodCell (drawingPeriodicPlanarSATPlacement f).period (link.second.position f.incidenceGraph)
    (a.1-b.1).natAbs+(a.2-b.2).natAbs ≤ 1 := by
  have clearance := retainedDrawingCompleteCarrierLink_hasForwardClearance wf degree locality member
  have span := retainedDrawingCompleteCarrierLink_position_span_lt_period wf degree locality member
  have positive := drawingPeriodicPlanarSATPlacement_period_pos f
  have hp : (0 : Int) < (drawingPeriodicPlanarSATPlacement f).period := by exact_mod_cast positive
  have period : ((drawingPeriodicPlanarSATPlacement f).period : Int) =
      planarMacroScale * drawingGridSize f.incidenceGraph := by
    simp [drawingPeriodicPlanarSATPlacement,planarMacroScale]
  by_cases horizontal : link.first.isHorizontal = true
  · simp [CarrierNode.HasForwardClearance,horizontal] at clearance span
    apply aligned_periodCells_local _ positive _ _ (Or.inr clearance.1) <;> omega
  · simp [CarrierNode.HasForwardClearance,horizontal] at clearance span
    apply aligned_periodCells_local _ positive _ _ (Or.inl clearance.1) <;> omega

theorem carrier_gauged_clause_local {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) {link : EqualityLink CarrierNode}
    (member : link ∈ retainedDrawingCompleteCarrierLinks f.incidenceGraph)
    {clause : EmbeddedClause (PlanarSATVariable V)}
    (clauseMember : clause ∈ drawingPlanarSATCarrierFormulaAt link) :
    PeriodicClause.IsLocal (clause.literals.map (localGaugedLiteral f)) := by
  have distance := carrier_periodCells_local wf degree locality member
  have reverse :
      ((periodCell (drawingPeriodicPlanarSATPlacement f).period (link.second.position f.incidenceGraph)).1 -
       (periodCell (drawingPeriodicPlanarSATPlacement f).period (link.first.position f.incidenceGraph)).1).natAbs +
      ((periodCell (drawingPeriodicPlanarSATPlacement f).period (link.second.position f.incidenceGraph)).2 -
       (periodCell (drawingPeriodicPlanarSATPlacement f).period (link.first.position f.incidenceGraph)).2).natAbs ≤ 1 := by
    dsimp at distance
    omega
  simp [drawingPlanarSATCarrierFormulaAt,equalityInstance,EmbeddedClause.rename,
    EmbeddedClause.map] at clauseMember
  rcases clauseMember with rfl | rfl <;>
    simp only [List.map_cons,List.map_nil,PeriodicClause.IsLocal,List.mem_cons,List.not_mem_nil,or_false] <;>
    intro a ha b hb <;> rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [PeriodicClause.offsetDistance,localGaugedLiteral_offset,
      planarSATCoreVariableMap,drawingPlanarSATVariablePosition,sub_self,Int.natAbs_zero,zero_add] <;>
    first | exact distance | exact reverse | omega

theorem retained_metadata_gauged_clause_local {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) (metadata : DrawingPlanarSATClauseMetadata V)
    (valid : metadata.RetainedValid f) :
    PeriodicClause.IsLocal (metadata.clause.literals.map (localGaugedLiteral f)) := by
  rcases metadata with ⟨clause,source⟩
  cases source with
  | carrier link index =>
      exact carrier_gauged_clause_local wf degree locality valid.1
        (List.fst_mem_of_mem_zipIdx valid.2)
  | crossover crossing index =>
      apply noncarrier_gauged_clause_local wf degree locality _ valid crossing.point
      simp [DrawingPlanarSATClauseSource.component,DrawingPlanarSATComponent.macrocellCenter]
  | bend bend index =>
      apply noncarrier_gauged_clause_local wf degree locality _ valid (bend.drawingPoint f.incidenceGraph)
      simp [DrawingPlanarSATClauseSource.component,DrawingPlanarSATComponent.macrocellCenter]
  | routedClause site =>
      apply noncarrier_gauged_clause_local wf degree locality _ valid
        (liftedIncidenceVertexPosition f (.clause site.1) site.2)
      simp [DrawingPlanarSATClauseSource.component,DrawingPlanarSATComponent.macrocellCenter]
  | routedVariable site armIndex arm link index =>
      apply noncarrier_gauged_clause_local wf degree locality _ valid
        (liftedIncidenceVertexPosition f (.variable site.1) site.2)
      simp [DrawingPlanarSATClauseSource.component,DrawingPlanarSATComponent.macrocellCenter]

theorem retained_gauged_formula_isLocal {V : Type*} [DecidableEq V] {f : PeriodicCNF V}
    (wf : f.incidenceGraph.IsWellFormed) (degree : f.incidenceGraph.DegreeAtMost 3)
    (locality : f.incidenceGraph.IsLocal) :
    (retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula f).erase.IsLocal := by
  rw [retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
  intro clause member
  simp only [PeriodicCNF.variableGauge,wrapPeriodicPlanarSATFormula,
    retainedDrawingPeriodicPlanarSATFormula,List.map_map,
    PeriodicClause.variableGauge,wrapPeriodicPlanarSATClause,periodicizePlanarSATClause,
    Function.comp_def] at member
  obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
  obtain ⟨index,lookup⟩ := List.mem_iff_getElem?.mp originalMember
  obtain ⟨metadata,_,clauseEq,valid⟩ := retainedDrawingPlanarSATClauseMetadata_lookup_valid f
    (List.mem_zipIdx_iff_getElem?.mpr lookup)
  change PeriodicClause.IsLocal (original.literals.map (localGaugedLiteral f))
  rw [← clauseEq]
  exact retained_metadata_gauged_clause_local wf degree locality metadata valid

end LeanTrominoes.PeriodicOrthocrossing
