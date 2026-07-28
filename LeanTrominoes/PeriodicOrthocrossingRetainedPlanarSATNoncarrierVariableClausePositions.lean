import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATVariablePositionInjectivity

/-!
# Retained variables avoid non-carrier clause positions

Every retained planar-SAT variable uses a fixed coordinate inside a
`20 × 20` macrocell: a carrier port, the routed-variable center, or an
internal crossover position.  This file classifies the fixed clause
coordinates of each non-carrier component and proves that no retained
variable can occupy one of them.

Most cases are direct local-coordinate inequalities.  The three apparent
coordinate coincidences occur in different kinds of macrocells: a crossover
clause versus a routed-variable center, a bend clause versus a crossover
variable, and a routed-variable clause versus a crossover variable.
Existing drawing-grid separation rules out equality of those centers.
-/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The three possible local-coordinate families of retained variables. -/
def IsRetainedPlanarSATVariableLocalPosition (position : Cell) : Prop :=
  IsCarrierPortLocalPosition position ∨
    position = duplicatorArmCenterPosition ∨
      ∃ internal : CrossoverInternal,
        position =
          CrossoverVariable.position
            (crossoverInternalVariable internal)

/-- The variable coordinates represented inside a crossover macrocell. -/
def IsCarrierOrCrossoverInternalLocalPosition
    (position : Cell) : Prop :=
  IsCarrierPortLocalPosition position ∨
    ∃ internal : CrossoverInternal,
      position =
        CrossoverVariable.position
          (crossoverInternalVariable internal)

/-- Every crossover clause has a bounded local coordinate distinct from
carrier ports and internal crossover variables. -/
theorem crossoverClause_localPosition_avoids_carrier_or_internal
    {Variable : Type*}
    {crossing : CrossingRecord}
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).zipIdx) :
    ∃ offset,
      clause.position =
        Cell.add (crossingMacroOrigin crossing) offset ∧
      (0 ≤ offset.1 ∧ offset.1 < planarMacroScale ∧
        0 ≤ offset.2 ∧ offset.2 < planarMacroScale) ∧
      ¬IsCarrierOrCrossoverInternalLocalPosition offset := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATCrossoverFormulaAt,
    scopedCrossoverInstance, instantiateFormula,
    crossoverFormula] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATCrossoverFormulaAt,
      scopedCrossoverInstance, instantiateFormula,
      EmbeddedClause.rename, EmbeddedClause.map,
      crossoverFormula, crossoverClause, EmbeddedClause.place,
      IsCarrierOrCrossoverInternalLocalPosition,
      IsCarrierPortLocalPosition,
      crossoverInternalVariable, CrossoverVariable.position,
      crossingMacroOrigin, Cell.add, Cell.scale, planarMacroScale]
  all_goals
    intro internal
    cases internal <;>
      norm_num [crossoverInternalVariable,
        CrossoverVariable.position]

/-- The carrier-port and routed-variable-center local coordinates. -/
def IsCarrierOrAtomLocalPosition (position : Cell) : Prop :=
  IsCarrierPortLocalPosition position ∨
    position = duplicatorArmCenterPosition

/-- Every bend clause has a bounded local coordinate distinct from carrier
ports and the routed-variable center. -/
theorem bendClause_localPosition_avoids_carrier_or_atom
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (routeBend : RouteBend)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph routeBend).zipIdx) :
    ∃ offset,
      clause.position =
        Cell.add
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint graph)) offset ∧
      (0 ≤ offset.1 ∧ offset.1 < planarMacroScale ∧
        0 ≤ offset.2 ∧ offset.2 < planarMacroScale) ∧
      ¬IsCarrierOrAtomLocalPosition offset := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATBendFormulaAt,
    drawingPlanarSATCarrierFormulaAt, equalityInstance] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATBendFormulaAt,
      drawingPlanarSATCarrierFormulaAt, equalityInstance,
      RouteBend.equalityLink, routeBendEqualityPositions,
      EmbeddedClause.rename, EmbeddedClause.map,
      IsCarrierOrAtomLocalPosition,
      IsCarrierPortLocalPosition, duplicatorArmCenterPosition,
      Cell.add, Cell.scale, planarMacroScale]

/-- A routed source clause's local coordinate is distinct from every
retained variable-coordinate family. -/
theorem routedClause_localPosition_avoids_variables
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : ClauseRouteSite)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    (equal :
      clause =
        (routedClauseAt formula site).rename
          planarSATExternalVariableMap) :
    ∃ offset,
      clause.position =
        Cell.add (routedClauseOrigin formula site) offset ∧
      (0 ≤ offset.1 ∧ offset.1 < planarMacroScale ∧
        0 ≤ offset.2 ∧ offset.2 < planarMacroScale) ∧
      ¬IsRetainedPlanarSATVariableLocalPosition offset := by
  subst clause
  refine ⟨(10, 10), ?_⟩
  simp [routedClauseAt, routedClauseOrigin,
    liftedIncidenceVertexMacroOrigin,
    EmbeddedClause.rename, EmbeddedClause.map,
    IsRetainedPlanarSATVariableLocalPosition,
    IsCarrierPortLocalPosition, duplicatorArmCenterPosition,
    crossoverInternalVariable, CrossoverVariable.position,
    Cell.add, Cell.scale, planarMacroScale]
  intro internal
  cases internal <;>
    norm_num [crossoverInternalVariable,
      CrossoverVariable.position]

/-- Every routed-variable clause has a bounded local coordinate distinct
from carrier ports and the routed-variable center. -/
theorem routedVariableClause_localPosition_avoids_carrier_or_atom
    {Variable : Type*}
    (origin : Cell)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (positionsEq :
      link.positions =
        ⟨Cell.add origin
            (duplicatorArmEqualityPositions arm).forward,
          Cell.add origin
            (duplicatorArmEqualityPositions arm).backward⟩)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (member :
      (clause, clauseIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx) :
    ∃ offset,
      clause.position = Cell.add origin offset ∧
      (0 ≤ offset.1 ∧ offset.1 < planarMacroScale ∧
        0 ≤ offset.2 ∧ offset.2 < planarMacroScale) ∧
      ¬IsCarrierOrAtomLocalPosition offset := by
  have indexLt := List.snd_lt_of_mem_zipIdx member
  simp [drawingPlanarSATRoutedVariableFormulaAt,
    equalityInstance] at indexLt
  interval_cases clauseIndex <;>
    simp_all [drawingPlanarSATRoutedVariableFormulaAt,
      equalityInstance, EmbeddedClause.rename,
      EmbeddedClause.map, IsCarrierOrAtomLocalPosition,
      IsCarrierPortLocalPosition, duplicatorArmCenterPosition,
      Cell.add, planarMacroScale] <;>
    cases arm <;>
      simp_all [duplicatorArmEqualityPositions]

/-- No retained variable occupies a crossover clause position. -/
theorem retainedVariablePosition_ne_crossoverClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPlanarSATVariableValid formula atom)
    (crossing : CrossingRecord)
    (crossingMem :
      crossing ∈ orientedCrossingHalo
        (PeriodicCNF.incidenceGraph formula))
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing).zipIdx) :
    drawingPlanarSATVariablePosition formula atom ≠
      clause.position := by
  rcases crossoverClause_localPosition_avoids_carrier_or_internal
      clauseMember with
    ⟨offset, clausePosition, offsetBounds, offsetAvoids⟩
  intro positionEq
  rcases atom with (⟨carrier⟩ | ⟨site⟩) |
    ⟨otherCrossing, internal⟩
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CarrierNode.localPosition_in_macrocell carrier)
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            CarrierNode.position_eq_scale_add_local,
            crossingMacroOrigin, clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inl
      (retainedCarrierNode_localPosition_isCarrierPort
        wellFormed degree isLocal atomValid)
  · have positionData :=
      planarSATMacrocellPosition_eq
        duplicatorArmCenterPosition_in_macrocell
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            liftedIncidenceVertexMacroOrigin,
            crossingMacroOrigin, clausePosition] using positionEq)
    exact
      (orientedCrossing_point_ne_liftedVertexPosition
        wellFormed degree crossingMem
        (drawingVariableRouteSite_vertex_mem formula atomValid)
        site.2)
        (by
          simpa [liftedIncidenceVertexPosition] using
            positionData.1.symm)
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CrossoverVariable.position_in_macrocell
          (crossoverInternalVariable internal))
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            crossingMacroOrigin, clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inr ⟨internal, rfl⟩

/-- No retained variable occupies a bend clause position. -/
theorem retainedVariablePosition_ne_bendClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPlanarSATVariableValid formula atom)
    (routeBend : RouteBend)
    (routeBendMem :
      routeBend ∈
        (drawingRouteBends
          (PeriodicCNF.incidenceGraph formula)).dedup)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATBendFormulaAt
          (Variable := Variable)
          (PeriodicCNF.incidenceGraph formula)
          routeBend).zipIdx) :
    drawingPlanarSATVariablePosition formula atom ≠
      clause.position := by
  rcases bendClause_localPosition_avoids_carrier_or_atom
      (PeriodicCNF.incidenceGraph formula) routeBend clauseMember with
    ⟨offset, clausePosition, offsetBounds, offsetAvoids⟩
  intro positionEq
  rcases atom with (⟨carrier⟩ | ⟨site⟩) |
    ⟨crossing, internal⟩
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CarrierNode.localPosition_in_macrocell carrier)
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            CarrierNode.position_eq_scale_add_local,
            clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inl
      (retainedCarrierNode_localPosition_isCarrierPort
        wellFormed degree isLocal atomValid)
  · have positionData :=
      planarSATMacrocellPosition_eq
        duplicatorArmCenterPosition_in_macrocell
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            liftedIncidenceVertexMacroOrigin,
            clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inr rfl
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CrossoverVariable.position_in_macrocell
          (crossoverInternalVariable internal))
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            crossingMacroOrigin, clausePosition] using positionEq)
    exact
      (orientedCrossing_point_ne_drawingRouteBend_drawingPoint
        wellFormed degree isLocal atomValid
        (List.mem_dedup.mp routeBendMem))
        positionData.1

/-- No retained variable occupies a routed source-clause position. -/
theorem retainedVariablePosition_ne_routedClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPlanarSATVariableValid formula atom)
    (site : ClauseRouteSite)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    (clauseEq :
      clause =
        (routedClauseAt formula site).rename
          planarSATExternalVariableMap) :
    drawingPlanarSATVariablePosition formula atom ≠
      clause.position := by
  rcases routedClause_localPosition_avoids_variables
      formula site clauseEq with
    ⟨offset, clausePosition, offsetBounds, offsetAvoids⟩
  intro positionEq
  rcases atom with (⟨carrier⟩ | ⟨variableSite⟩) |
    ⟨crossing, internal⟩
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CarrierNode.localPosition_in_macrocell carrier)
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            CarrierNode.position_eq_scale_add_local,
            routedClauseOrigin, liftedIncidenceVertexMacroOrigin,
            clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inl
      (retainedCarrierNode_localPosition_isCarrierPort
        wellFormed degree isLocal atomValid)
  · have positionData :=
      planarSATMacrocellPosition_eq
        duplicatorArmCenterPosition_in_macrocell
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            liftedIncidenceVertexMacroOrigin,
            routedClauseOrigin, clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inr (Or.inl rfl)
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CrossoverVariable.position_in_macrocell
          (crossoverInternalVariable internal))
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            crossingMacroOrigin, routedClauseOrigin,
            liftedIncidenceVertexMacroOrigin,
            clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inr (Or.inr ⟨internal, rfl⟩)

/-- No retained variable occupies a routed-variable clause position. -/
theorem retainedVariablePosition_ne_routedVariableClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPlanarSATVariableValid formula atom)
    (site : VariableRouteSite Variable)
    (siteMem : site ∈ drawingVariableRouteSites formula)
    (arm : DuplicatorArm)
    (link : EqualityLink (PlanarSATNode Variable))
    (linkMem : link ∈ routedVariableLinksAt formula site)
    (armEq : arm = link.first.duplicatorArm)
    {clause : EmbeddedClause (PlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx) :
    drawingPlanarSATVariablePosition formula atom ≠
      clause.position := by
  have linkPositions :=
    routedVariableLink_positions formula site linkMem
  have positionsEq :
      link.positions =
        ⟨Cell.add (routedVariableOrigin formula site)
            (duplicatorArmEqualityPositions arm).forward,
          Cell.add (routedVariableOrigin formula site)
            (duplicatorArmEqualityPositions arm).backward⟩ := by
    rw [linkPositions, armEq]
    rfl
  rcases routedVariableClause_localPosition_avoids_carrier_or_atom
      (routedVariableOrigin formula site) arm link positionsEq
      clauseMember with
    ⟨offset, clausePosition, offsetBounds, offsetAvoids⟩
  intro positionEq
  rcases atom with (⟨carrier⟩ | ⟨variableSite⟩) |
    ⟨crossing, internal⟩
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CarrierNode.localPosition_in_macrocell carrier)
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            CarrierNode.position_eq_scale_add_local,
            routedVariableOrigin, liftedIncidenceVertexMacroOrigin,
            clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inl
      (retainedCarrierNode_localPosition_isCarrierPort
        wellFormed degree isLocal atomValid)
  · have positionData :=
      planarSATMacrocellPosition_eq
        duplicatorArmCenterPosition_in_macrocell
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            liftedIncidenceVertexMacroOrigin,
            routedVariableOrigin, clausePosition] using positionEq)
    apply offsetAvoids
    rw [← positionData.2]
    exact Or.inr rfl
  · have positionData :=
      planarSATMacrocellPosition_eq
        (CrossoverVariable.position_in_macrocell
          (crossoverInternalVariable internal))
        offsetBounds
        (by
          simpa [drawingPlanarSATVariablePosition,
            crossingMacroOrigin, routedVariableOrigin,
            liftedIncidenceVertexMacroOrigin,
            clausePosition] using positionEq)
    exact
      (orientedCrossing_point_ne_liftedVertexPosition
        wellFormed degree atomValid
        (drawingVariableRouteSite_vertex_mem formula siteMem)
        site.2)
        (by
          simpa [liftedIncidenceVertexPosition] using
            positionData.1)

/-- No retained variable occupies the clause position of a retained
non-carrier component. -/
theorem retainedVariablePosition_ne_noncarrierClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (atom : PlanarSATVariable Variable)
    (atomValid :
      RetainedDrawingPlanarSATVariableValid formula atom)
    (metadata : DrawingPlanarSATClauseMetadata Variable)
    (valid : metadata.RetainedValid formula)
    (notCarrier :
      ¬∃ link, metadata.source.component = .carrier link) :
    drawingPlanarSATVariablePosition formula atom ≠
      metadata.clause.position := by
  rcases metadata with ⟨clause, source⟩
  cases source with
  | crossover crossing clauseIndex =>
      exact retainedVariablePosition_ne_crossoverClausePosition
        formula wellFormed degree isLocal atom atomValid
        crossing valid.1 valid.2
  | carrier link clauseIndex =>
      exact False.elim
        (notCarrier ⟨link, rfl⟩)
  | bend routeBend clauseIndex =>
      exact retainedVariablePosition_ne_bendClausePosition
        formula wellFormed degree isLocal atom atomValid
        routeBend valid.1 valid.2
  | routedClause site =>
      exact retainedVariablePosition_ne_routedClausePosition
        formula wellFormed degree isLocal atom atomValid
        site valid.2
  | routedVariable site armIndex arm link clauseIndex =>
      exact retainedVariablePosition_ne_routedVariableClausePosition
        formula wellFormed degree isLocal atom atomValid
        site valid.1 arm link
        (List.fst_mem_of_mem_zipIdx valid.2.1)
        valid.2.2.1 valid.2.2.2

end LeanTrominoes.PeriodicOrthocrossing
