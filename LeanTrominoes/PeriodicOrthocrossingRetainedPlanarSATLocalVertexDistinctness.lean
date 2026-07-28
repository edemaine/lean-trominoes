import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATClauseKeys
import LeanTrominoes.EmbeddedCNFIncidenceDrawingVertexCoverage

/-!
# Local vertex distinctness for retained planar-SAT components

Each selected finite component already carries a planarity certificate.
This file extracts the two vertex facts needed by the global assembly:
local clause positions are injective, and local variable positions avoid
local clause positions.  Equal positions in two metadata entries for the
same component therefore identify the same local clause index.
-/

namespace LeanTrominoes

namespace PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

theorem clausePositions_nodup_of_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (planar : drawing.IsPlanar) :
    (drawing.formula.map EmbeddedClause.position).Nodup := by
  exact planar.2.2.2.of_append_right

theorem variablePosition_ne_clausePosition_of_isPlanar
    {Variable : Type*} [DecidableEq Variable]
    {drawing : EmbeddedCNFIncidenceDrawing Variable}
    (planar : drawing.IsPlanar)
    {atom : Variable}
    (atomMem : atom ∈ drawing.variableVertices)
    {clause : EmbeddedClause Variable}
    (clauseMem : clause ∈ drawing.formula) :
    drawing.variablePosition atom ≠ clause.position := by
  have verticesNodup := planar.2.2.2
  rw [vertexPositions, List.nodup_append] at verticesNodup
  intro equal
  exact verticesNodup.2.2
    (drawing.variablePosition atom)
    (List.mem_map.mpr ⟨atom, atomMem, rfl⟩)
    clause.position
    (List.mem_map.mpr ⟨clause, clauseMem, rfl⟩)
    equal

end PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

theorem DrawingPlanarSATClauseMetadata.localClauseIndex_eq_of_position_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    (sameComponent :
      first.source.component = second.source.component)
    (positionEq : first.clause.position = second.clause.position) :
    first.source.localClauseIndex =
      second.source.localClauseIndex := by
  have sameDrawing :
      first.source.incidenceDrawing formula =
        second.source.incidenceDrawing formula :=
    first.source.incidenceDrawing_eq_of_component_eq
      formula second.source sameComponent
  have firstMember :=
    first.retainedLocalClauseMember
      wellFormed degree isLocal firstValid
  have secondMember :=
    second.retainedLocalClauseMember
      wellFormed degree isLocal secondValid
  rw [← sameDrawing] at secondMember
  have positionsNodup :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.clausePositions_nodup_of_isPlanar
      (first.retainedLocalDrawingIsPlanar
        wellFormed degree isLocal firstValid)
  have firstLookup :
      ((first.source.incidenceDrawing formula).formula.map
        EmbeddedClause.position)[first.source.localClauseIndex]? =
          some first.clause.position := by
    rw [List.getElem?_map,
      (List.mk_mem_zipIdx_iff_getElem?).mp firstMember]
    rfl
  have secondLookup :
      ((first.source.incidenceDrawing formula).formula.map
        EmbeddedClause.position)[second.source.localClauseIndex]? =
          some second.clause.position := by
    rw [List.getElem?_map,
      (List.mk_mem_zipIdx_iff_getElem?).mp secondMember]
    rfl
  rw [positionEq] at firstLookup
  exact List.Nodup.index_eq_of_getElem?_eq_some
    positionsNodup firstLookup secondLookup

theorem DrawingPlanarSATClauseMetadata.localVariablePosition_ne_clausePosition
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
    {atom : PlanarSATVariable Variable}
    (atomMem :
      atom ∈
        (metadata.source.incidenceDrawing formula).variableVertices) :
    drawingPlanarSATVariablePosition formula atom ≠
      metadata.clause.position := by
  have clauseMember :=
    List.fst_mem_of_mem_zipIdx
      (metadata.retainedLocalClauseMember
        wellFormed degree isLocal valid)
  have distinct :=
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.variablePosition_ne_clausePosition_of_isPlanar
      (metadata.retainedLocalDrawingIsPlanar
        wellFormed degree isLocal valid)
      atomMem clauseMember
  simpa using distinct

end PeriodicOrthocrossing
end LeanTrominoes
