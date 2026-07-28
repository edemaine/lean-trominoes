import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex
import LeanTrominoes.PeriodicOrthocrossingPlanarSATSourceTranslation

/-!
# Retained membership of planar-SAT clause sources

Periodic reindexing needs to separate two facts stored together in retained
metadata validity: the translated geometric component must still belong to
the retained finite window, and the translated clause must occupy the same
local index in that component's formula.

This file exposes those two predicates directly on clause sources.  Their
conjunction is exactly `DrawingPlanarSATClauseMetadata.RetainedValid`, so it
also characterizes membership in the retained metadata enumeration.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

namespace DrawingPlanarSATClauseSource

/-- The physical component named by a source belongs to the retained finite
family.  For routed-variable arms this includes the link's presentation
index and the arm selected by its first endpoint. -/
def RetainedComponentMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATClauseSource Variable → Prop :=
  let graph := PeriodicCNF.incidenceGraph formula
  fun source =>
    match source with
    | .crossover crossing _ =>
        crossing ∈ orientedCrossingHalo graph
    | .carrier link _ =>
        link ∈ retainedDrawingCompleteCarrierLinks graph
    | .bend routeBend _ =>
        routeBend ∈ (drawingRouteBends graph).dedup
    | .routedClause site =>
        site ∈ drawingClauseRouteSites formula
    | .routedVariable site armIndex arm link _ =>
        site ∈ drawingVariableRouteSites formula ∧
          (link, armIndex) ∈
            (routedVariableLinksAt formula site).zipIdx ∧
          arm = link.first.duplicatorArm

/-- The unpositioned local clause family named by a source. -/
def clauseFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    DrawingPlanarSATClauseSource Variable →
      List (EmbeddedClause (PlanarSATVariable Variable))
  | .crossover crossing _ =>
      drawingPlanarSATCrossoverFormulaAt crossing
  | .carrier link _ =>
      drawingPlanarSATCarrierFormulaAt link
  | .bend routeBend _ =>
      drawingPlanarSATBendFormulaAt
        (PeriodicCNF.incidenceGraph formula) routeBend
  | .routedClause site =>
      [(routedClauseAt formula site).rename
        planarSATExternalVariableMap]
  | .routedVariable _ _ _ link _ =>
      drawingPlanarSATRoutedVariableFormulaAt link

/-- The local clause family is determined by the geometric component; source
enumeration indices such as a routed-variable arm's global list index do not
affect it. -/
theorem clauseFormula_eq_of_component_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (first second : DrawingPlanarSATClauseSource Variable)
    (componentEq : first.component = second.component) :
    first.clauseFormula formula =
      second.clauseFormula formula := by
  cases first <;> cases second <;>
    simp_all [DrawingPlanarSATClauseSource.component,
      clauseFormula]

end DrawingPlanarSATClauseSource

namespace DrawingPlanarSATClauseMetadata

/-- Retained validity splits exactly into physical component membership and
same-index membership in the source's local clause family. -/
theorem retainedValid_iff_sourceMember_and_localClauseMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    metadata.RetainedValid formula ↔
      metadata.source.RetainedComponentMember formula ∧
        (metadata.clause, metadata.source.localClauseIndex) ∈
          (metadata.source.clauseFormula formula).zipIdx := by
  rcases metadata with ⟨clause, source⟩
  cases source <;>
    simp [DrawingPlanarSATClauseMetadata.RetainedValid,
      DrawingPlanarSATClauseSource.RetainedComponentMember,
      DrawingPlanarSATClauseSource.clauseFormula,
      DrawingPlanarSATClauseSource.localClauseIndex, and_assoc]

/-- A source and same-index local clause determine an entry of the retained
metadata enumeration. -/
theorem mem_retained_iff_sourceMember_and_localClauseMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    metadata ∈ retainedDrawingPlanarSATClauseMetadata formula ↔
      metadata.source.RetainedComponentMember formula ∧
        (metadata.clause, metadata.source.localClauseIndex) ∈
          (metadata.source.clauseFormula formula).zipIdx := by
  rw [metadata.mem_retained_iff_retainedValid formula,
    metadata.retainedValid_iff_sourceMember_and_localClauseMember formula]

end DrawingPlanarSATClauseMetadata

/-- Recover a concrete global retained-metadata lookup from a retained
source and a clause at its recorded local index. -/
theorem exists_retainedMetadataLookup_of_sourceMember
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (clause : EmbeddedClause (PlanarSATVariable Variable))
    (sourceMember : source.RetainedComponentMember formula)
    (localClauseMember :
      (clause, source.localClauseIndex) ∈
        (source.clauseFormula formula).zipIdx) :
    ∃ metadataIndex : Nat,
      (retainedDrawingPlanarSATClauseMetadata formula)[metadataIndex]? =
        some
          ({ clause := clause, source := source } :
            DrawingPlanarSATClauseMetadata Variable) := by
  let metadata : DrawingPlanarSATClauseMetadata Variable :=
    ⟨clause, source⟩
  have metadataMember :
      metadata ∈
        retainedDrawingPlanarSATClauseMetadata formula :=
    (DrawingPlanarSATClauseMetadata.mem_retained_iff_sourceMember_and_localClauseMember
      formula metadata).2 <| by
      simpa only [metadata] using
        And.intro sourceMember localClauseMember
  rcases List.mem_iff_getElem?.mp metadataMember with
    ⟨metadataIndex, metadataLookup⟩
  exact ⟨metadataIndex, by simpa only [metadata] using metadataLookup⟩

end PeriodicOrthocrossing
end LeanTrominoes
