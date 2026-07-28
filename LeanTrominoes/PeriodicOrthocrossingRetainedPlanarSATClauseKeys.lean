import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATComponentSeparation
import LeanTrominoes.PeriodicOrthocrossingPlanarSATClauseKeyLookup

/-!
# Unique component keys for retained planar SAT metadata

Replacing the carrier enumeration preserves the component/local-clause key
invariant.  Selected retained links are duplicate-free, and the other four
metadata families are unchanged.  Hence equal retained metadata keys identify
one global clause index.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 1200000

/-- Retained carrier metadata has unique component/local-clause keys. -/
theorem retainedDrawingPlanarSATCarrierClauseMetadata_keys_nodup
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) graph).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  simpa [retainedDrawingPlanarSATCarrierClauseMetadata,
    drawingPlanarSATCarrierClauseMetadataFor,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_flatMap, List.map_map, Function.comp_def] using
    (componentClauseKeyBlocks_nodup
      (retainedDrawingCompleteCarrierLinks graph)
      (retainedDrawingCompleteCarrierLinks_nodup graph)
      DrawingPlanarSATComponent.carrier
      (fun {_ _} equal =>
        DrawingPlanarSATComponent.carrier.inj equal)
      (fun link =>
        drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link))

/-- Every key from the retained carrier metadata family has carrier kind. -/
theorem retainedDrawingPlanarSATCarrierClauseMetadata_key_kind
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) graph).map
            DrawingPlanarSATClauseMetadata.componentClauseKey) :
    key.1.kind = .carrier := by
  rcases List.mem_map.mp keyMember with
    ⟨metadata, metadataMember, rfl⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨link, linkMember, metadataMember⟩
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  rfl

/-- The component/local-clause keys of the retained five-family metadata
list are pairwise distinct. -/
theorem retainedDrawingPlanarSATClauseMetadata_componentClauseKeys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((retainedDrawingPlanarSATClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  let graph := PeriodicCNF.incidenceGraph formula
  let crossoverKeys :=
    (drawingPlanarSATCrossoverClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.componentClauseKey
  let carrierKeys :=
    (retainedDrawingPlanarSATCarrierClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.componentClauseKey
  let bendKeys :=
    (drawingPlanarSATBendClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.componentClauseKey
  let routedClauseKeys :=
    (drawingPlanarSATRoutedClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey
  let routedVariableKeys :=
    (drawingPlanarSATRoutedVariableClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey
  have crossoverKeysNodup : crossoverKeys.Nodup :=
    drawingPlanarSATCrossoverClauseMetadata_keys_nodup graph
  have carrierKeysNodup : carrierKeys.Nodup :=
    retainedDrawingPlanarSATCarrierClauseMetadata_keys_nodup graph
  have bendKeysNodup : bendKeys.Nodup :=
    drawingPlanarSATBendClauseMetadata_keys_nodup graph
  have routedClauseKeysNodup : routedClauseKeys.Nodup :=
    drawingPlanarSATRoutedClauseMetadata_keys_nodup formula
  have routedVariableKeysNodup : routedVariableKeys.Nodup :=
    drawingPlanarSATRoutedVariableClauseMetadata_keys_nodup formula
  have crossoverKeysKind :
      ∀ key ∈ crossoverKeys, key.1.kind = .crossover :=
    fun _ member =>
      drawingPlanarSATCrossoverClauseMetadata_key_kind graph member
  have carrierKeysKind :
      ∀ key ∈ carrierKeys, key.1.kind = .carrier :=
    fun _ member =>
      retainedDrawingPlanarSATCarrierClauseMetadata_key_kind graph member
  have bendKeysKind :
      ∀ key ∈ bendKeys, key.1.kind = .bend :=
    fun _ member =>
      drawingPlanarSATBendClauseMetadata_key_kind graph member
  have routedClauseKeysKind :
      ∀ key ∈ routedClauseKeys, key.1.kind = .routedClause :=
    fun _ member =>
      drawingPlanarSATRoutedClauseMetadata_key_kind formula member
  have routedVariableKeysKind :
      ∀ key ∈ routedVariableKeys,
        key.1.kind = .routedVariable :=
    fun _ member =>
      drawingPlanarSATRoutedVariableClauseMetadata_key_kind
        formula member
  have crossoverCarrierDisjoint :
      List.Disjoint crossoverKeys carrierKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .crossover .carrier
      (by decide) crossoverKeysKind carrierKeysKind
  have crossoverBendDisjoint :
      List.Disjoint crossoverKeys bendKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .crossover .bend
      (by decide) crossoverKeysKind bendKeysKind
  have crossoverRoutedClauseDisjoint :
      List.Disjoint crossoverKeys routedClauseKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .crossover .routedClause
      (by decide) crossoverKeysKind routedClauseKeysKind
  have crossoverRoutedVariableDisjoint :
      List.Disjoint crossoverKeys routedVariableKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .crossover .routedVariable
      (by decide) crossoverKeysKind routedVariableKeysKind
  have carrierBendDisjoint :
      List.Disjoint carrierKeys bendKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .carrier .bend
      (by decide) carrierKeysKind bendKeysKind
  have carrierRoutedClauseDisjoint :
      List.Disjoint carrierKeys routedClauseKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .carrier .routedClause
      (by decide) carrierKeysKind routedClauseKeysKind
  have carrierRoutedVariableDisjoint :
      List.Disjoint carrierKeys routedVariableKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .carrier .routedVariable
      (by decide) carrierKeysKind routedVariableKeysKind
  have bendRoutedClauseDisjoint :
      List.Disjoint bendKeys routedClauseKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .bend .routedClause
      (by decide) bendKeysKind routedClauseKeysKind
  have bendRoutedVariableDisjoint :
      List.Disjoint bendKeys routedVariableKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .bend .routedVariable
      (by decide) bendKeysKind routedVariableKeysKind
  have routedClauseVariableDisjoint :
      List.Disjoint routedClauseKeys routedVariableKeys :=
    classifiedLists_disjoint _ _
      (fun key => key.1.kind) .routedClause .routedVariable
      (by decide) routedClauseKeysKind routedVariableKeysKind
  have crossoverCarrierNodup :
      (crossoverKeys ++ carrierKeys).Nodup :=
    crossoverKeysNodup.append carrierKeysNodup
      crossoverCarrierDisjoint
  have coreKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys).Nodup :=
    crossoverCarrierNodup.append bendKeysNodup (by
      rw [List.disjoint_append_left]
      exact ⟨crossoverBendDisjoint, carrierBendDisjoint⟩)
  have coreClauseKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys ++
        routedClauseKeys).Nodup :=
    coreKeysNodup.append routedClauseKeysNodup (by
      rw [List.disjoint_append_left,
        List.disjoint_append_left]
      exact
        ⟨⟨crossoverRoutedClauseDisjoint,
            carrierRoutedClauseDisjoint⟩,
          bendRoutedClauseDisjoint⟩)
  have allKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys ++
        routedClauseKeys ++ routedVariableKeys).Nodup :=
    coreClauseKeysNodup.append routedVariableKeysNodup (by
      rw [List.disjoint_append_left,
        List.disjoint_append_left,
        List.disjoint_append_left]
      exact
        ⟨⟨⟨crossoverRoutedVariableDisjoint,
              carrierRoutedVariableDisjoint⟩,
            bendRoutedVariableDisjoint⟩,
          routedClauseVariableDisjoint⟩)
  simpa [retainedDrawingPlanarSATClauseMetadata, graph,
    crossoverKeys, carrierKeys, bendKeys,
    routedClauseKeys, routedVariableKeys,
    List.map_append] using allKeysNodup

/-- Equal retained component/local-clause keys returned by two metadata
lookups force the same global clause index. -/
theorem
    retainedDrawingPlanarSATClauseMetadata_lookup_componentClauseKey_injective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstLookup :
      (retainedDrawingPlanarSATClauseMetadata
        formula)[firstClauseIndex]? = some firstMetadata)
    (secondLookup :
      (retainedDrawingPlanarSATClauseMetadata
        formula)[secondClauseIndex]? = some secondMetadata)
    (keysEqual :
      firstMetadata.componentClauseKey =
        secondMetadata.componentClauseKey) :
    firstClauseIndex = secondClauseIndex := by
  let keys :=
    (retainedDrawingPlanarSATClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey
  have keysNodup : keys.Nodup :=
    retainedDrawingPlanarSATClauseMetadata_componentClauseKeys_nodup
      formula
  have firstKeyLookup :
      keys[firstClauseIndex]? =
        some firstMetadata.componentClauseKey := by
    dsimp [keys]
    rw [List.getElem?_map, firstLookup]
    rfl
  have secondKeyLookup :
      keys[secondClauseIndex]? =
        some secondMetadata.componentClauseKey := by
    dsimp [keys]
    rw [List.getElem?_map, secondLookup]
    rfl
  rw [keysEqual] at firstKeyLookup
  exact List.Nodup.index_eq_of_getElem?_eq_some
    keysNodup firstKeyLookup secondKeyLookup

/-- Lookup-level component/local-clause key injectivity for the retained
presentation. -/
def RetainedDrawingPlanarSATComponentClauseKeysInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ {firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable}
    {firstClauseIndex secondClauseIndex : Nat},
    (retainedDrawingPlanarSATClauseMetadata
        formula)[firstClauseIndex]? = some firstMetadata →
      (retainedDrawingPlanarSATClauseMetadata
          formula)[secondClauseIndex]? = some secondMetadata →
      firstMetadata.source.component =
          secondMetadata.source.component →
      firstMetadata.source.localClauseIndex =
          secondMetadata.source.localClauseIndex →
      firstClauseIndex = secondClauseIndex

/-- The retained metadata enumeration has injective
component/local-clause keys. -/
theorem retainedDrawingPlanarSAT_componentClauseKeysInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    RetainedDrawingPlanarSATComponentClauseKeysInjective formula := by
  intro firstMetadata secondMetadata
    firstClauseIndex secondClauseIndex
    firstLookup secondLookup
    componentEqual localClauseIndexEqual
  apply
    retainedDrawingPlanarSATClauseMetadata_lookup_componentClauseKey_injective
      formula firstLookup secondLookup
  exact Prod.ext componentEqual localClauseIndexEqual

end PeriodicOrthocrossing
end LeanTrominoes
