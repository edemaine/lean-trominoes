import LeanTrominoes.PeriodicOrthocrossingPlanarSATLocalIncidenceDrawings

/-!
# Unique geometric-component clause keys

The finite planar-SAT formula is a concatenation of local gadget formulas.
This file proves that the pair consisting of a gadget's geometric component
and its local clause index occurs at exactly one global clause index.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The geometric component and local clause index named by one metadata
entry. -/
def DrawingPlanarSATClauseMetadata.componentClauseKey
    {Variable : Type*}
    (metadata : DrawingPlanarSATClauseMetadata Variable) :
    DrawingPlanarSATComponent Variable × Nat :=
  (metadata.source.component, metadata.source.localClauseIndex)

/-- Equal geometric-component/local-clause keys returned at two global
metadata positions identify the same global clause occurrence. -/
def DrawingPlanarSATComponentClauseKeysInjective
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Prop :=
  ∀ {firstMetadata secondMetadata :
      DrawingPlanarSATClauseMetadata Variable}
    {firstClauseIndex secondClauseIndex : Nat},
    (drawingPlanarSATClauseMetadata formula)[firstClauseIndex]? =
        some firstMetadata →
      (drawingPlanarSATClauseMetadata formula)[secondClauseIndex]? =
        some secondMetadata →
      firstMetadata.source.component =
          secondMetadata.source.component →
      firstMetadata.source.localClauseIndex =
          secondMetadata.source.localClauseIndex →
      firstClauseIndex = secondClauseIndex

/-- The five disjoint constructors of geometric components. -/
inductive DrawingPlanarSATComponentKind
  | crossover
  | carrier
  | bend
  | routedClause
  | routedVariable
  deriving DecidableEq

/-- Forget all component data except its geometric family. -/
def DrawingPlanarSATComponent.kind
    {Variable : Type*} :
    DrawingPlanarSATComponent Variable →
      DrawingPlanarSATComponentKind
  | .crossover _ => .crossover
  | .carrier _ => .carrier
  | .bend _ => .bend
  | .routedClause _ => .routedClause
  | .routedVariable _ _ _ => .routedVariable

/-- Pairing every presentation index with one fixed component remains
duplicate-free. -/
theorem indexedComponentClauseKeys_nodup
    {Component Value : Type*} [DecidableEq Component]
    (component : Component) (values : List Value) :
    (values.zipIdx.map fun tagged =>
      (component, tagged.2)).Nodup := by
  have taggedNodup :
      values.zipIdx.Nodup :=
    (List.nodup_zipIdx_map_snd values).of_map Prod.snd
  apply taggedNodup.map_on
  intro first firstMember second secondMember equal
  have indexEqual : first.2 = second.2 :=
    congrArg (fun key : Component × Nat => key.2) equal
  have firstLookup :=
    (List.mk_mem_zipIdx_iff_getElem?
      (l := values) (x := first.1) (i := first.2)).mp
        firstMember
  have secondLookup :=
    (List.mk_mem_zipIdx_iff_getElem?
      (l := values) (x := second.1) (i := second.2)).mp
        secondMember
  have valueEqual : first.1 = second.1 := by
    rw [indexEqual] at firstLookup
    exact Option.some.inj
      (firstLookup.symm.trans secondLookup)
  exact Prod.ext valueEqual indexEqual

/-- Duplicate-free component names, each carrying its own locally indexed
clause block, produce duplicate-free component/local-index keys. -/
theorem componentClauseKeyBlocks_nodup
    {Outer Component Value : Type*}
    [DecidableEq Outer] [DecidableEq Component]
    (outers : List Outer)
    (outerNodup : outers.Nodup)
    (component : Outer → Component)
    (componentInjective : Function.Injective component)
    (values : Outer → List Value) :
    (outers.flatMap fun outer =>
      (values outer).zipIdx.map fun tagged =>
        (component outer, tagged.2)).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · intro outer outerMember
    exact indexedComponentClauseKeys_nodup
      (component outer) (values outer)
  · exact
      (List.nodup_iff_pairwise_ne.mp outerNodup).imp fun
        {first second} different => by
          change List.Disjoint _ _
          rw [List.disjoint_left]
          intro key firstMember secondMember
          rcases List.mem_map.mp firstMember with
            ⟨firstTagged, firstTaggedMember, keyEqual⟩
          rcases List.mem_map.mp secondMember with
            ⟨secondTagged, secondTaggedMember, keyEqual'⟩
          apply different
          apply componentInjective
          exact congrArg Prod.fst
            (keyEqual.trans keyEqual'.symm)

/-- Duplicate-free blocks classified by distinct outer tags have a
duplicate-free flattening. -/
theorem taggedBlocks_nodup
    {Tag Value : Type*} [DecidableEq Tag]
    (blocks : List (Tag × List Value))
    (tagsNodup : (blocks.map Prod.fst).Nodup)
    (blocksNodup :
      ∀ block ∈ blocks, block.2.Nodup)
    (classify : Value → Tag)
    (classified :
      ∀ block ∈ blocks, ∀ value ∈ block.2,
        classify value = block.1) :
    (blocks.flatMap Prod.snd).Nodup := by
  rw [List.nodup_flatMap]
  constructor
  · exact blocksNodup
  · have tagsPairwise :
        blocks.Pairwise
          (fun first second => first.1 ≠ second.1) := by
      rw [← List.pairwise_map]
      exact List.nodup_iff_pairwise_ne.mp tagsNodup
    exact tagsPairwise.imp_of_mem fun
      {first second} firstMember secondMember tagNe => by
        change List.Disjoint first.2 second.2
        rw [List.disjoint_left]
        intro value firstValueMember secondValueMember
        exact tagNe
          ((classified first firstMember value firstValueMember).symm.trans
            (classified second secondMember
              value secondValueMember))

/-- Lists whose members have different classifier values are disjoint. -/
theorem classifiedLists_disjoint
    {Tag Value : Type*}
    (first second : List Value)
    (classify : Value → Tag)
    (firstTag secondTag : Tag)
    (different : firstTag ≠ secondTag)
    (firstClassified :
      ∀ value ∈ first, classify value = firstTag)
    (secondClassified :
      ∀ value ∈ second, classify value = secondTag) :
    List.Disjoint first second := by
  rw [List.disjoint_left]
  intro value firstMember secondMember
  exact different
    ((firstClassified value firstMember).symm.trans
      (secondClassified value secondMember))

/-- Flattening a block function that ignores `zipIdx`'s index is the same
as flattening it over the original list. -/
theorem zipIdx_flatMap_fst
    {Input Output : Type*}
    (values : List Input) (blocks : Input → List Output) :
    values.zipIdx.flatMap (fun tagged => blocks tagged.1) =
      values.flatMap blocks := by
  rw [← List.flatMap_map, List.zipIdx_map_fst]

/-- Adjacent pairs of a duplicate-free list are duplicate-free. -/
theorem consecutivePairs_nodup_of_nodup
    {Value : Type*} [DecidableEq Value]
    (values : List Value) (nodup : values.Nodup) :
    (consecutivePairs values).Nodup := by
  apply List.Nodup.of_map Prod.fst
  exact nodup.sublist (consecutivePairs_fst_sublist values)

/-- Each complete carrier chain contains no repeated equality link. -/
theorem completeCarrierLinks_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (key : Nat × Nat × Cell) :
    (completeCarrierLinks graph key).Nodup := by
  have pairsNodup :
      (consecutivePairs
        (completeCarrierNodes graph key)).Nodup :=
    consecutivePairs_nodup_of_nodup _
      (completeCarrierNodes_nodup graph key)
  have filteredNodup :=
    pairsNodup.filter fun pair =>
      !pair.1.sameCrossoverSite pair.2
  apply filteredNodup.map
  intro first second equal
  exact Prod.ext
    (congrArg EqualityLink.first equal)
    (congrArg EqualityLink.second equal)

/-- Complete carrier links from different occurrence keys are disjoint. -/
theorem completeCarrierLinks_disjoint_of_ne
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {firstKey secondKey : Nat × Nat × Cell}
    (different : firstKey ≠ secondKey) :
    List.Disjoint
      (completeCarrierLinks graph firstKey)
      (completeCarrierLinks graph secondKey) := by
  rw [List.disjoint_left]
  intro link firstMember secondMember
  have firstCommon :=
    completeCarrierLinks_common_key
      graph firstKey firstMember
  have secondCommon :=
    completeCarrierLinks_common_key
      graph secondKey secondMember
  exact different (firstCommon.1.symm.trans secondCommon.1)

/-- The complete represented carrier-link family has no duplicates. -/
theorem drawingCompleteCarrierLinks_nodup
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawingCompleteCarrierLinks graph).Nodup := by
  rw [drawingCompleteCarrierLinks, List.nodup_flatMap]
  constructor
  · intro key keyMember
    exact completeCarrierLinks_nodup graph key
  · exact
      (List.nodup_iff_pairwise_ne.mp
        (List.nodup_dedup
          ((drawingCarrierNodes graph).map
            CarrierNode.carrierKey))).imp fun
        {firstKey secondKey} different =>
          completeCarrierLinks_disjoint_of_ne graph different

/-- The active links at one routed-variable site have distinct first
endpoints and hence are duplicate-free. -/
theorem routedVariableLinksAt_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (routedVariableLinksAt formula site).Nodup := by
  have nodesNodup :
      (((variableRouteOccurrencesAt formula site).map fun occurrence =>
        (PlanarSATNode.carrier
          (.terminal
            (occurrence.targetTerminal formula)) :
          PlanarSATNode Variable)).dedup.take 3).Nodup :=
    (List.nodup_dedup _).take
  apply List.Nodup.of_map EqualityLink.first
  simpa [routedVariableLinksAt, routedVariableNodes, List.map_map,
    Function.comp_def] using nodesNodup

/-- Crossover metadata has unique component/local-clause keys. -/
theorem drawingPlanarSATCrossoverClauseMetadata_keys_nodup
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) graph).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  simpa [drawingPlanarSATCrossoverClauseMetadata,
    drawingPlanarSATCrossoverClauseMetadataFor,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_flatMap, List.map_map, Function.comp_def] using
    (componentClauseKeyBlocks_nodup
      (orientedCrossingHalo graph)
      (orientedCrossingHalo_nodup graph)
      DrawingPlanarSATComponent.crossover
      (fun {_ _} equal =>
        DrawingPlanarSATComponent.crossover.inj equal)
      (fun crossing =>
        drawingPlanarSATCrossoverFormulaAt
          (Variable := Variable) crossing))

/-- Complete-carrier metadata has unique component/local-clause keys. -/
theorem drawingPlanarSATCarrierClauseMetadata_keys_nodup
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((drawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) graph).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  simpa [drawingPlanarSATCarrierClauseMetadata,
    drawingPlanarSATCarrierClauseMetadataFor,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_flatMap, List.map_map, Function.comp_def] using
    (componentClauseKeyBlocks_nodup
      (drawingCompleteCarrierLinks graph)
      (drawingCompleteCarrierLinks_nodup graph)
      DrawingPlanarSATComponent.carrier
      (fun {_ _} equal =>
        DrawingPlanarSATComponent.carrier.inj equal)
      (fun link =>
        drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) link))

/-- Route-bend metadata has unique component/local-clause keys. -/
theorem drawingPlanarSATBendClauseMetadata_keys_nodup
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((drawingPlanarSATBendClauseMetadata
        (Variable := Variable) graph).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  simpa [drawingPlanarSATBendClauseMetadata,
    drawingPlanarSATBendClauseMetadataFor,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_flatMap, List.map_map, Function.comp_def] using
    (componentClauseKeyBlocks_nodup
      (drawingRouteBends graph).dedup
      (List.nodup_dedup _)
      DrawingPlanarSATComponent.bend
      (fun {_ _} equal =>
        DrawingPlanarSATComponent.bend.inj equal)
      (fun routeBend =>
        drawingPlanarSATBendFormulaAt
          (Variable := Variable) graph routeBend))

/-- Routed source-clause metadata has unique component/local-clause keys. -/
theorem drawingPlanarSATRoutedClauseMetadata_keys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((drawingPlanarSATRoutedClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  have mapped :=
    (drawingClauseRouteSites_nodup formula).map
      (f := fun site =>
        ((DrawingPlanarSATComponent.routedClause site :
            DrawingPlanarSATComponent Variable), 0))
      (fun first second equal =>
        DrawingPlanarSATComponent.routedClause.inj
          (congrArg
            (fun key :
              DrawingPlanarSATComponent Variable × Nat => key.1)
            equal))
  simpa [drawingPlanarSATRoutedClauseMetadata,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_map, Function.comp_def] using mapped

/-- Component/local-clause keys contributed by all active arms at one routed
variable site. -/
def routedVariableComponentClauseKeysAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    List (DrawingPlanarSATComponent Variable × Nat) :=
  (routedVariableLinksAt formula site).flatMap fun link =>
    (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx.map
      fun taggedClause =>
        (.routedVariable site link.first.duplicatorArm link,
          taggedClause.2)

/-- One routed-variable site's component/local-clause keys are unique. -/
theorem routedVariableComponentClauseKeysAt_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    (routedVariableComponentClauseKeysAt
      formula site).Nodup := by
  exact componentClauseKeyBlocks_nodup
    (routedVariableLinksAt formula site)
    (routedVariableLinksAt_nodup formula site)
    (fun link =>
      DrawingPlanarSATComponent.routedVariable
        site link.first.duplicatorArm link)
    (fun {first second} equal => by
      have linkEqual :
          some first = some second :=
        congrArg
          (fun component : DrawingPlanarSATComponent Variable =>
            match component with
            | .routedVariable _ _ link => some link
            | _ => none)
          equal
      exact Option.some.inj linkEqual)
    drawingPlanarSATRoutedVariableFormulaAt

/-- Projecting routed-variable metadata keys forgets only the enumeration
index of each active arm. -/
theorem drawingPlanarSATRoutedVariableClauseMetadata_keys
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    (drawingPlanarSATRoutedVariableClauseMetadata formula).map
        DrawingPlanarSATClauseMetadata.componentClauseKey =
      (drawingVariableRouteSites formula).flatMap fun site =>
        routedVariableComponentClauseKeysAt formula site := by
  simp [drawingPlanarSATRoutedVariableClauseMetadata,
    drawingPlanarSATRoutedVariableClauseMetadataFor,
    routedVariableComponentClauseKeysAt,
    DrawingPlanarSATClauseMetadata.componentClauseKey,
    DrawingPlanarSATClauseSource.component,
    DrawingPlanarSATClauseSource.localClauseIndex,
    List.map_flatMap, List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro site siteMember
  exact zipIdx_flatMap_fst
    (routedVariableLinksAt formula site)
    (fun link =>
      (drawingPlanarSATRoutedVariableFormulaAt link).zipIdx.map
        fun taggedClause =>
          (DrawingPlanarSATComponent.routedVariable
              site link.first.duplicatorArm link,
            taggedClause.2))

/-- Routed-variable metadata has unique component/local-clause keys across
all represented variable sites. -/
theorem drawingPlanarSATRoutedVariableClauseMetadata_keys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((drawingPlanarSATRoutedVariableClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  rw [drawingPlanarSATRoutedVariableClauseMetadata_keys,
    List.nodup_flatMap]
  constructor
  · intro site siteMember
    exact routedVariableComponentClauseKeysAt_nodup formula site
  · exact
      (List.nodup_iff_pairwise_ne.mp
        (List.nodup_dedup
          ((drawingCNFRouteOccurrences formula).map
            CNFRouteOccurrence.variableOccurrence))).imp fun
        {firstSite secondSite} different => by
          change List.Disjoint _ _
          rw [List.disjoint_left]
          intro key firstMember secondMember
          rcases List.mem_flatMap.mp firstMember with
            ⟨firstLink, firstLinkMember, firstMember⟩
          rcases List.mem_map.mp firstMember with
            ⟨firstClause, firstClauseMember, firstEqual⟩
          rcases List.mem_flatMap.mp secondMember with
            ⟨secondLink, secondLinkMember, secondMember⟩
          rcases List.mem_map.mp secondMember with
            ⟨secondClause, secondClauseMember, secondEqual⟩
          have componentEqual :
              DrawingPlanarSATComponent.routedVariable
                  firstSite
                  firstLink.first.duplicatorArm firstLink =
                DrawingPlanarSATComponent.routedVariable
                  secondSite
                  secondLink.first.duplicatorArm secondLink :=
            congrArg Prod.fst
              (firstEqual.trans secondEqual.symm)
          have siteEqual :
              some firstSite = some secondSite :=
            congrArg
              (fun component :
                  DrawingPlanarSATComponent Variable =>
                match component with
                | .routedVariable site _ _ => some site
                | _ => none)
              componentEqual
          exact different (Option.some.inj siteEqual)

/-- Every key from the crossover metadata family has crossover kind. -/
theorem drawingPlanarSATCrossoverClauseMetadata_key_kind
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) graph).map
            DrawingPlanarSATClauseMetadata.componentClauseKey) :
    key.1.kind = .crossover := by
  rcases List.mem_map.mp keyMember with
    ⟨metadata, metadataMember, rfl⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨crossing, crossingMember, metadataMember⟩
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  rfl

/-- Every key from the carrier metadata family has carrier kind. -/
theorem drawingPlanarSATCarrierClauseMetadata_key_kind
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (drawingPlanarSATCarrierClauseMetadata
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

/-- Every key from the bend metadata family has bend kind. -/
theorem drawingPlanarSATBendClauseMetadata_key_kind
    {Variable Vertex : Type*}
    [DecidableEq Variable] [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (drawingPlanarSATBendClauseMetadata
          (Variable := Variable) graph).map
            DrawingPlanarSATClauseMetadata.componentClauseKey) :
    key.1.kind = .bend := by
  rcases List.mem_map.mp keyMember with
    ⟨metadata, metadataMember, rfl⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨routeBend, routeBendMember, metadataMember⟩
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  rfl

/-- Every key from the routed source-clause family has routed-clause kind. -/
theorem drawingPlanarSATRoutedClauseMetadata_key_kind
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (drawingPlanarSATRoutedClauseMetadata formula).map
          DrawingPlanarSATClauseMetadata.componentClauseKey) :
    key.1.kind = .routedClause := by
  rcases List.mem_map.mp keyMember with
    ⟨metadata, metadataMember, rfl⟩
  rcases List.mem_map.mp metadataMember with
    ⟨site, siteMember, metadataEqual⟩
  subst metadata
  rfl

/-- Every key from the routed-variable family has routed-variable kind. -/
theorem drawingPlanarSATRoutedVariableClauseMetadata_key_kind
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {key : DrawingPlanarSATComponent Variable × Nat}
    (keyMember :
      key ∈
        (drawingPlanarSATRoutedVariableClauseMetadata formula).map
          DrawingPlanarSATClauseMetadata.componentClauseKey) :
    key.1.kind = .routedVariable := by
  rcases List.mem_map.mp keyMember with
    ⟨metadata, metadataMember, rfl⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨site, siteMember, metadataMember⟩
  rcases List.mem_flatMap.mp metadataMember with
    ⟨taggedLink, taggedLinkMember, metadataMember⟩
  rcases List.mem_map.mp metadataMember with
    ⟨taggedClause, taggedClauseMember, metadataEqual⟩
  subst metadata
  rfl

/-- The component/local-clause keys of the complete five-family metadata
list are pairwise distinct. -/
theorem drawingPlanarSATClauseMetadata_componentClauseKeys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    ((drawingPlanarSATClauseMetadata formula).map
      DrawingPlanarSATClauseMetadata.componentClauseKey).Nodup := by
  let graph := PeriodicCNF.incidenceGraph formula
  let crossoverKeys :=
    (drawingPlanarSATCrossoverClauseMetadata
      (Variable := Variable) graph).map
        DrawingPlanarSATClauseMetadata.componentClauseKey
  let carrierKeys :=
    (drawingPlanarSATCarrierClauseMetadata
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
  have crossoverKeysNodup : crossoverKeys.Nodup := by
    exact drawingPlanarSATCrossoverClauseMetadata_keys_nodup graph
  have carrierKeysNodup : carrierKeys.Nodup := by
    exact drawingPlanarSATCarrierClauseMetadata_keys_nodup graph
  have bendKeysNodup : bendKeys.Nodup := by
    exact drawingPlanarSATBendClauseMetadata_keys_nodup graph
  have routedClauseKeysNodup : routedClauseKeys.Nodup := by
    exact drawingPlanarSATRoutedClauseMetadata_keys_nodup formula
  have routedVariableKeysNodup : routedVariableKeys.Nodup := by
    exact drawingPlanarSATRoutedVariableClauseMetadata_keys_nodup
      formula
  have crossoverKeysKind :
      ∀ key ∈ crossoverKeys, key.1.kind = .crossover := by
    exact fun _ keyMember =>
      drawingPlanarSATCrossoverClauseMetadata_key_kind
        graph keyMember
  have carrierKeysKind :
      ∀ key ∈ carrierKeys, key.1.kind = .carrier := by
    exact fun _ keyMember =>
      drawingPlanarSATCarrierClauseMetadata_key_kind
        graph keyMember
  have bendKeysKind :
      ∀ key ∈ bendKeys, key.1.kind = .bend := by
    exact fun _ keyMember =>
      drawingPlanarSATBendClauseMetadata_key_kind
        graph keyMember
  have routedClauseKeysKind :
      ∀ key ∈ routedClauseKeys,
        key.1.kind = .routedClause := by
    exact fun _ keyMember =>
      drawingPlanarSATRoutedClauseMetadata_key_kind
        formula keyMember
  have routedVariableKeysKind :
      ∀ key ∈ routedVariableKeys,
        key.1.kind = .routedVariable := by
    exact fun _ keyMember =>
      drawingPlanarSATRoutedVariableClauseMetadata_key_kind
        formula keyMember
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
  have crossoverCarrierBendDisjoint :
      List.Disjoint (crossoverKeys ++ carrierKeys) bendKeys := by
    rw [List.disjoint_append_left]
    exact
      ⟨crossoverBendDisjoint, carrierBendDisjoint⟩
  have coreKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys).Nodup :=
    crossoverCarrierNodup.append bendKeysNodup
      crossoverCarrierBendDisjoint
  have coreRoutedClauseDisjoint :
      List.Disjoint
        (crossoverKeys ++ carrierKeys ++ bendKeys)
        routedClauseKeys := by
    rw [List.disjoint_append_left,
      List.disjoint_append_left]
    exact
      ⟨⟨crossoverRoutedClauseDisjoint,
          carrierRoutedClauseDisjoint⟩,
        bendRoutedClauseDisjoint⟩
  have coreClauseKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys ++
        routedClauseKeys).Nodup :=
    coreKeysNodup.append routedClauseKeysNodup
      coreRoutedClauseDisjoint
  have allPriorRoutedVariableDisjoint :
      List.Disjoint
        (crossoverKeys ++ carrierKeys ++ bendKeys ++
          routedClauseKeys)
        routedVariableKeys := by
    rw [List.disjoint_append_left,
      List.disjoint_append_left,
      List.disjoint_append_left]
    exact
      ⟨⟨⟨crossoverRoutedVariableDisjoint,
            carrierRoutedVariableDisjoint⟩,
          bendRoutedVariableDisjoint⟩,
        routedClauseVariableDisjoint⟩
  have allKeysNodup :
      (crossoverKeys ++ carrierKeys ++ bendKeys ++
        routedClauseKeys ++ routedVariableKeys).Nodup :=
    coreClauseKeysNodup.append routedVariableKeysNodup
      allPriorRoutedVariableDisjoint
  simpa [drawingPlanarSATClauseMetadata, graph,
    crossoverKeys, carrierKeys, bendKeys,
    routedClauseKeys, routedVariableKeys,
    List.map_append] using allKeysNodup

end PeriodicOrthocrossing
end LeanTrominoes
