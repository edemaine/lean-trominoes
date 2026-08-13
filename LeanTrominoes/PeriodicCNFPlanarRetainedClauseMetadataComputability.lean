/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVertexGadgetsComputability
import LeanTrominoes.PeriodicCNFPlanarRetainedSATClauseIndex

/-!
# Encodings for retained planar-SAT clause metadata

The retained planar formula records five kinds of local geometric clause
sources.  This module gives that source sum and the global clause/source pair
canonical primitive-recursive encodings, together with executable
constructors and projections used by the retained incidence-route lookup.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace DrawingPlanarSATClauseSource

abbrev RoutedVariableData (Variable : Type*) :=
  (((VariableRouteSite Variable × Nat) × DuplicatorArm) ×
    EqualityLink (PlanarSATNode Variable)) × Nat

private abbrev Data (Variable : Type*) :=
  (CrossingRecord × Nat) ⊕
    ((EqualityLink CarrierNode × Nat) ⊕
      ((RouteBend × Nat) ⊕
        (ClauseRouteSite ⊕ RoutedVariableData Variable)))

def equivData {Variable : Type*} :
    DrawingPlanarSATClauseSource Variable ≃ Data Variable where
  toFun
    | .crossover crossing localClauseIndex =>
        .inl (crossing, localClauseIndex)
    | .carrier link localClauseIndex =>
        .inr (.inl (link, localClauseIndex))
    | .bend routeBend localClauseIndex =>
        .inr (.inr (.inl (routeBend, localClauseIndex)))
    | .routedClause site =>
        .inr (.inr (.inr (.inl site)))
    | .routedVariable site armIndex arm link localClauseIndex =>
        .inr (.inr (.inr (.inr
          ((((site, armIndex), arm), link), localClauseIndex))))
  invFun
    | .inl data => .crossover data.1 data.2
    | .inr (.inl data) => .carrier data.1 data.2
    | .inr (.inr (.inl data)) => .bend data.1 data.2
    | .inr (.inr (.inr (.inl site))) => .routedClause site
    | .inr (.inr (.inr (.inr data))) =>
        .routedVariable data.1.1.1.1 data.1.1.1.2
          data.1.1.2 data.1.2 data.2
  left_inv source := by cases source <;> rfl
  right_inv
    | .inl _ => rfl
    | .inr (.inl _) => rfl
    | .inr (.inr (.inl _)) => rfl
    | .inr (.inr (.inr (.inl _))) => rfl
    | .inr (.inr (.inr (.inr _))) => rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (DrawingPlanarSATClauseSource Variable) :=
  Primcodable.ofEquiv (Data Variable) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem crossover_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : CrossingRecord × Nat =>
      (DrawingPlanarSATClauseSource.crossover data.1 data.2 :
        DrawingPlanarSATClauseSource Variable) := by
  change Primrec fun data : CrossingRecord × Nat =>
    (equivData (Variable := Variable)).symm (Sum.inl data)
  exact equivData_symm_primrec.comp
    (Primrec.sumInl : Primrec fun data : CrossingRecord × Nat =>
      (Sum.inl data : Data Variable))

theorem carrier_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : EqualityLink CarrierNode × Nat =>
      (DrawingPlanarSATClauseSource.carrier data.1 data.2 :
        DrawingPlanarSATClauseSource Variable) := by
  change Primrec fun data : EqualityLink CarrierNode × Nat =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inl data))
  have inner : Primrec fun data : EqualityLink CarrierNode × Nat =>
      (Sum.inl data : (EqualityLink CarrierNode × Nat) ⊕
        ((RouteBend × Nat) ⊕
          (ClauseRouteSite ⊕ RoutedVariableData Variable))) :=
    Primrec.sumInl
  exact equivData_symm_primrec.comp (Primrec.sumInr.comp inner)

theorem bend_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : RouteBend × Nat =>
      (DrawingPlanarSATClauseSource.bend data.1 data.2 :
        DrawingPlanarSATClauseSource Variable) := by
  change Primrec fun data : RouteBend × Nat =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inr (Sum.inl data)))
  have inner : Primrec fun data : RouteBend × Nat =>
      (Sum.inl data : (RouteBend × Nat) ⊕
        (ClauseRouteSite ⊕ RoutedVariableData Variable)) :=
    Primrec.sumInl
  have middle : Primrec fun data : RouteBend × Nat =>
      (Sum.inr (Sum.inl data) :
        (EqualityLink CarrierNode × Nat) ⊕
          ((RouteBend × Nat) ⊕
            (ClauseRouteSite ⊕ RoutedVariableData Variable))) :=
    Primrec.sumInr.comp inner
  exact equivData_symm_primrec.comp (Primrec.sumInr.comp middle)

theorem routedClause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun site : ClauseRouteSite =>
      (DrawingPlanarSATClauseSource.routedClause site :
        DrawingPlanarSATClauseSource Variable) := by
  change Primrec fun site : ClauseRouteSite =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inr (Sum.inr (Sum.inl site))))
  have inner : Primrec fun site : ClauseRouteSite =>
      (Sum.inl site : ClauseRouteSite ⊕ RoutedVariableData Variable) :=
    Primrec.sumInl
  have third : Primrec fun site : ClauseRouteSite =>
      (Sum.inr (Sum.inl site) : (RouteBend × Nat) ⊕
        (ClauseRouteSite ⊕ RoutedVariableData Variable)) :=
    Primrec.sumInr.comp inner
  have second : Primrec fun site : ClauseRouteSite =>
      (Sum.inr (Sum.inr (Sum.inl site)) :
        (EqualityLink CarrierNode × Nat) ⊕
          ((RouteBend × Nat) ⊕
            (ClauseRouteSite ⊕ RoutedVariableData Variable))) :=
    Primrec.sumInr.comp third
  exact equivData_symm_primrec.comp (Primrec.sumInr.comp second)

theorem routedVariable_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : RoutedVariableData Variable =>
      (DrawingPlanarSATClauseSource.routedVariable
        data.1.1.1.1 data.1.1.1.2 data.1.1.2 data.1.2 data.2 :
          DrawingPlanarSATClauseSource Variable) := by
  change Primrec fun data : RoutedVariableData Variable =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))
  have inner : Primrec fun data : RoutedVariableData Variable =>
      (Sum.inr data : ClauseRouteSite ⊕ RoutedVariableData Variable) :=
    Primrec.sumInr
  have third : Primrec fun data : RoutedVariableData Variable =>
      (Sum.inr (Sum.inr data) : (RouteBend × Nat) ⊕
        (ClauseRouteSite ⊕ RoutedVariableData Variable)) :=
    Primrec.sumInr.comp inner
  have second : Primrec fun data : RoutedVariableData Variable =>
      (Sum.inr (Sum.inr (Sum.inr data)) :
        (EqualityLink CarrierNode × Nat) ⊕
          ((RouteBend × Nat) ⊕
            (ClauseRouteSite ⊕ RoutedVariableData Variable))) :=
    Primrec.sumInr.comp third
  exact equivData_symm_primrec.comp (Primrec.sumInr.comp second)

end DrawingPlanarSATClauseSource

namespace DrawingPlanarSATClauseMetadata

def equivData {Variable : Type*} :
    DrawingPlanarSATClauseMetadata Variable ≃
      EmbeddedClause (PlanarSATVariable Variable) ×
        DrawingPlanarSATClauseSource Variable where
  toFun metadata := (metadata.clause, metadata.source)
  invFun data := ⟨data.1, data.2⟩
  left_inv metadata := by cases metadata; rfl
  right_inv data := by cases data; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (DrawingPlanarSATClauseMetadata Variable) :=
  Primcodable.ofEquiv
    (EmbeddedClause (PlanarSATVariable Variable) ×
      DrawingPlanarSATClauseSource Variable) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (DrawingPlanarSATClauseMetadata.clause :
      DrawingPlanarSATClauseMetadata Variable →
        EmbeddedClause (PlanarSATVariable Variable)) :=
  Primrec.fst.comp equivData_primrec

theorem source_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (DrawingPlanarSATClauseMetadata.source :
      DrawingPlanarSATClauseMetadata Variable →
        DrawingPlanarSATClauseSource Variable) :=
  Primrec.snd.comp equivData_primrec

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        EmbeddedClause (PlanarSATVariable Variable) ×
          DrawingPlanarSATClauseSource Variable =>
      DrawingPlanarSATClauseMetadata.mk data.1 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end DrawingPlanarSATClauseMetadata

theorem drawingPlanarSATCrossoverFormulaAt_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingPlanarSATCrossoverFormulaAt (Variable := Variable)) := by
  have formula : Primrec fun crossing : CrossingRecord =>
      scopedCrossoverInstance crossing
        (carrierNodeCrossingPorts crossing)
        (crossingMacroOrigin crossing) 1 :=
    scopedCrossoverInstance_primrec id carrierNodeCrossingPorts
      crossingMacroOrigin (fun _ => 1) Primrec.id
      carrierNodeCrossingPorts_primrec crossingMacroOrigin_primrec
      (Primrec.const 1)
  have rename : Primrec₂ fun (_crossing : CrossingRecord)
      (clause : EmbeddedClause
        (Sum CarrierNode (CrossingRecord × CrossoverInternal))) =>
      clause.rename (planarSATCoreVariableMap (Variable := Variable)) := by
    exact EmbeddedClause.rename_primrec
      (fun (_crossing : CrossingRecord) source =>
        planarSATCoreVariableMap source)
      (planarSATCoreVariableMap_primrec.comp Primrec.snd)
  exact (Primrec.list_map formula rename).of_eq fun _ => rfl

theorem drawingPlanarSATCarrierFormulaAt_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingPlanarSATCarrierFormulaAt (Variable := Variable)) := by
  have formula : Primrec fun link : EqualityLink CarrierNode =>
      equalityInstance link.first link.second link.positions :=
    EqualityLink.equalityInstance_primrec
  have rename : Primrec₂ fun (_link : EqualityLink CarrierNode)
      (clause : EmbeddedClause CarrierNode) =>
      (clause.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal))).rename
        (planarSATCoreVariableMap (Variable := Variable)) := by
    change Primrec fun input :
        EqualityLink CarrierNode × EmbeddedClause CarrierNode =>
      (input.2.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal))).rename
        (planarSATCoreVariableMap (Variable := Variable))
    have firstRename : Primrec fun input :
        EqualityLink CarrierNode × EmbeddedClause CarrierNode =>
      input.2.rename fun node =>
        (Sum.inl node :
          Sum CarrierNode
            (CrossingRecord × CrossoverInternal)) :=
      EmbeddedClause.rename_primrec
        (fun (_link : EqualityLink CarrierNode) node =>
          (Sum.inl node :
            Sum CarrierNode
              (CrossingRecord × CrossoverInternal)))
        (Primrec.sumInl.comp Primrec.snd)
    exact EmbeddedClause.rename_primrec
      (fun (_input : EqualityLink CarrierNode) source =>
        planarSATCoreVariableMap source)
      (planarSATCoreVariableMap_primrec.comp Primrec.snd) |>.comp
        (Primrec.pair Primrec.fst firstRename)
  exact (Primrec.list_map formula rename).of_eq fun _ => rfl

theorem drawingPlanarSATBendFormulaAt_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      drawingPlanarSATBendFormulaAt
        (Variable := Variable) input.1 input.2 :=
  drawingPlanarSATCarrierFormulaAt_primrec.comp
    RouteBend.equalityLink_primrec

theorem drawingPlanarSATRoutedVariableFormulaAt_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingPlanarSATRoutedVariableFormulaAt
      (Variable := Variable)) := by
  have formula : Primrec fun link : EqualityLink (PlanarSATNode Variable) =>
      equalityInstance link.first link.second link.positions :=
    EqualityLink.equalityInstance_primrec
  have rename : Primrec₂ fun
      (_link : EqualityLink (PlanarSATNode Variable))
      (clause : EmbeddedClause (PlanarSATNode Variable)) =>
      clause.rename planarSATExternalVariableMap := by
    exact EmbeddedClause.rename_primrec
      (fun (_link : EqualityLink (PlanarSATNode Variable)) source =>
        planarSATExternalVariableMap source)
      (planarSATExternalVariableMap_primrec.comp Primrec.snd)
  exact (Primrec.list_map formula rename).of_eq fun _ => rfl

private def crossoverMetadata
    {Variable : Type*}
    (input : CrossingRecord ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat)) :
    DrawingPlanarSATClauseMetadata Variable :=
  ⟨input.2.1, .crossover input.1 input.2.2⟩

private theorem crossoverMetadata_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (crossoverMetadata (Variable := Variable)) := by
  have sourceData : Primrec fun input : CrossingRecord ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (input.1, input.2.2) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  have source : Primrec fun input : CrossingRecord ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.crossover input.1 input.2.2 :
        DrawingPlanarSATClauseSource Variable) := by
    change Primrec fun input : CrossingRecord ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.equivData
        (Variable := Variable)).symm (Sum.inl (input.1, input.2.2))
    exact DrawingPlanarSATClauseSource.equivData_symm_primrec.comp
      (Primrec.sumInl.comp sourceData)
  exact (DrawingPlanarSATClauseMetadata.mk_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) source)).of_eq
      fun _ => rfl

theorem drawingPlanarSATCrossoverClauseMetadataFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingPlanarSATCrossoverClauseMetadataFor
      (Variable := Variable)) := by
  have tagged : Primrec fun crossing : CrossingRecord =>
      (drawingPlanarSATCrossoverFormulaAt
        (Variable := Variable) crossing).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      drawingPlanarSATCrossoverFormulaAt_primrec
  exact (Primrec.list_map tagged crossoverMetadata_primrec.to₂).of_eq
    fun _ => rfl

theorem drawingPlanarSATCrossoverClauseMetadata_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingPlanarSATCrossoverClauseMetadata
      (Variable := Variable) :
        PeriodicGraph Vertex →
          List (DrawingPlanarSATClauseMetadata Variable)) :=
  Primrec.list_flatMap orientedCrossingHalo_primrec
    (drawingPlanarSATCrossoverClauseMetadataFor_primrec.comp
      Primrec.snd).to₂

private def carrierMetadata
    {Variable : Type*}
    (input : EqualityLink CarrierNode ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat)) :
    DrawingPlanarSATClauseMetadata Variable :=
  ⟨input.2.1, .carrier input.1 input.2.2⟩

private theorem carrierMetadata_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (carrierMetadata (Variable := Variable)) := by
  have sourceData : Primrec fun input : EqualityLink CarrierNode ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (input.1, input.2.2) :=
    Primrec.pair Primrec.fst (Primrec.snd.comp Primrec.snd)
  have source : Primrec fun input : EqualityLink CarrierNode ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.carrier input.1 input.2.2 :
        DrawingPlanarSATClauseSource Variable) := by
    change Primrec fun input : EqualityLink CarrierNode ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.equivData
        (Variable := Variable)).symm
          (Sum.inr (Sum.inl (input.1, input.2.2)))
    have inner : Primrec fun input : EqualityLink CarrierNode ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (Sum.inl (input.1, input.2.2) :
          (EqualityLink CarrierNode × Nat) ⊕
            ((RouteBend × Nat) ⊕
              (ClauseRouteSite ⊕
                DrawingPlanarSATClauseSource.RoutedVariableData
                  Variable))) :=
      Primrec.sumInl.comp sourceData
    exact DrawingPlanarSATClauseSource.equivData_symm_primrec.comp
      (Primrec.sumInr.comp inner)
  exact (DrawingPlanarSATClauseMetadata.mk_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) source)).of_eq
      fun _ => rfl

theorem drawingPlanarSATCarrierClauseMetadataFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingPlanarSATCarrierClauseMetadataFor
      (Variable := Variable)) := by
  have tagged : Primrec fun link : EqualityLink CarrierNode =>
      (drawingPlanarSATCarrierFormulaAt
        (Variable := Variable) link).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      drawingPlanarSATCarrierFormulaAt_primrec
  exact (Primrec.list_map tagged carrierMetadata_primrec.to₂).of_eq
    fun _ => rfl

theorem retainedDrawingPlanarSATCarrierClauseMetadata_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (retainedDrawingPlanarSATCarrierClauseMetadata
      (Variable := Variable) :
        PeriodicGraph Vertex →
          List (DrawingPlanarSATClauseMetadata Variable)) :=
  Primrec.list_flatMap retainedDrawingCompleteCarrierLinks_primrec
    (drawingPlanarSATCarrierClauseMetadataFor_primrec.comp
      Primrec.snd).to₂

private def bendMetadata
    {Variable Vertex : Type*} [DecidableEq Vertex]
    (input : (PeriodicGraph Vertex × RouteBend) ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat)) :
    DrawingPlanarSATClauseMetadata Variable :=
  ⟨input.2.1, .bend input.1.2 input.2.2⟩

private theorem bendMetadata_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (bendMetadata (Variable := Variable) (Vertex := Vertex)) := by
  have sourceData : Primrec fun input :
      (PeriodicGraph Vertex × RouteBend) ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (input.1.2, input.2.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have source : Primrec fun input : (PeriodicGraph Vertex × RouteBend) ×
      (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.bend input.1.2 input.2.2 :
        DrawingPlanarSATClauseSource Variable) := by
    change Primrec fun input :
        (PeriodicGraph Vertex × RouteBend) ×
          (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (DrawingPlanarSATClauseSource.equivData
        (Variable := Variable)).symm
          (Sum.inr (Sum.inr (Sum.inl (input.1.2, input.2.2))))
    have inner : Primrec fun input :
        (PeriodicGraph Vertex × RouteBend) ×
          (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (Sum.inl (input.1.2, input.2.2) :
          (RouteBend × Nat) ⊕
            (ClauseRouteSite ⊕
              DrawingPlanarSATClauseSource.RoutedVariableData Variable)) :=
      Primrec.sumInl.comp sourceData
    have middle : Primrec fun input :
        (PeriodicGraph Vertex × RouteBend) ×
          (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (Sum.inr (Sum.inl (input.1.2, input.2.2)) :
          (EqualityLink CarrierNode × Nat) ⊕
            ((RouteBend × Nat) ⊕
              (ClauseRouteSite ⊕
                DrawingPlanarSATClauseSource.RoutedVariableData
                  Variable))) :=
      Primrec.sumInr.comp inner
    exact DrawingPlanarSATClauseSource.equivData_symm_primrec.comp
      (Primrec.sumInr.comp middle)
  exact (DrawingPlanarSATClauseMetadata.mk_primrec.comp
    (Primrec.pair (Primrec.fst.comp Primrec.snd) source)).of_eq
      fun _ => rfl

theorem drawingPlanarSATBendClauseMetadataFor_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      drawingPlanarSATBendClauseMetadataFor
        (Variable := Variable) input.1 input.2 := by
  have tagged : Primrec fun input : PeriodicGraph Vertex × RouteBend =>
      (drawingPlanarSATBendFormulaAt
        (Variable := Variable) input.1 input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      drawingPlanarSATBendFormulaAt_primrec
  exact (Primrec.list_map tagged bendMetadata_primrec.to₂).of_eq
    fun _ => rfl

theorem drawingPlanarSATBendClauseMetadata_primrec
    {Variable Vertex : Type*}
    [Primcodable Variable] [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec (drawingPlanarSATBendClauseMetadata
      (Variable := Variable) :
        PeriodicGraph Vertex →
          List (DrawingPlanarSATClauseMetadata Variable)) := by
  have bends : Primrec fun graph : PeriodicGraph Vertex =>
      (drawingRouteBends graph).dedup :=
    PeriodicThreeSATThree.dedup_primrec.comp drawingRouteBends_primrec
  exact (Primrec.list_flatMap bends
    (drawingPlanarSATBendClauseMetadataFor_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂).of_eq
        fun _ => rfl

private def routedClauseMetadata
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × ClauseRouteSite) :
    DrawingPlanarSATClauseMetadata Variable :=
  ⟨(routedClauseAt input.1 input.2).rename
      planarSATExternalVariableMap,
    .routedClause input.2⟩

private theorem routedClauseMetadata_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseMetadata (Variable := Variable)) := by
  have routed : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      routedClauseAt input.1 input.2 :=
    routedClauseAt_primrec
  have clause : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (routedClauseAt input.1 input.2).rename
        planarSATExternalVariableMap := by
    have rename : Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          EmbeddedClause (PlanarSATNode Variable) =>
        combined.2.rename planarSATExternalVariableMap :=
      EmbeddedClause.rename_primrec
        (fun (_input : PeriodicCNF Variable × ClauseRouteSite) source =>
          planarSATExternalVariableMap source)
        (planarSATExternalVariableMap_primrec.comp Primrec.snd)
    exact rename.comp (Primrec.pair Primrec.id routed)
  have source : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (DrawingPlanarSATClauseSource.routedClause input.2 :
        DrawingPlanarSATClauseSource Variable) :=
    DrawingPlanarSATClauseSource.routedClause_primrec.comp Primrec.snd
  exact (DrawingPlanarSATClauseMetadata.mk_primrec.comp
    (Primrec.pair clause source)).of_eq fun _ => rfl

theorem drawingPlanarSATRoutedClauseMetadata_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingPlanarSATRoutedClauseMetadata :
      PeriodicCNF Variable →
        List (DrawingPlanarSATClauseMetadata Variable)) :=
  Primrec.list_map drawingClauseRouteSites_primrec
    (routedClauseMetadata_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

private abbrev RoutedVariableBase (Variable : Type*) :=
  ((VariableRouteSite Variable × Nat) × DuplicatorArm) ×
    EqualityLink (PlanarSATNode Variable)

private def routedVariableMetadataFromData
    {Variable : Type*}
    (input : EmbeddedClause (PlanarSATVariable Variable) ×
      DrawingPlanarSATClauseSource.RoutedVariableData Variable) :
    DrawingPlanarSATClauseMetadata Variable :=
  ⟨input.1,
    .routedVariable input.2.1.1.1.1 input.2.1.1.1.2
      input.2.1.1.2 input.2.1.2 input.2.2⟩

private theorem routedVariableMetadataFromData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (routedVariableMetadataFromData
      (Variable := Variable)) := by
  have source : Primrec fun input :
      EmbeddedClause (PlanarSATVariable Variable) ×
        DrawingPlanarSATClauseSource.RoutedVariableData Variable =>
      (DrawingPlanarSATClauseSource.routedVariable
        input.2.1.1.1.1 input.2.1.1.1.2 input.2.1.1.2
          input.2.1.2 input.2.2 :
          DrawingPlanarSATClauseSource Variable) :=
    DrawingPlanarSATClauseSource.routedVariable_primrec.comp Primrec.snd
  exact (DrawingPlanarSATClauseMetadata.mk_primrec.comp
    (Primrec.pair Primrec.fst source)).of_eq
      fun _ => rfl

private theorem drawingPlanarSATRoutedVariableClauseMetadataFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : RoutedVariableBase Variable =>
      drawingPlanarSATRoutedVariableClauseMetadataFor
        input.1.1.1 input.1.1.2 input.1.2 input.2 := by
  have tagged : Primrec fun input : RoutedVariableBase Variable =>
      (drawingPlanarSATRoutedVariableFormulaAt
        (Variable := Variable) input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (drawingPlanarSATRoutedVariableFormulaAt_primrec.comp Primrec.snd)
  have metadataData : Primrec₂ fun
      (input : RoutedVariableBase Variable)
      (taggedClause : EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (taggedClause.1,
        (((((input.1.1.1, input.1.1.2), input.1.2), input.2),
          taggedClause.2) :
            DrawingPlanarSATClauseSource.RoutedVariableData Variable)) := by
    change Primrec fun combined : RoutedVariableBase Variable ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
      (combined.2.1,
        (((((combined.1.1.1.1, combined.1.1.1.2),
          combined.1.1.2), combined.1.2), combined.2.2) :
            DrawingPlanarSATClauseSource.RoutedVariableData Variable))
    have siteIndex : Primrec fun combined : RoutedVariableBase Variable ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (combined.1.1.1.1, combined.1.1.1.2) :=
      Primrec.pair
        (Primrec.fst.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.comp (Primrec.fst.comp
          (Primrec.fst.comp Primrec.fst)))
    have withArm : Primrec fun combined : RoutedVariableBase Variable ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        ((combined.1.1.1.1, combined.1.1.1.2),
          combined.1.1.2) :=
      Primrec.pair siteIndex
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    have withLink : Primrec fun combined : RoutedVariableBase Variable ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (((combined.1.1.1.1, combined.1.1.1.2),
          combined.1.1.2), combined.1.2) :=
      Primrec.pair withArm (Primrec.snd.comp Primrec.fst)
    have sourceData : Primrec fun combined : RoutedVariableBase Variable ×
        (EmbeddedClause (PlanarSATVariable Variable) × Nat) =>
        (((((combined.1.1.1.1, combined.1.1.1.2),
          combined.1.1.2), combined.1.2), combined.2.2) :
            DrawingPlanarSATClauseSource.RoutedVariableData Variable) :=
      Primrec.pair withLink (Primrec.snd.comp Primrec.snd)
    exact Primrec.pair (Primrec.fst.comp Primrec.snd) sourceData
  exact (Primrec.list_map tagged
    (routedVariableMetadataFromData_primrec.comp
      metadataData).to₂).of_eq fun _ => rfl

private def routedVariableBase
    {Variable : Type*}
    (input : (PeriodicCNF Variable × VariableRouteSite Variable) ×
      (EqualityLink (PlanarSATNode Variable) × Nat)) :
    RoutedVariableBase Variable :=
  (((input.1.2, input.2.2), input.2.1.first.duplicatorArm),
    input.2.1)

private theorem routedVariableBase_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (routedVariableBase (Variable := Variable)) := by
  have siteIndex : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (EqualityLink (PlanarSATNode Variable) × Nat) =>
      (input.1.2, input.2.2) :=
    Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  have arm : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (EqualityLink (PlanarSATNode Variable) × Nat) =>
      input.2.1.first.duplicatorArm :=
    PlanarSATNode.duplicatorArm_primrec.comp
      (EqualityLink.first_primrec.comp
        (Primrec.fst.comp Primrec.snd))
  have withArm : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (EqualityLink (PlanarSATNode Variable) × Nat) =>
      ((input.1.2, input.2.2), input.2.1.first.duplicatorArm) :=
    Primrec.pair siteIndex arm
  exact (Primrec.pair withArm
    (Primrec.fst.comp Primrec.snd)).of_eq fun _ => rfl

private theorem routedVariableMetadataAtSite_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : PeriodicCNF Variable ×
        VariableRouteSite Variable =>
      (routedVariableLinksAt input.1 input.2).zipIdx.flatMap
        fun taggedLink =>
          drawingPlanarSATRoutedVariableClauseMetadataFor
            input.2 taggedLink.2
              taggedLink.1.first.duplicatorArm taggedLink.1 := by
  have taggedLinks : Primrec fun input : PeriodicCNF Variable ×
      VariableRouteSite Variable =>
      (routedVariableLinksAt input.1 input.2).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      routedVariableLinksAt_primrec
  have one : Primrec₂ fun
      (input : PeriodicCNF Variable × VariableRouteSite Variable)
      (taggedLink : EqualityLink (PlanarSATNode Variable) × Nat) =>
      drawingPlanarSATRoutedVariableClauseMetadataFor
        input.2 taggedLink.2 taggedLink.1.first.duplicatorArm
          taggedLink.1 := by
    exact drawingPlanarSATRoutedVariableClauseMetadataFor_primrec.comp
      routedVariableBase_primrec |>.to₂
  exact (Primrec.list_flatMap taggedLinks one).of_eq fun _ => rfl

theorem drawingPlanarSATRoutedVariableClauseMetadata_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingPlanarSATRoutedVariableClauseMetadata :
      PeriodicCNF Variable →
        List (DrawingPlanarSATClauseMetadata Variable)) :=
  Primrec.list_flatMap drawingVariableRouteSites_primrec
    (routedVariableMetadataAtSite_primrec.comp
      (Primrec.pair Primrec.fst Primrec.snd)).to₂

theorem retainedDrawingPlanarSATClauseMetadata_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingPlanarSATClauseMetadata :
      PeriodicCNF Variable →
        List (DrawingPlanarSATClauseMetadata Variable)) := by
  have graph : Primrec fun formula : PeriodicCNF Variable =>
      PeriodicCNF.incidenceGraph formula :=
    PeriodicCNF.incidenceGraph_primrec
  have crossover : Primrec fun formula : PeriodicCNF Variable =>
      drawingPlanarSATCrossoverClauseMetadata
        (Variable := Variable) (PeriodicCNF.incidenceGraph formula) :=
    drawingPlanarSATCrossoverClauseMetadata_primrec.comp graph
  have carrier : Primrec fun formula : PeriodicCNF Variable =>
      retainedDrawingPlanarSATCarrierClauseMetadata
        (Variable := Variable) (PeriodicCNF.incidenceGraph formula) :=
    retainedDrawingPlanarSATCarrierClauseMetadata_primrec.comp graph
  have bend : Primrec fun formula : PeriodicCNF Variable =>
      drawingPlanarSATBendClauseMetadata
        (Variable := Variable) (PeriodicCNF.incidenceGraph formula) :=
    drawingPlanarSATBendClauseMetadata_primrec.comp graph
  have crossoverCarrier : Primrec fun formula : PeriodicCNF Variable =>
      drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
        retainedDrawingPlanarSATCarrierClauseMetadata
          (Variable := Variable) (PeriodicCNF.incidenceGraph formula) :=
    Primrec.list_append.comp crossover carrier
  have throughBend : Primrec fun formula : PeriodicCNF Variable =>
      drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
        retainedDrawingPlanarSATCarrierClauseMetadata
            (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
          drawingPlanarSATBendClauseMetadata
            (Variable := Variable) (PeriodicCNF.incidenceGraph formula) :=
    Primrec.list_append.comp crossoverCarrier bend
  have throughClause : Primrec fun formula : PeriodicCNF Variable =>
      drawingPlanarSATCrossoverClauseMetadata
          (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
        retainedDrawingPlanarSATCarrierClauseMetadata
            (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
          drawingPlanarSATBendClauseMetadata
              (Variable := Variable) (PeriodicCNF.incidenceGraph formula) ++
            drawingPlanarSATRoutedClauseMetadata formula :=
    Primrec.list_append.comp throughBend
      drawingPlanarSATRoutedClauseMetadata_primrec
  exact (Primrec.list_append.comp throughClause
    drawingPlanarSATRoutedVariableClauseMetadata_primrec).of_eq
      fun _ => rfl

theorem retainedDrawingPlanarSATClauseMetadata_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingPlanarSATClauseMetadata :
      PeriodicCNF Variable →
        List (DrawingPlanarSATClauseMetadata Variable)) :=
  retainedDrawingPlanarSATClauseMetadata_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
