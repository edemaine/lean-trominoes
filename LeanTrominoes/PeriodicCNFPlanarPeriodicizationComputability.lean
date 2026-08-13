/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVertexGadgetsComputability
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization

/-!
# Computability of retained planar-SAT periodicization

Finite translated planar-SAT variables are normalized to periodic
protovariables and literal offsets.  The retained embedded formula and the
opaque variable wrapper are thereby executable finite transformations.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

theorem CrossingRecord.periodNormalize_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CrossingRecord.periodNormalize :
      PeriodicGraph Vertex → CrossingRecord → CrossingRecord) := by
  change Primrec fun input : PeriodicGraph Vertex × CrossingRecord =>
    input.2.periodNormalize input.1
  have shift : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      crossingPeriodShift input.1 input.2 :=
    crossingPeriodShift_primrec
  have firstTranslate : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      Cell.sub input.2.firstTranslate
        (crossingPeriodShift input.1 input.2) :=
    Computability.cell_sub_primrec.comp
      (CrossingRecord.firstTranslate_primrec.comp Primrec.snd) shift
  have secondTranslate : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      Cell.sub input.2.secondTranslate
        (crossingPeriodShift input.1 input.2) :=
    Computability.cell_sub_primrec.comp
      (CrossingRecord.secondTranslate_primrec.comp Primrec.snd) shift
  have translation : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      (drawing input.1).periodTranslation
        (crossingPeriodShift input.1 input.2) :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      (drawing_primrec.comp Primrec.fst) shift
  have point : Primrec fun input :
      PeriodicGraph Vertex × CrossingRecord =>
      PeriodicGridDrawing.normalizePoint (drawing input.1)
        input.2.point (crossingPeriodShift input.1 input.2) :=
    Computability.cell_sub_primrec.comp
      (CrossingRecord.point_primrec.comp Primrec.snd) translation
  exact (CrossingRecord.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (CrossingRecord.first_primrec.comp Primrec.snd)
        firstTranslate)
      (Primrec.pair
        (Primrec.pair
          (CrossingRecord.second_primrec.comp Primrec.snd)
          secondTranslate)
        point))).of_eq fun _ => rfl

theorem CrossingBoundary.periodNormalize_primrec
    {Vertex : Type*} [Primcodable Vertex] [DecidableEq Vertex] :
    Primrec₂ (CrossingBoundary.periodNormalize :
      PeriodicGraph Vertex → CrossingBoundary → CrossingBoundary) := by
  change Primrec fun input : PeriodicGraph Vertex × CrossingBoundary =>
    input.2.periodNormalize input.1
  have crossing : Primrec fun input :
      PeriodicGraph Vertex × CrossingBoundary =>
      input.2.crossing.periodNormalize input.1 :=
    CrossingRecord.periodNormalize_primrec.comp Primrec.fst
      (CrossingBoundary.crossing_primrec.comp Primrec.snd)
  exact (CrossingBoundary.mk_primrec.comp
    (Primrec.pair crossing
      (CrossingBoundary.side_primrec.comp Primrec.snd))).of_eq
        fun _ => rfl

namespace PeriodicPlanarSATVariable

private abbrev Data (Variable : Type*) :=
  (IndexedGridSegment × SegmentEnd) ⊕
    (CrossingBoundary ⊕
      (Variable ⊕ (CrossingRecord × CrossoverInternal)))

def equivData {Variable : Type*} :
    PeriodicPlanarSATVariable Variable ≃ Data Variable where
  toFun
    | PeriodicPlanarSATVariable.terminal indexed endpoint =>
        .inl (indexed, endpoint)
    | PeriodicPlanarSATVariable.boundary crossingBoundary =>
        .inr (.inl crossingBoundary)
    | PeriodicPlanarSATVariable.atom originalAtom =>
        .inr (.inr (.inl originalAtom))
    | PeriodicPlanarSATVariable.crossoverInternal internal =>
        .inr (.inr (.inr internal))
  invFun
    | .inl data => .terminal data.1 data.2
    | .inr (.inl crossingBoundary) => .boundary crossingBoundary
    | .inr (.inr (.inl originalAtom)) => .atom originalAtom
    | .inr (.inr (.inr internal)) => .crossoverInternal internal
  left_inv inputVariable := by cases inputVariable <;> rfl
  right_inv
    | .inl _ => rfl
    | .inr (.inl _) => rfl
    | .inr (.inr (.inl _)) => rfl
    | .inr (.inr (.inr _)) => rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PeriodicPlanarSATVariable Variable) :=
  Primcodable.ofEquiv
    ((IndexedGridSegment × SegmentEnd) ⊕
      (CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal)))) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem terminal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : IndexedGridSegment × SegmentEnd =>
      (PeriodicPlanarSATVariable.terminal data.1 data.2 :
        PeriodicPlanarSATVariable Variable) := by
  change Primrec fun data : IndexedGridSegment × SegmentEnd =>
    (equivData (Variable := Variable)).symm (Sum.inl data)
  exact equivData_symm_primrec.comp
    (Primrec.sumInl : Primrec fun data :
      IndexedGridSegment × SegmentEnd =>
        (Sum.inl data : Data Variable))

theorem boundary_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun boundary : CrossingBoundary =>
      (PeriodicPlanarSATVariable.boundary boundary :
        PeriodicPlanarSATVariable Variable) := by
  change Primrec fun boundary : CrossingBoundary =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inl boundary))
  have inner : Primrec fun boundary : CrossingBoundary =>
      (Sum.inl boundary : CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal))) :=
    Primrec.sumInl
  exact equivData_symm_primrec.comp
    (Primrec.sumInr.comp inner)

theorem atom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun atom : Variable =>
      (PeriodicPlanarSATVariable.atom atom :
        PeriodicPlanarSATVariable Variable) := by
  change Primrec fun atom : Variable =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inr (Sum.inl atom)))
  have inner : Primrec fun atom : Variable =>
      (Sum.inl atom : Variable ⊕
        (CrossingRecord × CrossoverInternal)) :=
    Primrec.sumInl
  have middle : Primrec fun atom : Variable =>
      (Sum.inr (Sum.inl atom) : CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal))) :=
    Primrec.sumInr.comp inner
  exact equivData_symm_primrec.comp
    (Primrec.sumInr.comp middle)

theorem crossoverInternal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun internal : CrossingRecord × CrossoverInternal =>
      (PeriodicPlanarSATVariable.crossoverInternal internal :
        PeriodicPlanarSATVariable Variable) := by
  change Primrec fun internal : CrossingRecord × CrossoverInternal =>
    (equivData (Variable := Variable)).symm
      (Sum.inr (Sum.inr (Sum.inr internal)))
  have inner : Primrec fun internal :
      CrossingRecord × CrossoverInternal =>
      (Sum.inr internal : Variable ⊕
        (CrossingRecord × CrossoverInternal)) :=
    Primrec.sumInr
  have middle : Primrec fun internal :
      CrossingRecord × CrossoverInternal =>
      (Sum.inr (Sum.inr internal) : CrossingBoundary ⊕
        (Variable ⊕ (CrossingRecord × CrossoverInternal))) :=
    Primrec.sumInr.comp inner
  exact equivData_symm_primrec.comp
    (Primrec.sumInr.comp middle)

end PeriodicPlanarSATVariable

private def normalizeTerminal
    {Variable : Type*}
    (input : PeriodicCNF Variable × SegmentTerminal) :
    PeriodicPlanarSATVariable Variable × Cell :=
  (.terminal input.2.indexed input.2.endpoint, input.2.translate)

private theorem normalizeTerminal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (normalizeTerminal (Variable := Variable)) := by
  have atom : Primrec fun input :
      PeriodicCNF Variable × SegmentTerminal =>
      (PeriodicPlanarSATVariable.terminal input.2.indexed
        input.2.endpoint : PeriodicPlanarSATVariable Variable) :=
    PeriodicPlanarSATVariable.terminal_primrec.comp
      (Primrec.pair
        (SegmentTerminal.indexed_primrec.comp Primrec.snd)
        (SegmentTerminal.endpoint_primrec.comp Primrec.snd))
  exact (Primrec.pair atom
    (SegmentTerminal.translate_primrec.comp Primrec.snd)).of_eq
      fun _ => rfl

private def normalizeBoundary
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × CrossingBoundary) :
    PeriodicPlanarSATVariable Variable × Cell :=
  let graph := PeriodicCNF.incidenceGraph input.1
  (.boundary (input.2.periodNormalize graph),
    crossingPeriodShift graph input.2.crossing)

private theorem normalizeBoundary_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (normalizeBoundary (Variable := Variable)) := by
  have graph : Primrec fun input :
      PeriodicCNF Variable × CrossingBoundary =>
      PeriodicCNF.incidenceGraph input.1 :=
    PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst
  have normalized : Primrec fun input :
      PeriodicCNF Variable × CrossingBoundary =>
      input.2.periodNormalize (PeriodicCNF.incidenceGraph input.1) :=
    CrossingBoundary.periodNormalize_primrec.comp graph Primrec.snd
  have atom : Primrec fun input :
      PeriodicCNF Variable × CrossingBoundary =>
      (PeriodicPlanarSATVariable.boundary
        (input.2.periodNormalize
          (PeriodicCNF.incidenceGraph input.1)) :
            PeriodicPlanarSATVariable Variable) :=
    PeriodicPlanarSATVariable.boundary_primrec.comp normalized
  have shift : Primrec fun input :
      PeriodicCNF Variable × CrossingBoundary =>
      crossingPeriodShift (PeriodicCNF.incidenceGraph input.1)
        input.2.crossing :=
    crossingPeriodShift_primrec.comp graph
      (CrossingBoundary.crossing_primrec.comp Primrec.snd)
  exact (Primrec.pair atom shift).of_eq fun _ => rfl

private def normalizeAtom
    {Variable : Type*}
    (input : PeriodicCNF Variable × (Variable × Cell)) :
    PeriodicPlanarSATVariable Variable × Cell :=
  (.atom input.2.1, input.2.2)

private theorem normalizeAtom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (normalizeAtom (Variable := Variable)) := by
  exact (Primrec.pair
    (PeriodicPlanarSATVariable.atom_primrec.comp
      (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).of_eq fun _ => rfl

private def normalizeCarrier
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × CarrierNode) :
    PeriodicPlanarSATVariable Variable × Cell :=
  match input.2 with
  | .boundary boundary => normalizeBoundary (input.1, boundary)
  | .terminal terminal => normalizeTerminal (input.1, terminal)

private theorem normalizeCarrier_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (normalizeCarrier (Variable := Variable)) := by
  have data : Primrec fun input : PeriodicCNF Variable × CarrierNode =>
      CarrierNode.equivData input.2 :=
    CarrierNode.equivData_primrec.comp Primrec.snd
  have boundary : Primrec₂ fun
      (input : PeriodicCNF Variable × CarrierNode)
      (boundary : CrossingBoundary) =>
      normalizeBoundary (input.1, boundary) := by
    exact normalizeBoundary_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have terminal : Primrec₂ fun
      (input : PeriodicCNF Variable × CarrierNode)
      (terminal : SegmentTerminal) =>
      normalizeTerminal (input.1, terminal) := by
    exact normalizeTerminal_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn data boundary terminal).of_eq fun input => by
    rcases input with ⟨formula, node⟩
    cases node <;> rfl

private def normalizeExternal
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × PlanarSATNode Variable) :
    PeriodicPlanarSATVariable Variable × Cell :=
  match input.2 with
  | .carrier node => normalizeCarrier (input.1, node)
  | .atom occurrence => normalizeAtom (input.1, occurrence)

private theorem normalizeExternal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (normalizeExternal (Variable := Variable)) := by
  have data : Primrec fun input :
      PeriodicCNF Variable × PlanarSATNode Variable =>
      PlanarSATNode.equivData input.2 :=
    PlanarSATNode.equivData_primrec.comp Primrec.snd
  have carrier : Primrec₂ fun
      (input : PeriodicCNF Variable × PlanarSATNode Variable)
      (node : CarrierNode) => normalizeCarrier (input.1, node) := by
    exact normalizeCarrier_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have atom : Primrec₂ fun
      (input : PeriodicCNF Variable × PlanarSATNode Variable)
      (occurrence : Variable × Cell) =>
      normalizeAtom (input.1, occurrence) := by
    exact normalizeAtom_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn data carrier atom).of_eq fun input => by
    rcases input with ⟨formula, node⟩
    cases node <;> rfl

private def normalizeInternal
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal)) :
    PeriodicPlanarSATVariable Variable × Cell :=
  let graph := PeriodicCNF.incidenceGraph input.1
  (.crossoverInternal
      (input.2.1.periodNormalize graph, input.2.2),
    crossingPeriodShift graph input.2.1)

private theorem normalizeInternal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (normalizeInternal (Variable := Variable)) := by
  have graph : Primrec fun input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal) =>
      PeriodicCNF.incidenceGraph input.1 :=
    PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst
  have crossing : Primrec fun input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal) =>
      input.2.1.periodNormalize (PeriodicCNF.incidenceGraph input.1) :=
    CrossingRecord.periodNormalize_primrec.comp graph
      (Primrec.fst.comp Primrec.snd)
  have internal : Primrec fun input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal) =>
      (input.2.1.periodNormalize
        (PeriodicCNF.incidenceGraph input.1), input.2.2) :=
    Primrec.pair crossing (Primrec.snd.comp Primrec.snd)
  have atom : Primrec fun input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal) =>
      (PeriodicPlanarSATVariable.crossoverInternal
        (input.2.1.periodNormalize
          (PeriodicCNF.incidenceGraph input.1), input.2.2) :
            PeriodicPlanarSATVariable Variable) :=
    PeriodicPlanarSATVariable.crossoverInternal_primrec.comp internal
  have shift : Primrec fun input : PeriodicCNF Variable ×
      (CrossingRecord × CrossoverInternal) =>
      crossingPeriodShift (PeriodicCNF.incidenceGraph input.1)
        input.2.1 :=
    crossingPeriodShift_primrec.comp graph
      (Primrec.fst.comp Primrec.snd)
  exact (Primrec.pair atom shift).of_eq fun _ => rfl

theorem normalizePlanarSATVariable_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (normalizePlanarSATVariable :
      PeriodicCNF Variable → PlanarSATVariable Variable →
        PeriodicPlanarSATVariable Variable × Cell) := by
  change Primrec fun input :
      PeriodicCNF Variable × PlanarSATVariable Variable =>
    normalizePlanarSATVariable input.1 input.2
  have external : Primrec₂ fun
      (input : PeriodicCNF Variable × PlanarSATVariable Variable)
      (node : PlanarSATNode Variable) =>
      normalizeExternal (input.1, node) := by
    exact normalizeExternal_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  have internal : Primrec₂ fun
      (input : PeriodicCNF Variable × PlanarSATVariable Variable)
      (value : CrossingRecord × CrossoverInternal) =>
      normalizeInternal (input.1, value) := by
    exact normalizeInternal_primrec.comp
      (Primrec.pair
        (Primrec.fst.comp₂ Primrec₂.left)
        Primrec₂.right)
  exact (Primrec.sumCasesOn Primrec.snd external internal).of_eq
    fun input => by
      rcases input with ⟨formula, inputVariable⟩
      rcases inputVariable with node | internal
      · rcases node with carrier | atom
        · cases carrier <;> rfl
        · rfl
      · rfl

theorem periodicizePlanarSATLiteral_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (periodicizePlanarSATLiteral :
      PeriodicCNF Variable → PlanarSATVariable Variable × Bool →
        PeriodicLiteral (PeriodicPlanarSATVariable Variable)) := by
  change Primrec fun input : PeriodicCNF Variable ×
      (PlanarSATVariable Variable × Bool) =>
    periodicizePlanarSATLiteral input.1 input.2
  have normalized : Primrec fun input : PeriodicCNF Variable ×
      (PlanarSATVariable Variable × Bool) =>
      normalizePlanarSATVariable input.1 input.2.1 :=
    normalizePlanarSATVariable_primrec.comp Primrec.fst
      (Primrec.fst.comp Primrec.snd)
  exact (PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair (Primrec.fst.comp normalized)
      (Primrec.pair (Primrec.snd.comp normalized)
        (Primrec.snd.comp Primrec.snd)))).of_eq fun _ => rfl

theorem periodicizePlanarSATClause_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (periodicizePlanarSATClause :
      PeriodicCNF Variable →
        EmbeddedClause (PlanarSATVariable Variable) →
          PeriodicClause (PeriodicPlanarSATVariable Variable)) := by
  change Primrec fun input : PeriodicCNF Variable ×
      EmbeddedClause (PlanarSATVariable Variable) =>
    periodicizePlanarSATClause input.1 input.2
  have literals : Primrec fun input : PeriodicCNF Variable ×
      EmbeddedClause (PlanarSATVariable Variable) =>
      input.2.literals :=
    EmbeddedClause.literals_primrec.comp Primrec.snd
  have one : Primrec₂ fun
      (input : PeriodicCNF Variable ×
        EmbeddedClause (PlanarSATVariable Variable))
      (literal : PlanarSATVariable Variable × Bool) =>
      periodicizePlanarSATLiteral input.1 literal := by
    exact periodicizePlanarSATLiteral_primrec.comp
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact (Primrec.list_map literals one).of_eq fun _ => rfl

theorem retainedDrawingPeriodicPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PeriodicCNF (PeriodicPlanarSATVariable Variable)) := by
  have clauses : Primrec fun formula : PeriodicCNF Variable =>
      (retainedDrawingPlanarSATFormula formula).map
        (periodicizePlanarSATClause formula) :=
    Primrec.list_map retainedDrawingPlanarSATFormula_primrec
      periodicizePlanarSATClause_primrec
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

theorem retainedDrawingPeriodicPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingPeriodicPlanarSATFormula :
      PeriodicCNF Variable →
        PeriodicCNF (PeriodicPlanarSATVariable Variable)) :=
  retainedDrawingPeriodicPlanarSATFormula_primrec.to_comp

namespace WrappedPeriodicVariable

noncomputable instance {Original : Type*} [Primcodable Original] :
    Primcodable (WrappedPeriodicVariable Original) :=
  Primcodable.ofEquiv Original
    { toFun := WrappedPeriodicVariable.original
      invFun := WrappedPeriodicVariable.mk
      left_inv := fun value => by cases value; rfl
      right_inv := fun _ => rfl }

theorem mk_primrec
    {Original : Type*} [Primcodable Original] :
    Primrec (WrappedPeriodicVariable.mk :
      Original → WrappedPeriodicVariable Original) :=
  Primrec.of_equiv_symm

theorem original_primrec
    {Original : Type*} [Primcodable Original] :
    Primrec (WrappedPeriodicVariable.original :
      WrappedPeriodicVariable Original → Original) :=
  Primrec.of_equiv

end WrappedPeriodicVariable

theorem wrapPeriodicPlanarSATLiteral_primrec
    {Original : Type*} [Primcodable Original] :
    Primrec (wrapPeriodicPlanarSATLiteral :
      PeriodicLiteral Original →
        PeriodicLiteral (WrappedPeriodicVariable Original)) := by
  exact (PeriodicLiteral.equivData_symm_primrec.comp
    (Primrec.pair
      (WrappedPeriodicVariable.mk_primrec.comp
        PeriodicThreeCNF.literal_atom_primrec)
      (Primrec.pair PeriodicThreeCNF.literal_offset_primrec
        PeriodicThreeCNF.literal_value_primrec))).of_eq fun _ => rfl

theorem wrapPeriodicPlanarSATClause_primrec
    {Original : Type*} [Primcodable Original] :
    Primrec (wrapPeriodicPlanarSATClause :
      PeriodicClause Original →
        PeriodicClause (WrappedPeriodicVariable Original)) := by
  exact (Primrec.list_map Primrec.id
    (wrapPeriodicPlanarSATLiteral_primrec.comp Primrec.snd).to₂).of_eq
      fun _ => rfl

theorem wrapPeriodicPlanarSATFormula_primrec
    {Original : Type*} [Primcodable Original] :
    Primrec (wrapPeriodicPlanarSATFormula :
      PeriodicCNF Original →
        PeriodicCNF (WrappedPeriodicVariable Original)) := by
  have clauses : Primrec fun source : PeriodicCNF Original =>
      source.clauses.map wrapPeriodicPlanarSATClause :=
    Primrec.list_map PeriodicCNF.equivData_primrec
      (wrapPeriodicPlanarSATClause_primrec.comp Primrec.snd).to₂
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

end PeriodicOrthocrossing
end LeanTrominoes
