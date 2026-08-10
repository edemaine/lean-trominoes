import LeanTrominoes.PeriodicCNFPlanarIncidenceComputability
import LeanTrominoes.PeriodicCNFPlanarVertexGadgets
import LeanTrominoes.PeriodicOrthocrossingCrossoverComputability
import LeanTrominoes.PrimrecListSort

/-!
# Computability of routed planar-SAT vertex gadgets

The neighboring clause and variable sites, their ordered routed incidences,
and the positioned clause and duplicator families are primitive recursive.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

namespace PlanarSATNode

def equivData {Variable : Type*} : PlanarSATNode Variable ≃
    CarrierNode ⊕ (Variable × Cell) where
  toFun
    | .carrier node => .inl node
    | .atom occurrence => .inr occurrence
  invFun
    | .inl node => .carrier node
    | .inr occurrence => .atom occurrence
  left_inv node := by cases node <;> rfl
  right_inv data := by cases data <;> rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (PlanarSATNode Variable) :=
  Primcodable.ofEquiv
    (CarrierNode ⊕ (Variable × Cell)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem carrier_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PlanarSATNode.carrier :
      CarrierNode → PlanarSATNode Variable) :=
  equivData_symm_primrec.comp Primrec.sumInl

theorem atom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PlanarSATNode.atom :
      (Variable × Cell) → PlanarSATNode Variable) :=
  equivData_symm_primrec.comp Primrec.sumInr

end PlanarSATNode

theorem drawingClauseRouteSites_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingClauseRouteSites :
      PeriodicCNF Variable → List ClauseRouteSite) := by
  have taggedClauses : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have one : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      neighborTranslations.map fun translate =>
        (taggedClause.2, translate) := by
    change Primrec fun input :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
      neighborTranslations.map fun translate =>
        (input.2.2, translate)
    have site : Primrec₂ fun
        (input : PeriodicCNF Variable ×
          (PeriodicClause Variable × Nat))
        (translate : Cell) => (input.2.2, translate) := by
      exact (Primrec.pair
        ((Primrec.snd.comp Primrec.snd).comp₂ Primrec₂.left)
        Primrec₂.right).of_eq fun _ => rfl
    exact Primrec.list_map
      (Primrec.const neighborTranslations) site
  exact (Primrec.list_flatMap taggedClauses one).of_eq fun _ => rfl

theorem drawingVariableRouteSites_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingVariableRouteSites :
      PeriodicCNF Variable → List (VariableRouteSite Variable)) := by
  have occurrences : Primrec fun formula : PeriodicCNF Variable =>
      drawingCNFRouteOccurrences formula :=
    drawingCNFRouteOccurrences_primrec
  have sites : Primrec fun formula : PeriodicCNF Variable =>
      (drawingCNFRouteOccurrences formula).map
        CNFRouteOccurrence.variableOccurrence :=
    Primrec.list_map occurrences
      (CNFRouteOccurrence.variableOccurrence_primrec.comp
        Primrec.snd).to₂
  exact PeriodicThreeSATThree.dedup_primrec.comp sites

theorem clauseRouteOccurrencesAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (clauseRouteOccurrencesAt :
      PeriodicCNF Variable → ClauseRouteSite →
        List (CNFRouteOccurrence Variable)) := by
  change Primrec fun input : PeriodicCNF Variable × ClauseRouteSite =>
    clauseRouteOccurrencesAt input.1 input.2
  have tagged : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (PeriodicCNF.incidencesWithMetadata input.1).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicCNF.incidencesWithMetadata_primrec.comp Primrec.fst)
  have sameClause : PrimrecRel fun
      (taggedIncidence : CNFIncidence Variable × Nat)
      (site : ClauseRouteSite) =>
      taggedIncidence.1.clauseIndex = site.1 := by
    change PrimrecPred fun input :
        (CNFIncidence Variable × Nat) × ClauseRouteSite =>
      input.1.1.clauseIndex = input.2.1
    exact Primrec.eq.comp
      (CNFIncidence.clauseIndex_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have filtered : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (PeriodicCNF.incidencesWithMetadata input.1).zipIdx.filter
        fun taggedIncidence =>
          taggedIncidence.1.clauseIndex = input.2.1 :=
    sameClause.listFilter.comp tagged Primrec.snd
  have occurrence : Primrec₂ fun
      (input : PeriodicCNF Variable × ClauseRouteSite)
      (taggedIncidence : CNFIncidence Variable × Nat) =>
      CNFRouteOccurrence.mk taggedIncidence.1
        taggedIncidence.2 input.2.2 := by
    change Primrec fun combined :
        (PeriodicCNF Variable × ClauseRouteSite) ×
          (CNFIncidence Variable × Nat) =>
      CNFRouteOccurrence.mk combined.2.1 combined.2.2
        combined.1.2.2
    exact CNFRouteOccurrence.mk_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  exact (Primrec.list_map filtered occurrence).of_eq fun _ => rfl

private def variableRouteOccurrencesAtUnsorted
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × VariableRouteSite Variable) :
    List (CNFRouteOccurrence Variable) :=
  (drawingCNFRouteOccurrences input.1).filter fun occurrence =>
    occurrence.variableOccurrence = input.2

private theorem variableRouteOccurrencesAtUnsorted_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (variableRouteOccurrencesAtUnsorted
      (Variable := Variable)) := by
  have sameSite : PrimrecRel fun
      (occurrence : CNFRouteOccurrence Variable)
      (site : VariableRouteSite Variable) =>
      occurrence.variableOccurrence = site := by
    change PrimrecPred fun input :
        CNFRouteOccurrence Variable × VariableRouteSite Variable =>
      input.1.variableOccurrence = input.2
    exact Primrec.eq.comp
      (CNFRouteOccurrence.variableOccurrence_primrec.comp Primrec.fst)
      Primrec.snd
  exact (sameSite.listFilter.comp
    (drawingCNFRouteOccurrences_primrec.comp Primrec.fst)
    Primrec.snd).of_eq fun _ => rfl

theorem variableRouteOccurrencesAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (variableRouteOccurrencesAt :
      PeriodicCNF Variable → VariableRouteSite Variable →
        List (CNFRouteOccurrence Variable)) := by
  change Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
    variableRouteOccurrencesAt input.1 input.2
  let lessEq :
      (PeriodicCNF Variable × VariableRouteSite Variable) →
        CNFRouteOccurrence Variable →
          CNFRouteOccurrence Variable → Bool :=
    fun _ first second => decide (first.edgeIndex ≤ second.edgeIndex)
  have lessEqPrimrec : Primrec fun input :
      ((PeriodicCNF Variable × VariableRouteSite Variable) ×
        CNFRouteOccurrence Variable) × CNFRouteOccurrence Variable =>
      lessEq input.1.1 input.1.2 input.2 := by
    exact (Primrec.nat_le.comp
      (CNFRouteOccurrence.edgeIndex_primrec.comp
        (Primrec.snd.comp Primrec.fst))
      (CNFRouteOccurrence.edgeIndex_primrec.comp Primrec.snd)).decide
  have sorted := Computability.boolInsertionSort_primrec
    (variableRouteOccurrencesAtUnsorted (Variable := Variable))
    lessEq variableRouteOccurrencesAtUnsorted_primrec lessEqPrimrec
  exact sorted.of_eq fun input => by
    rw [Computability.boolInsertionSort_eq_insertionSort
      (lessEq input)
      (fun first second : CNFRouteOccurrence Variable =>
        first.edgeIndex ≤ second.edgeIndex)
      (fun _ _ => by simp [lessEq])]
    rfl

theorem liftedIncidenceVertexPosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      liftedIncidenceVertexPosition input.1.1 input.1.2 input.2 := by
  have graph : Primrec fun input :
      (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      PeriodicCNF.incidenceGraph input.1.1 :=
    PeriodicCNF.incidenceGraph_primrec.comp
      (Primrec.fst.comp Primrec.fst)
  have drawingValue : Primrec fun input :
      (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      drawing (PeriodicCNF.incidenceGraph input.1.1) :=
    drawing_primrec.comp graph
  have vertexIndex : Primrec fun input :
      (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      (PeriodicCNF.incidenceGraph input.1.1).vertices.idxOf input.1.2 :=
    Primrec.list_idxOf.comp
      (Primrec.snd.comp Primrec.fst)
      (PeriodicGraph.vertices_primrec.comp graph)
  have stored : Primrec fun input :
      (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      PeriodicGridDrawing.vertexPosition
        (PeriodicCNF.incidenceGraph input.1.1)
        (drawing (PeriodicCNF.incidenceGraph input.1.1)) input.1.2 :=
    ((Primrec.list_getD ((0, 0) : Cell)).comp
      (PeriodicGridDrawing.vertexPositions_primrec.comp drawingValue)
      vertexIndex).of_eq fun _ => rfl
  have translated : Primrec fun input :
      (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      (drawing (PeriodicCNF.incidenceGraph input.1.1)).periodTranslation
        input.2 :=
    PeriodicGridDrawing.periodTranslation_primrec.comp
      drawingValue Primrec.snd
  exact (Computability.cell_add_primrec.comp stored translated).of_eq
    fun _ => rfl

theorem liftedIncidenceVertexMacroOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × CNFVertex Variable) × Cell =>
      liftedIncidenceVertexMacroOrigin input.1.1 input.1.2 input.2 :=
  (Computability.cell_scale_primrec.comp
    (Primrec.const planarMacroScale)
    liftedIncidenceVertexPosition_primrec).of_eq fun _ => rfl

private def routedClausePosition
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × ClauseRouteSite) : Cell :=
  Cell.add
    (liftedIncidenceVertexMacroOrigin input.1
      (.clause input.2.1) input.2.2) (10, 10)

private def routedClauseOriginInput
    {Variable : Type*}
    (input : PeriodicCNF Variable × ClauseRouteSite) :
    (PeriodicCNF Variable × CNFVertex Variable) × Cell :=
  ((input.1, .clause input.2.1), input.2.2)

private theorem routedClauseOriginInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (routedClauseOriginInput (Variable := Variable)) := by
  have clauseVertex : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      (CNFVertex.clause input.2.1 : CNFVertex Variable) :=
    CNFVertex.clause_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (Primrec.pair
    (Primrec.pair Primrec.fst clauseVertex)
    (Primrec.snd.comp Primrec.snd)).of_eq fun _ => rfl

private def routedClauseOrigin
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × ClauseRouteSite) : Cell :=
  liftedIncidenceVertexMacroOrigin input.1
    (.clause input.2.1) input.2.2

private theorem routedClauseOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseOrigin (Variable := Variable)) := by
  exact (liftedIncidenceVertexMacroOrigin_primrec.comp
    routedClauseOriginInput_primrec).of_eq fun _ => rfl

private theorem routedClausePosition_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClausePosition (Variable := Variable)) := by
  exact (Computability.cell_add_primrec.comp routedClauseOrigin_primrec
    (Primrec.const ((10, 10) : Cell))).of_eq fun _ => rfl

private def routedClauseLiteral
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable × ClauseRouteSite) ×
      CNFRouteOccurrence Variable) : PlanarSATNode Variable × Bool :=
  ((PlanarSATNode.carrier
    (.terminal (input.2.sourceTerminal input.1.1)) :
      PlanarSATNode Variable),
    input.2.incidence.literal.value)

private theorem routedClauseLiteral_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseLiteral (Variable := Variable)) := by
  have terminal : Primrec fun combined :
      (PeriodicCNF Variable × ClauseRouteSite) ×
        CNFRouteOccurrence Variable =>
      combined.2.sourceTerminal combined.1.1 :=
    CNFRouteOccurrence.sourceTerminal_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  have node : Primrec fun combined :
      (PeriodicCNF Variable × ClauseRouteSite) ×
        CNFRouteOccurrence Variable =>
      (PlanarSATNode.carrier (.terminal
        (combined.2.sourceTerminal combined.1.1)) :
          PlanarSATNode Variable) :=
    PlanarSATNode.carrier_primrec.comp
      (CarrierNode.terminal_primrec.comp terminal)
  have value : Primrec fun combined :
      (PeriodicCNF Variable × ClauseRouteSite) ×
        CNFRouteOccurrence Variable =>
      combined.2.incidence.literal.value :=
    PeriodicThreeCNF.literal_value_primrec.comp
      (CNFIncidence.literal_primrec.comp
        (CNFRouteOccurrence.incidence_primrec.comp Primrec.snd))
  exact (Primrec.pair node value).of_eq fun _ => rfl

private def routedClauseLiterals
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × ClauseRouteSite) :
    List (PlanarSATNode Variable × Bool) :=
  (clauseRouteOccurrencesAt input.1 input.2).map fun occurrence =>
    routedClauseLiteral (input, occurrence)

private theorem routedClauseLiterals_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedClauseLiterals (Variable := Variable)) := by
  have occurrences : Primrec fun input :
      PeriodicCNF Variable × ClauseRouteSite =>
      clauseRouteOccurrencesAt input.1 input.2 :=
    clauseRouteOccurrencesAt_primrec
  exact (Primrec.list_map occurrences
    routedClauseLiteral_primrec.to₂).of_eq fun _ => rfl

theorem routedClauseAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (routedClauseAt :
      PeriodicCNF Variable → ClauseRouteSite →
        EmbeddedClause (PlanarSATNode Variable)) := by
  exact (EmbeddedClause.mk_primrec.comp
    (Primrec.pair routedClausePosition_primrec
      routedClauseLiterals_primrec)).of_eq fun _ => rfl

theorem drawingRoutedClauseFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingRoutedClauseFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATNode Variable))) :=
  (Primrec.list_map drawingClauseRouteSites_primrec
    routedClauseAt_primrec).of_eq fun _ => rfl

private def routedVariableNode
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable × VariableRouteSite Variable) ×
      CNFRouteOccurrence Variable) : PlanarSATNode Variable :=
  .carrier (.terminal (input.2.targetTerminal input.1.1))

private theorem routedVariableNode_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableNode (Variable := Variable)) := by
  have terminal : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        CNFRouteOccurrence Variable =>
      input.2.targetTerminal input.1.1 :=
    CNFRouteOccurrence.targetTerminal_primrec.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (PlanarSATNode.carrier_primrec.comp
    (CarrierNode.terminal_primrec.comp terminal)).of_eq fun _ => rfl

theorem routedVariableNodes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (routedVariableNodes :
      PeriodicCNF Variable → VariableRouteSite Variable →
        List (PlanarSATNode Variable)) := by
  change Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
    routedVariableNodes input.1 input.2
  have occurrences : Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
      variableRouteOccurrencesAt input.1 input.2 :=
    variableRouteOccurrencesAt_primrec
  have nodes : Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
      (variableRouteOccurrencesAt input.1 input.2).map fun occurrence =>
        routedVariableNode (input, occurrence) :=
    Primrec.list_map occurrences routedVariableNode_primrec.to₂
  exact (PeriodicThreeSATThree.dedup_primrec.comp nodes).of_eq
    fun _ => rfl

private def routedVariableOriginInput
    {Variable : Type*}
    (input : PeriodicCNF Variable × VariableRouteSite Variable) :
    (PeriodicCNF Variable × CNFVertex Variable) × Cell :=
  ((input.1, .variable input.2.1), input.2.2)

private theorem routedVariableOriginInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (routedVariableOriginInput (Variable := Variable)) := by
  have vertex : Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
      (CNFVertex.variable input.2.1 : CNFVertex Variable) :=
    CNFVertex.variable_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (Primrec.pair
    (Primrec.pair Primrec.fst vertex)
    (Primrec.snd.comp Primrec.snd)).of_eq fun _ => rfl

theorem routedVariableOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (routedVariableOrigin :
      PeriodicCNF Variable → VariableRouteSite Variable → Cell) := by
  exact (liftedIncidenceVertexMacroOrigin_primrec.comp
    routedVariableOriginInput_primrec).of_eq fun _ => rfl

namespace DuplicatorArm

def equivFin : DuplicatorArm ≃ Fin 3 where
  toFun
    | .left => 0
    | .middle => 1
    | .right => 2
  invFun index :=
    match index.1 with
    | 0 => .left
    | 1 => .middle
    | _ => .right
  left_inv arm := by cases arm <;> rfl
  right_inv index := by
    rcases index with ⟨index, indexLt⟩
    apply Fin.ext
    interval_cases index <;> rfl

noncomputable instance : Primcodable DuplicatorArm :=
  Primcodable.ofEquiv (Fin 3) equivFin

theorem equivFin_primrec : Primrec equivFin :=
  Primrec.of_equiv

theorem equivFin_symm_primrec : Primrec equivFin.symm :=
  Primrec.of_equiv_symm

end DuplicatorArm

theorem SegmentTerminal.duplicatorArm_primrec :
    Primrec SegmentTerminal.duplicatorArm := by
  have localPosition : Primrec fun terminal : SegmentTerminal =>
      segmentTerminalLocalPosition terminal.indexed.segment
        terminal.endpoint :=
    segmentTerminalLocalPosition_primrec.comp
      (IndexedGridSegment.segment_primrec.comp
        SegmentTerminal.indexed_primrec)
      SegmentTerminal.endpoint_primrec
  have isLeft : PrimrecPred fun terminal : SegmentTerminal =>
      segmentTerminalLocalPosition terminal.indexed.segment
        terminal.endpoint = DuplicatorArm.left.portPosition :=
    Primrec.eq.comp localPosition
      (Primrec.const DuplicatorArm.left.portPosition)
  have isMiddle : PrimrecPred fun terminal : SegmentTerminal =>
      segmentTerminalLocalPosition terminal.indexed.segment
        terminal.endpoint = DuplicatorArm.middle.portPosition :=
    Primrec.eq.comp localPosition
      (Primrec.const DuplicatorArm.middle.portPosition)
  exact (Primrec.ite isLeft
    (Primrec.const DuplicatorArm.left)
    (Primrec.ite isMiddle
      (Primrec.const DuplicatorArm.middle)
      (Primrec.const DuplicatorArm.right))).of_eq fun terminal => by
        simp [SegmentTerminal.duplicatorArm]

theorem PlanarSATNode.duplicatorArm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (PlanarSATNode.duplicatorArm :
      PlanarSATNode Variable → DuplicatorArm) := by
  have carrier : Primrec fun node : CarrierNode =>
      match node with
      | .terminal terminal => terminal.duplicatorArm
      | .boundary _ => .right := by
    exact (Primrec.sumCasesOn CarrierNode.equivData_primrec
      ((Primrec.const DuplicatorArm.right).comp₂ Primrec₂.right)
      (SegmentTerminal.duplicatorArm_primrec.comp₂
        Primrec₂.right)).of_eq fun node => by
          cases node <;> rfl
  exact (Primrec.sumCasesOn PlanarSATNode.equivData_primrec
    (carrier.comp₂ Primrec₂.right)
    ((Primrec.const DuplicatorArm.right).comp₂
      Primrec₂.right)).of_eq fun node => by
        cases node with
        | carrier node => cases node <;> rfl
        | atom _ => rfl

theorem duplicatorArmEqualityPositions_primrec :
    Primrec duplicatorArmEqualityPositions := by
  have isLeft : PrimrecPred fun arm : DuplicatorArm =>
      arm = .left :=
    Primrec.eq.comp Primrec.id
      (Primrec.const DuplicatorArm.left)
  have isMiddle : PrimrecPred fun arm : DuplicatorArm =>
      arm = .middle :=
    Primrec.eq.comp Primrec.id
      (Primrec.const DuplicatorArm.middle)
  exact (Primrec.ite isLeft
    (Primrec.const (duplicatorArmEqualityPositions .left))
    (Primrec.ite isMiddle
      (Primrec.const (duplicatorArmEqualityPositions .middle))
      (Primrec.const
        (duplicatorArmEqualityPositions .right)))).of_eq fun arm => by
          cases arm <;> rfl

theorem routedVariableEqualityPositions_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        (PeriodicCNF Variable × VariableRouteSite Variable) ×
          DuplicatorArm =>
      routedVariableEqualityPositions input.1.1 input.1.2 input.2 := by
  have origin : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm =>
      routedVariableOrigin input.1.1 input.1.2 :=
    routedVariableOrigin_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  have localPositions : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm =>
      duplicatorArmEqualityPositions input.2 :=
    duplicatorArmEqualityPositions_primrec.comp Primrec.snd
  have forward : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm =>
      Cell.add (routedVariableOrigin input.1.1 input.1.2)
        (duplicatorArmEqualityPositions input.2).forward :=
    Computability.cell_add_primrec.comp origin
      (EqualityPositions.forward_primrec.comp localPositions)
  have backward : Primrec fun input :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        DuplicatorArm =>
      Cell.add (routedVariableOrigin input.1.1 input.1.2)
        (duplicatorArmEqualityPositions input.2).backward :=
    Computability.cell_add_primrec.comp origin
      (EqualityPositions.backward_primrec.comp localPositions)
  exact (EqualityPositions.mk_primrec.comp
    (Primrec.pair forward backward)).of_eq fun _ => rfl

private def routedVariableTaggedNodes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × VariableRouteSite Variable) :
    List (PlanarSATNode Variable × Nat) :=
  (routedVariableNodes input.1 input.2).take 3 |>.zipIdx

private theorem routedVariableTaggedNodes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableTaggedNodes (Variable := Variable)) := by
  have nodes : Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
      routedVariableNodes input.1 input.2 :=
    routedVariableNodes_primrec
  have firstThree : Primrec fun input :
      PeriodicCNF Variable × VariableRouteSite Variable =>
      (routedVariableNodes input.1 input.2).take 3 :=
    Primrec.list_take.comp (Primrec.const 3) nodes
  exact (PeriodicThreeSATThree.zipIdx_primrec.comp firstThree).of_eq
    fun _ => rfl

private def routedVariableLinkPositionInput
    {Variable : Type*}
    (combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat)) :
    (PeriodicCNF Variable × VariableRouteSite Variable) ×
      DuplicatorArm :=
  (combined.1, combined.2.1.duplicatorArm)

private theorem routedVariableLinkPositionInput_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (routedVariableLinkPositionInput
      (Variable := Variable)) := by
  have arm : Primrec fun combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat) =>
      combined.2.1.duplicatorArm :=
    PlanarSATNode.duplicatorArm_primrec.comp
      (Primrec.fst.comp Primrec.snd)
  exact (Primrec.pair Primrec.fst arm).of_eq fun _ => rfl

private def routedVariableLinkPositions
    {Variable : Type*} [DecidableEq Variable]
    (combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat)) : EqualityPositions :=
  routedVariableEqualityPositions combined.1.1 combined.1.2
    combined.2.1.duplicatorArm

private theorem routedVariableLinkPositions_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableLinkPositions (Variable := Variable)) := by
  exact (routedVariableEqualityPositions_primrec.comp
    routedVariableLinkPositionInput_primrec).of_eq fun _ => rfl

private def routedVariableLinkData
    {Variable : Type*} [DecidableEq Variable]
    (combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat)) :
    (PlanarSATNode Variable × PlanarSATNode Variable) ×
      EqualityPositions :=
  ((combined.2.1, .atom combined.1.2),
    routedVariableLinkPositions combined)

private theorem routedVariableLinkData_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableLinkData (Variable := Variable)) := by
  have first : Primrec fun combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat) =>
    combined.2.1 :=
    Primrec.fst.comp Primrec.snd
  have second : Primrec fun combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat) =>
    (PlanarSATNode.atom combined.1.2 : PlanarSATNode Variable) :=
    PlanarSATNode.atom_primrec.comp
      (Primrec.snd.comp Primrec.fst)
  exact (Primrec.pair (Primrec.pair first second)
    routedVariableLinkPositions_primrec).of_eq fun _ => rfl

private def routedVariableLink
    {Variable : Type*} [DecidableEq Variable]
    (combined :
      (PeriodicCNF Variable × VariableRouteSite Variable) ×
        (PlanarSATNode Variable × Nat)) :
    EqualityLink (PlanarSATNode Variable) :=
  EqualityLink.equivData.symm (routedVariableLinkData combined)

private theorem routedVariableLink_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableLink (Variable := Variable)) := by
  exact EqualityLink.equivData_symm_primrec.comp
    routedVariableLinkData_primrec

theorem routedVariableLinksAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (routedVariableLinksAt :
      PeriodicCNF Variable → VariableRouteSite Variable →
        List (EqualityLink (PlanarSATNode Variable))) := by
  exact (Primrec.list_map routedVariableTaggedNodes_primrec
    routedVariableLink_primrec.to₂).of_eq fun _ => rfl

theorem routedVariableFormulaAt_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (routedVariableFormulaAt :
      PeriodicCNF Variable → VariableRouteSite Variable →
        List (EmbeddedClause (PlanarSATNode Variable))) := by
  exact (equalityFamily_primrec.comp
    routedVariableLinksAt_primrec).of_eq fun _ => rfl

theorem drawingRoutedVariableFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingRoutedVariableFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATNode Variable))) := by
  exact (Primrec.list_flatMap drawingVariableRouteSites_primrec
    routedVariableFormulaAt_primrec).of_eq fun _ => rfl

theorem drawingRoutedClauseFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (drawingRoutedClauseFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATNode Variable))) :=
  drawingRoutedClauseFormula_primrec.to_comp

theorem drawingRoutedVariableFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (drawingRoutedVariableFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATNode Variable))) :=
  drawingRoutedVariableFormula_primrec.to_comp

theorem planarSATCoreVariableMap_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (planarSATCoreVariableMap :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) →
        PlanarSATVariable Variable) := by
  have carrier : Primrec fun node : CarrierNode =>
      (Sum.inl (PlanarSATNode.carrier node) :
        PlanarSATVariable Variable) :=
    Primrec.sumInl.comp PlanarSATNode.carrier_primrec
  exact (Primrec.sumCasesOn Primrec.id
    (carrier.comp₂ Primrec₂.right)
    (Primrec.sumInr.comp₂ Primrec₂.right)).of_eq
      fun input => by cases input <;> rfl

theorem planarSATExternalVariableMap_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (planarSATExternalVariableMap :
      PlanarSATNode Variable → PlanarSATVariable Variable) :=
  Primrec.sumInl

theorem retainedScopedDrawingPlanarSATCore_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedScopedDrawingPlanarSATCore :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  have core : Primrec fun formula : PeriodicCNF Variable =>
      retainedDrawingRoutePlanarCoreFormula
        (PeriodicCNF.incidenceGraph formula) :=
    retainedDrawingRoutePlanarCoreFormula_primrec.comp
      PeriodicCNF.incidenceGraph_primrec
  have rename : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (clause : EmbeddedClause
        (Sum CarrierNode (CrossingRecord × CrossoverInternal))) =>
      clause.rename (planarSATCoreVariableMap (Variable := Variable)) := by
    change Primrec fun input : PeriodicCNF Variable ×
        EmbeddedClause
          (Sum CarrierNode (CrossingRecord × CrossoverInternal)) =>
      input.2.rename (planarSATCoreVariableMap (Variable := Variable))
    exact EmbeddedClause.rename_primrec
      (fun (_formula : PeriodicCNF Variable) source =>
        planarSATCoreVariableMap source)
      (planarSATCoreVariableMap_primrec.comp Primrec.snd)
  exact (Primrec.list_map core rename).of_eq fun _ => rfl

theorem scopedDrawingRoutedClauseFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (scopedDrawingRoutedClauseFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  have rename : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (clause : EmbeddedClause (PlanarSATNode Variable)) =>
      clause.rename
        (planarSATExternalVariableMap (Variable := Variable)) := by
    change Primrec fun input : PeriodicCNF Variable ×
        EmbeddedClause (PlanarSATNode Variable) =>
      input.2.rename
        (planarSATExternalVariableMap (Variable := Variable))
    exact EmbeddedClause.rename_primrec
      (fun (_formula : PeriodicCNF Variable) source =>
        planarSATExternalVariableMap source)
      (planarSATExternalVariableMap_primrec.comp Primrec.snd)
  exact (Primrec.list_map
    drawingRoutedClauseFormula_primrec rename).of_eq fun _ => rfl

theorem scopedDrawingRoutedVariableFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (scopedDrawingRoutedVariableFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  have rename : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (clause : EmbeddedClause (PlanarSATNode Variable)) =>
      clause.rename
        (planarSATExternalVariableMap (Variable := Variable)) := by
    change Primrec fun input : PeriodicCNF Variable ×
        EmbeddedClause (PlanarSATNode Variable) =>
      input.2.rename
        (planarSATExternalVariableMap (Variable := Variable))
    exact EmbeddedClause.rename_primrec
      (fun (_formula : PeriodicCNF Variable) source =>
        planarSATExternalVariableMap source)
      (planarSATExternalVariableMap_primrec.comp Primrec.snd)
  exact (Primrec.list_map
    drawingRoutedVariableFormula_primrec rename).of_eq fun _ => rfl

private def retainedDrawingPlanarSATPrefix
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  retainedScopedDrawingPlanarSATCore formula ++
    scopedDrawingRoutedClauseFormula formula

private theorem retainedDrawingPlanarSATPrefix_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingPlanarSATPrefix :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  exact (Primrec.list_append.comp
    retainedScopedDrawingPlanarSATCore_primrec
    scopedDrawingRoutedClauseFormula_primrec).of_eq fun _ => rfl

private def computedRetainedDrawingPlanarSATFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    List (EmbeddedClause (PlanarSATVariable Variable)) :=
  retainedDrawingPlanarSATPrefix formula ++
    scopedDrawingRoutedVariableFormula formula

private theorem computedRetainedDrawingPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (computedRetainedDrawingPlanarSATFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  exact (Primrec.list_append.comp
    retainedDrawingPlanarSATPrefix_primrec
    scopedDrawingRoutedVariableFormula_primrec).of_eq fun _ => rfl

theorem retainedDrawingPlanarSATFormula_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (retainedDrawingPlanarSATFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) := by
  change Primrec
    (computedRetainedDrawingPlanarSATFormula (Variable := Variable))
  exact computedRetainedDrawingPlanarSATFormula_primrec

theorem retainedDrawingPlanarSATFormula_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable (retainedDrawingPlanarSATFormula :
      PeriodicCNF Variable →
        List (EmbeddedClause (PlanarSATVariable Variable))) :=
  retainedDrawingPlanarSATFormula_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
