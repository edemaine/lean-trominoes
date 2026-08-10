import LeanTrominoes.PeriodicCNFIncidenceGraphComputability
import LeanTrominoes.PeriodicCNFPlanarIncidences
import LeanTrominoes.PeriodicOrthocrossingCarrierEncodingComputability
import LeanTrominoes.PeriodicOrthocrossingConstructionComputability

/-!
# Computability of routed CNF incidences

This module encodes the syntax-rich CNF incidences and their translated route
occurrences.  It proves the finite occurrence enumeration, route geometry,
and canonical source and target terminals primitive recursive.
-/

noncomputable section

namespace LeanTrominoes

set_option maxHeartbeats 1000000

namespace CNFIncidence

def equivData {Variable : Type*} : CNFIncidence Variable ≃
    (Nat × PeriodicClause Variable) ×
      (Nat × PeriodicLiteral Variable) where
  toFun incidence :=
    ((incidence.clauseIndex, incidence.clause),
      (incidence.literalIndex, incidence.literal))
  invFun data :=
    ⟨data.1.1, data.1.2, data.2.1, data.2.2⟩
  left_inv incidence := by cases incidence; rfl
  right_inv data := by
    rcases data with ⟨⟨clauseIndex, clause⟩,
      literalIndex, literal⟩
    rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (CNFIncidence Variable) :=
  Primcodable.ofEquiv
    ((Nat × PeriodicClause Variable) ×
      (Nat × PeriodicLiteral Variable)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem clauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFIncidence.clauseIndex :
      CNFIncidence Variable → Nat) :=
  ((Primrec.fst.comp Primrec.fst).comp
    equivData_primrec).of_eq fun _ => rfl

theorem clause_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFIncidence.clause :
      CNFIncidence Variable → PeriodicClause Variable) :=
  ((Primrec.snd.comp Primrec.fst).comp
    equivData_primrec).of_eq fun _ => rfl

theorem literalIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFIncidence.literalIndex :
      CNFIncidence Variable → Nat) :=
  ((Primrec.fst.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem literal_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFIncidence.literal :
      CNFIncidence Variable → PeriodicLiteral Variable) :=
  ((Primrec.snd.comp Primrec.snd).comp
    equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Nat × PeriodicClause Variable) ×
          (Nat × PeriodicLiteral Variable) =>
      CNFIncidence.mk data.1.1 data.1.2 data.2.1 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

theorem edge_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFIncidence.edge :
      CNFIncidence Variable → PeriodicEdge (CNFVertex Variable)) := by
  have anchor : Primrec fun incidence : CNFIncidence Variable =>
      PeriodicCNF.clauseAnchor incidence.clause :=
    PeriodicCNF.clauseAnchor_primrec.comp clause_primrec
  exact (PeriodicCNF.incidenceEdge_primrec.comp
    (Primrec.pair
      (Primrec.pair clauseIndex_primrec anchor)
      literal_primrec)).of_eq fun _ => rfl

end CNFIncidence

namespace PeriodicCNF

theorem incidencesWithMetadata_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (incidencesWithMetadata :
      PeriodicCNF Variable → List (CNFIncidence Variable)) := by
  have taggedClauses : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.equivData_primrec
  have one : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (taggedClause : PeriodicClause Variable × Nat) =>
      taggedClause.1.zipIdx.map fun taggedLiteral =>
        CNFIncidence.mk taggedClause.2 taggedClause.1
          taggedLiteral.2 taggedLiteral.1 := by
    change Primrec fun input :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
      input.2.1.zipIdx.map fun taggedLiteral =>
        CNFIncidence.mk input.2.2 input.2.1
          taggedLiteral.2 taggedLiteral.1
    have taggedLiterals : Primrec fun input :
        PeriodicCNF Variable × (PeriodicClause Variable × Nat) =>
        input.2.1.zipIdx :=
      PeriodicThreeSATThree.zipIdx_primrec.comp
        (Primrec.fst.comp Primrec.snd)
    have incidence : Primrec₂ fun
        (input : PeriodicCNF Variable ×
          (PeriodicClause Variable × Nat))
        (taggedLiteral : PeriodicLiteral Variable × Nat) =>
        CNFIncidence.mk input.2.2 input.2.1
          taggedLiteral.2 taggedLiteral.1 := by
      change Primrec fun combined :
          (PeriodicCNF Variable ×
            (PeriodicClause Variable × Nat)) ×
              (PeriodicLiteral Variable × Nat) =>
        CNFIncidence.mk combined.1.2.2 combined.1.2.1
          combined.2.2 combined.2.1
      exact CNFIncidence.mk_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.pair
            (Primrec.snd.comp Primrec.snd)
            (Primrec.fst.comp Primrec.snd)))
    exact Primrec.list_map taggedLiterals incidence
  exact (Primrec.list_flatMap taggedClauses one).of_eq fun _ => rfl

end PeriodicCNF

namespace PeriodicOrthocrossing

namespace CNFRouteOccurrence

def equivData {Variable : Type*} : CNFRouteOccurrence Variable ≃
    (CNFIncidence Variable × Nat) × Cell where
  toFun occurrence :=
    ((occurrence.incidence, occurrence.edgeIndex), occurrence.translate)
  invFun data := ⟨data.1.1, data.1.2, data.2⟩
  left_inv occurrence := by cases occurrence; rfl
  right_inv data := by
    rcases data with ⟨⟨incidence, edgeIndex⟩, translate⟩
    rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (CNFRouteOccurrence Variable) :=
  Primcodable.ofEquiv
    ((CNFIncidence Variable × Nat) × Cell) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem incidence_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.incidence :
      CNFRouteOccurrence Variable → CNFIncidence Variable) :=
  ((Primrec.fst.comp Primrec.fst).comp
    equivData_primrec).of_eq fun _ => rfl

theorem edgeIndex_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.edgeIndex :
      CNFRouteOccurrence Variable → Nat) :=
  ((Primrec.snd.comp Primrec.fst).comp
    equivData_primrec).of_eq fun _ => rfl

theorem translate_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.translate :
      CNFRouteOccurrence Variable → Cell) :=
  (Primrec.snd.comp equivData_primrec).of_eq fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data : (CNFIncidence Variable × Nat) × Cell =>
      CNFRouteOccurrence.mk data.1.1 data.1.2 data.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

theorem edge_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.edge :
      CNFRouteOccurrence Variable →
        PeriodicEdge (CNFVertex Variable)) :=
  CNFIncidence.edge_primrec.comp incidence_primrec

theorem routeKey_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.routeKey :
      CNFRouteOccurrence Variable → RouteOccurrenceKey) :=
  (Primrec.pair edgeIndex_primrec translate_primrec).of_eq
    fun _ => rfl

theorem clauseOccurrence_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.clauseOccurrence :
      CNFRouteOccurrence Variable → Nat × Cell) :=
  (Primrec.pair
    (CNFIncidence.clauseIndex_primrec.comp incidence_primrec)
    translate_primrec).of_eq fun _ => rfl

theorem variableOccurrence_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CNFRouteOccurrence.variableOccurrence :
      CNFRouteOccurrence Variable → Variable × Cell) := by
  have atom : Primrec fun occurrence : CNFRouteOccurrence Variable =>
      occurrence.incidence.literal.atom :=
    PeriodicThreeCNF.literal_atom_primrec.comp
      (CNFIncidence.literal_primrec.comp incidence_primrec)
  have translated : Primrec fun occurrence : CNFRouteOccurrence Variable =>
      Cell.add occurrence.translate occurrence.edge.offset :=
    Computability.cell_add_primrec.comp translate_primrec
      (PeriodicEdge.offset_primrec.comp edge_primrec)
  exact (Primrec.pair atom translated).of_eq fun _ => rfl

private def constructedRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × CNFRouteOccurrence Variable) :
    List Cell :=
  constructedEdgeRoute (PeriodicCNF.incidenceGraph input.1)
    input.2.edge input.2.edgeIndex

private def constructedRouteInput
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × CNFRouteOccurrence Variable) :
    (PeriodicGraph (CNFVertex Variable) ×
      PeriodicEdge (CNFVertex Variable)) × Nat :=
  ((PeriodicCNF.incidenceGraph input.1, input.2.edge),
    input.2.edgeIndex)

private theorem constructedRouteInput_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (constructedRouteInput (Variable := Variable)) := by
  exact (Primrec.pair
    (Primrec.pair
      (PeriodicCNF.incidenceGraph_primrec.comp Primrec.fst)
      (edge_primrec.comp Primrec.snd))
    (edgeIndex_primrec.comp Primrec.snd)).of_eq fun _ => rfl

private theorem constructedRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (constructedRoute (Variable := Variable)) := by
  exact (constructedEdgeRoute_primrec.comp
    constructedRouteInput_primrec).of_eq fun _ => rfl

private theorem getLast?_getD_eq_getLastD
    {Item : Type*} (items : List Item) (fallback : Item) :
    items.getLast?.getD fallback = items.getLastD fallback := by
  induction items with
  | nil => rfl
  | cons head tail induction =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          simp only [List.getLast?, List.getLastD]
          exact induction

theorem taggedSegments_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (CNFRouteOccurrence.taggedSegments :
      PeriodicCNF Variable → CNFRouteOccurrence Variable →
        List (GridSegment × Nat)) := by
  change Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
    input.2.taggedSegments input.1
  have route : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      constructedEdgeRoute
        (PeriodicCNF.incidenceGraph input.1)
        input.2.edge input.2.edgeIndex :=
    constructedRoute_primrec
  exact (PeriodicThreeSATThree.zipIdx_primrec.comp
    (gridPolylineSegments_primrec.comp route)).of_eq fun _ => rfl

theorem sourceTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (CNFRouteOccurrence.sourceTerminal :
      PeriodicCNF Variable → CNFRouteOccurrence Variable →
        SegmentTerminal) := by
  change Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
    input.2.sourceTerminal input.1
  have segments : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      input.2.taggedSegments input.1 :=
    taggedSegments_primrec
  have first : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      (input.2.taggedSegments input.1).getD
        0 defaultTaggedGridSegment :=
    (Primrec.list_getD defaultTaggedGridSegment).comp
      segments (Primrec.const 0)
  have indexed : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      IndexedGridSegment.mk input.2.edgeIndex
        ((input.2.taggedSegments input.1).getD
          0 defaultTaggedGridSegment).2
        ((input.2.taggedSegments input.1).getD
          0 defaultTaggedGridSegment).1 :=
    IndexedGridSegment.mk_primrec.comp
      (Primrec.pair
        (edgeIndex_primrec.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp first)
          (Primrec.fst.comp first)))
  exact (SegmentTerminal.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair indexed
        (translate_primrec.comp Primrec.snd))
      (Primrec.const SegmentEnd.start))).of_eq fun _ => rfl

theorem targetTerminal_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec₂ (CNFRouteOccurrence.targetTerminal :
      PeriodicCNF Variable → CNFRouteOccurrence Variable →
        SegmentTerminal) := by
  change Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
    input.2.targetTerminal input.1
  have segments : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      input.2.taggedSegments input.1 :=
    taggedSegments_primrec
  have last : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      (input.2.taggedSegments input.1).getLastD
        defaultTaggedGridSegment :=
    ((Primrec.list_getD defaultTaggedGridSegment).comp
      (Primrec.list_reverse.comp segments) (Primrec.const 0)).of_eq
        fun input => by
          simp only [List.getD_eq_getElem?_getD,
            ← List.head?_eq_getElem?, List.head?_reverse]
          exact getLast?_getD_eq_getLastD _ _
  have indexed : Primrec fun input :
      PeriodicCNF Variable × CNFRouteOccurrence Variable =>
      IndexedGridSegment.mk input.2.edgeIndex
        ((input.2.taggedSegments input.1).getLastD
          defaultTaggedGridSegment).2
        ((input.2.taggedSegments input.1).getLastD
          defaultTaggedGridSegment).1 :=
    IndexedGridSegment.mk_primrec.comp
      (Primrec.pair
        (edgeIndex_primrec.comp Primrec.snd)
        (Primrec.pair
          (Primrec.snd.comp last)
          (Primrec.fst.comp last)))
  exact (SegmentTerminal.mk_primrec.comp
    (Primrec.pair
      (Primrec.pair indexed
        (translate_primrec.comp Primrec.snd))
      (Primrec.const SegmentEnd.finish))).of_eq fun _ => rfl

end CNFRouteOccurrence

theorem drawingCNFRouteOccurrences_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (drawingCNFRouteOccurrences :
      PeriodicCNF Variable → List (CNFRouteOccurrence Variable)) := by
  have tagged : Primrec fun formula : PeriodicCNF Variable =>
      (PeriodicCNF.incidencesWithMetadata formula).zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      PeriodicCNF.incidencesWithMetadata_primrec
  have one : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (taggedIncidence : CNFIncidence Variable × Nat) =>
      neighborTranslations.map fun translate =>
        CNFRouteOccurrence.mk taggedIncidence.1
          taggedIncidence.2 translate := by
    change Primrec fun input :
        PeriodicCNF Variable × (CNFIncidence Variable × Nat) =>
      neighborTranslations.map fun translate =>
        CNFRouteOccurrence.mk input.2.1 input.2.2 translate
    have occurrence : Primrec₂ fun
        (input : PeriodicCNF Variable ×
          (CNFIncidence Variable × Nat))
        (translate : Cell) =>
        CNFRouteOccurrence.mk input.2.1 input.2.2 translate := by
      change Primrec fun combined :
          (PeriodicCNF Variable ×
            (CNFIncidence Variable × Nat)) × Cell =>
        CNFRouteOccurrence.mk combined.1.2.1
          combined.1.2.2 combined.2
      exact CNFRouteOccurrence.mk_primrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          Primrec.snd)
    exact Primrec.list_map
      (Primrec.const neighborTranslations) occurrence
  exact (Primrec.list_flatMap tagged one).of_eq fun _ => rfl

end PeriodicOrthocrossing
end LeanTrominoes
