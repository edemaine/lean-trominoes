import LeanTrominoes.PeriodicCNFPlanarRetainedBendRouteComputability

/-!
# Computability of retained local incidence-route lookup

The retained clause metadata has five geometric source constructors.  This
module decodes that finite sum, invokes the corresponding executable local
route family, and proves that the resulting total lookup is exactly the
semantic route family used by the retained planar incidence drawing.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

private abbrev SourceRouteInput (Variable : Type*) (Source : Type*) :=
  (PeriodicCNF Variable × Source) × Nat

private abbrev SourceRouteRestThree (Variable : Type*) :=
  ClauseRouteSite ⊕ DrawingPlanarSATClauseSource.RoutedVariableData Variable

private abbrev SourceRouteRestTwo (Variable : Type*) :=
  (RouteBend × Nat) ⊕ SourceRouteRestThree Variable

private abbrev SourceRouteRestOne (Variable : Type*) :=
  (EqualityLink CarrierNode × Nat) ⊕ SourceRouteRestTwo Variable

private abbrev SourceRouteData (Variable : Type*) :=
  (CrossingRecord × Nat) ⊕ SourceRouteRestOne Variable

private def routedVariableSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable
      (DrawingPlanarSATClauseSource.RoutedVariableData Variable)) :
    List Cell :=
  routedVariableRoute
    ((((input.1.1, input.1.2.1.1.1.1), input.1.2.1.1.2),
      input.1.2.2), input.2)

private theorem routedVariableSourceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (routedVariableSourceRoute (Variable := Variable)) := by
  exact routedVariableRoute_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.fst.comp
                  (Primrec.fst.comp
                    (Primrec.snd.comp Primrec.fst))))))
          (Primrec.snd.comp
            (Primrec.fst.comp
              (Primrec.fst.comp
                (Primrec.snd.comp Primrec.fst)))))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

private def sourceRouteRestThree
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable (SourceRouteRestThree Variable)) :
    List Cell :=
  match input.1.2 with
  | .inl site => routedClauseRoute (((input.1.1, site), 0), input.2)
  | .inr data => routedVariableSourceRoute ((input.1.1, data), input.2)

private theorem sourceRouteRestThree_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (sourceRouteRestThree (Variable := Variable)) := by
  have source : Primrec fun input :
      SourceRouteInput Variable (SourceRouteRestThree Variable) =>
      input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have routedClause : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestThree Variable))
      (site : ClauseRouteSite) =>
      routedClauseRoute (((input.1.1, site), 0), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestThree Variable))
        (site : ClauseRouteSite) =>
        (((input.1.1, site), 0), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestThree Variable) ×
            ClauseRouteSite =>
        (((combined.1.1.1, combined.2), 0), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            Primrec.snd)
          (Primrec.const 0))
        (Primrec.snd.comp Primrec.fst)
    exact routedClauseRoute_primrec.comp₂ routeInput
  have routedVariable : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestThree Variable))
      (data : DrawingPlanarSATClauseSource.RoutedVariableData Variable) =>
      routedVariableSourceRoute ((input.1.1, data), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestThree Variable))
        (data : DrawingPlanarSATClauseSource.RoutedVariableData Variable) =>
        ((input.1.1, data), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestThree Variable) ×
            DrawingPlanarSATClauseSource.RoutedVariableData Variable =>
        ((combined.1.1.1, combined.2), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    exact routedVariableSourceRoute_primrec.comp₂ routeInput
  exact (Primrec.sumCasesOn source routedClause routedVariable).of_eq
    fun input => by
      rcases input with ⟨⟨formula, source⟩, literalIndex⟩
      cases source <;> rfl

private def sourceRouteRestTwo
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable (SourceRouteRestTwo Variable)) :
    List Cell :=
  match input.1.2 with
  | .inl data => bendRoute (((input.1.1, data.1), data.2), input.2)
  | .inr data => sourceRouteRestThree ((input.1.1, data), input.2)

private theorem sourceRouteRestTwo_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (sourceRouteRestTwo (Variable := Variable)) := by
  have source : Primrec fun input :
      SourceRouteInput Variable (SourceRouteRestTwo Variable) =>
      input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have bend : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestTwo Variable))
      (data : RouteBend × Nat) =>
      bendRoute (((input.1.1, data.1), data.2), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestTwo Variable))
        (data : RouteBend × Nat) =>
        (((input.1.1, data.1), data.2), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestTwo Variable) ×
            (RouteBend × Nat) =>
        (((combined.1.1.1, combined.2.1), combined.2.2),
          combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact bendRoute_primrec.comp₂ routeInput
  have rest : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestTwo Variable))
      (data : SourceRouteRestThree Variable) =>
      sourceRouteRestThree ((input.1.1, data), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestTwo Variable))
        (data : SourceRouteRestThree Variable) =>
        ((input.1.1, data), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestTwo Variable) ×
            SourceRouteRestThree Variable =>
        ((combined.1.1.1, combined.2), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    exact sourceRouteRestThree_primrec.comp₂ routeInput
  exact (Primrec.sumCasesOn source bend rest).of_eq
    fun input => by
      rcases input with ⟨⟨formula, source⟩, literalIndex⟩
      cases source <;> rfl

private def sourceRouteRestOne
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable (SourceRouteRestOne Variable)) :
    List Cell :=
  match input.1.2 with
  | .inl data => carrierRoute (((input.1.1, data.1), data.2), input.2)
  | .inr data => sourceRouteRestTwo ((input.1.1, data), input.2)

private theorem sourceRouteRestOne_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (sourceRouteRestOne (Variable := Variable)) := by
  have source : Primrec fun input :
      SourceRouteInput Variable (SourceRouteRestOne Variable) =>
      input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have carrier : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestOne Variable))
      (data : EqualityLink CarrierNode × Nat) =>
      carrierRoute (((input.1.1, data.1), data.2), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestOne Variable))
        (data : EqualityLink CarrierNode × Nat) =>
        (((input.1.1, data.1), data.2), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestOne Variable) ×
            (EqualityLink CarrierNode × Nat) =>
        (((combined.1.1.1, combined.2.1), combined.2.2),
          combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact carrierRoute_primrec.comp₂ routeInput
  have rest : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteRestOne Variable))
      (data : SourceRouteRestTwo Variable) =>
      sourceRouteRestTwo ((input.1.1, data), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteRestOne Variable))
        (data : SourceRouteRestTwo Variable) =>
        ((input.1.1, data), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteRestOne Variable) ×
            SourceRouteRestTwo Variable =>
        ((combined.1.1.1, combined.2), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    exact sourceRouteRestTwo_primrec.comp₂ routeInput
  exact (Primrec.sumCasesOn source carrier rest).of_eq
    fun input => by
      rcases input with ⟨⟨formula, source⟩, literalIndex⟩
      cases source <;> rfl

private def sourceRouteData
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable (SourceRouteData Variable)) :
    List Cell :=
  match input.1.2 with
  | .inl data => crossoverRoute (((input.1.1, data.1), data.2), input.2)
  | .inr data => sourceRouteRestOne ((input.1.1, data), input.2)

private theorem sourceRouteData_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (sourceRouteData (Variable := Variable)) := by
  have source : Primrec fun input :
      SourceRouteInput Variable (SourceRouteData Variable) =>
      input.1.2 :=
    Primrec.snd.comp Primrec.fst
  have crossover : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteData Variable))
      (data : CrossingRecord × Nat) =>
      crossoverRoute (((input.1.1, data.1), data.2), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteData Variable))
        (data : CrossingRecord × Nat) =>
        (((input.1.1, data.1), data.2), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteData Variable) ×
            (CrossingRecord × Nat) =>
        (((combined.1.1.1, combined.2.1), combined.2.2),
          combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact crossoverRoute_primrec.comp₂ routeInput
  have rest : Primrec₂ fun
      (input : SourceRouteInput Variable (SourceRouteData Variable))
      (data : SourceRouteRestOne Variable) =>
      sourceRouteRestOne ((input.1.1, data), input.2) := by
    have routeInput : Primrec₂ fun
        (input : SourceRouteInput Variable (SourceRouteData Variable))
        (data : SourceRouteRestOne Variable) =>
        ((input.1.1, data), input.2) := by
      change Primrec fun combined :
          SourceRouteInput Variable (SourceRouteData Variable) ×
            SourceRouteRestOne Variable =>
        ((combined.1.1.1, combined.2), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (Primrec.snd.comp Primrec.fst)
    exact sourceRouteRestOne_primrec.comp₂ routeInput
  exact (Primrec.sumCasesOn source crossover rest).of_eq
    fun input => by
      rcases input with ⟨⟨formula, source⟩, literalIndex⟩
      cases source <;> rfl

def drawingPlanarSATSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : SourceRouteInput Variable
      (DrawingPlanarSATClauseSource Variable)) : List Cell :=
  sourceRouteData
    ((input.1.1, DrawingPlanarSATClauseSource.equivData input.1.2),
      input.2)

theorem drawingPlanarSATSourceRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (drawingPlanarSATSourceRoute (Variable := Variable)) := by
  exact sourceRouteData_primrec.comp
    (Primrec.pair
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        (DrawingPlanarSATClauseSource.equivData_primrec.comp
          (Primrec.snd.comp Primrec.fst)))
      Primrec.snd)

theorem drawingPlanarSATSourceRoute_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (source : DrawingPlanarSATClauseSource Variable)
    (literalIndex : Nat) :
    drawingPlanarSATSourceRoute ((formula, source), literalIndex) =
      (source.incidenceDrawing formula).routes
        source.localClauseIndex literalIndex := by
  cases source with
  | crossover crossing clauseIndex => rfl
  | carrier link clauseIndex =>
      dsimp [drawingPlanarSATSourceRoute, sourceRouteData,
        sourceRouteRestOne, DrawingPlanarSATClauseSource.equivData,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.localClauseIndex, carrierRoute,
        drawingPlanarSATCarrierLensIncidenceDrawing,
        EqualityLink.lensDrawing, placedEqualityLensDrawing,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.renameToImage,
        EmbeddedCNFIncidenceDrawing.rename,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        EmbeddedCNFIncidenceDrawing.translate,
        horizontalEqualityLensDrawing]
      rw [List.map_map]
      rfl
  | bend routeBend clauseIndex =>
      exact bendRoute_eq_sourceRoute
        formula routeBend clauseIndex literalIndex
  | routedClause site => rfl
  | routedVariable site armIndex arm link clauseIndex => rfl

def retainedDrawingPlanarSATLocalIncidenceRouteLookup
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable × Nat) × Nat) : List Cell :=
  match
      (retainedDrawingPlanarSATClauseMetadata
        input.1.1)[input.1.2]? with
  | none => []
  | some metadata =>
      drawingPlanarSATSourceRoute
        ((input.1.1, metadata.source), input.2)

theorem retainedDrawingPlanarSATLocalIncidenceRouteLookup_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec
      (retainedDrawingPlanarSATLocalIncidenceRouteLookup
        (Variable := Variable)) := by
  have metadata : Primrec fun input :
      (PeriodicCNF Variable × Nat) × Nat =>
      (retainedDrawingPlanarSATClauseMetadata
        input.1.1)[input.1.2]? :=
    Primrec.list_getElem?.comp
      (retainedDrawingPlanarSATClauseMetadata_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input :
      (PeriodicCNF Variable × Nat) × Nat =>
      ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun
      (input : (PeriodicCNF Variable × Nat) × Nat)
      (metadata : DrawingPlanarSATClauseMetadata Variable) =>
      drawingPlanarSATSourceRoute
        ((input.1.1, metadata.source), input.2) := by
    have routeInput : Primrec₂ fun
        (input : (PeriodicCNF Variable × Nat) × Nat)
        (metadata : DrawingPlanarSATClauseMetadata Variable) =>
        ((input.1.1, metadata.source), input.2) := by
      change Primrec fun combined :
          (((PeriodicCNF Variable × Nat) × Nat) ×
            DrawingPlanarSATClauseMetadata Variable) =>
        ((combined.1.1.1, combined.2.source), combined.1.2)
      exact Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (DrawingPlanarSATClauseMetadata.source_primrec.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst)
    exact drawingPlanarSATSourceRoute_primrec.comp₂ routeInput
  exact (Primrec.option_casesOn metadata none some).of_eq
    fun input => by
      unfold retainedDrawingPlanarSATLocalIncidenceRouteLookup
      rcases input with ⟨⟨formula, clauseIndex⟩, literalIndex⟩
      cases h : (retainedDrawingPlanarSATClauseMetadata
        formula)[clauseIndex]?
      <;> rfl

private theorem retainedDrawingPlanarSATLocalIncidenceRouteLookup_eq
    {Variable : Type*} [DecidableEq Variable]
    (input : (PeriodicCNF Variable × Nat) × Nat) :
    retainedDrawingPlanarSATLocalIncidenceRouteLookup input =
      retainedDrawingPlanarSATLocalIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  unfold retainedDrawingPlanarSATLocalIncidenceRouteLookup
    retainedDrawingPlanarSATLocalIncidenceRoutes
  cases h : (retainedDrawingPlanarSATClauseMetadata
    input.1.1)[input.1.2]?
  · rfl
  ·
    exact drawingPlanarSATSourceRoute_eq
      input.1.1 _ input.2

theorem retainedDrawingPlanarSATLocalIncidenceRoutes_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDrawingPlanarSATLocalIncidenceRoutes
        input.1.1 input.1.2 input.2 := by
  exact
    retainedDrawingPlanarSATLocalIncidenceRouteLookup_primrec.of_eq
      retainedDrawingPlanarSATLocalIncidenceRouteLookup_eq

theorem retainedDrawingPlanarSATLocalIncidenceRoutes_computable
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Computable fun input : (PeriodicCNF Variable × Nat) × Nat =>
      retainedDrawingPlanarSATLocalIncidenceRoutes
        input.1.1 input.1.2 input.2 :=
  retainedDrawingPlanarSATLocalIncidenceRoutes_primrec.to_comp

end PeriodicOrthocrossing
end LeanTrominoes
