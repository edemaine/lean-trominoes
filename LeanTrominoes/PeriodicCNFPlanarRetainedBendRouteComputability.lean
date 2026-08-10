import LeanTrominoes.PeriodicCNFPlanarRetainedLocalIncidenceRoutesComputability

/-!
# Computability of retained bend-corner incidence routes

This module specializes the executable translated corner table to the
input-dependent macrocell and compass ports of one routed bend.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 1000000

abbrev BendRouteInput (Variable : Type*) :=
  ((PeriodicCNF Variable × RouteBend) × Nat) × Nat

private def incidenceDrawingGridSize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) : Nat :=
  16 * (formula.variableOccurrences.dedup.length +
    formula.clauses.length + formula.clauses.flatten.length + 1)

private theorem incidenceDrawingGridSize_eq_drawingGridSize
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) :
    incidenceDrawingGridSize formula =
      drawingGridSize (PeriodicCNF.incidenceGraph formula) := by
  simp [incidenceDrawingGridSize, drawingGridSize,
    PeriodicCNF.incidenceGraph,
    PeriodicCNF.incidenceVariableVertices,
    PeriodicCNF.incidenceClauseVertices,
    PeriodicCNF.clauseIncidenceEdges,
    PeriodicCNF.variableOccurrences]
  simpa only [List.map_map, Function.comp_def] using
    (congrArg (fun clauses => (clauses.map List.length).sum)
      (List.zipIdx_map_fst 0 formula.clauses)).symm

private def bendRouteOrigin
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × RouteBend) : Cell :=
  Cell.scale planarMacroScale
    (Cell.add
      (Cell.scale (incidenceDrawingGridSize input.1) input.2.translate)
      input.2.bend)

private def bendRoutePorts (routeBend : RouteBend) :
    CornerPort × CornerPort :=
  (routeBend.incomingPort, routeBend.outgoingPort)

private def bendRouteGeometryData
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable × RouteBend) :
    Cell × (CornerPort × CornerPort) :=
  (bendRouteOrigin input, bendRoutePorts input.2)

private def bendRouteData
    {Variable : Type*} [DecidableEq Variable]
    (input : BendRouteInput Variable) : TranslatedCornerRouteInput :=
  ((bendRouteGeometryData input.1.1, input.1.2), input.2)

def bendRoute
    {Variable : Type*} [DecidableEq Variable]
    (input : BendRouteInput Variable) : List Cell :=
  translatedCornerRoute (bendRouteData input)

private theorem incidenceDrawingGridSize_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (incidenceDrawingGridSize (Variable := Variable)) := by
  have clauses : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses :=
    PeriodicCNF.equivData_primrec
  have variableCount : Primrec fun formula : PeriodicCNF Variable =>
      formula.variableOccurrences.dedup.length :=
    Primrec.list_length.comp
      (PeriodicThreeSATThree.dedup_primrec.comp
        PeriodicCNF.variableOccurrences_primrec)
  have clauseCount : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.length :=
    Primrec.list_length.comp clauses
  have edgeCount : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.flatten.length :=
    Primrec.list_length.comp (Primrec.list_flatten.comp clauses)
  exact (Primrec.nat_mul.comp (Primrec.const 16)
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp variableCount clauseCount)
        edgeCount)
      (Primrec.const 1))).of_eq fun _ => rfl

private theorem bendRouteOrigin_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (bendRouteOrigin (Variable := Variable)) := by
  have drawingTranslate : Primrec fun input :
      PeriodicCNF Variable × RouteBend =>
      Cell.scale (incidenceDrawingGridSize input.1) input.2.translate :=
    Computability.cell_scale_primrec.comp
      (Computability.int_ofNat_primrec.comp
        (incidenceDrawingGridSize_primrec.comp Primrec.fst))
      (RouteBend.translate_primrec.comp Primrec.snd)
  have drawingPoint : Primrec fun input :
      PeriodicCNF Variable × RouteBend =>
      Cell.add
        (Cell.scale (incidenceDrawingGridSize input.1) input.2.translate)
        input.2.bend :=
    Computability.cell_add_primrec.comp drawingTranslate
      (RouteBend.bend_primrec.comp Primrec.snd)
  exact (Computability.cell_scale_primrec.comp
    (Primrec.const planarMacroScale) drawingPoint).of_eq fun _ => rfl

private theorem bendRoutePorts_primrec :
    Primrec bendRoutePorts := by
  exact (Primrec.pair RouteBend.incomingPort_primrec
    RouteBend.outgoingPort_primrec).of_eq fun _ => rfl

private theorem bendRouteGeometryData_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (bendRouteGeometryData (Variable := Variable)) := by
  exact (Primrec.pair bendRouteOrigin_primrec
    (bendRoutePorts_primrec.comp Primrec.snd)).of_eq fun _ => rfl

private theorem bendRouteData_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (bendRouteData (Variable := Variable)) := by
  change Primrec fun input : BendRouteInput Variable =>
    ((bendRouteGeometryData input.1.1, input.1.2), input.2)
  exact Primrec.pair
    (Primrec.pair
      (bendRouteGeometryData_primrec.comp
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst))
    Primrec.snd

theorem bendRoute_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec (bendRoute (Variable := Variable)) :=
  translatedCornerRoute_primrec.comp bendRouteData_primrec

theorem bendRoute_eq_sourceRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (routeBend : RouteBend)
    (clauseIndex literalIndex : Nat) :
    bendRoute ((((formula, routeBend), clauseIndex), literalIndex)) =
      (drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).routes clauseIndex literalIndex := by
  rw [drawingPlanarSATBendCornerIncidenceDrawing]
  simp only [EmbeddedCNFIncidenceDrawing.rename]
  unfold bendRoute bendRouteData bendRouteGeometryData bendRouteOrigin
    bendRoutePorts translatedCornerRoute RouteBend.cornerDrawing
    placedCornerEqualityDrawing EmbeddedCNFIncidenceDrawing.renameToImage
  simp only [EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate, cornerEqualityDrawing]
  rw [incidenceDrawingGridSize_eq_drawingGridSize]
  rfl

end PeriodicOrthocrossing
end LeanTrominoes
