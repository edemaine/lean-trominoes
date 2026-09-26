/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativeThreeDMTargetCoordinates
import LeanTrominoes.PeriodicGridDrawingVertexTable
import LeanTrominoes.UnaryPointFieldsCompiler

/-! # The complete native 3DM drawing vertex table -/
noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Turing Gadget PeriodicThreeDM UnaryColumn DelimitedDirectionDisplacement
variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language) [Inhabited encoding.Γ]
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 2048

private theorem orderedPositions (p : PeriodicThreeDM) (d : PeriodicGridDrawing)
    (first rest : List Cell) (positions : d.vertexPositions = first ++ rest)
    (length : first.length = p.triples.length) (compatible : d.IsCompatible p.incidenceGraph) :
    d.vertexPositions = first ++ (CountedContractedIncidence.horizontalElementPairs p).map
      (fun e => d.vertexPosition p.incidenceGraph (.element e.1 e.2)) := by
  have triples : p.tripleVertices.map (d.vertexPosition p.incidenceGraph) = first := by
    rw [tripleVertices, List.map_map, ← length, ← List.map_range_getD first (0,0)]
    simp only [List.length_map,List.length_range]
    apply List.map_congr_left
    intro i hi
    have bound : i < first.length := List.mem_range.mp hi
    have graphBound : i < p.incidenceGraph.vertices.length := by
      simp only [incidenceGraph,List.length_append,tripleVertices,List.length_map,List.length_range]
      omega
    have atIndex : p.incidenceGraph.vertices[i] = .triple i := by
      simp [incidenceGraph,tripleVertices,List.getElem_append_left,← length,bound]
    have index := p.incidenceGraph_vertices_nodup.idxOf_getElem i graphBound
    rw [atIndex] at index
    change d.vertexPosition p.incidenceGraph (.triple i) = _
    rw [PeriodicGridDrawing.vertexPosition,index,positions,
      List.getD_eq_getElem _ _ (by simp; omega),List.getElem_append_left bound,
      List.getD_eq_getElem _ _ bound]
  rw [PeriodicGridDrawing.vertexPositions_eq_map_vertexPosition p.incidenceGraph d
    p.incidenceGraph_vertices_nodup compatible.2.1]
  simp only [incidenceGraph,List.map_append]
  congr 1
  simp only [elementVertices,coloredElementVertices,CountedContractedIncidence.horizontalElementPairs,
    incidenceColors,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_append,List.map_map,List.append_assoc]
  rfl

private theorem elementPositive (p : PeriodicThreeDM) (d : PeriodicGridDrawing)
    (compatible : d.IsCompatible p.incidenceGraph) (e : WireColor × Nat)
    (bound : e.2 < p.elementCount e.1) (horizontal : Bool) :
    0 < component horizontal (d.vertexPosition p.incidenceGraph (.element e.1 e.2)) := by
  have member : PeriodicThreeDMVertex.element e.1 e.2 ∈ p.incidenceGraph.vertices := by
    rcases e with ⟨color,atom⟩
    cases color <;> simp [incidenceGraph,elementVertices,coloredElementVertices,bound]
  have inside := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem member)
  cases horizontal <;> simp only [component] <;> exact (by rcases inside with ⟨hx,_,hy,_⟩; assumption)

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMVertexPositions (s : List encoding.Γ) :
    (nativeThreeDMDrawing decider s).vertexPositions = nativeThreeDMTriplePositions decider s ++
      (nativeThreeDMElements decider s).map (nativeThreeDMElementPoint decider s) := by
  apply orderedPositions (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s)
    (nativeThreeDMTriplePositions decider s)
    (horizontalThreeDMColoredPositionsComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s))
  · rw [nativeThreeDMDrawing,horizontalThreeDMDrawingComputed_vertexPositions]
    rfl
  · exact nativeThreeDMTriplePositions_length decider s
  · exact nativeThreeDMDrawing_compatible decider s

omit [Inhabited encoding.Γ] in
theorem nativeThreeDMElementPoint_positive (s : List encoding.Γ) (e : WireColor × Nat)
    (he : e ∈ nativeThreeDMElements decider s) (horizontal : Bool) :
    0 < component horizontal (nativeThreeDMElementPoint decider s e) :=
  elementPositive (nativeThreeDMProblem decider s) (nativeThreeDMDrawing decider s)
    (nativeThreeDMDrawing_compatible decider s) e ((nativeThreeDMElement_mem decider s e).1 he) horizontal

def nativeThreeDMElementSignedCoordinateCompiler (horizontal positive : Bool) :
    Compiler (nativeThreeDMElements decider) (fun s e =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal (nativeThreeDMElementPoint decider s e))) := by
  cases positive
  · apply TM2ComputableInPolyTime.of_eq (constant (nativeThreeDMElementCoordinateCompiler decider horizontal) 0)
    intro s
    apply List.map_congr_left
    intro e he
    have pos := nativeThreeDMElementPoint_positive decider s e he horizontal
    simp only [SignedUnaryCoordinateRefinement.field,Bool.false_eq_true,↓reduceIte]
    omega
  · exact nativeThreeDMElementCoordinateCompiler decider horizontal

private theorem pointValue_eq (horizontal positive : Bool) (point : Cell) :
    PeriodicOrthocrossing.CarrierCrossingPointField.pointValue (PeriodicOrthocrossing.coordinateFieldOfBools horizontal positive) point =
      SignedUnaryCoordinateRefinement.field positive (component horizontal point) := by
  cases horizontal <;> cases positive <;> rfl

def nativeThreeDMVertexCoordinateCompiler (horizontal positive : Bool) :
    Compiler (fun s => (nativeThreeDMDrawing decider s).vertexPositions) (fun _ point =>
      SignedUnaryCoordinateRefinement.field positive (component horizontal point)) := by
  let physical := UnaryFieldClosure.appendCompiler id _ _
    (directSourceFinalTripleCoordinatesComputableInPolyTime decider horizontal positive)
    (nativeThreeDMElementSignedCoordinateCompiler decider horizontal positive)
  apply TM2ComputableInPolyTime.of_eq physical
  intro s
  dsimp only
  rw [nativeThreeDMVertexPositions,List.map_append,List.map_map]
  have first := directSourceFinalTripleCoordinates_eq_horizontal decider horizontal positive s
  have firstEq : directSourceFinalTripleCoordinates decider horizontal positive s = (nativeThreeDMTriplePositions decider s).map
      (fun point => SignedUnaryCoordinateRefinement.field positive (component horizontal point)) := by
    apply first.trans
    apply List.map_congr_left
    intro point _
    exact pointValue_eq horizontal positive point
  rw [firstEq]
  rfl

def nativeThreeDMVertexFieldsCompiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun s => (nativeThreeDMDrawing decider s).vertexPositions.flatMap PeriodicGridDrawing.Arithmetic.pointFields) :=
  pointFieldsCompiler (rows := fun s => (nativeThreeDMDrawing decider s).vertexPositions) (point := fun _ p => p)
    (nativeThreeDMVertexCoordinateCompiler decider true true) (nativeThreeDMVertexCoordinateCompiler decider true false)
    (nativeThreeDMVertexCoordinateCompiler decider false true) (nativeThreeDMVertexCoordinateCompiler decider false false)

end LeanTrominoes.PeriodicCNFStripReduction
end
