/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicThreeDMPlanarQueries
import LeanTrominoes.PeriodicThreeDMEdgeIndices

/-! # Native vertex and route count checks -/
namespace LeanTrominoes.PeriodicThreeDM.DrawingCounts
open Gadget NormalizationCompiler PeriodicGridDrawing BoundedArithmetic BoundedArithmetic.Expr PlanarQueries

def predicate : Expr := andE
  (eqE (var 4) (problemField 0 3+problemField 0 0+problemField 0 1+problemField 0 2))
  (eqE (NativeRoutes.routeCount 1) (3*problemField 0 3))

theorem noPower : predicate.noPower=true := by decide

theorem correct (input : Input) : predicate.Truth (FlatEncoding.Planar.fields input) ↔
    input.drawing.vertexPositions.length=input.problem.incidenceGraph.vertices.length ∧
    input.drawing.edgeRoutes.length=input.problem.incidenceGraph.edges.length := by
  have r := header_eval input [] 0
  have g := header_eval input [] 1
  have b := header_eval input [] 2
  have n := header_eval input [] 3
  change (problemField 0 0).eval (FlatEncoding.Planar.fields input)=input.problem.redCount at r
  change (problemField 0 1).eval (FlatEncoding.Planar.fields input)=input.problem.greenCount at g
  change (problemField 0 2).eval (FlatEncoding.Planar.fields input)=input.problem.blueCount at b
  change (problemField 0 3).eval (FlatEncoding.Planar.fields input)=input.problem.triples.length at n
  have routes := NativeRoutes.routeCount_eval input.drawing [(Arithmetic.fields input.drawing).length]
    (FlatEncoding.fields input.problem)
  change (NativeRoutes.routeCount 1).eval (FlatEncoding.Planar.fields input)=input.drawing.edgeRoutes.length at routes
  have verts : (var 4).eval (FlatEncoding.Planar.fields input)=input.drawing.vertexPositions.length := rfl
  simp only [predicate,truth_and,truth_eq,eval_add,eval_mul,r,g,b,n,routes,verts,
    show (3:Expr).eval (FlatEncoding.Planar.fields input)=3 from rfl,
    incidence_vertices_length,incidence_edges_length]

end LeanTrominoes.PeriodicThreeDM.DrawingCounts
