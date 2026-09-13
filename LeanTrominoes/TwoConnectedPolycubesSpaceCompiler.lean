/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubesSpaceGeometry
import LeanTrominoes.Theorem55CompilerComputability

/-! # Executable, primitive-recursive compilation of the connected full-space tile -/

namespace LeanTrominoes.TwoConnectedPolycubes.SpaceCompiler

abbrev Input := Theorem55Compiler.Input

def compile (input : Input) : List Voxel :=
  (Theorem55Compiler.compile input).map (fun c => (c,0)) ++
  (Theorem55Compiler.compile input).map (fun c => (c,1)) ++
  (Theorem55Compiler.compile input).map (fun c => (c,2)) ++
  (Theorem55Compiler.squareList (3 * input.1)).map (fun c => (c,-1)) ++
  (Theorem55Compiler.squareList (3 * input.1)).map (fun c => (c,3))

private theorem layer_toFinset (cells : List Cell) (z : Int) :
    (cells.map (fun c => (c,z))).toFinset = Polycube.extrude cells.toFinset {z} := by
  ext c
  simp [Prod.ext_iff,Polycube.mem_extrude,eq_comm]

private theorem layers_eq (body cap : Polyomino) :
    Polycube.extrude body {0} ∪ Polycube.extrude body {1} ∪ Polycube.extrude body {2} ∪
      Polycube.extrude cap {-1} ∪ Polycube.extrude cap {3} =
      Polycube.extrude body {0,1,2} ∪ Polycube.extrude cap {-1,3} := by
  ext c
  simp only [Finset.mem_union,Polycube.mem_extrude,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem compile_source {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    (compile (Theorem55Compiler.sourceInput presentation)).toFinset =
      KeyedPeriodicComplement.spaceTile (3 * Theorem55Source.period presentation)
        (Theorem55Source.holes presentation) := by
  simp only [compile,List.toFinset_append,layer_toFinset,Theorem55Compiler.compile_source,
    Theorem55Compiler.squareList_toFinset]
  exact layers_eq _ _

theorem compile_source_correct {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    spaceProblem (compile (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  have large := Theorem55Source.period_large presentation
  exact (spaceProblem_iff_of_mask (n := 3 * Theorem55Source.period presentation)
    (by omega) (by omega) (Theorem55Source.holes presentation)
    (Theorem55Source.holes_admissible presentation) (Theorem55Source.region presentation)
    (Theorem55Source.holes_carrier presentation) _ (compile_source presentation)).trans
      (Theorem55Source.tileable_iff presentation)

theorem compile_primrec : Primrec compile := by
  have size : Primrec (fun input : Input => 3 * input.1) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst
  have body (z : Int) : Primrec (fun input : Input =>
      (Theorem55Compiler.compile input).map (fun c => (c,z))) :=
    Primrec.list_map Theorem55Compiler.compile_primrec
      (Primrec.pair Primrec.snd (Primrec.const z))
  have cap (z : Int) : Primrec (fun input : Input =>
      (Theorem55Compiler.squareList (3 * input.1)).map (fun c => (c,z))) :=
    Primrec.list_map (Theorem55Compiler.squareList_primrec.comp size)
      (Primrec.pair Primrec.snd (Primrec.const z))
  exact Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp
      (Primrec.list_append.comp (body 0) (body 1)) (body 2)) (cap (-1))) (cap 3)

end LeanTrominoes.TwoConnectedPolycubes.SpaceCompiler
