/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TwoConnectedPolycubesSlabGeometry
import LeanTrominoes.Theorem55CompilerComputability

/-! # Executable, primitive-recursive compilation of the connected slab tile -/

namespace LeanTrominoes.TwoConnectedPolycubes.SlabCompiler

abbrev Input := Theorem55Compiler.Input

def compile (input : Input) : List Voxel :=
  (Theorem55Compiler.compile input).map (fun c => (c, 0)) ++
    (Theorem55Compiler.squareList (3 * input.1)).map (fun c => (c, 1))

theorem layer_toFinset (cells : List Cell) (z : Int) :
    (cells.map (fun c => (c, z))).toFinset = Polycube.extrude cells.toFinset {z} := by
  ext c
  simp [Prod.ext_iff, Polycube.mem_extrude, eq_comm]

theorem compile_source {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    (compile (Theorem55Compiler.sourceInput presentation)).toFinset =
      KeyedPeriodicComplement.slabTile (3 * Theorem55Source.period presentation)
        (Theorem55Source.holes presentation) := by
  simp only [compile, List.toFinset_append, layer_toFinset, Theorem55Compiler.compile_source,
    Theorem55Compiler.squareList_toFinset]
  rfl

theorem compile_source_correct {problem : PeriodicThreeDM} (presentation : problem.PlanarPresentation) :
    slabTwoProblem (compile (Theorem55Compiler.sourceInput presentation)) ↔
      Tromino.I.Tileable (presentation.normalizedOrthogonalDrawing.periodicRegion .I).carrier := by
  have large := Theorem55Source.period_large presentation
  exact (slabTwoProblem_iff_of_mask (n := 3 * Theorem55Source.period presentation)
    (by omega) (by omega) (Theorem55Source.holes presentation)
    (Theorem55Source.holes_admissible presentation) (Theorem55Source.region presentation)
    (Theorem55Source.holes_carrier presentation) _ (compile_source presentation)).trans
      (Theorem55Source.tileable_iff presentation)

theorem compile_primrec : Primrec compile := by
  have size : Primrec (fun input : Input => 3 * input.1) :=
    Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst
  have lower : Primrec (fun input : Input =>
      (Theorem55Compiler.compile input).map (fun c => (c, (0 : Int)))) :=
    Primrec.list_map Theorem55Compiler.compile_primrec
      (Primrec.pair Primrec.snd (Primrec.const 0))
  have upper : Primrec (fun input : Input =>
      (Theorem55Compiler.squareList (3 * input.1)).map (fun c => (c, (1 : Int)))) :=
    Primrec.list_map (Theorem55Compiler.squareList_primrec.comp size)
      (Primrec.pair Primrec.snd (Primrec.const 1))
  exact Primrec.list_append.comp lower upper

end LeanTrominoes.TwoConnectedPolycubes.SlabCompiler
