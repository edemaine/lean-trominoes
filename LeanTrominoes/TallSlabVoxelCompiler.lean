/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TallSlabPlaneCompiler
import LeanTrominoes.TwoConnectedPolycubesTallSlabGeometry

/-! # An explicit primitive-recursive list of the taller-slab tile's voxels -/

namespace LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler

open KeyedPeriodicComplement

def layers (lo hi : Nat) : List Int :=
  ((List.range hi).filter (fun z => decide (lo ≤ z))).map Int.ofNat

def extrudeList (cells : List Cell) (zs : List Int) : List Voxel := cells.product zs

def compile (height : Nat) (input : Input) : List Voxel :=
  extrudeList (planeCompile height input) (layers 0 (slabBodyHeight height)) ++
    extrudeList (Theorem55Compiler.squareList (period height input)) (layers (slabBodyHeight height) height)

theorem layers_toFinset (lo hi : Nat) : (layers lo hi).toFinset = Finset.Ico (lo : Int) hi := by
  ext z
  simp only [layers,List.mem_toFinset,List.mem_map,List.mem_filter,List.mem_range,
    decide_eq_true_eq,Finset.mem_Ico]
  constructor
  · rintro ⟨i,⟨hhi,hlo⟩,rfl⟩
    change (lo : Int) ≤ (i : Int) ∧ (i : Int) < hi
    omega
  · intro h
    exact ⟨z.toNat,⟨by omega,by omega⟩,by change (z.toNat : Int) = z; omega⟩

theorem extrudeList_toFinset (cells : List Cell) (zs : List Int) :
    (extrudeList cells zs).toFinset = Polycube.extrude cells.toFinset zs.toFinset := by
  ext c
  simp [extrudeList,Polycube.extrude,List.product,List.mem_flatMap,Prod.ext_iff]

theorem compile_source (height : Nat) {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    (compile height (Theorem55Compiler.sourceInput presentation)).toFinset =
      tallSlabTile height ((height+1)*(3*Theorem55Source.period presentation))
        (repeatMask (height+1) (3*Theorem55Source.period presentation) (Theorem55Source.holes presentation)) := by
  simp only [compile,List.toFinset_append,extrudeList_toFinset,layers_toFinset,
    planeCompile_eq_tile,compiledHoles_source,Theorem55Compiler.squareList_toFinset]
  rfl

private theorem extrudeList_primrec (zs : List Int) {f : Input → List Cell} (hf : Primrec f) :
    Primrec (fun a => extrudeList (f a) zs) := by
  have rows : Primrec (fun a : Input × Cell => zs.map (fun z => (a.2,z))) :=
    Primrec.list_map (Primrec.const zs) (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact Primrec.list_flatMap hf rows

theorem compile_primrec (height : Nat) : Primrec (compile height) :=
  Primrec.list_append.comp
    (extrudeList_primrec _ (planeCompile_primrec height))
    (extrudeList_primrec _ (Theorem55Compiler.squareList_primrec.comp (period_primrec height)))

end LeanTrominoes.TwoConnectedPolycubes.TallSlabCompiler
