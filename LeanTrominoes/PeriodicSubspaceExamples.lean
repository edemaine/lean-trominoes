/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceStripTilingMembership
import LeanTrominoes.PeriodicSubspaceTilingCoRE

/-! # Regressions for arbitrary periodic subspace footprints -/
namespace LeanTrominoes.PeriodicSubspaceTiling.Examples
open Strip

/-- Empty targets and empty palettes are accepted, including irrelevant
mandatory kinds with empty footprints. -/
example : FieldPredicate.check (0,([],[]),[1000000]) 0 0=true := by decide

/-- A target cell with no covering placement is rejected. -/
example : FieldPredicate.check (0,([0],[]),[]) 0 0=false := by decide

/-- Duplicate cell records of the same placement are harmless. -/
example : FieldPredicate.check (0,([0],[((7,0),0),((7,0),0)]),[]) 1 1=true := by decide

/-- Distinct selected placements covering one cell violate exact cover. -/
example : FieldPredicate.check (0,([0],[((7,0),0),((8,0),0)]),[]) 3 3=false := by decide

/-- Sparse kind names do not enlarge the bit window. -/
example : bits ([0],[((1000000,0),0)]) 0=1 := rfl

/-- A variable footprint may cover several representatives; no connectivity
or fixed palette assumption occurs in the transition test. -/
example : FieldPredicate.check (0,([0,99],[((7,0),0),((7,99),0)]),[7]) 1 1=true := by decide

/-- Both signs of a displacement at the bounding-box boundary are handled. -/
example : FieldPredicate.check (1,([0,99],[((7,0),-1),((7,99),1)]),[7]) 63 63=true := by decide

/-- Overlap agreement is required when consecutive windows share columns. -/
example : FieldPredicate.check (1,([0],[((7,0),0)]),[]) 7 0=false := by decide

/-- Prescribed overlapping orbits cannot be completed. -/
example : FieldPredicate.check (0,([0],[((7,0),0),((8,0),0)]),[7,8]) 1 1=false := by decide

/-- A prescribed footprint outside the target is rejected. -/
example : FieldPredicate.check (0,([],[((7,0),0)]),[7]) 1 1=false := by decide

/-- Offsets exceeding the declared bounding box are rejected. -/
example : FieldPredicate.check (0,([0],[((7,0),1)]),[]) 1 1=false := by decide

example (input : Strip.Input) : Encoding.decode (Encoding.fields input)=some input :=
  Encoding.decode_fields input

example (p : Polynomial Nat) : Complexity.InPSPACE (PolynomialBoxEncoding.finEncoding p)
    (fun input => Problem input.val) := completion_inPSPACE p

example (p : Polynomial Nat) : Complexity.InPSPACE (PolynomialBoxTilingEncoding.finEncoding p)
    (fun input => TilingProblem input.val) := tiling_inPSPACE p

example : LeanWang.CoREPred (@Tileable (Fin 3 → Int) _) := lattice_tileable_coRE 3

end LeanTrominoes.PeriodicSubspaceTiling.Examples
