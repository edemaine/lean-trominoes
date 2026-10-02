/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicSubspaceGeometry
import LeanTrominoes.PeriodicSubspaceStripTilingMembership

/-! # Lemma 5.1: general periodic subspace tiling and completion membership

Input footprints are finite cell records in fundamental-domain coordinates:
tile-placement orbit, representative cell, and lattice displacement. Listing
every prototile/orientation at each allowed representative anchor produces
this presentation. No palette-size, connectedness, or periodic-solution
assumption is made. `tileable_iff_realized` identifies the record semantics
with geometric exact cover in a fundamental-domain chart.

General membership is co-r.e. in every dimension, even without a bounding-box
restriction. Strip membership is PSPACE for every fixed polynomial bounding
box in the native binary input length, for both tiling and completion.
-/
namespace LeanTrominoes.PeriodicSubspaceTiling

theorem lemma51 (d : Nat) (p : Polynomial Nat) :
    LeanWang.CoREPred (@Tileable (Fin d → Int) _) ∧
    LeanWang.CoREPred (@Completable (Fin d → Int) _) ∧
    Complexity.InPSPACE (Strip.PolynomialBoxTilingEncoding.finEncoding p)
      (fun input => Strip.TilingProblem input.val) ∧
    Complexity.InPSPACE (Strip.PolynomialBoxEncoding.finEncoding p)
      (fun input => Strip.Problem input.val) :=
  ⟨lattice_tileable_coRE d,lattice_completable_coRE d,
    Strip.tiling_inPSPACE p,Strip.completion_inPSPACE p⟩

end LeanTrominoes.PeriodicSubspaceTiling
