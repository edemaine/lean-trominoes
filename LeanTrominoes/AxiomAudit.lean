/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.FiniteTrominoRegionNPComplete
import LeanTrominoes.FiniteTrominoCompletionNPComplete
import LeanTrominoes.CompletionCompleteness
import LeanTrominoes.CompletionStripHardness
import LeanTrominoes.TwoConnectedPolycubesSpaceProof
import LeanTrominoes.TwoConnectedPolycubesSlabsProof
import LeanTrominoes.Theorem52Proof
import LeanTrominoes.Theorem55Proof
import LeanTrominoes.Theorem55StripProof
import LeanTrominoes.ThreeTranslationProof
import LeanTrominoes.ThreeTranslationPolycubesProof
import Lean.Util.CollectAxioms

/-!
# Axiom regression checks for the main completeness theorems

All finite certificates are checked by Lean's kernel. These checks reject
any assumption beyond the three standard Lean axioms, including native
execution certificates and unfinished proofs.
-/

open Lean Elab Command in
run_cmd do
  for name in [``LeanTrominoes.Tromino.FiniteCoordinateColumns.region_npComplete,
      ``LeanTrominoes.Tromino.FiniteCoordinateColumns.completion_npComplete,
      ``LeanTrominoes.PeriodicTrominoPrefill.planeProblem_coREComplete,
      ``LeanTrominoes.PeriodicStripTrominoPrefill.problem_PSPACEComplete,
      ``LeanTrominoes.TwoConnectedPolycubes.spaceProved,
      ``LeanTrominoes.TwoConnectedPolycubes.slabsProved,
      ``LeanTrominoes.ThreeTranslationPolyominoes.proved,
      ``LeanTrominoes.ThreeTranslationPolycubes.proved,
      ``LeanTrominoes.Theorem52.proved,
      ``LeanTrominoes.Theorem55.planeProved,
      ``LeanTrominoes.Theorem55.stripProved] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do
      throwError "{name} depends on unexpected axioms: {extra}"
