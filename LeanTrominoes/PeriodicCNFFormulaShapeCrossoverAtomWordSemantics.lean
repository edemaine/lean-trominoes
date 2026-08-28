/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverDeduplication

/-! # Atom-word column of normalized crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Flattening one canonical normalized crossover block exposes the fixed
Figure 8(b) literal-role template, instantiated at the given crossing. -/
theorem canonicalNormalizedCrossoverBlock_atomWords
    {Variable : Type}
    (crossing : CrossingRecord)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    (canonicalNormalizedCrossoverBlock
        (Variable := Variable) crossing).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      crossoverFormula.flatMap fun clause =>
        clause.literals.map fun literal =>
          word ⟨normalizedCrossoverAtom crossing literal.1⟩ := by
  unfold canonicalNormalizedCrossoverBlock
    FormulaShapeCrossoverDirection.wrappedNormalizedClause
  rw [List.flatMap_map]
  simp only [List.map_map, Function.comp_def]
  conv_rhs =>
    rw [← List.zipIdx_map_fst 0 crossoverFormula,
      List.flatMap_map]

/-- The deduplicated crossover family has one fixed atom-role block for each
canonical crossing, in the exact canonical-halo presentation order. -/
theorem crossoverMetadataNormalizedClauses_dedup_atomWords
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (word : WrappedPeriodicPlanarSATVariable Variable → List Bool) :
    ((crossoverMetadataNormalizedClauses source).dedup).flatMap
        (fun clause => clause.map fun literal => word literal.atom) =
      (canonicalizedCrossingHalo source.incidenceGraph).flatMap fun crossing =>
        crossoverFormula.flatMap fun clause =>
          clause.literals.map fun literal =>
            word ⟨normalizedCrossoverAtom crossing literal.1⟩ := by
  rw [crossoverMetadataNormalizedClauses_dedup_eq
    source wellFormed degree isLocal, List.flatMap_assoc]
  apply List.flatMap_congr
  intro crossing _crossingMember
  exact canonicalNormalizedCrossoverBlock_atomWords crossing word

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
