/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverNormalizedFamily

/-! # Distinctness of canonical normalized crossover blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

private def normalizedCrossoverLiteral
    {Variable : Type}
    (crossing : CrossingRecord)
    (literal : CrossoverVariable × Bool) :
    PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) :=
  ⟨⟨normalizedCrossoverAtom crossing literal.1⟩,
    (0, 0), literal.2⟩

private theorem normalizedCrossoverLiteral_injective
    {Variable : Type}
    (crossing : CrossingRecord) :
    Function.Injective
      (@normalizedCrossoverLiteral Variable crossing) := by
  rintro ⟨firstRole, firstValue⟩ ⟨secondRole, secondValue⟩ equal
  have atomEqual :
      normalizedCrossoverAtom (Variable := Variable) crossing firstRole =
        normalizedCrossoverAtom (Variable := Variable) crossing secondRole := by
    exact congrArg
      (fun literal :
        PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) =>
          literal.atom.original)
      equal
  have pairEqual :
      (crossing, firstRole) = (crossing, secondRole) :=
    (@normalizedCrossoverAtom_jointly_injective Variable) atomEqual
  apply Prod.ext
  · exact congrArg Prod.snd pairEqual
  · exact congrArg
      (fun literal :
        PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) =>
          literal.value)
      equal

private theorem crossoverFormula_indexedLiteralLists_nodup :
    (crossoverFormula.zipIdx.map fun taggedClause =>
      taggedClause.1.literals).Nodup := by
  native_decide

private theorem crossoverFormula_clauses_nonempty :
    ∀ clause ∈ crossoverFormula, clause.literals ≠ [] := by
  native_decide

/-- No fixed crossover clause repeats within one canonical normalized
block. -/
theorem canonicalNormalizedCrossoverBlock_nodup
    {Variable : Type}
    (crossing : CrossingRecord) :
    (canonicalNormalizedCrossoverBlock
      (Variable := Variable) crossing).Nodup := by
  have mappedNodup :=
    crossoverFormula_indexedLiteralLists_nodup.map
      ((normalizedCrossoverLiteral_injective
        (Variable := Variable) crossing).list_map)
  unfold canonicalNormalizedCrossoverBlock
    FormulaShapeCrossoverDirection.wrappedNormalizedClause
  change (crossoverFormula.zipIdx.map fun taggedClause =>
    taggedClause.1.literals.map
      (normalizedCrossoverLiteral
        (Variable := Variable) crossing)).Nodup
  exact mappedNodup

/-- A normalized crossover clause identifies its canonical crossing key, so
blocks attached to unequal keys are disjoint. -/
theorem canonicalNormalizedCrossoverBlock_disjoint
    {Variable : Type}
    {first second : CrossingRecord}
    (different : first ≠ second) :
    List.Disjoint
      (canonicalNormalizedCrossoverBlock
        (Variable := Variable) first)
      (canonicalNormalizedCrossoverBlock second) := by
  rw [List.disjoint_left]
  intro normalizedClause firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨firstTagged, firstTaggedMember, firstEqual⟩
  rcases List.mem_map.mp secondMember with
    ⟨secondTagged, secondTaggedMember, secondEqual⟩
  have clauseEqual :
      FormulaShapeCrossoverDirection.wrappedNormalizedClause
          (Variable := Variable) first firstTagged.1 =
        FormulaShapeCrossoverDirection.wrappedNormalizedClause
          second secondTagged.1 :=
    firstEqual.trans secondEqual.symm
  have firstNonempty :=
    crossoverFormula_clauses_nonempty firstTagged.1
      (List.fst_mem_of_mem_zipIdx firstTaggedMember)
  have secondNonempty :=
    crossoverFormula_clauses_nonempty secondTagged.1
      (List.fst_mem_of_mem_zipIdx secondTaggedMember)
  cases firstLiterals : firstTagged.1.literals with
  | nil =>
      exact (firstNonempty firstLiterals).elim
  | cons firstLiteral firstRest =>
      cases secondLiterals : secondTagged.1.literals with
      | nil =>
          exact (secondNonempty secondLiterals).elim
      | cons secondLiteral secondRest =>
          rcases firstLiteral with ⟨firstRole, firstValue⟩
          rcases secondLiteral with ⟨secondRole, secondValue⟩
          have literalEqual :
              normalizedCrossoverLiteral
                  (Variable := Variable) first
                  (firstRole, firstValue) =
                normalizedCrossoverLiteral second
                  (secondRole, secondValue) := by
            simpa [FormulaShapeCrossoverDirection.wrappedNormalizedClause,
              normalizedCrossoverLiteral,
              firstLiterals, secondLiterals] using
              congrArg List.head? clauseEqual
          have atomEqual :
              normalizedCrossoverAtom
                  (Variable := Variable) first firstRole =
                normalizedCrossoverAtom
                  (Variable := Variable) second secondRole := by
            exact congrArg
              (fun literal :
                PeriodicLiteral
                  (WrappedPeriodicPlanarSATVariable Variable) =>
                  literal.atom.original)
              literalEqual
          have pairEqual :
              (first, firstRole) = (second, secondRole) :=
            (@normalizedCrossoverAtom_jointly_injective Variable)
              atomEqual
          exact different (congrArg Prod.fst pairEqual)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
