import LeanTrominoes.PlanarOneInThree
import LeanTrominoes.PeriodicOneInThreeOccurrences

/-!
# Occurrence bounds for the positioned exact-one reduction

The Figure 9 layout changes only clause positions, not the literal
presentation of the already verified periodic exact-one gadget.  This file
connects the finite embedded occurrence list to that periodic presentation
and transfers its three-occurrence theorem.
-/

namespace LeanTrominoes
namespace PlanarOneInThree

open PlanarThreeSAT

/-- Variable occurrences of a finite embedded formula, in presentation
order. -/
def variableOccurrences {Variable : Type*}
    (formula : List (EmbeddedClause Variable)) : List Variable :=
  formula.flatMap fun clause => clause.literals.map Prod.fst

/-- Every variable occurs at most `bound` times in the finite embedded
presentation. -/
def OccurrencesAtMost {Variable : Type*}
    [BEq Variable] [LawfulBEq Variable]
    (bound : Nat) (formula : List (EmbeddedClause Variable)) : Prop :=
  ∀ atom, (variableOccurrences formula).count atom ≤ bound

/-- Regard a finite embedded disjunctive formula as a zero-offset periodic
formula. -/
def zeroOffsetFormula {Variable : Type*}
    (source : List (EmbeddedClause Variable)) :
    PeriodicCNF Variable :=
  ⟨source.map zeroOffsetClause⟩

@[simp]
theorem zeroOffsetFormula_variableOccurrences {Variable : Type*}
    (source : List (EmbeddedClause Variable)) :
    PeriodicCNF.variableOccurrences (zeroOffsetFormula source) =
      variableOccurrences source := by
  simp [PeriodicCNF.variableOccurrences, zeroOffsetFormula,
    variableOccurrences, zeroOffsetClause, List.flatMap_map,
    List.map_map, Function.comp_def]

/-- Clause positions and generated-clause indices do not affect the
occurrence list of one local gadget. -/
theorem clauseGadget_variableOccurrences {Variable : Type*}
    (clauseIndex : Nat) (source : EmbeddedClause Variable) :
    variableOccurrences (clauseGadget clauseIndex source) =
      PeriodicCNF.variableOccurrences
        ⟨PeriodicOneInThree.clauseClauses
          clauseIndex (zeroOffsetClause source)⟩ := by
  let generated :=
    PeriodicOneInThree.clauseClauses
      clauseIndex (zeroOffsetClause source)
  calc
    variableOccurrences (clauseGadget clauseIndex source) =
        generated.zipIdx.flatMap fun taggedClause =>
          taggedClause.1.map PeriodicLiteral.atom := by
            simp [variableOccurrences, clauseGadget,
              embedGeneratedClause, generated, List.flatMap_map,
              List.map_map, Function.comp_def]
    _ = (generated.zipIdx.map Prod.fst).flatMap
          (fun clause => clause.map PeriodicLiteral.atom) := by
            rw [List.flatMap_map]
    _ = generated.flatMap
          (fun clause => clause.map PeriodicLiteral.atom) := by
            rw [List.zipIdx_map_fst]
    _ = PeriodicCNF.variableOccurrences
          ⟨PeriodicOneInThree.clauseClauses
            clauseIndex (zeroOffsetClause source)⟩ := by
            rfl

/-- The positioned target has exactly the same variable-occurrence list as
the underlying periodic exact-one reduction. -/
theorem formula_variableOccurrences {Variable : Type*}
    (source : List (EmbeddedClause Variable)) :
    variableOccurrences (formula source) =
      PeriodicCNF.variableOccurrences
        (PeriodicOneInThree.formula (zeroOffsetFormula source)) := by
  unfold formula
  rw [variableOccurrences, PeriodicCNF.variableOccurrences,
    PeriodicOneInThree.formula]
  rw [List.flatMap_assoc]
  change
    source.zipIdx.flatMap (fun taggedSource =>
      variableOccurrences
        (clauseGadget taggedSource.2 taggedSource.1)) =
      _
  simp_rw [clauseGadget_variableOccurrences]
  simp [zeroOffsetFormula, List.zipIdx_map,
    PeriodicCNF.variableOccurrences, List.flatMap_assoc,
    List.flatMap_map]

/-- The positioned Figure 9 replacement preserves the three-occurrence
bound: original occurrences are copied once and every auxiliary occurs at
most twice. -/
theorem formula_occurrencesAtMostThree {Variable : Type*}
    [DecidableEq Variable]
    (source : List (EmbeddedClause Variable))
    (width :
      ∀ clause ∈ source, clause.literals.length ≤ 3)
    (occurrences : OccurrencesAtMost 3 source) :
    OccurrencesAtMost 3 (formula source) := by
  let periodicSource := zeroOffsetFormula source
  have periodicWidth : periodicSource.WidthAtMost 3 := by
    intro clause clauseMem
    rcases List.mem_map.mp clauseMem with
      ⟨embeddedClause, embeddedMem, clauseEq⟩
    subst clause
    simpa [zeroOffsetClause, PeriodicClause.WidthAtMost] using
      width embeddedClause embeddedMem
  have periodicOccurrences : periodicSource.OccurrencesAtMost 3 := by
    intro atom
    rw [zeroOffsetFormula_variableOccurrences]
    exact occurrences atom
  have generated :=
    PeriodicOneInThree.formula_occurrencesAtMostThree
      periodicSource periodicWidth periodicOccurrences
  intro atom
  rw [formula_variableOccurrences]
  exact generated atom

end PlanarOneInThree
end LeanTrominoes
