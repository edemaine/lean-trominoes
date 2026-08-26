/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates

/-! # Packing direct final incidence queries into clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicCNF
open PeriodicOrthocrossing

/-- If the finite literal profiles of a nonempty clause agree with a
directed profile and its incidence queries all select one direct atlas kind
at their presentation indices, packing the incidence queries gives exactly
the stable direct clause query for that profile. -/
theorem retainedFinalCopiedClauseQueryOfLiterals_eq_directOfProfile
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (kind : RetainedDirectClauseKind)
    (profile : FormulaShapeDirectionOrdering.DirectedClauseProfile)
    (literalsNonempty : literals ≠ [])
    (profilesEq :
      profile.taggedLiterals.map Prod.fst =
        literals.map FormulaShapeDirectionOrdering.literalProfile)
    (directionQueries :
      ∀ taggedLiteral ∈ literals.zipIdx,
        ∃ query : RetainedDirectSourceNormalizedDirectionQuery,
          retainedFinalCopiedSourceDirectionQuery
              formula clauseIndex taggedLiteral.2 taggedLiteral.1 =
            .direct query ∧
          query.kind = kind ∧
          query.literalIndex.val = taggedLiteral.2) :
    retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex literals =
      RetainedFinalCopiedClauseQuery.directOfProfile kind profile := by
  cases profile with
  | unary first firstDirection =>
      have literalsLength : literals.length = 1 := by
        simpa only [
          FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
          List.map_cons, List.map_nil, List.length_cons, List.length_nil,
          List.length_map]
          using congrArg List.length profilesEq.symm
      cases literals with
      | nil => contradiction
      | cons firstLiteral rest =>
        cases rest with
        | cons secondLiteral tail => simp at literalsLength
        | nil =>
          have firstMember :
              (firstLiteral, 0) ∈ [firstLiteral].zipIdx := by simp
          rcases directionQueries
              (firstLiteral, 0) firstMember with
            ⟨firstQuery, firstQueryEq, firstKindEq, firstIndexEq⟩
          rcases firstQuery with ⟨firstKind, firstIndex⟩
          simp only at firstKindEq firstIndexEq
          subst firstKind
          have firstIndexValueEq : firstIndex = (0 : Fin 3) :=
            Fin.ext firstIndexEq
          subst firstIndex
          simp only [
            FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
            List.map_cons, List.map_nil, List.cons.injEq]
              at profilesEq
          have firstEq := profilesEq.1
          subst first
          simp [retainedFinalCopiedClauseQueryOfLiterals,
            RetainedFinalCopiedClauseQuery.ofList,
            RetainedFinalCopiedClauseQuery.directOfProfile,
            firstQueryEq]
  | binary first firstDirection second secondDirection =>
      have literalsLength : literals.length = 2 := by
        simpa only [
          FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
          List.map_cons, List.map_nil, List.length_cons, List.length_nil,
          List.length_map]
          using congrArg List.length profilesEq.symm
      rcases List.length_eq_two.mp literalsLength with
        ⟨firstLiteral, secondLiteral, rfl⟩
      have firstMember :
          (firstLiteral, 0) ∈ [firstLiteral, secondLiteral].zipIdx := by
        simp
      have secondMember :
          (secondLiteral, 1) ∈ [firstLiteral, secondLiteral].zipIdx := by
        simp
      rcases directionQueries
          (firstLiteral, 0) firstMember with
        ⟨firstQuery, firstQueryEq, firstKindEq, firstIndexEq⟩
      rcases directionQueries
          (secondLiteral, 1) secondMember with
        ⟨secondQuery, secondQueryEq, secondKindEq, secondIndexEq⟩
      rcases firstQuery with ⟨firstKind, firstIndex⟩
      rcases secondQuery with ⟨secondKind, secondIndex⟩
      simp only at firstKindEq firstIndexEq secondKindEq secondIndexEq
      subst firstKind
      subst secondKind
      have firstIndexValueEq : firstIndex = (0 : Fin 3) :=
        Fin.ext firstIndexEq
      have secondIndexValueEq : secondIndex = (1 : Fin 3) :=
        Fin.ext secondIndexEq
      subst firstIndex
      subst secondIndex
      simp only [
        FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
        List.map_cons, List.map_nil, List.cons.injEq]
          at profilesEq
      rcases profilesEq with ⟨firstEq, secondEq, _⟩
      subst first
      subst second
      simp [retainedFinalCopiedClauseQueryOfLiterals,
        RetainedFinalCopiedClauseQuery.ofList,
        RetainedFinalCopiedClauseQuery.directOfProfile,
        firstQueryEq, secondQueryEq]
  | ternary first firstDirection second secondDirection third thirdDirection =>
      have literalsLength : literals.length = 3 := by
        simpa only [
          FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
          List.map_cons, List.map_nil, List.length_cons, List.length_nil,
          List.length_map]
          using congrArg List.length profilesEq.symm
      rcases List.length_eq_three.mp literalsLength with
        ⟨firstLiteral, secondLiteral, thirdLiteral, rfl⟩
      have firstMember :
          (firstLiteral, 0) ∈
            [firstLiteral, secondLiteral, thirdLiteral].zipIdx := by
        simp
      have secondMember :
          (secondLiteral, 1) ∈
            [firstLiteral, secondLiteral, thirdLiteral].zipIdx := by
        simp
      have thirdMember :
          (thirdLiteral, 2) ∈
            [firstLiteral, secondLiteral, thirdLiteral].zipIdx := by
        simp
      rcases directionQueries
          (firstLiteral, 0) firstMember with
        ⟨firstQuery, firstQueryEq, firstKindEq, firstIndexEq⟩
      rcases directionQueries
          (secondLiteral, 1) secondMember with
        ⟨secondQuery, secondQueryEq, secondKindEq, secondIndexEq⟩
      rcases directionQueries
          (thirdLiteral, 2) thirdMember with
        ⟨thirdQuery, thirdQueryEq, thirdKindEq, thirdIndexEq⟩
      rcases firstQuery with ⟨firstKind, firstIndex⟩
      rcases secondQuery with ⟨secondKind, secondIndex⟩
      rcases thirdQuery with ⟨thirdKind, thirdIndex⟩
      simp only at firstKindEq firstIndexEq secondKindEq secondIndexEq
      simp only at thirdKindEq thirdIndexEq
      subst firstKind
      subst secondKind
      subst thirdKind
      have firstIndexValueEq : firstIndex = (0 : Fin 3) :=
        Fin.ext firstIndexEq
      have secondIndexValueEq : secondIndex = (1 : Fin 3) :=
        Fin.ext secondIndexEq
      have thirdIndexValueEq : thirdIndex = (2 : Fin 3) :=
        Fin.ext thirdIndexEq
      subst firstIndex
      subst secondIndex
      subst thirdIndex
      simp only [
        FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals,
        List.map_cons, List.map_nil, List.cons.injEq]
          at profilesEq
      rcases profilesEq with ⟨firstEq, secondEq, thirdEq, _⟩
      subst first
      subst second
      subst third
      simp [retainedFinalCopiedClauseQueryOfLiterals,
        RetainedFinalCopiedClauseQuery.ofList,
        RetainedFinalCopiedClauseQuery.directOfProfile,
        firstQueryEq, secondQueryEq, thirdQueryEq]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
