/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryFamilyPresentation

/-! # Directness of packed final copied-clause queries -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing

namespace RetainedFinalCopiedSourceDirectionQuery

/-- A mixed source-direction query actually selects the finite direct atlas. -/
def IsDirect (query : RetainedFinalCopiedSourceDirectionQuery) : Prop :=
  ∃ direct, query = .direct direct

instance instDecidableIsDirect
    (query : RetainedFinalCopiedSourceDirectionQuery) :
    Decidable query.IsDirect := by
  cases query with
  | direct direct => exact isTrue ⟨direct, rfl⟩
  | fallback direction =>
      exact isFalse (by
        rintro ⟨direct, equality⟩
        cases equality)

end RetainedFinalCopiedSourceDirectionQuery

namespace RetainedFinalCopiedClauseQuery

/-- Every incidence field of a packed clause query is direct. -/
def AllDirect : RetainedFinalCopiedClauseQuery → Prop
  | .precomputed _ => False
  | .unary _ first => first.IsDirect
  | .binary _ first _ second => first.IsDirect ∧ second.IsDirect
  | .ternary _ first _ second _ third =>
      first.IsDirect ∧ second.IsDirect ∧ third.IsDirect

instance instDecidableAllDirect
    (query : RetainedFinalCopiedClauseQuery) :
    Decidable query.AllDirect := by
  cases query <;> simp only [AllDirect] <;> infer_instance

private theorem forall_mem_map_iff
    {Source Target : Type}
    (values : List Source) (emit : Source → Target)
    (property : Target → Prop) :
    (∀ item ∈ values.map emit, property item) ↔
      ∀ value ∈ values, property (emit value) := by
  constructor
  · intro all value valueMember
    exact all (emit value) (List.mem_map.mpr
      ⟨value, valueMember, rfl⟩)
  · intro all item itemMember
    rcases List.mem_map.mp itemMember with
      ⟨value, valueMember, rfl⟩
    exact all value valueMember

private theorem allDirect_ofList_iff
    (items : List
      (PeriodicCNF.UnaryProgramClauseProfile.LiteralProfile ×
        RetainedFinalCopiedSourceDirectionQuery))
    (nonempty : items ≠ [])
    (width : items.length ≤ 3) :
    (RetainedFinalCopiedClauseQuery.ofList items).AllDirect ↔
      ∀ item ∈ items, item.2.IsDirect := by
  rcases items with _ | ⟨first, rest⟩
  · contradiction
  rcases rest with _ | ⟨second, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList, AllDirect]
  rcases rest with _ | ⟨third, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    rcases second with ⟨secondProfile, secondQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList, AllDirect]
  rcases rest with _ | ⟨fourth, rest⟩
  · rcases first with ⟨firstProfile, firstQuery⟩
    rcases second with ⟨secondProfile, secondQuery⟩
    rcases third with ⟨thirdProfile, thirdQuery⟩
    simp [RetainedFinalCopiedClauseQuery.ofList, AllDirect]
  · simp only [List.length_cons] at width
    omega

/-- Directness of an exact packed nonempty width-three clause query is
equivalent to directness of every source-direction field before packing. -/
theorem allDirect_queryOfLiterals_iff
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex : Nat)
    (literals :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (nonempty : literals ≠ [])
    (width : literals.length ≤ 3) :
    (retainedFinalCopiedClauseQueryOfLiterals
        formula clauseIndex literals).AllDirect ↔
      ∀ taggedLiteral ∈ literals.zipIdx,
        (retainedFinalCopiedSourceDirectionQuery
          formula clauseIndex taggedLiteral.2 taggedLiteral.1).IsDirect := by
  let emit := fun taggedLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
    (PeriodicCNF.FormulaShapeDirectionOrdering.literalProfile
        taggedLiteral.1,
      retainedFinalCopiedSourceDirectionQuery
        formula clauseIndex taggedLiteral.2 taggedLiteral.1)
  have mappedNonempty : literals.zipIdx.map emit ≠ [] := by
    intro mappedNil
    have lengths := congrArg List.length mappedNil
    simp only [List.length_map, List.length_zipIdx,
      List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp lengths)
  have mappedWidth : (literals.zipIdx.map emit).length ≤ 3 := by
    simpa only [List.length_map, List.length_zipIdx] using width
  have emitEq :
      (fun taggedLiteral :
          PeriodicLiteral
            (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
        (PeriodicCNF.FormulaShapeDirectionOrdering.literalProfile
            taggedLiteral.1,
          retainedFinalCopiedSourceDirectionQuery
            formula clauseIndex taggedLiteral.2 taggedLiteral.1)) =
        emit := rfl
  unfold retainedFinalCopiedClauseQueryOfLiterals
  rw [emitEq]
  rw [allDirect_ofList_iff _ mappedNonempty mappedWidth,
    forall_mem_map_iff]

end RetainedFinalCopiedClauseQuery

/-- An emitted source-direction query is direct exactly when the underlying
final route-choice lookup succeeds. -/
theorem retainedFinalCopiedSourceDirectionQuery_isDirect_iff
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (clauseIndex literalIndex : Nat)
    (literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)) :
    (retainedFinalCopiedSourceDirectionQuery
        formula clauseIndex literalIndex literal).IsDirect ↔
      ∃ choice,
        retainedFinalDirectSourceRouteChoice?
            formula clauseIndex literalIndex =
          some choice := by
  unfold retainedFinalCopiedSourceDirectionQuery
  cases choiceLookup : retainedFinalDirectSourceRouteChoice?
      formula clauseIndex literalIndex with
  | none => simp [RetainedFinalCopiedSourceDirectionQuery.IsDirect]
  | some choice =>
      simp [RetainedFinalCopiedSourceDirectionQuery.IsDirect]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
