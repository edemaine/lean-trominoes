import LeanTrominoes.PlanarThreeSATOcurrences
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization
import LeanTrominoes.PeriodicCNFDeduplication

/-!
# Normalizing periodic equality-link families

Finite neighboring-block constructions often list the same equality link at
several cell translations.  This file normalizes each endpoint to a
protovariable and offset, subtracts the first endpoint's offset, and identifies
the resulting link by its two protovariables and relative offset.

After clause deduplication, the normalized equality formula is a permutation
of the two implication clauses for the deduplicated normalized links.
Consequently its variable-occurrence degree is exactly twice the endpoint
degree of that finite normalized-link list.
-/

namespace LeanTrominoes
namespace PeriodicEquality

open PlanarThreeSAT

structure NormalizedLink (Variable : Type*) where
  first : Variable
  second : Variable
  relativeOffset : Cell
  deriving DecidableEq, Repr

def normalizeLink {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (link : EqualityLink Source) : NormalizedLink Target where
  first := (normalize link.first).1
  second := (normalize link.second).1
  relativeOffset :=
    Cell.sub (normalize link.second).2 (normalize link.first).2

def periodicizeLiteral {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (literal : Source × Bool) : PeriodicLiteral Target :=
  ⟨(normalize literal.1).1, (normalize literal.1).2, literal.2⟩

def periodicizeClause {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (clause : EmbeddedClause Source) : PeriodicClause Target :=
  clause.literals.map (periodicizeLiteral normalize)

def normalizedClause {Variable : Type*}
    (input : NormalizedLink Variable × Bool) :
    PeriodicClause Variable :=
  if input.2 then
    [⟨input.1.first, (0, 0), true⟩,
      ⟨input.1.second, input.1.relativeOffset, false⟩]
  else
    [⟨input.1.first, (0, 0), false⟩,
      ⟨input.1.second, input.1.relativeOffset, true⟩]

theorem normalizedClause_injective
    {Variable : Type*} :
    Function.Injective (@normalizedClause Variable) := by
  rintro ⟨⟨firstFirst, firstSecond, firstOffset⟩, firstPolarity⟩
    ⟨⟨secondFirst, secondSecond, secondOffset⟩, secondPolarity⟩
    equal
  cases firstPolarity <;> cases secondPolarity <;>
    simp [normalizedClause] at equal ⊢
  all_goals exact equal

def normalizedFormulaClauses {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source)) :
    List (PeriodicClause Target) :=
  ((equalityFamily links).map (periodicizeClause normalize)).map
    PeriodicClause.anchorNormalize

theorem equalityInstance_normalized
    {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (link : EqualityLink Source) :
    ((equalityInstance link.first link.second link.positions).map
      (periodicizeClause normalize)).map
        PeriodicClause.anchorNormalize =
      (([normalizeLink normalize link].product [true, false]).map
        normalizedClause) := by
  rcases normalize link.first with ⟨first, ⟨firstX, firstY⟩⟩
  rcases normalize link.second with ⟨second, ⟨secondX, secondY⟩⟩
  simp [equalityInstance, periodicizeClause, periodicizeLiteral,
    PeriodicClause.anchorNormalize, PeriodicLiteral.anchorNormalize,
    PeriodicCNF.clauseAnchor, normalizeLink, normalizedClause,
    Cell.sub, List.product]

theorem normalizedFormulaClauses_eq
    {Source Target : Type*}
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source)) :
    normalizedFormulaClauses normalize links =
      ((links.map (normalizeLink normalize)).product [true, false]).map
        normalizedClause := by
  unfold normalizedFormulaClauses equalityFamily
  induction links with
  | nil =>
      rfl
  | cons link links induction =>
      rw [List.flatMap_cons, List.map_append, List.map_append]
      rw [equalityInstance_normalized]
      rw [show
        (List.map PeriodicClause.anchorNormalize
          (List.map (periodicizeClause normalize)
            (List.flatMap
              (fun link =>
                equalityInstance link.first link.second link.positions)
              links))) =
            ((links.map (normalizeLink normalize)).product
              [true, false]).map normalizedClause by
        exact induction]
      simp [List.product]

theorem normalizedClauseKeys_nodup
    {Variable : Type*} [DecidableEq Variable]
    (links : List (NormalizedLink Variable))
    (linksNodup : links.Nodup) :
    (links.product [true, false]).Nodup := by
  exact linksNodup.product (by decide)

theorem normalizedClauses_nodup
    {Variable : Type*} [DecidableEq Variable]
    (links : List (NormalizedLink Variable))
    (linksNodup : links.Nodup) :
    ((links.product [true, false]).map normalizedClause).Nodup := by
  exact (normalizedClauseKeys_nodup links linksNodup).map
    normalizedClause_injective

theorem dedup_normalizedFormulaClauses_perm
    {Source Target : Type*} [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source)) :
    (normalizedFormulaClauses normalize links).dedup.Perm
      ((((links.map (normalizeLink normalize)).dedup).product
        [true, false]).map normalizedClause) := by
  rw [normalizedFormulaClauses_eq]
  apply (List.perm_ext_iff_of_nodup
    (List.nodup_dedup _)
    (normalizedClauses_nodup _
      (List.nodup_dedup _))).mpr
  intro clause
  simp [List.product]

def normalizedLinkEndpoints {Variable : Type*}
    (links : List (NormalizedLink Variable)) : List Variable :=
  links.flatMap fun link => [link.first, link.second]

theorem normalizedClauses_occurrence_count
    {Variable : Type*} [DecidableEq Variable]
    (links : List (NormalizedLink Variable))
    (atom : Variable) :
    (PeriodicCNF.variableOccurrences
      ⟨(links.product [true, false]).map normalizedClause⟩).count atom =
        2 * (normalizedLinkEndpoints links).count atom := by
  unfold PeriodicCNF.variableOccurrences normalizedLinkEndpoints
  induction links with
  | nil =>
      simp [List.product]
  | cons link links induction =>
      simp only [List.product, List.flatMap_cons, List.map_append,
        List.flatMap_append, List.count_append]
      have tailCount :
          (List.flatMap
            (fun clause => clause.map PeriodicLiteral.atom)
            ((List.flatMap
              (fun link =>
                [true, false].map (Prod.mk link))
              links).map normalizedClause)).count atom =
            2 *
              ((List.flatMap
                (fun link : NormalizedLink Variable =>
                  [link.first, link.second]) links).count atom) := by
        simpa [PeriodicCNF.variableOccurrences, List.product]
          using induction
      rw [tailCount]
      rcases link with ⟨first, second, offset⟩
      by_cases firstEq : first = atom <;>
        by_cases secondEq : second = atom <;>
          simp [normalizedClause, firstEq, secondEq] <;>
          omega

def deduplicatedNormalizedFormula
    {Source Target : Type*} [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source)) :
    PeriodicCNF Target :=
  ⟨(normalizedFormulaClauses normalize links).dedup⟩

theorem deduplicatedNormalizedFormula_occurrence_count
    {Source Target : Type*} [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source))
    (atom : Target) :
    (deduplicatedNormalizedFormula normalize links).variableOccurrences.count
        atom =
      2 * (normalizedLinkEndpoints
        ((links.map (normalizeLink normalize)).dedup)).count atom := by
  have clausesPerm :=
    dedup_normalizedFormulaClauses_perm normalize links
  have occurrencesPerm :
      (deduplicatedNormalizedFormula normalize links).variableOccurrences.Perm
        (PeriodicCNF.variableOccurrences
          ⟨((((links.map (normalizeLink normalize)).dedup).product
            [true, false]).map normalizedClause)⟩) := by
    exact clausesPerm.flatMap fun clause _ =>
      List.Perm.refl (clause.map PeriodicLiteral.atom)
  rw [occurrencesPerm.count atom]
  exact normalizedClauses_occurrence_count
    ((links.map (normalizeLink normalize)).dedup) atom

theorem deduplicatedNormalizedFormula_occurrencesAtMost
    {Source Target : Type*} [DecidableEq Target]
    (normalize : Source → Target × Cell)
    (links : List (EqualityLink Source))
    (degree bound : Nat)
    (boundEq : bound = 2 * degree)
    (endpointDegree :
      ∀ atom,
        (normalizedLinkEndpoints
          ((links.map (normalizeLink normalize)).dedup)).count atom ≤
            degree) :
    (deduplicatedNormalizedFormula normalize links).OccurrencesAtMost
      bound := by
  intro atom
  rw [deduplicatedNormalizedFormula_occurrence_count]
  rw [boundEq]
  exact Nat.mul_le_mul_left 2 (endpointDegree atom)

end PeriodicEquality
end LeanTrominoes
