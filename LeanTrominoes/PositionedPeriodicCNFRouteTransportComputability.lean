import LeanTrominoes.PositionedPeriodicCNFComputability
import LeanTrominoes.PositionedPeriodicCNFDeduplicationRoutes

/-!
# Computability of positioned periodic-CNF route transport

This module proves that the two generic route reindexings used by the planar
hardness pipeline are primitive recursive.  Clause-anchor normalization maps
every route point by the source clause's physical anchor.  Clause-orbit
deduplication then selects the first source clause with the retained literal
list and applies the same normalization to that representative route.
-/

noncomputable section

namespace LeanTrominoes
namespace PositionedPeriodicCNF

set_option maxHeartbeats 1000000

private theorem clause_idxOf_decidableEq_eq
    {Variable : Type*} [DecidableEq Variable]
    (clause : PeriodicClause Variable)
    (clauses : List (PeriodicClause Variable)) :
    @List.idxOf (PeriodicClause Variable)
        instBEqOfDecidableEq clause clauses =
      clauses.idxOf clause := by
  induction clauses with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.idxOf_cons, Bool.cond_eq_ite, beq_iff_eq]
      rw [induction]

theorem representativeClauseIndex_primrec
    {Variable : Type*} [Primcodable Variable] [DecidableEq Variable] :
    Primrec fun input :
        PositionedPeriodicCNF Variable × PeriodicClause Variable =>
      input.1.representativeClauseIndex input.2 := by
  have clauses : Primrec fun input :
      PositionedPeriodicCNF Variable × PeriodicClause Variable =>
      input.1.erase.clauses :=
    PeriodicCNF.equivData_primrec.comp
      (erase_primrec.comp Primrec.fst)
  exact (Primrec.list_idxOf.comp Primrec.snd clauses).of_eq
    fun input => clause_idxOf_decidableEq_eq
      input.2 input.1.erase.clauses

/-- Representative-indexed lookup into a primitive-recursive auxiliary list
is primitive recursive. -/
theorem representativeItem?_primrec
    {Input Variable Item : Type*}
    [Primcodable Input] [Primcodable Variable] [Primcodable Item]
    [DecidableEq Variable]
    (source finalSource : Input → PositionedPeriodicCNF Variable)
    (items : Input → List Item)
    (sourcePrimrec : Primrec source)
    (finalSourcePrimrec : Primrec finalSource)
    (itemsPrimrec : Primrec items) :
    Primrec fun input : Input × Nat =>
      representativeItem? (source input.1) (finalSource input.1)
        (items input.1) input.2 := by
  let Query := Input × Nat
  have finalClauses : Primrec fun input : Query =>
      (finalSource input.1).clauses :=
    clauses_primrec.comp (finalSourcePrimrec.comp Primrec.fst)
  have selected : Primrec fun input : Query =>
      (finalSource input.1).clauses[input.2]? :=
    Primrec.list_getElem?.comp finalClauses Primrec.snd
  have someClause : Primrec₂ fun (input : Query)
      (finalClause : PositionedPeriodicClause Variable) =>
      (items input.1)[
        (source input.1).representativeClauseIndex
          finalClause.literals]? := by
    let Combined := Query × PositionedPeriodicClause Variable
    have representativeIndex : Primrec fun input : Combined =>
        (source input.1.1).representativeClauseIndex
          input.2.literals :=
      representativeClauseIndex_primrec.comp
        (Primrec.pair
          (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd))
    exact Primrec.list_getElem?.comp
      (itemsPrimrec.comp (Primrec.fst.comp Primrec.fst))
      representativeIndex
  exact (Primrec.option_casesOn selected
    (Primrec.const none) someClause).of_eq fun input => by
      unfold representativeItem?
      cases (finalSource input.1).clauses[input.2]? <;> rfl

/-- Primitive-recursive route normalization, parameterized only by the
computational data it actually uses: period, positioned clause, and route.
The variable-position function is carried through for exact agreement with
`normalizeIncidenceRoute`, but is not inspected. -/
theorem normalizeIncidenceRoute_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (period : Input → Nat)
    (position : Input → Variable → Cell)
    (clause : Input → PositionedPeriodicClause Variable)
    (route : Input → List Cell)
    (periodPrimrec : Primrec period)
    (clausePrimrec : Primrec clause)
    (routePrimrec : Primrec route) :
    Primrec fun input =>
      normalizeIncidenceRoute
        ({ period := period input
           position := position input } :
          PeriodicVariablePlacement Variable)
        (clause input) (route input) := by
  have anchor : Primrec fun input : Input =>
      PeriodicCNF.clauseAnchor (clause input).literals :=
    PeriodicCNF.clauseAnchor_primrec.comp
      (PositionedPeriodicClause.literals_primrec.comp clausePrimrec)
  have transform : Primrec fun input : Input × Cell =>
      Cell.sub input.2
        (Cell.scale (period input.1)
          (PeriodicCNF.clauseAnchor (clause input.1).literals)) := by
    have translation : Primrec fun input : Input × Cell =>
        Cell.scale (period input.1)
          (PeriodicCNF.clauseAnchor (clause input.1).literals) :=
      Computability.cell_scale_primrec.comp
        (Computability.int_ofNat_primrec.comp
          (periodPrimrec.comp Primrec.fst))
        (anchor.comp Primrec.fst)
    exact Computability.cell_sub_primrec.comp Primrec.snd translation
  exact (Primrec.list_map routePrimrec transform.to₂).of_eq
    fun _ => rfl

/-- A primitive-recursive source, physical period, and raw route family give
a primitive-recursive clause-anchor-normalized route lookup. -/
theorem anchorNormalizedIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (period : Input → Nat)
    (position : Input → Variable → Cell)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      (source input.1.1).anchorNormalizedIncidenceRoutes
        { period := period input.1.1
          position := position input.1.1 }
        (routes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have clauses : Primrec fun input : Query =>
      (source input.1.1).clauses :=
    PositionedPeriodicCNF.clauses_primrec.comp
      (sourcePrimrec.comp (Primrec.fst.comp Primrec.fst))
  have selected : Primrec fun input : Query =>
      (source input.1.1).clauses[input.1.2]? :=
    Primrec.list_getElem?.comp clauses (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause Variable) =>
      normalizeIncidenceRoute
        ({ period := period input.1.1
           position := position input.1.1 } :
          PeriodicVariablePlacement Variable)
        clause (routes input.1.1 input.1.2 input.2) := by
    exact normalizeIncidenceRoute_primrec
      (Input := Query × PositionedPeriodicClause Variable)
      (fun input => period input.1.1.1)
      (fun input => position input.1.1.1)
      Prod.snd
      (fun input => routes input.1.1.1 input.1.1.2 input.1.2)
      (periodPrimrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd
      (routesPrimrec.comp Primrec.fst)
  exact (Primrec.option_casesOn selected none some).of_eq
    fun input => by
      unfold anchorNormalizedIncidenceRoutes
      cases h : (source input.1.1).clauses[input.1.2]?
      <;> rfl

/-- Reindexing a primitive-recursive route family through first-orbit
representatives and normalizing the selected routes is primitive recursive. -/
theorem deduplicatedIncidenceRoutes_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PositionedPeriodicCNF Variable)
    (period : Input → Nat)
    (position : Input → Variable → Cell)
    (routes : Input → IncidenceRoutes)
    (sourcePrimrec : Primrec source)
    (periodPrimrec : Primrec period)
    (routesPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      routes input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × Nat =>
      (source input.1.1).deduplicatedIncidenceRoutes
        { period := period input.1.1
          position := position input.1.1 }
        (routes input.1.1) input.1.2 input.2 := by
  let Query := (Input × Nat) × Nat
  have deduplicated : Primrec fun input : Query =>
      (source input.1.1).deduplicateByLiterals :=
    PositionedPeriodicCNF.deduplicateByLiterals_primrec source
      sourcePrimrec |>.comp (Primrec.fst.comp Primrec.fst)
  have clauses : Primrec fun input : Query =>
      (source input.1.1).deduplicateByLiterals.clauses :=
    PositionedPeriodicCNF.clauses_primrec.comp deduplicated
  have selected : Primrec fun input : Query =>
      (source input.1.1).deduplicateByLiterals.clauses[input.1.2]? :=
    Primrec.list_getElem?.comp clauses (Primrec.snd.comp Primrec.fst)
  have none : Primrec fun _input : Query => ([] : List Cell) :=
    Primrec.const []
  have some : Primrec₂ fun (input : Query)
      (clause : PositionedPeriodicClause Variable) =>
      normalizeIncidenceRoute
        ({ period := period input.1.1
           position := position input.1.1 } :
          PeriodicVariablePlacement Variable)
        clause
        (routes input.1.1
          ((source input.1.1).representativeClauseIndex clause.literals)
          input.2) := by
    let Combined := Query × PositionedPeriodicClause Variable
    have representativeIndex : Primrec fun input : Combined =>
        (source input.1.1.1).representativeClauseIndex
          input.2.literals :=
      representativeClauseIndex_primrec.comp
        (Primrec.pair
          (sourcePrimrec.comp
            (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst))))
          (PositionedPeriodicClause.literals_primrec.comp Primrec.snd))
    have selectedRoute : Primrec fun input : Combined =>
        routes input.1.1.1
          ((source input.1.1.1).representativeClauseIndex
            input.2.literals)
          input.1.2 :=
      routesPrimrec.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
            representativeIndex)
          (Primrec.snd.comp Primrec.fst))
    exact normalizeIncidenceRoute_primrec
      (Input := Combined)
      (fun input => period input.1.1.1)
      (fun input => position input.1.1.1)
      Prod.snd
      (fun input => routes input.1.1.1
        ((source input.1.1.1).representativeClauseIndex
          input.2.literals)
        input.1.2)
      (periodPrimrec.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      Primrec.snd selectedRoute
  exact (Primrec.option_casesOn selected none some).of_eq
    fun input => by
      unfold deduplicatedIncidenceRoutes
      cases h : (source input.1.1).deduplicateByLiterals.clauses[input.1.2]?
      <;> rfl

end PositionedPeriodicCNF
end LeanTrominoes
