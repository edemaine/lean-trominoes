/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeCNFCorrectness
import LeanTrominoes.WangPeriodicCNFComputability
import Mathlib.Computability.Partrec

/-!
# Computability of periodic 3CNF splitting

The standard suffix-named clause chain is primitive recursive under the
canonical encodings.  Naming an auxiliary by its remaining suffix makes the
implementation a direct structural recursion on lists.
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicThreeCNF

theorem literal_atom_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (PeriodicLiteral.atom : PeriodicLiteral Variable → Variable) :=
  Primrec.fst.comp PeriodicLiteral.equivData_primrec

theorem literal_offset_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (PeriodicLiteral.offset : PeriodicLiteral Variable → Cell) :=
  Primrec.fst.comp
    (Primrec.snd.comp PeriodicLiteral.equivData_primrec)

theorem literal_value_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (PeriodicLiteral.value : PeriodicLiteral Variable → Bool) :=
  Primrec.snd.comp
    (Primrec.snd.comp PeriodicLiteral.equivData_primrec)

theorem anchor_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (anchor : PeriodicClause Variable → Cell) := by
  have offsetOption : Primrec fun clause : PeriodicClause Variable =>
      clause.head?.map PeriodicLiteral.offset :=
    Primrec.option_map Primrec.list_head?
      (literal_offset_primrec.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp offsetOption
    (Primrec.const (0, 0))).of_eq fun _ => rfl

theorem liftLiteral_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (liftLiteral :
      PeriodicLiteral Variable →
        PeriodicLiteral (ThreeCNFVariable Variable)) := by
  have data : Primrec fun literal : PeriodicLiteral Variable =>
      ((Sum.inl literal.atom : ThreeCNFVariable Variable),
        literal.offset, literal.value) :=
    Primrec.pair (Primrec.sumInl.comp literal_atom_primrec)
      (Primrec.pair literal_offset_primrec literal_value_primrec)
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem auxiliary_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun input :
        (PeriodicClause Variable × PeriodicClause Variable) × Bool =>
      auxiliary input.1.1 input.1.2 input.2 := by
  have atom : Primrec fun input :
      (PeriodicClause Variable × PeriodicClause Variable) × Bool =>
      (Sum.inr input.1 : ThreeCNFVariable Variable) :=
    Primrec.sumInr.comp Primrec.fst
  have data : Primrec fun input :
      (PeriodicClause Variable × PeriodicClause Variable) × Bool =>
      ((Sum.inr input.1 : ThreeCNFVariable Variable),
        anchor input.1.1, input.2) :=
    Primrec.pair atom
      (Primrec.pair
        (anchor_primrec.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

private def continuationStep {Variable : Type*}
    (source : PeriodicClause Variable) (first : PeriodicLiteral Variable)
    (rest : PeriodicClause Variable)
    (recursive : List (PeriodicClause (ThreeCNFVariable Variable))) :
    List (PeriodicClause (ThreeCNFVariable Variable)) :=
  match rest with
  | [] =>
      [[auxiliary source [first] false, liftLiteral first]]
  | [second] =>
      [[auxiliary source [first, second] false,
        liftLiteral first, liftLiteral second]]
  | second :: third :: rest =>
      [auxiliary source (first :: second :: third :: rest) false,
        liftLiteral first,
        auxiliary source (second :: third :: rest) true] :: recursive

private theorem continuationStep_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec fun input :
        PeriodicClause Variable ×
          (PeriodicLiteral Variable × PeriodicClause Variable ×
            List (PeriodicClause (ThreeCNFVariable Variable))) =>
      continuationStep input.1 input.2.1 input.2.2.1 input.2.2.2 := by
  let Input := PeriodicClause Variable ×
    (PeriodicLiteral Variable × PeriodicClause Variable ×
      List (PeriodicClause (ThreeCNFVariable Variable)))
  let Output := List (PeriodicClause (ThreeCNFVariable Variable))
  let source : Primrec fun input : Input => input.1 := Primrec.fst
  let first : Primrec fun input : Input => input.2.1 :=
    Primrec.fst.comp Primrec.snd
  let rest : Primrec fun input : Input => input.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let recursive : Primrec fun input : Input => input.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  let firstSuffix : Primrec fun input : Input => [input.2.1] :=
    Primrec.list_cons.comp first (Primrec.const [])
  let firstAux : Primrec fun input : Input =>
      auxiliary input.1 [input.2.1] false :=
    auxiliary_primrec.comp
      (Primrec.pair (Primrec.pair source firstSuffix) (Primrec.const false))
  let firstLift : Primrec fun input : Input => liftLiteral input.2.1 :=
    liftLiteral_primrec.comp first
  let nilClause : Primrec fun input : Input =>
      [auxiliary input.1 [input.2.1] false, liftLiteral input.2.1] :=
    Primrec.list_cons.comp firstAux
      (Primrec.list_cons.comp firstLift (Primrec.const []))
  let nilResult : Primrec fun input : Input =>
      [[auxiliary input.1 [input.2.1] false, liftLiteral input.2.1]] :=
    Primrec.list_cons.comp nilClause (Primrec.const [])
  have consCase : Primrec₂ fun (input : Input)
      (secondAndTail : PeriodicLiteral Variable × PeriodicClause Variable) =>
      match secondAndTail.2 with
      | [] =>
          [[auxiliary input.1 [input.2.1, secondAndTail.1] false,
            liftLiteral input.2.1, liftLiteral secondAndTail.1]]
      | third :: rest =>
          [auxiliary input.1
              (input.2.1 :: secondAndTail.1 :: third :: rest) false,
            liftLiteral input.2.1,
            auxiliary input.1 (secondAndTail.1 :: third :: rest) true] ::
            input.2.2.2 := by
    change Primrec fun pair : Input ×
        (PeriodicLiteral Variable × PeriodicClause Variable) =>
      match pair.2.2 with
      | [] =>
          [[auxiliary pair.1.1 [pair.1.2.1, pair.2.1] false,
            liftLiteral pair.1.2.1, liftLiteral pair.2.1]]
      | third :: rest =>
          [auxiliary pair.1.1
              (pair.1.2.1 :: pair.2.1 :: third :: rest) false,
            liftLiteral pair.1.2.1,
            auxiliary pair.1.1 (pair.2.1 :: third :: rest) true] ::
            pair.1.2.2.2
    let PairInput := Input ×
      (PeriodicLiteral Variable × PeriodicClause Variable)
    let tail : Primrec fun pair : PairInput => pair.2.2 :=
      Primrec.snd.comp Primrec.snd
    let outer : Primrec fun pair : PairInput => pair.1 := Primrec.fst
    let second : Primrec fun pair : PairInput => pair.2.1 :=
      Primrec.fst.comp Primrec.snd
    let pairSource : Primrec fun pair : PairInput => pair.1.1 :=
      source.comp Primrec.fst
    let pairFirst : Primrec fun pair : PairInput => pair.1.2.1 :=
      first.comp Primrec.fst
    let pairRecursive : Primrec fun pair : PairInput => pair.1.2.2.2 :=
      recursive.comp Primrec.fst
    let nilSuffix : Primrec fun pair : PairInput =>
        [pair.1.2.1, pair.2.1] :=
      Primrec.list_cons.comp pairFirst
        (Primrec.list_cons.comp second (Primrec.const []))
    let nilAux : Primrec fun pair : PairInput =>
        auxiliary pair.1.1 [pair.1.2.1, pair.2.1] false :=
      auxiliary_primrec.comp
        (Primrec.pair (Primrec.pair pairSource nilSuffix)
          (Primrec.const false))
    let secondLift : Primrec fun pair : PairInput =>
        liftLiteral pair.2.1 :=
      liftLiteral_primrec.comp second
    let nilHead : Primrec fun pair : PairInput =>
        [auxiliary pair.1.1 [pair.1.2.1, pair.2.1] false,
          liftLiteral pair.1.2.1, liftLiteral pair.2.1] :=
      Primrec.list_cons.comp nilAux
        (Primrec.list_cons.comp
          (firstLift.comp Primrec.fst)
          (Primrec.list_cons.comp secondLift (Primrec.const [])))
    let nilOutput : Primrec fun pair : PairInput =>
        [[auxiliary pair.1.1 [pair.1.2.1, pair.2.1] false,
          liftLiteral pair.1.2.1, liftLiteral pair.2.1]] :=
      Primrec.list_cons.comp nilHead (Primrec.const [])
    have tailCons : Primrec₂ fun (pair : PairInput)
        (thirdAndRest : PeriodicLiteral Variable × PeriodicClause Variable) =>
        [auxiliary pair.1.1
            (pair.1.2.1 :: pair.2.1 :: thirdAndRest.1 :: thirdAndRest.2) false,
          liftLiteral pair.1.2.1,
          auxiliary pair.1.1
            (pair.2.1 :: thirdAndRest.1 :: thirdAndRest.2) true] ::
          pair.1.2.2.2 := by
      change Primrec fun combined : PairInput ×
          (PeriodicLiteral Variable × PeriodicClause Variable) =>
        [auxiliary combined.1.1.1
            (combined.1.1.2.1 :: combined.1.2.1 ::
              combined.2.1 :: combined.2.2) false,
          liftLiteral combined.1.1.2.1,
          auxiliary combined.1.1.1
            (combined.1.2.1 :: combined.2.1 :: combined.2.2) true] ::
          combined.1.1.2.2.2
      let Combined := PairInput ×
        (PeriodicLiteral Variable × PeriodicClause Variable)
      let combinedPair : Primrec fun combined : Combined => combined.1 :=
        Primrec.fst
      let third : Primrec fun combined : Combined => combined.2.1 :=
        Primrec.fst.comp Primrec.snd
      let finalRest : Primrec fun combined : Combined => combined.2.2 :=
        Primrec.snd.comp Primrec.snd
      let fullSuffix : Primrec fun combined : Combined =>
          combined.1.1.2.1 :: combined.1.2.1 ::
            combined.2.1 :: combined.2.2 :=
        Primrec.list_cons.comp (pairFirst.comp Primrec.fst)
          (Primrec.list_cons.comp (second.comp Primrec.fst)
            (Primrec.list_cons.comp third finalRest))
      let tailSuffix : Primrec fun combined : Combined =>
          combined.1.2.1 :: combined.2.1 :: combined.2.2 :=
        Primrec.list_cons.comp (second.comp Primrec.fst)
          (Primrec.list_cons.comp third finalRest)
      let fullAux : Primrec fun combined : Combined =>
          auxiliary combined.1.1.1
            (combined.1.1.2.1 :: combined.1.2.1 ::
              combined.2.1 :: combined.2.2) false :=
        auxiliary_primrec.comp
          (Primrec.pair
            (Primrec.pair (pairSource.comp Primrec.fst) fullSuffix)
            (Primrec.const false))
      let tailAux : Primrec fun combined : Combined =>
          auxiliary combined.1.1.1
            (combined.1.2.1 :: combined.2.1 :: combined.2.2) true :=
        auxiliary_primrec.comp
          (Primrec.pair
            (Primrec.pair (pairSource.comp Primrec.fst) tailSuffix)
            (Primrec.const true))
      let head : Primrec fun combined : Combined =>
          [auxiliary combined.1.1.1
              (combined.1.1.2.1 :: combined.1.2.1 ::
                combined.2.1 :: combined.2.2) false,
            liftLiteral combined.1.1.2.1,
            auxiliary combined.1.1.1
              (combined.1.2.1 :: combined.2.1 :: combined.2.2) true] :=
        Primrec.list_cons.comp fullAux
          (Primrec.list_cons.comp
            (firstLift.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.list_cons.comp tailAux (Primrec.const [])))
      exact Primrec.list_cons.comp head (pairRecursive.comp Primrec.fst)
    exact (Primrec.list_casesOn tail nilOutput tailCons).of_eq fun pair => by
      cases pair.2.2 <;> rfl
  exact (Primrec.list_casesOn rest nilResult consCase).of_eq fun input => by
    rcases input with ⟨source, first, rest, recursive⟩
    cases rest with
    | nil => rfl
    | cons second tail => cases tail <;> rfl

theorem continuation_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec₂ (continuation :
      PeriodicClause Variable → PeriodicClause Variable →
        List (PeriodicClause (ThreeCNFVariable Variable))) := by
  change Primrec fun input :
      PeriodicClause Variable × PeriodicClause Variable =>
    continuation input.1 input.2
  have step : Primrec₂ fun
      (input : PeriodicClause Variable × PeriodicClause Variable)
      (state : PeriodicLiteral Variable × PeriodicClause Variable ×
        List (PeriodicClause (ThreeCNFVariable Variable))) =>
      continuationStep input.1 state.1 state.2.1 state.2.2 := by
    change Primrec fun combined :
        (PeriodicClause Variable × PeriodicClause Variable) ×
          (PeriodicLiteral Variable × PeriodicClause Variable ×
            List (PeriodicClause (ThreeCNFVariable Variable))) =>
      continuationStep combined.1.1 combined.2.1
        combined.2.2.1 combined.2.2.2
    exact continuationStep_primrec.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  have recursion := Primrec.list_rec
    (f := fun input : PeriodicClause Variable × PeriodicClause Variable =>
      input.2)
    (g := fun input =>
      [[auxiliary input.1 [] false]])
    (h := fun input state =>
      continuationStep input.1 state.1 state.2.1 state.2.2)
    Primrec.snd
    (Primrec.list_cons.comp
      (Primrec.list_cons.comp
        (auxiliary_primrec.comp
          (Primrec.pair
            (Primrec.pair Primrec.fst (Primrec.const []))
            (Primrec.const false)))
        (Primrec.const []))
      (Primrec.const []))
    step
  exact recursion.of_eq fun input => by
    induction input.2 with
    | nil => rfl
    | cons first rest ih =>
        change continuationStep input.1 first rest
            (List.rec [[auxiliary input.1 [] false]]
              (fun b l recursive =>
                continuationStep input.1 b l recursive) rest) =
          continuation input.1 (first :: rest)
        have ih' :
            List.rec [[auxiliary input.1 [] false]]
                (fun b l recursive =>
                  continuationStep input.1 b l recursive) rest =
              continuation input.1 rest := by
          simpa using ih
        rw [ih']
        cases rest with
        | nil => rfl
        | cons second tail => cases tail <;> rfl

/-- A range-free implementation of clause splitting convenient for the
primitive-recursive proof. -/
def computableClauseClauses {Variable : Type*}
    (source : PeriodicClause Variable) :
    List (PeriodicClause (ThreeCNFVariable Variable)) :=
  if source.length ≤ 3 then
    [source.map liftLiteral]
  else
    ((source.take 2).map liftLiteral ++
      [auxiliary source (source.drop 2) true]) ::
      continuation source (source.drop 2)

theorem computableClauseClauses_eq {Variable : Type*}
    (source : PeriodicClause Variable) :
    computableClauseClauses source = clauseClauses source := by
  rcases source with _ | ⟨first, rest⟩
  · rfl
  · cases rest with
    | nil => rfl
    | cons second rest =>
        cases rest with
        | nil => rfl
        | cons third rest =>
            cases rest with
            | nil => rfl
            | cons fourth rest =>
                simp [computableClauseClauses, clauseClauses]

theorem computableClauseClauses_primrec {Variable : Type*}
    [Primcodable Variable] :
    Primrec (computableClauseClauses :
      PeriodicClause Variable →
        List (PeriodicClause (ThreeCNFVariable Variable))) := by
  have length : Primrec fun source : PeriodicClause Variable => source.length :=
    Primrec.list_length
  have short : PrimrecPred fun source : PeriodicClause Variable =>
      source.length ≤ 3 :=
    Primrec.nat_le.comp length (Primrec.const 3)
  have lifted : Primrec fun source : PeriodicClause Variable =>
      source.map liftLiteral :=
    Primrec.list_map Primrec.id
      (liftLiteral_primrec.comp Primrec.snd).to₂
  have shortOutput : Primrec fun source : PeriodicClause Variable =>
      [source.map liftLiteral] :=
    Primrec.list_cons.comp lifted (Primrec.const [])
  have prefixList : Primrec fun source : PeriodicClause Variable =>
      source.take 2 :=
    Primrec.list_take.comp (Primrec.const 2) Primrec.id
  have suffix : Primrec fun source : PeriodicClause Variable =>
      source.drop 2 :=
    Primrec.list_drop.comp (Primrec.const 2) Primrec.id
  have liftedPrefix : Primrec fun source : PeriodicClause Variable =>
      (source.take 2).map liftLiteral :=
    Primrec.list_map prefixList
      (liftLiteral_primrec.comp Primrec.snd).to₂
  have positiveAux : Primrec fun source : PeriodicClause Variable =>
      auxiliary source (source.drop 2) true :=
    auxiliary_primrec.comp
      (Primrec.pair (Primrec.pair Primrec.id suffix)
        (Primrec.const true))
  have head : Primrec fun source : PeriodicClause Variable =>
      (source.take 2).map liftLiteral ++
        [auxiliary source (source.drop 2) true] :=
    Primrec.list_append.comp liftedPrefix
      (Primrec.list_cons.comp positiveAux (Primrec.const []))
  have tail : Primrec fun source : PeriodicClause Variable =>
      continuation source (source.drop 2) :=
    continuation_primrec.comp Primrec.id suffix
  have longOutput : Primrec fun source : PeriodicClause Variable =>
      ((source.take 2).map liftLiteral ++
        [auxiliary source (source.drop 2) true]) ::
        continuation source (source.drop 2) :=
    Primrec.list_cons.comp head tail
  exact Primrec.ite short shortOutput longOutput

theorem clauseClauses_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (clauseClauses :
      PeriodicClause Variable →
        List (PeriodicClause (ThreeCNFVariable Variable))) :=
  computableClauseClauses_primrec.of_eq computableClauseClauses_eq

/-- The complete width-three conversion is primitive recursive. -/
theorem formula_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (formula :
      PeriodicCNF Variable →
        PeriodicCNF (ThreeCNFVariable Variable)) := by
  have clauses : Primrec fun source : PeriodicCNF Variable =>
      source.clauses.flatMap clauseClauses :=
    Primrec.list_flatMap PeriodicCNF.equivData_primrec
      (clauseClauses_primrec.comp Primrec.snd).to₂
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq fun _ => rfl

theorem formula_computable {Variable : Type*} [Primcodable Variable] :
    Computable (formula :
      PeriodicCNF Variable →
        PeriodicCNF (ThreeCNFVariable Variable)) :=
  formula_primrec.to_comp

/-- The local periodic 3CNF decision predicate, treating presentations that
are nonlocal or contain a wider clause as no-instances. -/
def LocalThreeCNFHolds
    (threeCNF : PeriodicCNF (ThreeCNFVariable LeanWang.WangTile)) : Prop :=
  threeCNF.IsLocal ∧ threeCNF.WidthAtMost 3 ∧ threeCNF.Satisfiable

/-- The composition of the Wang encoding with the width-three conversion. -/
def wangFormula (tiles : LeanWang.TileSet) :
    PeriodicCNF (ThreeCNFVariable LeanWang.WangTile) :=
  formula (WangPeriodicCNF.formula tiles)

theorem wangFormula_computable : Computable wangFormula :=
  formula_computable.comp WangPeriodicCNF.formula_computable

/-- The composed Wang encoding satisfies the exact local 3CNF endpoint. -/
theorem wangFormula_correct (tiles : LeanWang.TileSet) :
    LeanWang.TilesPlane tiles ↔ LocalThreeCNFHolds (wangFormula tiles) := by
  constructor
  · intro tilesPlane
    refine ⟨formula_isLocal (WangPeriodicCNF.formula_isLocal tiles),
      formula_widthAtMostThree _, ?_⟩
    exact (satisfiable_iff _).1
      ((WangPeriodicCNF.formula_correct tiles).1 tilesPlane)
  · intro localThreeCNF
    exact (WangPeriodicCNF.formula_correct tiles).2
      ((satisfiable_iff _).2 localThreeCNF.2.2)

/-- Local periodic 3CNF satisfiability is co-r.e.-hard. -/
theorem localThreeCNFCoREHard :
    LeanWang.CoREHard LocalThreeCNFHolds := by
  intro α _ source source_coRE
  obtain ⟨reduce, reduce_computable, reduce_correct⟩ :=
    LeanWang.domino_problem_coRE_hard source source_coRE
  refine ⟨wangFormula ∘ reduce,
    wangFormula_computable.comp reduce_computable, ?_⟩
  intro input
  rw [reduce_correct input]
  exact wangFormula_correct (reduce input)

end PeriodicThreeCNF
end LeanTrominoes
