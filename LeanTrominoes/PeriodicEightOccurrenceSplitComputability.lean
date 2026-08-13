/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplit
import LeanTrominoes.PeriodicThreeSATThreeComputability

/-!
# Computability of fixed-eight occurrence splitting

The fixed-eight split is primitive recursive when its source formula and
clause/literal-indexed compass-port lookup are primitive recursive in a common
external input.  The proof deliberately consumes the lookup function rather
than the proof-carrying, function-valued `OccurrencePorts` structure, so later
geometric constructions need only expose their finite port calculation.
-/

noncomputable section

namespace LeanTrominoes

namespace OccurrenceSplitRing

deriving instance Fintype for Port

noncomputable instance : Primcodable Port :=
  Primcodable.ofEquiv (Fin (Fintype.card Port))
    (Fintype.equivFin Port)

end OccurrenceSplitRing

namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing

theorem portIndex_primrec : Primrec portIndex :=
  Primrec.dom_finite portIndex

theorem copy_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Variable × Port => copy input.1 input.2 := by
  exact (Primrec.pair Primrec.fst
    (Primrec.pair
      (portIndex_primrec.comp Primrec.snd)
      (Primrec.const 0))).of_eq fun _ => rfl

/-- The constant nine-copy ring, parameterized only by its source atom. -/
theorem copies_primrec {Variable : Type*} [Primcodable Variable] :
    Primrec (copies : Variable →
      List (ThreeOccurrenceVariable Variable)) := by
  have copyAt (index : Nat) : Primrec fun atom : Variable =>
      (atom, index, 0) :=
    Primrec.pair Primrec.id
      (Primrec.pair (Primrec.const index) (Primrec.const 0))
  have output : Primrec fun atom : Variable =>
      [(atom, 8, 0), (atom, 3, 0), (atom, 4, 0),
        (atom, 5, 0), (atom, 6, 0), (atom, 7, 0),
        (atom, 0, 0), (atom, 1, 0), (atom, 2, 0)] :=
    Primrec.list_cons.comp (copyAt 8) <|
    Primrec.list_cons.comp (copyAt 3) <|
    Primrec.list_cons.comp (copyAt 4) <|
    Primrec.list_cons.comp (copyAt 5) <|
    Primrec.list_cons.comp (copyAt 6) <|
    Primrec.list_cons.comp (copyAt 7) <|
    Primrec.list_cons.comp (copyAt 0) <|
    Primrec.list_cons.comp (copyAt 1) <|
    Primrec.list_cons.comp (copyAt 2) (Primrec.const [])
  exact output.of_eq fun _ => rfl

theorem cycleClausesFor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (cycleClausesFor : Variable →
      List (PeriodicClause (ThreeOccurrenceVariable Variable))) :=
  PeriodicThreeSATThree.cycleClauses_primrec.comp copies_primrec

theorem occurrenceLiteral_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (ports : Input → Nat → Nat → Port)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2) :
    Primrec fun input :
        ((Input × Nat) × Nat) × PeriodicLiteral Variable =>
      occurrenceLiteral
        { port := ports input.1.1.1 }
        input.1.1.2 input.1.2 input.2 := by
  have selectedCopy : Primrec fun input :
      ((Input × Nat) × Nat) × PeriodicLiteral Variable =>
      copy input.2.atom
        (ports input.1.1.1 input.1.1.2 input.1.2) :=
    copy_primrec.comp
      (Primrec.pair
        (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
        (portsPrimrec.comp Primrec.fst))
  have data : Primrec fun input :
      ((Input × Nat) × Nat) × PeriodicLiteral Variable =>
      (copy input.2.atom
          (ports input.1.1.1 input.1.1.2 input.1.2),
        input.2.offset, input.2.value) :=
    Primrec.pair selectedCopy
      (Primrec.pair
        (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
        (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq
    fun _ => rfl

theorem occurrenceClause_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (ports : Input → Nat → Nat → Port)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2) :
    Primrec fun input : (Input × Nat) × PeriodicClause Variable =>
      occurrenceClause { port := ports input.1.1 }
        input.1.2 input.2 := by
  let ClauseInput := (Input × Nat) × PeriodicClause Variable
  have tagged : Primrec fun input : ClauseInput => input.2.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp Primrec.snd
  have literal : Primrec₂ fun (input : ClauseInput)
      (item : PeriodicLiteral Variable × Nat) =>
      occurrenceLiteral { port := ports input.1.1 }
        input.1.2 item.2 item.1 := by
    change Primrec fun combined :
        ClauseInput × (PeriodicLiteral Variable × Nat) =>
      occurrenceLiteral { port := ports combined.1.1.1 }
        combined.1.1.2 combined.2.2 combined.2.1
    exact occurrenceLiteral_primrec ports portsPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair
          (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map tagged literal

theorem occurrenceClauses_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (source : Input → PeriodicCNF Variable)
    (ports : Input → Nat → Nat → Port)
    (sourcePrimrec : Primrec source)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2) :
    Primrec fun input => occurrenceClauses (source input)
      { port := ports input } := by
  have tagged : Primrec fun input : Input =>
      (source input).clauses.zipIdx :=
    PeriodicThreeSATThree.zipIdx_primrec.comp
      (PeriodicCNF.equivData_primrec.comp sourcePrimrec)
  have clause : Primrec₂ fun (input : Input)
      (item : PeriodicClause Variable × Nat) =>
      occurrenceClause { port := ports input } item.2 item.1 := by
    change Primrec fun combined :
        Input × (PeriodicClause Variable × Nat) =>
      occurrenceClause { port := ports combined.1 }
        combined.2.2 combined.2.1
    exact occurrenceClause_primrec ports portsPrimrec |>.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst
          (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd))
  exact Primrec.list_map tagged clause

theorem allCycleClauses_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (sourcePrimrec : Primrec source) :
    Primrec fun input => allCycleClauses (source input) := by
  have atoms : Primrec fun input =>
      PeriodicThreeSATThree.sourceVariables (source input) :=
    PeriodicThreeSATThree.sourceVariables_primrec.comp sourcePrimrec
  have cycles : Primrec₂ fun (_input : Input) (atom : Variable) =>
      cycleClausesFor atom :=
    (cycleClausesFor_primrec.comp Primrec.snd).to₂
  exact Primrec.list_flatMap atoms cycles

/-- Fixed-eight occurrence splitting is primitive recursive from a
primitive-recursive source and primitive-recursive total port lookup. -/
theorem formula_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (ports : Input → Nat → Nat → Port)
    (sourcePrimrec : Primrec source)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2) :
    Primrec fun input => formula (source input) { port := ports input } := by
  have clauses : Primrec fun input =>
      occurrenceClauses (source input) { port := ports input } ++
        allCycleClauses (source input) :=
    Primrec.list_append.comp
      (occurrenceClauses_primrec source ports sourcePrimrec portsPrimrec)
      (allCycleClauses_primrec source sourcePrimrec)
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq
    fun _ => rfl

theorem formula_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    [DecidableEq Variable]
    (source : Input → PeriodicCNF Variable)
    (ports : Input → Nat → Nat → Port)
    (sourcePrimrec : Primrec source)
    (portsPrimrec : Primrec fun input : (Input × Nat) × Nat =>
      ports input.1.1 input.1.2 input.2) :
    Computable fun input => formula (source input) { port := ports input } :=
  (formula_primrec source ports sourcePrimrec portsPrimrec).to_comp

end PeriodicEightOccurrenceSplit
end LeanTrominoes
