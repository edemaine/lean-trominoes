/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Computability
import LeanTrominoes.PeriodicThreeCNFComputability
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization
import LeanTrominoes.PositionedPeriodicCNFVariableGauge

/-!
# Computability of periodic CNF gauge changes

The planar hardness construction repeatedly changes the finite presentation
of a periodic CNF without changing its semantics.  This module proves that
the two gauge operations which survive after positions are erased are
primitive recursive:

* clause-anchor normalization subtracts the first literal offset from every
  literal of the clause; and
* a variable gauge adds an input-dependent offset to every occurrence of a
  protovariable.

The family versions deliberately allow both the formula and the gauge to
depend on an external input.  That is the form needed by the Wang reduction,
whose canonical variable gauge is computed from the source tile set.
-/

noncomputable section

namespace LeanTrominoes

namespace PeriodicLiteral

theorem anchorNormalize_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : Cell × PeriodicLiteral Variable =>
      input.2.anchorNormalize input.1 := by
  have data : Primrec fun input : Cell × PeriodicLiteral Variable =>
      (input.2.atom, Cell.sub input.2.offset input.1, input.2.value) :=
    Primrec.pair
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
      (Primrec.pair
        (Computability.cell_sub_primrec.comp
          (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
          Primrec.fst)
        (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

theorem variableGauge_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (gauge : Input → Variable → Cell)
    (gaugePrimrec :
      Primrec fun input : Input × Variable => gauge input.1 input.2) :
    Primrec fun input : Input × PeriodicLiteral Variable =>
      input.2.variableGauge (gauge input.1) := by
  have gaugeAt : Primrec fun input : Input × PeriodicLiteral Variable =>
      gauge input.1 input.2.atom :=
    gaugePrimrec.comp
      (Primrec.pair Primrec.fst
        (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd))
  have data : Primrec fun input : Input × PeriodicLiteral Variable =>
      (input.2.atom,
        Cell.add input.2.offset (gauge input.1 input.2.atom),
        input.2.value) :=
    Primrec.pair
      (PeriodicThreeCNF.literal_atom_primrec.comp Primrec.snd)
      (Primrec.pair
        (Computability.cell_add_primrec.comp
          (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd)
          gaugeAt)
        (PeriodicThreeCNF.literal_value_primrec.comp Primrec.snd))
  exact (PeriodicLiteral.equivData_symm_primrec.comp data).of_eq fun _ => rfl

end PeriodicLiteral

namespace PeriodicCNF

theorem clauseAnchor_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (clauseAnchor : PeriodicClause Variable → Cell) := by
  have offset : Primrec fun clause : PeriodicClause Variable =>
      clause.head?.map PeriodicLiteral.offset :=
    Primrec.option_map Primrec.list_head?
      (PeriodicThreeCNF.literal_offset_primrec.comp Primrec.snd).to₂
  exact (Primrec.option_getD.comp offset
    (Primrec.const ((0, 0) : Cell))).of_eq fun _ => rfl

end PeriodicCNF

namespace PeriodicClause

theorem anchorNormalize_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (anchorNormalize :
      PeriodicClause Variable → PeriodicClause Variable) := by
  have one : Primrec₂ fun (clause : PeriodicClause Variable)
      (literal : PeriodicLiteral Variable) =>
      literal.anchorNormalize (PeriodicCNF.clauseAnchor clause) := by
    change Primrec fun input :
        PeriodicClause Variable × PeriodicLiteral Variable =>
      input.2.anchorNormalize (PeriodicCNF.clauseAnchor input.1)
    exact PeriodicLiteral.anchorNormalize_primrec.comp
      (Primrec.pair
        (PeriodicCNF.clauseAnchor_primrec.comp Primrec.fst)
        Primrec.snd)
  exact (Primrec.list_map (Primrec.id :
      Primrec (fun clause : PeriodicClause Variable => clause)) one).of_eq
    fun _ => rfl

theorem variableGauge_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (gauge : Input → Variable → Cell)
    (gaugePrimrec :
      Primrec fun input : Input × Variable => gauge input.1 input.2) :
    Primrec fun input : Input × PeriodicClause Variable =>
      input.2.variableGauge (gauge input.1) := by
  have one : Primrec₂ fun (input : Input × PeriodicClause Variable)
      (literal : PeriodicLiteral Variable) =>
      literal.variableGauge (gauge input.1) := by
    change Primrec fun combined :
        (Input × PeriodicClause Variable) × PeriodicLiteral Variable =>
      combined.2.variableGauge (gauge combined.1.1)
    exact PeriodicLiteral.variableGauge_primrec gauge gaugePrimrec |>.comp
      (Primrec.pair
        (Primrec.fst.comp Primrec.fst)
        Primrec.snd)
  simpa [PeriodicClause.variableGauge] using
    Primrec.list_map Primrec.snd one

end PeriodicClause

namespace PeriodicCNF

theorem anchorNormalize_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (anchorNormalize :
      PeriodicCNF Variable → PeriodicCNF Variable) := by
  have one : Primrec₂ fun (_formula : PeriodicCNF Variable)
      (clause : PeriodicClause Variable) =>
      clause.anchorNormalize :=
    PeriodicClause.anchorNormalize_primrec.comp₂ Primrec₂.right
  have clauses : Primrec fun formula : PeriodicCNF Variable =>
      formula.clauses.map PeriodicClause.anchorNormalize :=
    Primrec.list_map PeriodicCNF.equivData_primrec
      one
  exact (PeriodicCNF.equivData_symm_primrec.comp clauses).of_eq fun _ => rfl

theorem anchorNormalize_computable
    {Variable : Type*} [Primcodable Variable] :
    Computable (anchorNormalize :
      PeriodicCNF Variable → PeriodicCNF Variable) :=
  anchorNormalize_primrec.to_comp

theorem variableGauge_primrec
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (formula : Input → PeriodicCNF Variable)
    (gauge : Input → Variable → Cell)
    (formulaPrimrec : Primrec formula)
    (gaugePrimrec :
      Primrec fun input : Input × Variable => gauge input.1 input.2) :
    Primrec fun input => (formula input).variableGauge (gauge input) := by
  have clauses : Primrec fun input : Input =>
      (formula input).clauses :=
    PeriodicCNF.equivData_primrec.comp formulaPrimrec
  have one : Primrec₂ fun (input : Input)
      (clause : PeriodicClause Variable) =>
      clause.variableGauge (gauge input) := by
    exact PeriodicClause.variableGauge_primrec gauge gaugePrimrec
  have gaugedClauses : Primrec fun input : Input =>
      (formula input).clauses.map
        (PeriodicClause.variableGauge (gauge input)) :=
    Primrec.list_map clauses one
  exact (PeriodicCNF.equivData_symm_primrec.comp gaugedClauses).of_eq
    fun _ => rfl

theorem variableGauge_computable
    {Input Variable : Type*} [Primcodable Input] [Primcodable Variable]
    (formula : Input → PeriodicCNF Variable)
    (gauge : Input → Variable → Cell)
    (formulaPrimrec : Primrec formula)
    (gaugePrimrec :
      Primrec fun input : Input × Variable => gauge input.1 input.2) :
    Computable fun input => (formula input).variableGauge (gauge input) :=
  (variableGauge_primrec formula gauge formulaPrimrec gaugePrimrec).to_comp

end PeriodicCNF

end LeanTrominoes
