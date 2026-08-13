/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATInstantiation
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierFormulaComputability

/-!
# Computability of finite planar-3SAT gadgets

This module supplies canonical encodings for the fixed crossover variable
types and the four-port record.  It also proves the generic embedded-clause
renaming and affine-placement operations primitive recursive, in the
input-dependent form needed to instantiate a family of crossover gadgets.
-/

noncomputable section

namespace LeanTrominoes
namespace PlanarThreeSAT

namespace CrossoverVariable

def toFin : CrossoverVariable → Fin 13
    | .aLeft => 0
    | .aInnerLeft => 1
    | .upperLeft => 2
    | .lowerLeft => 3
    | .bTop => 4
    | .bInnerTop => 5
    | .center => 6
    | .bInnerBottom => 7
    | .bBottom => 8
    | .upperRight => 9
    | .lowerRight => 10
    | .aInnerRight => 11
    | .aRight => 12

def ofFin (index : Fin 13) : CrossoverVariable :=
  match index.1 with
    | 0 => .aLeft
    | 1 => .aInnerLeft
    | 2 => .upperLeft
    | 3 => .lowerLeft
    | 4 => .bTop
    | 5 => .bInnerTop
    | 6 => .center
    | 7 => .bInnerBottom
    | 8 => .bBottom
    | 9 => .upperRight
    | 10 => .lowerRight
    | 11 => .aInnerRight
    | _ => .aRight

def equivFin : CrossoverVariable ≃ Fin 13 where
  toFun := (toFin)
  invFun := (ofFin)
  left_inv := by
    intro value
    cases value <;> rfl
  right_inv := by
    intro index
    rcases index with ⟨index, indexLt⟩
    apply Fin.ext
    interval_cases index <;> rfl

noncomputable instance : Primcodable CrossoverVariable :=
  Primcodable.ofEquiv (Fin 13) equivFin

theorem equivFin_primrec : Primrec equivFin :=
  Primrec.of_equiv

theorem equivFin_symm_primrec : Primrec equivFin.symm :=
  Primrec.of_equiv_symm

end CrossoverVariable

namespace CrossoverInternal

def toFin : CrossoverInternal → Fin 9
    | .aInnerLeft => 0
    | .upperLeft => 1
    | .lowerLeft => 2
    | .bInnerTop => 3
    | .center => 4
    | .bInnerBottom => 5
    | .upperRight => 6
    | .lowerRight => 7
    | .aInnerRight => 8

def ofFin (index : Fin 9) : CrossoverInternal :=
  match index.1 with
    | 0 => .aInnerLeft
    | 1 => .upperLeft
    | 2 => .lowerLeft
    | 3 => .bInnerTop
    | 4 => .center
    | 5 => .bInnerBottom
    | 6 => .upperRight
    | 7 => .lowerRight
    | _ => .aInnerRight

def equivFin : CrossoverInternal ≃ Fin 9 where
  toFun := (toFin)
  invFun := (ofFin)
  left_inv := by
    intro value
    cases value <;> rfl
  right_inv := by
    intro index
    rcases index with ⟨index, indexLt⟩
    apply Fin.ext
    interval_cases index <;> rfl

noncomputable instance : Primcodable CrossoverInternal :=
  Primcodable.ofEquiv (Fin 9) equivFin

theorem equivFin_primrec : Primrec equivFin :=
  Primrec.of_equiv

theorem equivFin_symm_primrec : Primrec equivFin.symm :=
  Primrec.of_equiv_symm

end CrossoverInternal

namespace CrossoverPorts

def equivData {Variable : Type*} : CrossoverPorts Variable ≃
    (Variable × Variable) × (Variable × Variable) where
  toFun ports :=
    ((ports.aLeft, ports.aRight), (ports.bTop, ports.bBottom))
  invFun data := ⟨data.1.1, data.1.2, data.2.1, data.2.2⟩
  left_inv ports := by cases ports; rfl
  right_inv data := by rcases data with ⟨⟨aLeft, aRight⟩, bTop, bBottom⟩; rfl

noncomputable instance {Variable : Type*} [Primcodable Variable] :
    Primcodable (CrossoverPorts Variable) :=
  Primcodable.ofEquiv
    ((Variable × Variable) × (Variable × Variable)) equivData

theorem equivData_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)) :=
  Primrec.of_equiv

theorem equivData_symm_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (equivData (Variable := Variable)).symm :=
  Primrec.of_equiv_symm

theorem aLeft_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CrossoverPorts.aLeft : CrossoverPorts Variable → Variable) :=
  ((Primrec.fst.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem aRight_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CrossoverPorts.aRight : CrossoverPorts Variable → Variable) :=
  ((Primrec.snd.comp Primrec.fst).comp equivData_primrec).of_eq
    fun _ => rfl

theorem bTop_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CrossoverPorts.bTop : CrossoverPorts Variable → Variable) :=
  ((Primrec.fst.comp Primrec.snd).comp equivData_primrec).of_eq
    fun _ => rfl

theorem bBottom_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec (CrossoverPorts.bBottom : CrossoverPorts Variable → Variable) :=
  ((Primrec.snd.comp Primrec.snd).comp equivData_primrec).of_eq
    fun _ => rfl

theorem mk_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun data :
        (Variable × Variable) × (Variable × Variable) =>
      CrossoverPorts.mk data.1.1 data.1.2 data.2.1 data.2.2 :=
  equivData_symm_primrec.of_eq fun _ => rfl

end CrossoverPorts

namespace EmbeddedClause

/-- Map both parts of an embedded clause by input-dependent
primitive-recursive functions. -/
theorem map_primrec
    {Input Source Target : Type*}
    [Primcodable Input] [Primcodable Source] [Primcodable Target]
    (variableMap : Input → Source → Target)
    (positionMap : Input → Cell → Cell)
    (variableMapPrimrec :
      Primrec fun input : Input × Source =>
        variableMap input.1 input.2)
    (positionMapPrimrec :
      Primrec fun input : Input × Cell =>
        positionMap input.1 input.2) :
    Primrec fun input : Input × EmbeddedClause Source =>
      input.2.map (variableMap input.1) (positionMap input.1) := by
  have position : Primrec fun input : Input × EmbeddedClause Source =>
      positionMap input.1 input.2.position :=
    positionMapPrimrec.comp
      (Primrec.pair Primrec.fst
        (EmbeddedClause.position_primrec.comp Primrec.snd))
  have literals : Primrec fun input : Input × EmbeddedClause Source =>
      input.2.literals.map fun literal =>
        (variableMap input.1 literal.1, literal.2) := by
    have one : Primrec₂ fun
        (input : Input × EmbeddedClause Source)
        (literal : Source × Bool) =>
        (variableMap input.1 literal.1, literal.2) := by
      change Primrec fun combined :
          (Input × EmbeddedClause Source) × (Source × Bool) =>
        (variableMap combined.1.1 combined.2.1, combined.2.2)
      exact Primrec.pair
        (variableMapPrimrec.comp
          (Primrec.pair
            (Primrec.fst.comp Primrec.fst)
            (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_map
      (EmbeddedClause.literals_primrec.comp Primrec.snd) one
  exact (EmbeddedClause.mk_primrec.comp
    (Primrec.pair position literals)).of_eq fun _ => rfl

theorem rename_primrec
    {Input Source Target : Type*}
    [Primcodable Input] [Primcodable Source] [Primcodable Target]
    (variableMap : Input → Source → Target)
    (variableMapPrimrec :
      Primrec fun input : Input × Source =>
        variableMap input.1 input.2) :
    Primrec fun input : Input × EmbeddedClause Source =>
      input.2.rename (variableMap input.1) := by
  exact (map_primrec variableMap (fun _ => id)
    variableMapPrimrec Primrec.snd).of_eq fun _ => rfl

theorem place_primrec
    {Variable : Type*} [Primcodable Variable] :
    Primrec fun input : (Cell × Int) × EmbeddedClause Variable =>
      input.2.place input.1.1 input.1.2 := by
  have positionMap : Primrec fun input : (Cell × Int) × Cell =>
      Cell.add input.1.1 (Cell.scale input.1.2 input.2) :=
    Computability.cell_add_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Computability.cell_scale_primrec.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (map_primrec (fun _ => id)
    (fun data position =>
      Cell.add data.1 (Cell.scale data.2 position))
    Primrec.snd positionMap).of_eq fun _ => rfl

end EmbeddedClause

/-- Instantiate a computed embedded formula using computed renaming and
affine-placement data. -/
theorem instantiateFormula_primrec
    {Input Source Target : Type*}
    [Primcodable Input] [Primcodable Source] [Primcodable Target]
    (variableMap : Input → Source → Target)
    (origin : Input → Cell)
    (scale : Input → Int)
    (formula : Input → List (EmbeddedClause Source))
    (variableMapPrimrec :
      Primrec fun input : Input × Source =>
        variableMap input.1 input.2)
    (originPrimrec : Primrec origin)
    (scalePrimrec : Primrec scale)
    (formulaPrimrec : Primrec formula) :
    Primrec fun input =>
      instantiateFormula (variableMap input)
        (origin input) (scale input) (formula input) := by
  have one : Primrec₂ fun (input : Input)
      (clause : EmbeddedClause Source) =>
      (clause.rename (variableMap input)).place
        (origin input) (scale input) := by
    change Primrec fun combined : Input × EmbeddedClause Source =>
      (combined.2.rename (variableMap combined.1)).place
        (origin combined.1) (scale combined.1)
    have renamed : Primrec fun combined :
        Input × EmbeddedClause Source =>
        combined.2.rename (variableMap combined.1) :=
      EmbeddedClause.rename_primrec variableMap variableMapPrimrec
    exact EmbeddedClause.place_primrec.comp
      (Primrec.pair
        (Primrec.pair
          (originPrimrec.comp Primrec.fst)
          (scalePrimrec.comp Primrec.fst))
        renamed)
  exact (Primrec.list_map formulaPrimrec one).of_eq fun _ => rfl

theorem scopedCrossoverVariableMap_primrec
    {Input Site Variable : Type*}
    [Primcodable Input] [Primcodable Site] [Primcodable Variable]
    (ports : Input → Site → CrossoverPorts Variable)
    (portsPrimrec : Primrec fun input : Input × Site =>
      ports input.1 input.2) :
    Primrec fun input : (Input × Site) × CrossoverVariable =>
      scopedCrossoverVariableMap input.1.2
        (ports input.1.1 input.1.2) input.2 := by
  have portsAt : Primrec fun input :
      (Input × Site) × CrossoverVariable =>
      ports input.1.1 input.1.2 :=
    portsPrimrec.comp Primrec.fst
  have aLeft : Primrec fun input :
      (Input × Site) × CrossoverVariable =>
      (Sum.inl (ports input.1.1 input.1.2).aLeft :
        Sum Variable (Site × CrossoverInternal)) :=
    Primrec.sumInl.comp (CrossoverPorts.aLeft_primrec.comp portsAt)
  have aRight : Primrec fun input :
      (Input × Site) × CrossoverVariable =>
      (Sum.inl (ports input.1.1 input.1.2).aRight :
        Sum Variable (Site × CrossoverInternal)) :=
    Primrec.sumInl.comp (CrossoverPorts.aRight_primrec.comp portsAt)
  have bTop : Primrec fun input :
      (Input × Site) × CrossoverVariable =>
      (Sum.inl (ports input.1.1 input.1.2).bTop :
        Sum Variable (Site × CrossoverInternal)) :=
    Primrec.sumInl.comp (CrossoverPorts.bTop_primrec.comp portsAt)
  have bBottom : Primrec fun input :
      (Input × Site) × CrossoverVariable =>
      (Sum.inl (ports input.1.1 input.1.2).bBottom :
        Sum Variable (Site × CrossoverInternal)) :=
    Primrec.sumInl.comp (CrossoverPorts.bBottom_primrec.comp portsAt)
  have internal (name : CrossoverInternal) :
      Primrec fun input : (Input × Site) × CrossoverVariable =>
        (Sum.inr (input.1.2, name) :
          Sum Variable (Site × CrossoverInternal)) :=
    Primrec.sumInr.comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.const name))
  have is (name : CrossoverVariable) :
      Primrec fun input : (Input × Site) × CrossoverVariable =>
        decide (input.2 = name) :=
    ((Primrec.eq.comp
      (CrossoverVariable.equivFin_primrec.comp Primrec.snd)
      (Primrec.const (CrossoverVariable.equivFin name))).decide).of_eq
        fun input => by simp
  exact (Primrec.cond (is .aLeft) aLeft
    (Primrec.cond (is .aInnerLeft) (internal .aInnerLeft)
    (Primrec.cond (is .upperLeft) (internal .upperLeft)
    (Primrec.cond (is .lowerLeft) (internal .lowerLeft)
    (Primrec.cond (is .bTop) bTop
    (Primrec.cond (is .bInnerTop) (internal .bInnerTop)
    (Primrec.cond (is .center) (internal .center)
    (Primrec.cond (is .bInnerBottom) (internal .bInnerBottom)
    (Primrec.cond (is .bBottom) bBottom
    (Primrec.cond (is .upperRight) (internal .upperRight)
    (Primrec.cond (is .lowerRight) (internal .lowerRight)
    (Primrec.cond (is .aInnerRight) (internal .aInnerRight)
      aRight)))))))))))).of_eq fun input => by
        cases input.2 <;> rfl

theorem scopedCrossoverInstance_primrec
    {Input Site Variable : Type*}
    [Primcodable Input] [Primcodable Site] [Primcodable Variable]
    (site : Input → Site)
    (ports : Input → CrossoverPorts Variable)
    (origin : Input → Cell)
    (scale : Input → Int)
    (sitePrimrec : Primrec site)
    (portsPrimrec : Primrec ports)
    (originPrimrec : Primrec origin)
    (scalePrimrec : Primrec scale) :
    Primrec fun input =>
      scopedCrossoverInstance (site input) (ports input)
        (origin input) (scale input) := by
  let indexedPorts : Input → Site → CrossoverPorts Variable :=
    fun input _ => ports input
  have indexedPortsPrimrec : Primrec fun input : Input × Site =>
      indexedPorts input.1 input.2 :=
    portsPrimrec.comp Primrec.fst
  have variableMap : Primrec fun input :
      Input × CrossoverVariable =>
      scopedCrossoverVariableMap (site input.1)
        (ports input.1) input.2 := by
    have generic := scopedCrossoverVariableMap_primrec
      indexedPorts indexedPortsPrimrec
    exact generic.comp
      (Primrec.pair
        (Primrec.pair Primrec.fst (sitePrimrec.comp Primrec.fst))
        Primrec.snd)
  exact (instantiateFormula_primrec
    (fun input sourceVariable =>
      scopedCrossoverVariableMap (site input)
        (ports input) sourceVariable)
    origin scale (fun _ => crossoverFormula)
    variableMap originPrimrec scalePrimrec
      (Primrec.const crossoverFormula)).of_eq fun _ => rfl

theorem crossoverFamily_primrec
    {Input Site Variable : Type*}
    [Primcodable Input] [Primcodable Site] [Primcodable Variable]
    (sites : Input → List Site)
    (ports : Input → Site → CrossoverPorts Variable)
    (origin : Input → Site → Cell)
    (scale : Input → Int)
    (sitesPrimrec : Primrec sites)
    (portsPrimrec : Primrec fun input : Input × Site =>
      ports input.1 input.2)
    (originPrimrec : Primrec fun input : Input × Site =>
      origin input.1 input.2)
    (scalePrimrec : Primrec scale) :
    Primrec fun input =>
      crossoverFamily (sites input) (ports input)
        (origin input) (scale input) := by
  have one : Primrec₂ fun (input : Input) (site : Site) =>
      scopedCrossoverInstance site (ports input site)
        (origin input site) (scale input) := by
    change Primrec fun combined : Input × Site =>
      scopedCrossoverInstance combined.2
        (ports combined.1 combined.2)
        (origin combined.1 combined.2) (scale combined.1)
    exact scopedCrossoverInstance_primrec
      (fun input : Input × Site => input.2)
      (fun input => ports input.1 input.2)
      (fun input => origin input.1 input.2)
      (fun input => scale input.1)
      Primrec.snd portsPrimrec originPrimrec
      (scalePrimrec.comp Primrec.fst)
  exact (Primrec.list_flatMap sitesPrimrec one).of_eq fun _ => rfl

end PlanarThreeSAT
end LeanTrominoes
