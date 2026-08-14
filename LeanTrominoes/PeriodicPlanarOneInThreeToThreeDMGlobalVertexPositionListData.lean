/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalPositionData

/-! # Named data-only blocks of assembled vertex positions -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

def assembledTriplePositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  (triples source).map
    (assembledTriplePositionData source variableOrigin clauseOrigin)

def assembledRedElementPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  (redElements source).map
    (assembledRedElementPositionData source variableOrigin clauseOrigin)

def assembledGreenElementPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  (greenElements source).map
    (assembledGreenElementPositionData source variableOrigin clauseOrigin)

def assembledBlueElementPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  (blueElements source).map
    (assembledBlueElementPositionData source variableOrigin clauseOrigin)

def assembledGreenBlueElementPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  assembledGreenElementPositionsData source variableOrigin clauseOrigin ++
    assembledBlueElementPositionsData source variableOrigin clauseOrigin

def assembledColoredElementPositionsData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  assembledRedElementPositionsData source variableOrigin clauseOrigin ++
    assembledGreenBlueElementPositionsData source variableOrigin clauseOrigin

def assembledVertexPositionListData
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (variableOrigin : Variable → Cell)
    (clauseOrigin : Nat → Cell) : List Cell :=
  assembledTriplePositionsData source variableOrigin clauseOrigin ++
    assembledColoredElementPositionsData source variableOrigin clauseOrigin

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
