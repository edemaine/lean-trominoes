/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Domino.DominoWordRAMEndpointValues
import LeanTrominoes.Computation.RAM.NaturalSemantics
import LeanTrominoes.Computation.RAM.RegisterFrame

/-! # Ordinary RAM instructions writing two padded graph endpoints

The first 64 registers belong to the arithmetic probe. Candidate indices and
endpoint pointers occupy registers64–71, and only the endpoint cursor changes.
Dimension and phase are fixed parameters of the unrolled program.
-/
namespace LeanTrominoes.Domino.WordRAM.EndpointWriter
open ComplexityAbstract.RAM
abbrev Data := NaturalData 128
abbrev Code := Structured.Code 128
namespace H
abbrev u : Fin 128 := 64
abbrev v : Fin 128 := 65
abbrev n : Fin 128 := 66
abbrev parities : Fin 128 := 67
abbrev active : Fin 128 := 68
abbrev index : Fin 128 := 69
abbrev left : Fin 128 := 70
abbrev right : Fin 128 := 71
end H
namespace R
abbrev two : Fin 128 := 96
abbrev one : Fin 128 := 97
abbrev coordinate : Fin 128 := 98
abbrev address : Fin 128 := 99
abbrev bit : Fin 128 := 100
abbrev sum : Fin 128 := 101
abbrev xor : Fin 128 := 102
abbrev weight : Fin 128 := 103
abbrev term : Fin 128 := 104
abbrev phase : Fin 128 := 105
abbrev source : Fin 128 := 106
abbrev target : Fin 128 := 107
abbrev capacity : Fin 128 := 108
abbrev dummy : Fin 128 := 109
abbrev storeAddress : Fin 128 := 110
abbrev constant : Fin 128 := 111
end R

def constant (dst : Fin 128) (value : Nat) : Code := .atom (.constant dst value)
def add (dst a b : Fin 128) : Code := .atom (.arithmetic .add dst a b)
def mul (dst a b : Fin 128) : Code := .atom (.arithmetic .mul dst a b)
def copy (dst src : Fin 128) : Code := .atom (.copy dst src)

def header : Code := .seq (constant R.two 2) <| .seq (constant R.one 1) (constant R.phase 0)
def headed (data : Data) := ((data.set R.two 2).set R.one 1).set R.phase 0

def xorStep {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) (i : Fin d) : Code :=
  .seq (constant R.coordinate i.val) <|
  .seq (add R.address H.parities R.coordinate) <|
  .seq (.atom (.load R.bit R.address)) <|
  .seq (constant R.sum (phase i).val) <|
  .seq (add R.sum R.sum R.bit) <|
  .seq (.atom (.arithmetic .mod R.xor R.sum R.two)) <|
  .seq (constant R.weight (2^i.val)) <|
  .seq (mul R.term R.xor R.weight) (add R.phase R.phase R.term)

def xor1 (data : Data) (i : Nat) := data.set R.coordinate i
def xor2 (data : Data) (i : Nat) := (xor1 data i).set R.address (data.1 H.parities+i)
def xor3 (data : Data) (i : Nat) := (xor2 data i).set R.bit (data.2 (data.1 H.parities+i))
def xor4 (data : Data) (i bit : Nat) := (xor3 data i).set R.sum bit
def xor5 (data : Data) (i bit : Nat) := (xor4 data i bit).set R.sum (bit+data.2 (data.1 H.parities+i))
def xor6 (data : Data) (i bit : Nat) := (xor5 data i bit).set R.xor ((bit+data.2 (data.1 H.parities+i))%data.1 R.two)
def xor7 (data : Data) (i bit : Nat) := (xor6 data i bit).set R.weight (2^i)
def xor8 (data : Data) (i bit : Nat) := (xor7 data i bit).set R.term (((bit+data.2 (data.1 H.parities+i))%data.1 R.two)*2^i)
def xorState (data : Data) (i bit : Nat) := (xor8 data i bit).set R.phase
  (data.1 R.phase+((bit+data.2 (data.1 H.parities+i))%data.1 R.two)*2^i)

def xorList {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) : List (Fin d) → Code
  | [] => copy R.phase R.phase
  | i::rest => .seq (xorStep phase i) (xorList phase rest)

def endpoints {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) : Code :=
  .seq (constant R.capacity (2^d)) <|
  .seq (mul R.source R.capacity H.u) <|
  .seq (constant R.constant (finFunctionFinEquiv phase).val) <|
  .seq (add R.source R.source R.constant) <|
  .seq (mul R.target R.capacity H.v) <|
  .seq (add R.target R.target R.phase) (mul R.dummy H.n R.capacity)

def choose : Code := .branch (.eq H.active R.phase)
  (.seq (copy R.source R.dummy) (copy R.target R.dummy)) (copy R.constant R.constant)

/-- Each endpoint pair uses four address/store instructions and one cursor increment. -/
def writePair (source target : Fin 128) : Code :=
  .seq (add R.storeAddress H.left H.index) <|
  .seq (.atom (.store R.storeAddress source)) <|
  .seq (add R.storeAddress H.right H.index) <|
  .seq (.atom (.store R.storeAddress target)) (add H.index H.index R.one)

def footer : Code := .seq (constant R.phase 0) <| .seq choose <|
  .seq (writePair R.source R.target) (writePair R.target R.source)
def program {d : Nat} (phase : PeriodicLatticeGraph.DoubleCover.Phase d) : Code :=
  .seq (.seq header (xorList phase (List.finRange d))) (.seq (endpoints phase) footer)

end LeanTrominoes.Domino.WordRAM.EndpointWriter
