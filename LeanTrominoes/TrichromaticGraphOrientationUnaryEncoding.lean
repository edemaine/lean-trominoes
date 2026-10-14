/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.TrichromaticGraphOrientationFlatEncoding
import LeanTrominoes.FiniteCoordinateEncoding

/-! # Lossless unary records for finite colored graph orientation -/
namespace LeanTrominoes.TrichromaticGraphOrientation.UnaryEncoding
open UnaryFieldEncoderMachine
open Tromino.FiniteCoordinateColumns (symbolBool unaryFields_bool)

def decodeUnary (symbols : List Symbol) : Option (List Nat) :=
  CompletionStripEncoding.decodeUnaryAux 0 (symbols.map symbolBool)

@[simp] theorem decodeUnary_fields (fields : List Nat) : decodeUnary (unaryFields fields)=some fields := by
  rw [decodeUnary,unaryFields_bool,CompletionStripEncoding.decodeUnaryAux_unaryFields]

def decode (symbols : List Symbol) : Option Input := decodeUnary symbols >>= FlatEncoding.decodeFields

def finEncoding : _root_.LeanTrominoes.FiniteEncoding Input where
  Γ := Symbol
  ΓFin := inferInstance
  encoding := {
    encode graph := unaryFields (FlatEncoding.fields graph)
    decode := decode
    decode_encode graph := by simp [decode] }

theorem edgeCount_le_length (graph : Input) : graph.2.length ≤ (finEncoding.encode graph).length := by
  simp only [FiniteEncoding.encode,finEncoding,unaryFields_length]
  have fields := FlatEncoding.fields_length graph
  omega

end LeanTrominoes.TrichromaticGraphOrientation.UnaryEncoding
