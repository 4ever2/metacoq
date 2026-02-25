(* Primitive types *)

From Stdlib Require Import Uint63 PrimFloat SpecFloat FloatOps ZArith HexadecimalString.
From Bytestring Require Import Bytestring.
From MetaRocq.Utils Require Import MRString.
Local Open Scope bs.

Variant prim_tag :=
  | primInt
  | primFloat
  | primString
  | primArray.
Derive NoConfusion EqDec for prim_tag.
