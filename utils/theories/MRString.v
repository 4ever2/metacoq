From Stdlib Require Import Strings.Byte.
From Bytestring Require Import ByteCompare Bytestring ByteCompareSpec.
From MetaRocq.Utils Require Import MRCompare ReflectEq.
From Bytestring Require Export BytestringUtils.


Global Program Instance byte_reflect_eq : ReflectEq byte :=
  {| ReflectEq.eqb := ByteCompare.eqb |}.
Next Obligation.
  rewrite ByteCompareSpec.eqb_compare.
  destruct (compare_spec x y); constructor; auto.
  all:apply lt_not_eq in H.
  - assumption.
  - now apply not_eq_sym.
Qed.

From Stdlib Require Import Orders.
Module StringOT <: UsualOrderedType.
Include Bytestring.StringOT.

#[global] Program Instance reflect_eq_string : ReflectEq String.t := {
  eqb := String.eqb
}.
Next Obligation.
  rename x into s, y into s'.
  destruct (String.eqb s s') eqn:e; constructor.
  - rewrite String.eqb_compare in e. fold (compare s s') in e.
    now destruct (StringOT.compare_spec s s').
  - rewrite String.eqb_compare in e.
    fold (compare s s') in e.
    destruct (StringOT.compare_spec s s').
    now apply lt_not_eq.
    now apply lt_not_eq.
    now apply not_eq_sym, lt_not_eq.
Qed.
End StringOT.

Module StringOTOrig := OrdersAlt.Backport_OT StringOT.

Notation string_compare := StringOT.compare.
Notation string_compare_eq := StringOT.compare_eq.
Notation CompareSpec_string := StringOT.compare_spec.
