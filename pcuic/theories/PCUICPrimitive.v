(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Universes BasicAst Reflect
     Environment EnvironmentTyping.
From Equations Require Import Equations.
From Coq Require Import ssreflect.

Variant prim_tag := 
  | primInt
  | primFloat.
  (* | primArray. *)
Derive NoConfusion EqDec for prim_tag.

(** We don't enforce the type of the array here*)
Record array_model (term : Type) :=
  { array_instance : Instance.t;
    array_type : term;
    array_default : term;
    array_value : list term }.
Derive NoConfusion for array_model.
Instance array_model_eqdec {term} (e : EqDec term) : EqDec (array_model term).
Proof. eqdec_proof. Qed.

Inductive prim_model (term : Type) : prim_tag -> Type :=
| primIntModel (i : uint63_model) : prim_model term primInt
| primFloatModel (f : float64_model) : prim_model term primFloat.
(* | primArrayModel (a : array_model term) : prim_model term primArray. *)
Arguments primIntModel {term}.
Arguments primFloatModel {term}.
(* Arguments primArrayModel {term}. *)

Derive Signature NoConfusion for prim_model.

Definition prim_model_of (term : Type) (p : prim_tag) : Type := 
  match p with
  | primInt => uint63_model
  | primFloat => float64_model
  (* | primArray => array_model term *)
  end.

Definition prim_val term := ∑ t : prim_tag, prim_model term t.
Definition prim_val_tag {term} (s : prim_val term) := s.π1.
Definition prim_val_model {term} (s : prim_val term) : prim_model term (prim_val_tag s) := s.π2.

Definition prim_model_val {term} (p : prim_val term) : prim_model_of term (prim_val_tag p) :=
  match prim_val_model p in prim_model _ t return prim_model_of term t with
  | primIntModel i => i
  | primFloatModel f => f
  (* | primArrayModel a => a *)
  end.

Lemma exist_irrel_eq {A} (P : A -> bool) (x y : sig P) : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x as [x p], y as [y q]; simpl; intros ->.
  now destruct (uip p q).
Qed.

Instance reflect_eq_Z : ReflectEq Z := EqDec_ReflectEq _.

Local Obligation Tactic := idtac.
#[program]
Instance reflect_eq_uint63 : ReflectEq uint63_model := 
  { eqb x y := eqb (proj1_sig x) (proj1_sig y) }.
Next Obligation.
  cbn -[eqb].
  intros x y.
  elim: eqb_spec. constructor.
  now apply exist_irrel_eq.
  intros neq; constructor => H'; apply neq; now subst x.
Qed.

Instance reflect_eq_spec_float : ReflectEq SpecFloat.spec_float := EqDec_ReflectEq _.
  
#[program]
Instance reflect_eq_float64 : ReflectEq float64_model := 
  { eqb x y := eqb (proj1_sig x) (proj1_sig y) }.
Next Obligation.
  cbn -[eqb].
  intros x y.
  elim: eqb_spec. constructor.
  now apply exist_irrel_eq.
  intros neq; constructor => H'; apply neq; now subst x.
Qed.

(** Propositional UIP is needed below *)
Set Equations With UIP.

Instance prim_model_eqdec {term} (*e : EqDec term*) : forall p : prim_tag, EqDec (prim_model term p).
Proof. eqdec_proof. Qed.

Instance prim_tag_model_eqdec term : EqDec (prim_val term).
Proof. eqdec_proof. Defined.

Instance prim_val_reflect_eq term : ReflectEq (prim_val term) := EqDec_ReflectEq _.

(** Printing *)

Definition string_of_float64_model (f : float64_model) := 
  "<>".

Definition string_of_prim {term} (soft : term -> string) (p : prim_val term) : string :=
  match p.π2 return string with
  | primIntModel f => "(int: " ^ string_of_Z (proj1_sig f) ^ ")"
  | primFloatModel f => "(float: " ^ string_of_float64_model f ^ ")"
  (* | primArrayModel a => "(array:" ^ ")" *)
  end.
