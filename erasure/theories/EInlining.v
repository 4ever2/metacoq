From Stdlib Require Import List String Arith Lia ssreflect ssrbool.
Import ListNotations.
From Equations Require Import Equations.
Set Equations Transparent.

From MetaRocq.PCUIC Require Import PCUICAstUtils.
From MetaRocq.Utils Require Import MRList bytestring utils monad_utils.
From MetaRocq.Erasure Require Import EPrimitive EAst EEnvMap EInduction EGlobalEnv.

Import Kernames.
Import MRMonadNotation.

(* Inlining hints *)
Definition inlining := KernameSet.t.
(* Fast maps for actual inlinings *)
Definition constants_inlining := KernameMap.t term.

Section Inline.
  Context (inlining : constants_inlining).

  Equations inline (t : term) : term :=
    | tVar na => tVar na
    | tLambda nm bod => tLambda nm (inline bod)
    | tLetIn nm dfn bod => tLetIn nm (inline dfn) (inline bod)
    | tApp fn arg => tApp (inline fn) (inline arg)
    | tConst nm with KernameMap.find nm inlining :=
      { | Some body := (* Already inlined body *) body
        | None := tConst nm }
    | tConstruct i m args => tConstruct i m (map inline args)
    | tCase i mch brs => tCase i mch (map (on_snd inline) brs)
    | tFix mfix idx => tFix (map (map_def inline) mfix) idx
    | tCoFix mfix idx => tCoFix (map (map_def inline) mfix) idx
    | tProj p bod => tProj p (inline bod)
    | tPrim p => tPrim (map_prim inline p)
    | tLazy t => tLazy (inline t)
    | tForce t => tForce (inline t)
    | tRel n => tRel n
    | tBox => tBox
    | tEvar ev args => tEvar ev (map inline args).
End Inline.

Definition inline_constant_decl inlining cb :=
  {| cst_body := option_map (inline inlining) cb.(cst_body) |}.

Definition inline_decl inlining d : (kername * global_decl) :=
  match d.2 with
  | ConstantDecl cb => (d.1, ConstantDecl (inline_constant_decl inlining cb))
  | InductiveDecl idecl => d
  end.

Definition inline_add (inlining : inlining) (acc : global_context × constants_inlining) decl :=
  let '(Σ, inls) := acc in
  if KernameSet.mem decl.1 inlining then
    match decl.2 with
    | ConstantDecl {| cst_body := Some body |} => KernameMap.add decl.1 body inls
    | _ => inls
    end
  else inls.

Definition inline_env (inlining : KernameSet.t) Σ : global_context × constants_inlining :=
  let inline_decl '(Σ, inls) decl :=
    let inldecl := inline_decl inls decl in
    (inldecl :: Σ, inline_add inlining (Σ, inls) inldecl)
  in
  fold_left (inline_decl) (rev Σ) ([], KernameMap.empty _).

Definition inlined_program :=
  (global_context × constants_inlining) × term.

Definition inlined_program_inlinings (pr : inlined_program) : constants_inlining :=
  pr.1.2.

Coercion inlined_program_inlinings : inlined_program >-> constants_inlining.

Definition inline_program inlining (p : program) : inlined_program :=
  let '(Σ', inls) := inline_env inlining p.1 in
  (Σ', inls, inline inls p.2).

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Definition forget_inlining_info (pr : inlined_program) : eprogram :=
  let '((Σ', inls), p) := pr in
  (Σ', p).

Coercion forget_inlining_info : inlined_program >-> eprogram.

Definition eval_inlined_program wfl (pr : inlined_program) := eval_eprogram wfl pr.

Lemma fold_right_rev_left :
  forall [A B : Type] (f : B -> A -> B) (l : list A) (i : B),
  fold_left f (rev l) i = fold_right (fun (x : A) (y : B) => f y x) i l.
Proof. Admitted.

Lemma fresh_inline_env {Σ : global_context} :
  forall kn inlining,
  fresh_global kn Σ -> fresh_global kn (inline_env inlining Σ).1.
Proof. Admitted.

Lemma inlining_env_wf {efl : EEnvFlags} {Σ : global_context} :
  WcbvFlags ->
  forall inlining : inlining,
  wf_glob Σ -> wf_glob (inline_env inlining Σ).1.
Proof.
  intros flags inlining wfΣ.
  induction Σ using rev_ind.
  - assumption.
  - assert (wfl : wf_glob l) by admit.
    assert (wfx : wf_glob [x]) by admit. clear wfΣ.
    apply IHΣ in wfl. clear IHΣ.
    unfold  inline_env in *.
    rewrite rev_app. cbn [rev].
    rewrite fold_left_app.
    cbn.
    Search (fold_left _ (_ ++ _) _).

  induction wfΣ.
  - constructor.
  - destruct d.
    + admit.
    + cbn. constructor.
  induction Σ.
  - assumption.
  - inversion H0; subst.
    apply IHΣ in H3; clear IHΣ.
    apply fresh_inline_env with (inlining := inlining0) in H5.
    unfold inline_env.
    rewrite rev_cons.
    rewrite fold_left_app.
    unfold inline_env in *.
    destruct (fold_left _ (rev _) _).
    cbn in *.
    destruct d; cbn.
    + constructor; auto.
      cbn -[inline_constant_decl].
        cbn in H4.
    + constructor; auto.
Admitted.



Lemma q : forall inlining0 Σ t,
    (forget_inlining_info (inline_program inlining0 (Σ, t))).1
    = (inline_env inlining0 Σ).1.
Proof.
  intros.
  unfold inline_program.
  cbn [fst].
  destruct (inline_env inlining0 Σ).
  reflexivity.
Qed.

Lemma trust_inlining_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall inlining : inlining,
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (inline_program inlining input).
Proof.
  intros.
  destruct input.
  unfold wf_eprogram in *.
  cbn in *.
  destruct H0.
  split.
  - rewrite q.
    apply inlining_env_wf; auto.
  - admit.
Admitted.



Lemma optimize_env_wf {efl : EEnvFlags} {Σ : GlobalContextMap.t} :
  has_tBox -> has_tRel ->
  wf_glob Σ -> wf_glob (efl := disable_projections_env_flag efl) (optimize_env Σ).
Proof.
Proof.
Axiom trust_inlining_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining (p : Transform.program _ term)
  (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  let ip := inline_program inlining p in
  eval_eprogram wfl ip v' /\ v' = inline ip v.

Import Transform.

Program Definition inline_transformation (efl : EEnvFlags) (wfl : WcbvFlags) inlining :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_inlined_program wfl) :=
  {| name := "inlining ";
    transform p _ := inline_program inlining p ;
    pre p := wf_eprogram efl p ;
    post (p : inlined_program) := wf_eprogram efl p ;
    obseq p hp (p' : inlined_program) v v' := v' = inline p' v |}.

Next Obligation.
  now apply trust_inlining_wf.
Qed.
Next Obligation.
  now eapply trust_inlining_pres.
Qed.

#[global]
Axiom trust_inline_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining,
  TransformExt.t (inline_transformation efl wfl inlining)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1.1 p'.1.1).

Definition extends_inlined_eprogram (p q : inlined_program) :=
  extends p.1.1 q.1.1 /\ p.2 = q.2.

#[global]
Axiom trust_inline_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) inlining,
  TransformExt.t (inline_transformation efl wfl inlining)
    extends_eprogram extends_inlined_eprogram.


Program Definition forget_inlining_info_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
      (eval_inlined_program wfl) (eval_eprogram wfl) :=
    {| name := "forgetting about inlining info";
      transform p _ := (p.1.1, p.2) ;
      pre (p : inlined_program) := wf_eprogram efl p ;
      post (p : eprogram) := wf_eprogram efl p ;
      obseq p hp p' v v' := v' = v |}.

  Next Obligation.
    destruct input as [[Σ inls] t].
    exact p.
  Qed.
  Next Obligation.
    exists v; split => //. subst p'.
    now destruct p as [[Σ inls] t].
  Qed.

#[global]
Lemma forget_inlining_info_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inlining_info_transformation efl wfl)
    (fun p p' => extends p.1.1 p'.1.1) (fun p p' => extends p.1 p'.1).
Proof.
  intros.
  red. now intros [[] ?] [[] ?]; cbn.
Qed.

#[global]
Lemma forget_inlining_info_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (forget_inlining_info_transformation efl wfl)
    extends_inlined_eprogram extends_eprogram.
Proof.
  intros ? ? [[] ?] [[] ?]; cbn.
  now rewrite /extends_inlined_eprogram /extends_eprogram /=.
Qed.
