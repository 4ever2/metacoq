From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ssreflect ssrbool.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst EProgram.

Definition map_subterms (f : term -> term) (t : term) : term :=
  match t with
  | tEvar n ts => tEvar n (map f ts)
  | tLambda na body => tLambda na (f body)
  | tLetIn na val body => tLetIn na (f val) (f body)
  | tApp hd arg => tApp (f hd) (f arg)
  | tCase p disc brs =>
    tCase p (f disc) (map (on_snd f) brs)
  | tProj p t => tProj p (f t)
  | tFix def i => tFix (map (map_def f) def) i
  | tCoFix def i => tCoFix (map (map_def f) def) i
  | tPrim p => tPrim (map_prim f p)
  | tLazy t => tLazy (f t)
  | tForce t => tForce (f t)
  | tConstruct ind n args => tConstruct ind n (map f args)
  | tRel n => tRel n
  | tVar na => tVar na
  | tConst kn => tConst kn
  | tBox => tBox
  end.

Section betared.

  Fixpoint beta_body (body : term) (args : list term) {struct args} : term :=
    match args with
    | [] => body
    | a :: args =>
        match body with
        | tLambda na body => beta_body (body{0 := a}) args
        | _ => mkApps body (a :: args)
        end
    end.

  Fixpoint betared_aux (args : list term) (t : term) : term :=
    match t with
    | tApp hd arg => betared_aux (betared_aux [] arg :: args) hd
    | tLambda na body =>
      let b := betared_aux [] body in
      beta_body (tLambda na b) args
    | t => mkApps (map_subterms (betared_aux []) t) args
    end.

  Definition betared : term -> term := betared_aux [].

  Definition betared_in_constant_body cst :=
    {| cst_body := option_map betared (cst_body cst); |}.

  Definition betared_in_decl d :=
    match d with
    | ConstantDecl cst => ConstantDecl (betared_in_constant_body cst)
    | _ => d
    end.

End betared.

Definition betared_env (Σ : global_declarations) : global_declarations :=
  map (fun '(kn, decl) => (kn, betared_in_decl decl)) Σ.

Definition betared_program (p : program) : program :=
  (betared_env p.1, betared p.2).

From MetaRocq.Erasure Require Import EProgram EWellformed EWcbvEval.
From MetaRocq.Common Require Import Transform.

Lemma fresh_betared_env {Σ : global_context} :
  forall kn,
  EGlobalEnv.fresh_global kn Σ -> EGlobalEnv.fresh_global kn (betared_env Σ).
Proof.
  intros.
  induction Σ.
  - auto.
  - inversion H. subst.
    cbn.
    destruct a. cbn in *.
    unfold EGlobalEnv.fresh_global.
    constructor.
    + assumption.
    + apply Forall_map.
      apply Forall_forall.
      intros x HIn.
      apply PCUICWfUniverses.Forall_In with (x := x) in H3; auto.
      destruct x. assumption.
Qed.

Lemma lookup_env_betared {Σ : global_context} kn :
  EGlobalEnv.lookup_env (betared_env Σ) kn = option_map (fun decl => betared_in_decl decl) (EGlobalEnv.lookup_env Σ kn).
Proof.
  induction Σ; cbn; auto.
  destruct a. cbn.
  destruct (eqb_spec kn k) => //.
Qed.

Lemma lookup_constant_betared {Σ : global_context} c :
  option_map betared_in_constant_body (EGlobalEnv.lookup_constant Σ c) = EGlobalEnv.lookup_constant (betared_env Σ) c.
Proof.
  rewrite /EGlobalEnv.lookup_constant.
  rewrite lookup_env_betared.
  destruct EGlobalEnv.lookup_env => //=.
  destruct g => //.
Qed.

Lemma lookup_minductive_betared {Σ : global_context} i :
  EGlobalEnv.lookup_minductive Σ i = EGlobalEnv.lookup_minductive (betared_env Σ) i.
Proof.
  rewrite /EGlobalEnv.lookup_minductive.
  rewrite lookup_env_betared.
  destruct EGlobalEnv.lookup_env => //=.
  destruct g => //.
Qed.

Lemma lookup_inductive_betared {Σ : global_context} p :
  EGlobalEnv.lookup_inductive Σ p = EGlobalEnv.lookup_inductive (betared_env Σ) p.
Proof.
  rewrite /EGlobalEnv.lookup_inductive.
  by rewrite lookup_minductive_betared.
Qed.

Lemma lookup_constructor_betared {Σ : global_context} p k :
  EGlobalEnv.lookup_constructor Σ p k = EGlobalEnv.lookup_constructor (betared_env Σ) p k.
Proof.
  rewrite /EGlobalEnv.lookup_constructor.
  by rewrite lookup_inductive_betared.
Qed.

Lemma lookup_constructor_pars_args_betared {Σ : global_context} i n :
  EGlobalEnv.lookup_constructor_pars_args Σ i n = EGlobalEnv.lookup_constructor_pars_args (betared_env Σ) i n.
Proof.
  rewrite /EGlobalEnv.lookup_constructor_pars_args.
  by rewrite lookup_constructor_betared.
Qed.

Lemma lookup_projection_betared {Σ : global_context} p :
  EGlobalEnv.lookup_projection Σ p = EGlobalEnv.lookup_projection (betared_env Σ) p.
Proof.
  rewrite /EGlobalEnv.lookup_projection.
  by rewrite lookup_constructor_betared.
Qed.

Lemma betared_aux_length args :
  #|args| = #|map (betared_aux []) args|.
Proof.
  induction args; cbn.
  - reflexivity.
  - rewrite IHargs.
    reflexivity.
Qed.

Lemma betared_aux_isLambda x :
  isLambda (dbody x) -> isLambda (betared_aux [] (dbody x)).
Proof.
  intros.
  destruct dbody; auto.
  discriminate.
Qed.

Lemma betared_env_wf_brs {Σ : global_context} ind l :
    wf_brs Σ ind l = wf_brs (betared_env Σ) ind l.
Proof.
  rewrite /wf_brs.
  by rewrite -lookup_inductive_betared.
Qed.

Lemma beta_body_wf {efl : EEnvFlags} {haslam : has_tLambda} {hasapp : has_tApp}  {Σ : global_context} t k args :
  wellformed (betared_env Σ) k t ->
  All (fun x => wellformed (betared_env Σ) k x) args ->
  wellformed (betared_env Σ) k (beta_body t args).
Proof.
  intros.
  generalize dependent t.
  generalize dependent k.
  induction args; intros; simpl; auto.
  destruct t; simpl; try (
    rewrite wellformed_mkApps; auto;
    inversion X; subst;
    apply All_forallb in X0;
    rtoProp; split; try assumption;
    simpl; inversion H; rewrite H2; auto
  ).
  - inversion X; subst.
    apply IHargs; auto.
    apply wellformed_subst; simpl.
    + by rtoProp.
    + inversion H.
      move: H2 => /andP[] => //.
Qed.

Lemma betared_hasapp {efl : EEnvFlags} {Σ : global_context} t k :
  ~ has_tApp ->
  wellformed Σ k t ->
  (betared t) = t.
Proof.
  intros hasapp.
  induction t in k |- * using EInduction.term_forall_list_ind; intros; simpl in *; cbn; auto.
  - f_equal.
    rtoProp.
    apply forallb_All in H0.
    apply All_forall with (b := k) in X.
    apply All_impl_All in X; auto.
    apply All_map_id.
    assumption.
  - f_equal.
    rtoProp.
    eauto.
  - rtoProp.
    f_equal; eauto.
  - rtoProp.
    contradiction.
  - rtoProp.
    f_equal.
    destruct cstr_as_blocks.
    + rtoProp.
      apply forallb_All in H2.
      apply All_forall with (b := k) in X.
      apply All_impl_All in X; auto.
      apply All_map_id.
      assumption.
    + by destruct args.
  - rtoProp.
    f_equal.
    + eauto.
    + clear IHt H hasapp.
      apply All_map_id.
      apply Forall_All.
      apply In_Forall.
      intros x HIn.
      apply All_Forall in X.
      apply forallb_Forall in H1.
      apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
      apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
      unfold on_snd.
      erewrite X; eauto.
      by destruct x.
  - rtoProp.
    f_equal.
    eauto.
  - unfold wf_fix in H.
    rtoProp.
    f_equal.
    clear H hasapp H2 H0.
    apply All_map_id.
    apply Forall_All.
    apply In_Forall.
    intros x HIn.
    apply All_Forall in X.
    apply forallb_Forall in H1.
    apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
    apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
    unfold map_def.
    erewrite X; eauto.
    by destruct x.
  - unfold wf_fix in H.
    rtoProp.
    f_equal.
    clear H hasapp H0.
    apply All_map_id.
    apply Forall_All.
    apply In_Forall.
    intros x HIn.
    apply All_Forall in X.
    apply forallb_Forall in H1.
    apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
    apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
    unfold map_def.
    erewrite X; eauto.
    by destruct x.
  - rtoProp.
    f_equal.
    destruct p, p; auto.
    cbn in *.
    unfold test_array_model in *; rtoProp.
    inversion_clear X.
    destruct X0 as [X Xall].
    destruct a.
    cbn in *.
    f_equal.
    f_equal.
    unfold map_array_model; cbn.
    erewrite X; eauto; clear X.
    f_equal.
    apply All_map_id.
    apply Forall_All.
    apply In_Forall.
    intros x HIn.
    apply All_Forall in Xall.
    apply forallb_Forall in H1.
    apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
    apply PCUICWfUniverses.Forall_In with (x := x) in Xall; eauto.
  - rtoProp.
    f_equal.
    eauto.
  - rtoProp.
    f_equal.
    eauto.
Qed.

Lemma betared_env_hasapp {efl : EEnvFlags} {Σ : global_context} :
  ~ has_tApp ->
  wf_glob Σ ->
  (betared_env Σ) = Σ.
Proof.
  intros hasapp wfΣ.
  induction Σ; auto; cbn.
  destruct a, g; cbn.
  - inversion wfΣ; subst.
    repeat f_equal.
    2: apply IHΣ; assumption.
    unfold betared_in_constant_body.
    destruct c, cst_body; cbn; auto.
    erewrite betared_hasapp; eauto.
    inversion H3; eauto.
  - inversion wfΣ; subst.
    f_equal.
    apply IHΣ.
    assumption.
Qed.

Lemma forallb_wf_betared {efl : EEnvFlags} {Σ : global_context} k args :
  ~ has_tApp ->
  forallb (wellformed Σ k) args ->
  forallb (wellformed Σ k) (map (betared) args).
Proof.
  intros hasapp wfargs.
  apply forallb_Forall.
  apply forallb_Forall in wfargs.
  apply Forall_map.
  apply In_Forall => x HIn.
  apply PCUICWfUniverses.Forall_In with (x := x) in wfargs; auto.
  erewrite betared_hasapp; eauto.
Qed.

Lemma betared_aux_wf {efl : EEnvFlags} {Σ : global_context} t k args :
  wf_glob Σ ->
  wellformed Σ k t ->
  All (fun x => wellformed (betared_env Σ) k x) args ->
  (has_tApp \/ (~ has_tApp /\ args = [])) ->
  wellformed (betared_env Σ) k (betared_aux args t).
Proof.
  intros wfΣ.
  induction t in k, args |- * using EInduction.term_forall_list_ind; intros; simpl in *.
  - destruct H0 as [hasapp | [hasapp ->]]; auto.
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    by apply All_forallb.
  - destruct H0 as [hasapp | [hasapp ->]]; auto.
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    by apply All_forallb.
  - destruct H0 as [hasapp | [hasapp ->]]; auto.
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    by apply All_forallb.
  - (* tEvar *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { fold betared.
      simpl.
      rtoProp; repeat split; auto.
      rewrite betared_env_hasapp; auto.
      apply forallb_wf_betared; auto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    2: by apply All_forallb.
    apply forallb_Forall.
    apply forallb_Forall in H0.
    apply All_Forall in X.
    apply All_Forall in X0.
    apply Forall_map.
    apply In_Forall.
    intros x HIn.
    apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
    apply PCUICWfUniverses.Forall_In with (x := x) in H0; auto.
  - destruct H0 as [hasapp | [hasapp ->]]; auto.
    + move: H => /andP[] => hasLambda wft.
      apply (@beta_body_wf _ hasLambda hasapp); auto.
      simpl; rtoProp; repeat split; auto.
    + simpl; rtoProp; repeat split; auto.
  - destruct H0 as [hasapp | [hasapp ->]]; auto.
    + rewrite wellformed_mkApps; auto.
      simpl; rtoProp; repeat split; auto.
      by apply All_forallb.
    + simpl; rtoProp; repeat split; auto.
  - move: H => /andP[] /andP[] => hasapp wft1 wft2.
    fold (betared t2). apply IHt1; auto.
    apply All_cons; auto.
    apply IHt2; auto.
  - (*tConst *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rewrite betared_env_hasapp; auto. }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    rewrite <- lookup_constant_betared.
    destruct EGlobalEnv.lookup_constant => //=.
    apply/orP; move/orP: H0 => H0; destruct H0 as [-> | H0]; auto.
    destruct cst_body; auto.
    by apply All_forallb.
  - (* tConstruct *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rewrite betared_env_hasapp; auto.
          simpl; rtoProp; repeat split; auto.
          destruct cstr_as_blocks; auto.
          2: by destruct args0.
          rtoProp; split; auto.
          by rewrite -betared_aux_length.
          apply forallb_wf_betared; auto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    1: by rewrite -lookup_constructor_betared.
    2: by apply All_forallb.
    destruct cstr_as_blocks.
    + rtoProp; split.
      * rewrite -lookup_constructor_pars_args_betared.
        destruct EGlobalEnv.lookup_constructor_pars_args; auto.
        by rewrite -betared_aux_length.
      * apply forallb_Forall.
        apply forallb_Forall in H2.
        apply All_Forall in X.
        apply All_Forall in X0.
        apply Forall_map.
        apply In_Forall.
        intros x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
        apply PCUICWfUniverses.Forall_In with (x := x) in H2; auto.
    + by destruct args0.
  - (* tCase *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rewrite betared_env_hasapp; auto.
          simpl; rtoProp; repeat split; auto.
          - by rewrite length_map.
          - fold betared. erewrite betared_hasapp; eauto.
          - apply forallb_Forall.
            apply forallb_Forall in H1.
            apply Forall_map.
            apply In_Forall => x HIn.
            apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
            fold betared. setoid_rewrite betared_hasapp; eauto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    + by rewrite length_map -betared_env_wf_brs.
    + clear H H0 IHt wfΣ.
      apply forallb_Forall.
      apply forallb_Forall in H1.
      apply All_Forall in X.
      apply Forall_map; cbn.
      apply In_Forall.
      intros x HIn.
      apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
      apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
    + by apply All_forallb.
  - (* tProj *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rtoProp. cbn [mkApps].
      rewrite betared_env_hasapp; auto.
      setoid_rewrite betared_hasapp; eauto.
      simpl; rtoProp; auto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    + by rewrite <- lookup_projection_betared.
    + by apply All_forallb.
  - (* tFix *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rtoProp. cbn [mkApps].
      rewrite betared_env_hasapp; auto.
      unfold wf_fix in *; rtoProp.
      simpl; rtoProp; repeat split; auto.
      + apply forallb_Forall.
        apply forallb_Forall in H1.
        apply forallb_Forall in H2.
        apply Forall_map.
        apply In_Forall => x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
        apply PCUICWfUniverses.Forall_In with (x := x) in H2; auto.
        fold betared. setoid_rewrite betared_hasapp; eauto.
      + unfold wf_fix; simpl; rtoProp; repeat split.
        all: rewrite length_map; auto.
        apply forallb_Forall.
        apply Forall_map.
        apply forallb_Forall in H2.
        apply In_Forall => x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H2; auto.
        unfold test_def in *.
        setoid_rewrite betared_hasapp; eauto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    + apply forallb_Forall.
      apply forallb_Forall in H1.
      apply All_Forall in X.
      apply Forall_map; cbn.
      apply In_Forall.
      intros x HIn.
      apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
      apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
      by apply betared_aux_isLambda.
    + clear H.
      unfold wf_fix in *.
      rtoProp; split.
      * by rewrite length_map.
      * unfold test_def in *.
        apply forallb_Forall.
        apply forallb_Forall in H0.
        apply All_Forall in X.
        apply Forall_map; cbn.
        apply In_Forall.
        intros x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H0; auto.
        apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
        rewrite length_map; auto.
    + by apply All_forallb.
  - (* tCoFix *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rewrite betared_env_hasapp; auto.
      simpl; unfold wf_fix in *; rtoProp.
      simpl; rtoProp; repeat split; auto.
      + by rewrite length_map.
      + rewrite length_map; auto.
        apply forallb_Forall.
        apply Forall_map.
        apply forallb_Forall in H1.
        apply In_Forall => x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
        unfold test_def in *.
        setoid_rewrite betared_hasapp; eauto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    unfold wf_fix in *.
    rtoProp; split.
    + by rewrite length_map.
    + unfold test_def in *.
      apply forallb_Forall.
      apply forallb_Forall in H1.
      apply All_Forall in X.
      apply Forall_map; cbn.
      apply In_Forall.
      intros x HIn.
      apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
      apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
      rewrite length_map; auto.
    + by apply All_forallb.
  - (* tPrim *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    2: { rewrite betared_env_hasapp; auto.
      simpl; rtoProp; repeat split; auto.
      + destruct p, p; auto.
      + destruct p, p; auto.
        cbn in *.
        unfold test_array_model in *; rtoProp.
        split; cbn.
        setoid_rewrite betared_hasapp; eauto.
        apply forallb_Forall.
        apply Forall_map.
        apply forallb_Forall in H1.
        apply In_Forall => x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
        setoid_rewrite betared_hasapp; eauto.
    }
    rewrite wellformed_mkApps; auto.
    simpl; rtoProp; repeat split; auto.
    + destruct p, p; auto.
    + destruct p, p; auto.
      cbn in *.
      unfold test_array_model in *; rtoProp.
      split; cbn.
      * now inversion_clear X.
      * inversion_clear X.
        destruct X1 as [_ X].
        apply forallb_Forall.
        apply forallb_Forall in H1.
        apply All_Forall in X.
        apply Forall_map; cbn.
        apply In_Forall.
        intros x HIn.
        apply PCUICWfUniverses.Forall_In with (x := x) in H1; auto.
        apply PCUICWfUniverses.Forall_In with (x := x) in X; auto.
    + by apply All_forallb.
  - (* tLazy *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    + rewrite wellformed_mkApps; auto.
      simpl; rtoProp; repeat split; auto.
      by apply All_forallb.
    + simpl; rtoProp; repeat split; auto.
  - (* tForce *)
    destruct H0 as [hasapp | [hasapp ->]]; auto.
    + rewrite wellformed_mkApps; auto.
      simpl; rtoProp; repeat split; auto.
      by apply All_forallb.
    + simpl; rtoProp; repeat split; auto.
Qed.

Lemma betared_wf {efl : EEnvFlags} {Σ : global_context} t k:
  wf_glob Σ ->
  wellformed Σ k t -> wellformed (betared_env Σ) k (betared t).
Proof.
  intros wfΣ wft.
  unfold betared.
  apply betared_aux_wf; try assumption.
  - constructor.
  - destruct has_tApp; auto.
Qed.

Lemma betared_env_wf {efl : EEnvFlags} {Σ : global_context} :
  wf_glob Σ -> wf_glob (betared_env Σ).
Proof.
  intros wfΣ.
  induction wfΣ.
  - constructor.
  - cbn. fold (betared_env Σ).
    apply fresh_betared_env in H0.
    constructor; auto.
    destruct d; auto.
    unfold wf_global_decl in H; cbn in H.
    cbn.
    destruct (cst_body c); auto; cbn in *.
    apply betared_wf; auto.
Qed.

Lemma trust_betared_wf :
  forall efl : EEnvFlags,
  WcbvFlags ->
  forall (input : Transform.program _ term),
  wf_eprogram efl input -> wf_eprogram efl (betared_program input).
Proof.
  intros efl flags p [].
  split.
  - apply betared_env_wf. assumption.
  - apply betared_wf; assumption.
Qed.

Axiom trust_betared_pres :
  forall (efl : EEnvFlags) (wfl : WcbvFlags) (p : Transform.program _ term)
  (v : term),
  wf_eprogram efl p ->
  eval_eprogram wfl p v ->
  exists v' : term,
  eval_eprogram wfl (betared_program p) v' /\ v' = betared v.

Import Transform.

Program Definition betared_transformation (efl : EEnvFlags) (wfl : WcbvFlags) :
  Transform.t _ _ EAst.term EAst.term _ _
    (eval_eprogram wfl) (eval_eprogram wfl) :=
  {| name := "betared ";
    transform p _ := betared_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram efl p ;
    obseq p hp p' v v' := v' = betared v |}.

Next Obligation.
  now apply trust_betared_wf.
Qed.
Next Obligation.
  now eapply trust_betared_pres.
Qed.

Import EProgram EGlobalEnv.

#[global]
Axiom betared_transformation_ext :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (betared_transformation efl wfl)
    (fun p p' => extends p.1 p'.1) (fun p p' => extends p.1 p'.1).

#[global]
Axiom betared_transformation_ext' :
  forall (efl : EEnvFlags) (wfl : WcbvFlags),
  TransformExt.t (betared_transformation efl wfl)
    extends_eprogram extends_eprogram.
