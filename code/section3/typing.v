
(*

-> Section 3 in paper
-> Union + Null type

*)

Require Import TLC.LibLN.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import syntax.

(** definitions *)

(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall A B e,
     lc_exp (e_abs A B e) ->
     value (e_abs A B e)
 | val_null :
     value e_null.

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (A B:typ) (e:exp),
     lc_exp (e_abs A B e) ->
     findtype  (e_abs A B e) (t_arrow A B)
 | findtype_null : 
     findtype e_null t_unit.

#[export]
Hint Constructors value findtype : core.

(* defns Typing *)
Inductive typing : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt  G  ->
     typing G (e_lit i5) t_int
 | typ_null : forall G,
      okt G ->
      typing G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt  G  ->
      binds  x A G  ->
     typing G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     typing G e1 (t_arrow A B) ->
     typing G e2 A ->
     typing G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing G e B ->
     B <: A ->
     typing G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      inhabited B ->
      ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing G (e_abs A B e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     A *s1 B ->
     typing G (e_typeof e A e1 B e2) C.

(* defns Reduction *)
Reserved Notation "e --> e'" (at level 80).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     e1 --> e1' ->
     (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     e --> e' ->
     (e_app v e) --> (e_app v e')
 | step_beta : forall (A B:typ) (e:exp) (v:exp),
     lc_exp (e_abs A B e) ->
     value v ->
     e_app  (e_abs A B e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     e --> e' ->
     (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     C <: A ->
     (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     C <: B ->
     (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "e --> e'" := (step e e') : env_scope.

#[export]
Hint Constructors typing step : core.


(** Gathering free names already used in the proofs *)


Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let D := gather_vars_with (fun x : exp => fv_exp x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u D \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- subtyping ?E _ _  => E
  | |- typing ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_exp_wrt_exp_rec j v e = open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j v e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

(* Structural gradual typing and an executable closure semantics. *)
(* The legacy closed boundary layer remains available after module removal. *)
Inductive gtyping : gexp -> gtyp -> Prop :=
| gt_embed : forall e A, typing empty e A -> gtyping (g_embed e) (g_static A)
| gt_inject : forall e A, gtyping e (g_static A) -> gtyping (g_inject e) g_unknown
| gt_project : forall e A, gtyping e g_unknown -> gtyping (g_project A e) (g_static A)
| gt_pack : forall v C, typing empty v C -> findtype v C -> gtyping (g_pack C v) g_unknown
| gt_error : forall T, gtyping g_error T.

Inductive gvalue : gexp -> Prop :=
| gv_static : forall v, value v -> gvalue (g_embed v)
| gv_dynamic : forall C v, value v -> gvalue (g_pack C v).

Inductive gstep : gexp -> gexp -> Prop :=
| gs_static : forall e e', step e e' -> gstep (g_embed e) (g_embed e')
| gs_inject_ctx : forall e e', gstep e e' -> gstep (g_inject e) (g_inject e')
| gs_project_ctx : forall A e e', gstep e e' -> gstep (g_project A e) (g_project A e')
| gs_inject_value : forall v C, value v -> findtype v C ->
    gstep (g_inject (g_embed v)) (g_pack C v)
| gs_project_ok : forall A C v, C <: A -> gstep (g_project A (g_pack C v)) (g_embed v)
| gs_project_fail : forall A C v, ~ (C <: A) -> gstep (g_project A (g_pack C v)) g_error
| gs_inject_error : gstep (g_inject g_error) g_error
| gs_project_error : forall A, gstep (g_project A g_error) g_error.

#[local] Hint Constructors gtyping gvalue gstep : core.

Lemma value_has_tag : forall v, value v -> exists C, findtype v C.
Proof. intros v V; inversion V; subst; eauto. Qed.

Lemma tag_is_value : forall v C, findtype v C -> value v.
Proof. intros v C F; inversion F; subst; auto. Qed.

Lemma successful_projection_typing : forall v C A,
  gtyping (g_pack C v) g_unknown -> C <: A -> typing empty v A.
Proof. intros v C A T S; inversion T; subst; eauto. Qed.

Lemma static_value_no_step : forall v e, value v -> step v e -> False.
Proof. intros v e V R; inversion V; subst; inversion R. Qed.

Lemma gradual_value_no_step : forall v e, gvalue v -> gstep v e -> False.
Proof.
  intros v e V R; inversion V; subst; inversion R; subst;
    eauto using static_value_no_step.
Qed.

Lemma error_no_step : forall e, ~ gstep g_error e.
Proof. intros e H; inversion H. Qed.

Theorem static_embedding : forall e A,
  gtyping (g_embed e) (g_static A) <-> typing empty e A.
Proof. split; intro H; inversion H; subst; auto. Qed.

Theorem static_step_embedding : forall e e',
  gstep (g_embed e) e' <-> exists s, e' = g_embed s /\ step e s.
Proof.
  split; intro H.
  - inversion H; subst; eauto.
  - destruct H as [s [Eq R]]; subst; auto.
Qed.

Theorem unknown_not_top : g_unknown <> g_static t_top.
Proof. discriminate. Qed.

Theorem packed_tag_preserved : forall C v,
  gtyping (g_pack C v) g_unknown -> findtype v C /\ typing empty v C.
Proof. intros C v H; inversion H; subst; auto. Qed.

Inductive gsteps : gexp -> gexp -> Prop :=
| gsteps_refl : forall e, gsteps e e
| gsteps_cons : forall e e' e'', gstep e e' -> gsteps e' e'' -> gsteps e e''.

#[local] Hint Constructors gsteps : core.

Inductive sgtyping : list sgtyp -> sgexp -> sgtyp -> Prop :=
| sgt_var : forall G x A, nth_error G x = Some A -> sgtyping G (sg_var x) A
| sgt_lit : forall G n, sgtyping G (sg_lit n) sg_int
| sgt_null : forall G, sgtyping G sg_null sg_unit
| sgt_lam : forall G D A B e C, sgtyping (A :: G) e C -> sgconsistent C B ->
    sgtyping G (sg_lam D A B e) (sg_arrow A B)
| sgt_app : forall G f a T A B C, sgtyping G f T -> sgmatch T A B ->
    sgtyping G a C -> sgconsistent C A -> sgtyping G (sg_app f a) B
| sgt_ann : forall G e A B, sgtyping G e B -> sgconsistent B A ->
    sgtyping G (sg_ann e A) A
| sgt_inl : forall G e A B C, sgtyping G e C -> sgconsistent C A ->
    sgtyping G (sg_inl e A B) (sg_union A B)
| sgt_inr : forall G e A B C, sgtyping G e C -> sgconsistent C B ->
    sgtyping G (sg_inr e A B) (sg_union A B)
| sgt_switch : forall G e D l E r A T B C,
    sgtyping G e T -> D *a E ->
    sgtyping (sg_lift D :: G) l B -> sgconsistent B A ->
    sgtyping (sg_lift E :: G) r C -> sgconsistent C A ->
    sgtyping G (sg_switch e D l E r A) A.

Fixpoint sg_callable (v : sgval) : bool :=
  match v with
  | sg_closure _ _ _ _ _ => true
  | sg_wrapper _ _ w => sg_callable w
  | _ => false
  end.

(* Casts inspect structure, with left-biased union choice. Arrow casts install
   a wrapper; its domain check happens when the wrapper is applied. *)
Fixpoint sg_cast (A : sgtyp) (v : sgval) : sgresult :=
  match A with
  | sg_any | sg_top => sg_done v
  | sg_int => match v with sg_vint _ => sg_done v | _ => sg_error end
  | sg_unit => match v with sg_vunit => sg_done v | _ => sg_error end
  | sg_bot => sg_error
  | sg_arrow A B => if sg_callable v then sg_done (sg_wrapper A B v) else sg_error
  | sg_union A B => match sg_cast A v with
                    | sg_done w => sg_done w
                    | _ => sg_cast B v
                    end
  end.

Definition sg_bind (r : sgresult) (k : sgval -> sgresult) : sgresult :=
  match r with sg_done v => k v | sg_error => sg_error | sg_timeout => sg_timeout end.

(* Static descriptor tests use the existing subtype relation. This decider
   is classical (as is static progress); all other interpreter clauses compute. *)
Definition sg_test (C D : typ) : bool :=
  If (C <: D) then true else false.

Fixpoint sg_eval (fuel : nat) (rho : list sgval) (e : sgexp) {struct fuel} : sgresult :=
  match fuel with
  | O => sg_timeout
  | S k =>
    match e with
    | sg_var x => match nth_error rho x with Some v => sg_done v | None => sg_error end
    | sg_lit n => sg_done (sg_vint n)
    | sg_null => sg_done sg_vunit
    | sg_lam D A B body => sg_done (sg_closure D A B body rho)
    | sg_app f a => sg_bind (sg_eval k rho f) (fun v =>
                     sg_bind (sg_eval k rho a) (sg_apply k v))
    | sg_ann e A => sg_bind (sg_eval k rho e) (sg_cast A)
    | sg_inl e A B => sg_bind (sg_eval k rho e) (sg_cast A)
    | sg_inr e A B => sg_bind (sg_eval k rho e) (sg_cast B)
    | sg_switch e D l E r A => sg_bind (sg_eval k rho e) (fun v =>
        if sg_test (sg_tag v) D then sg_bind (sg_cast (sg_lift D) v) (fun checked =>
          sg_bind (sg_eval k (checked :: rho) l) (sg_cast A))
        else if sg_test (sg_tag v) E then sg_bind (sg_cast (sg_lift E) v) (fun checked =>
          sg_bind (sg_eval k (checked :: rho) r) (sg_cast A))
        else sg_error)
    end
  end
with sg_apply (fuel : nat) (f a : sgval) {struct fuel} : sgresult :=
  match fuel with
  | O => sg_timeout
  | S k => match f with
    | sg_closure D A B body rho => sg_bind (sg_cast A a) (fun v =>
          sg_bind (sg_eval k (v :: rho) body) (sg_cast B))
    | sg_wrapper A B w => sg_bind (sg_cast A a) (fun v =>
          sg_bind (sg_apply k w v) (sg_cast B))
    | _ => sg_error
    end
  end.

#[local] Hint Constructors sgprecision sgconsistent sgmatch sgtyping : sg.

Lemma sg_precision_refl : forall A, sgprecision A A.
Proof. induction A; eauto with sg. Qed.

Lemma sg_precision_trans : forall A B C,
  sgprecision A B -> sgprecision B C -> sgprecision A C.
Proof.
  intros A B C H; generalize dependent C.
  induction H; intros C K; inversion K; subst; eauto with sg.
Qed.

Lemma sg_consistent_refl : forall A, sgconsistent A A.
Proof. induction A; eauto with sg. Qed.

Lemma sg_consistent_weaken : forall A B,
  sgconsistent A B -> forall A' B',
  sgprecision A A' -> sgprecision B B' -> sgconsistent A' B'.
Proof.
  induction 1; intros X0 Y0 P Q.
  all: try solve [inversion P; subst; inversion Q; subst; eauto with sg].
  eapply sg_con_sub; [eassumption | | ];
    eapply sg_precision_trans; eassumption.
Qed.

Lemma sg_match_weaken : forall T A B, sgmatch T A B ->
  forall T', sgprecision T T' -> exists A' B',
    sgmatch T' A' B' /\ sgprecision A A' /\ sgprecision B B'.
Proof.
  intros T A B M T' P; inversion M; subst; inversion P; subst;
    eauto 6 with sg.
Qed.

Definition sg_env_precision := Forall2 sgprecision.

Lemma sg_lookup_precision : forall G G', sg_env_precision G G' ->
  forall x A, nth_error G x = Some A ->
  exists A', nth_error G' x = Some A' /\ sgprecision A A'.
Proof.
  intros G G' P; induction P; intros index T Eq; destruct index; simpl in *;
    try discriminate.
  - inversion Eq; subst; eauto.
  - eauto.
Qed.

Theorem sg_static_gradual_guarantee : forall e e', sgterm_precision e e' ->
  forall G G' A, sg_env_precision G G' -> sgtyping G e A ->
  exists A', sgtyping G' e' A' /\ sgprecision A A'.
Proof.
  induction 1; intros G G' T Env Ty; inversion Ty; subst.
  - eapply sg_lookup_precision in Env; eauto.
    destruct Env as [A' [Look Prec]]. exists A'; split; eauto with sg.
  - exists sg_int; split; eauto with sg.
  - exists sg_unit; split; eauto with sg.
  - assert (Ext : sg_env_precision (A :: G) (A' :: G')).
    { constructor; assumption. }
    assert (BodyEx : exists C', sgtyping (A' :: G') e' C' /\ sgprecision C C').
    { eapply IHsgterm_precision; eauto. }
    destruct BodyEx as [C' [Body Prec]].
    exists (sg_arrow A' B'); split; eauto with sg.
    eapply sgt_lam; eauto. eapply sg_consistent_weaken; eauto.
  - match goal with TF : sgtyping G f ?FT |- _ =>
      destruct (IHsgterm_precision1 G G' FT Env TF) as [T' [Fun PT]] end.
    match goal with M : sgmatch _ _ _ |- _ =>
      destruct (sg_match_weaken _ _ _ M _ PT) as [X [Y [Match [PX PY]]]] end.
    match goal with TA : sgtyping G a ?AT |- _ =>
      destruct (IHsgterm_precision2 G G' AT Env TA) as [C' [Arg PC]] end.
    exists Y; split; auto. eapply sgt_app; eauto.
    eapply sg_consistent_weaken; eauto.
  - match goal with TE : sgtyping G e ?ET |- _ =>
      destruct (IHsgterm_precision G G' ET Env TE) as [C' [Body PC]] end.
    exists A'; split; auto. eapply sgt_ann; eauto.
    eapply sg_consistent_weaken; eauto.
  - match goal with TE : sgtyping G e ?ET |- _ =>
      destruct (IHsgterm_precision G G' ET Env TE) as [C' [Body PC]] end.
    exists (sg_union A' B'); split; eauto with sg.
    eapply sgt_inl; eauto. eapply sg_consistent_weaken; eauto.
  - match goal with TE : sgtyping G e ?ET |- _ =>
      destruct (IHsgterm_precision G G' ET Env TE) as [C' [Body PC]] end.
    exists (sg_union A' B'); split; eauto with sg.
    eapply sgt_inr; eauto. eapply sg_consistent_weaken; eauto.
  - match goal with TE : sgtyping G e ?ET |- _ =>
      destruct (IHsgterm_precision1 G G' ET Env TE) as [T' [Scr PS]] end.
    assert (ED : sg_env_precision (sg_lift D :: G) (sg_lift D :: G')).
    { constructor; auto using sg_precision_refl. }
    assert (EE : sg_env_precision (sg_lift E :: G) (sg_lift E :: G')).
    { constructor; auto using sg_precision_refl. }
    match goal with TL : sgtyping (sg_lift D :: G) l ?LT |- _ =>
      destruct (IHsgterm_precision2 _ _ LT ED TL) as [B' [Left PL]] end.
    match goal with TR : sgtyping (sg_lift E :: G) r ?RT |- _ =>
      destruct (IHsgterm_precision3 _ _ RT EE TR) as [C' [Right PR]] end.
    exists A'; split; auto.
    eapply sgt_switch with (T := T') (B := B') (C := C').
    + exact Scr.
    + assumption.
    + exact Left.
    + eapply sg_consistent_weaken with (A := B) (B := T); eauto.
    + exact Right.
    + eapply sg_consistent_weaken with (A := C) (B := T); eauto.
Qed.

(* First-order runtime data has exact observational equality; this relation
   is independent of typing and of the evaluation relation. *)
Inductive sgdata : sgval -> Prop :=
| sg_data_int : forall n, sgdata (sg_vint n)
| sg_data_unit : sgdata sg_vunit.

Lemma sg_cast_data_identity : forall A v w,
  sgdata v -> sg_cast A v = sg_done w -> w = v.
Proof.
  induction A; intros v w V Cast; simpl in Cast;
    try solve [inversion Cast; auto];
    try solve [inversion V; subst; inversion Cast; auto].
  destruct (sg_cast A1 v) eqn:E.
  - inversion Cast; subst. eapply IHA1; eauto.
  - eapply IHA2; eauto.
  - eapply IHA2; eauto.
Qed.

Theorem sg_cast_data_gradual_guarantee : forall A A', sgprecision A A' ->
  forall v w, sgdata v -> sg_cast A v = sg_done w ->
    sg_cast A' v = sg_done w.
Proof.
  induction 1; intros v w V Cast; simpl in *; auto.
  - f_equal. symmetry. eapply sg_cast_data_identity; eauto.
  - inversion V; subst; discriminate.
  - destruct (sg_cast A v) eqn:E.
    + inversion Cast; subst.
      rewrite (IHsgprecision1 _ _ V E). reflexivity.
    + specialize (IHsgprecision2 _ _ V Cast).
      destruct (sg_cast A' v) eqn:F; auto.
      assert (s = w).
      { transitivity v; eauto using sg_cast_data_identity.
        symmetry; eapply sg_cast_data_identity; eauto. }
      subst; reflexivity.
    + specialize (IHsgprecision2 _ _ V Cast).
      destruct (sg_cast A' v) eqn:F; auto.
      assert (s = w).
      { transitivity v; eauto using sg_cast_data_identity.
        symmetry; eapply sg_cast_data_identity; eauto. }
      subst; reflexivity.
Qed.

(* This dynamic guarantee covers arbitrary open computations under an outer
   annotation, including applications, when their result is first-order data.
   It does NOT assert simulation for arbitrary source-term precision. *)
Theorem sg_annotation_dynamic_guarantee : forall fuel rho e A A' v w,
  sgprecision A A' -> sg_eval fuel rho e = sg_done v -> sgdata v ->
  sg_eval (S fuel) rho (sg_ann e A) = sg_done w ->
  sg_eval (S fuel) rho (sg_ann e A') = sg_done w.
Proof.
  intros fuel rho e A A' v w P Eval Data Run.
  simpl in *; rewrite Eval in *; simpl in *.
  eapply sg_cast_data_gradual_guarantee; eauto.
Qed.

Theorem sg_annotation_unknown_guarantee : forall fuel rho e A w,
  sg_eval (S fuel) rho (sg_ann e A) = sg_done w ->
  exists v, sg_eval (S fuel) rho (sg_ann e sg_any) = sg_done v /\
    sg_cast A v = sg_done w.
Proof.
  intros fuel rho e A w H; simpl in *.
  destruct (sg_eval fuel rho e); simpl in *; try discriminate.
  eauto.
Qed.

Theorem sg_cast_preserves_descriptor : forall A v w,
  sg_cast A v = sg_done w -> sg_tag v = sg_tag w.
Proof.
  induction A; intros v w H; simpl in H; try solve [inversion H; auto];
    try solve [destruct v; inversion H; auto].
  - destruct (sg_callable v); inversion H; reflexivity.
  - destruct (sg_cast A1 v) eqn:E.
    + inversion H; subst; eauto.
    + eauto.
    + eauto.
Qed.

(* Runtime precision is structural, not defined by evaluation or typing.
   A precise value may carry additional delayed checks. *)
Inductive sgvalue_precision : sgval -> sgval -> Prop :=
| sgv_int : forall n, sgvalue_precision (sg_vint n) (sg_vint n)
| sgv_unit : sgvalue_precision sg_vunit sg_vunit
| sgv_closure : forall D A A' B B' e e' rho rho',
    sgprecision A A' -> sgprecision B B' -> sgterm_precision e e' ->
    sgvalues_precision rho rho' ->
    sgvalue_precision (sg_closure D A B e rho) (sg_closure D A' B' e' rho')
| sgv_wrapper : forall A A' B B' v v',
    sgprecision A A' -> sgprecision B B' -> sgvalue_precision v v' ->
    sgvalue_precision (sg_wrapper A B v) (sg_wrapper A' B' v')
| sgv_forget : forall A B v v', sgvalue_precision v v' ->
    sgvalue_precision (sg_wrapper A B v) v'
with sgvalues_precision : list sgval -> list sgval -> Prop :=
| sgvs_nil : sgvalues_precision [] []
| sgvs_cons : forall v v' rho rho', sgvalue_precision v v' ->
    sgvalues_precision rho rho' -> sgvalues_precision (v :: rho) (v' :: rho').

#[local] Hint Constructors sgvalue_precision sgvalues_precision : sg.

Lemma sg_value_descriptor_precision : forall v v', sgvalue_precision v v' ->
  sg_tag v = sg_tag v'.
Proof. induction 1; simpl; auto. Qed.

Lemma sg_value_callable_precision : forall v v', sgvalue_precision v v' ->
  sg_callable v = sg_callable v'.
Proof. induction 1; simpl; auto. Qed.

Lemma sg_values_lookup : forall rho rho', sgvalues_precision rho rho' ->
  forall x v, nth_error rho x = Some v ->
  exists v', nth_error rho' x = Some v' /\ sgvalue_precision v v'.
Proof.
  induction 1; intros x w E; destruct x; simpl in *; try discriminate.
  - inversion E; subst; eauto.
  - eauto.
Qed.

Lemma sg_cast_no_timeout : forall A v, sg_cast A v <> sg_timeout.
Proof.
  induction A; intros v; simpl; try discriminate.
  - destruct v; discriminate.
  - destruct v; discriminate.
  - destruct (sg_callable v); discriminate.
  - destruct (sg_cast A1 v) eqn:E; eauto; discriminate.
Qed.

Lemma sg_cast_forget : forall A v v' w,
  sgvalue_precision v v' -> sg_cast A v = sg_done w ->
  sgvalue_precision w v'.
Proof.
  induction A; intros v v' w V C; simpl in C;
    try solve [inversion C; subst; assumption].
  - destruct v; inversion C; subst; assumption.
  - destruct v; inversion C; subst; assumption.
  - destruct (sg_callable v); inversion C; subst; eauto with sg.
  - destruct (sg_cast A1 v) eqn:E; eauto.
    inversion C; subst; eauto.
Qed.

(* If weakening changes a failed union alternative into a successful one,
   that alternative returns its input unchanged. It cannot add a wrapper. *)
Lemma sg_cast_new_success : forall A A', sgprecision A A' ->
  forall v v' w', sgvalue_precision v v' -> sg_cast A v = sg_error ->
  sg_cast A' v' = sg_done w' -> w' = v'.
Proof.
  induction 1; intros v v' w' V C C'; simpl in *;
    try solve [inversion C'; reflexivity];
    try solve [destruct v'; inversion C'; reflexivity].
  - rewrite <- (sg_value_callable_precision _ _ V) in C'.
    destruct (sg_callable v); discriminate.
  - destruct (sg_cast A v) eqn:E; try discriminate.
    + destruct (sg_cast A' v') eqn:E'; eauto.
      inversion C'; subst; eauto.
    + exfalso; eapply sg_cast_no_timeout; eauto.
Qed.

(* A successful cast is preserved by simultaneous type and value weakening.
   The result may lose a delayed wrapper, but remains structurally related to
   the original result. *)
Lemma sg_cast_precision : forall A A' v v' w, sgprecision A A' ->
  sgvalue_precision v v' -> sg_cast A v = sg_done w ->
  exists w', sg_cast A' v' = sg_done w' /\ sgvalue_precision w w'.
Proof.
  intros A A' v v' w P; revert v v' w.
  induction P as [A| | | | |A A' B B' PA IHA PB IHB|
    A A' B B' PA IHA PB IHB]; intros v v' w V C; simpl in *.
  - exists v'; split; auto. eapply sg_cast_forget; eauto.
  - inversion C; subst; eauto.
  - inversion V; subst; inversion C; subst; eauto with sg.
  - inversion C.
  - inversion V; subst; inversion C; subst; eauto with sg.
  - rewrite <- (sg_value_callable_precision _ _ V).
    destruct (sg_callable v) eqn:Call; try discriminate.
    inversion C; subst.
    exists (sg_wrapper A' B' v'); split; eauto with sg.
  - destruct (sg_cast A v) eqn:E.
    + inversion C; subst.
      destruct (IHA _ _ _ V E) as [z [Z Pz]].
      rewrite Z; eauto.
    + destruct (sg_cast A' v') eqn:E'.
        * assert (s = v') by
          (exact (sg_cast_new_success A A' PA v v' s V E E')).
        subst; exists v'; split; auto. eapply sg_cast_forget; eauto.
      * destruct (IHB _ _ _ V C) as [z [Z Pz]].
        exists z; split; auto.
      * exfalso; eapply sg_cast_no_timeout; eauto.
    + exfalso; eapply sg_cast_no_timeout; eauto.
Qed.

(* Only terminating successful runs are ordered here; timeout is not divergence. *)
Definition sg_success_precision (r r' : sgresult) : Prop :=
  forall v, r = sg_done v ->
    exists v', r' = sg_done v' /\ sgvalue_precision v v'.

Lemma sg_bind_precision : forall r r' k k',
  sg_success_precision r r' ->
  (forall v v', sgvalue_precision v v' -> sg_success_precision (k v) (k' v')) ->
  sg_success_precision (sg_bind r k) (sg_bind r' k').
Proof.
  intros r r' k k' R K v E; destruct r; simpl in E; try discriminate.
  destruct (R _ eq_refl) as [w [W P]]; rewrite W; simpl.
  eapply K; eauto.
Qed.

Lemma sg_cast_success_precision : forall A A' v v',
  sgprecision A A' -> sgvalue_precision v v' ->
  sg_success_precision (sg_cast A v) (sg_cast A' v').
Proof. intros A A' v v' P V w C; eapply sg_cast_precision; eauto. Qed.

(* Simultaneous induction on the precise run's fuel. The target may use any
   larger budget, not just the predecessor budget. In the forget case this
   lets the target skip a wrapper while the precise run consumes one unit. *)
Theorem sg_evaluation_simulation : forall fuel,
  (forall e e', sgterm_precision e e' ->
    forall rho rho', sgvalues_precision rho rho' ->
    forall fuel', fuel <= fuel' ->
    sg_success_precision (sg_eval fuel rho e) (sg_eval fuel' rho' e')) /\
  (forall f f', sgvalue_precision f f' ->
    forall a a', sgvalue_precision a a' ->
    forall fuel', fuel <= fuel' ->
    sg_success_precision (sg_apply fuel f a) (sg_apply fuel' f' a')).
Proof.
  induction fuel as [| smaller [IHexpr IHapp]].
  - split.
    + intros srcTerm dstTerm Terms envSrc envDst Envs budget Bound answer Run.
      discriminate Run.
    + intros funSrc funDst Funs argSrc argDst Args budget Bound answer Run.
      discriminate Run.
  - split.
    + intros srcTerm dstTerm Terms envSrc envDst Envs budget Bound.
      destruct budget as [| more]; [inversion Bound |].
      assert (Smaller : smaller <= more) by (apply le_S_n; exact Bound).
      destruct Terms as
        [index | number |
        | descriptor domSrc domDst codSrc codDst bodySrc bodyDst PDom PCod PBody
        | funSrc funDst argSrc argDst PFun PArg
        | subSrc subDst targetSrc targetDst PSub PTarget
        | subSrc subDst leftSrc leftDst rightSrc rightDst PSub PLeft PRight
        | subSrc subDst leftSrc leftDst rightSrc rightDst PSub PLeft PRight
        | scrSrc scrDst descLeft leftSrc leftDst descRight rightSrc rightDst
            targetSrc targetDst PScr PLeft PRight PTarget];
        cbn [sg_eval].
      * intros answer Run.
        destruct (nth_error envSrc index) as [found |] eqn:Lookup;
          try discriminate Run.
        inversion Run; subst answer.
        destruct (sg_values_lookup _ _ Envs _ _ Lookup)
          as [target [TargetLookup Related]].
        exists target; split; [rewrite TargetLookup; reflexivity | exact Related].
      * intros answer Run; inversion Run; subst answer.
        eexists; split; [reflexivity | constructor].
      * intros answer Run; inversion Run; subst answer.
        eexists; split; [reflexivity | constructor].
      * intros answer Run; inversion Run; subst answer.
        eexists; split; [reflexivity | eapply sgv_closure; eauto].
      * eapply sg_bind_precision.
        -- exact (IHexpr _ _ PFun _ _ Envs _ Smaller).
        -- intros resultFunSrc resultFunDst RelatedFun.
           eapply sg_bind_precision.
           ++ exact (IHexpr _ _ PArg _ _ Envs _ Smaller).
           ++ intros resultArgSrc resultArgDst RelatedArg.
              exact (IHapp _ _ RelatedFun _ _ RelatedArg _ Smaller).
      * eapply sg_bind_precision.
        -- exact (IHexpr _ _ PSub _ _ Envs _ Smaller).
        -- intros subValSrc subValDst RelatedSub.
           exact (sg_cast_success_precision _ _ _ _ PTarget RelatedSub).
      * eapply sg_bind_precision.
        -- exact (IHexpr _ _ PSub _ _ Envs _ Smaller).
        -- intros subValSrc subValDst RelatedSub.
           exact (sg_cast_success_precision _ _ _ _ PLeft RelatedSub).
      * eapply sg_bind_precision.
        -- exact (IHexpr _ _ PSub _ _ Envs _ Smaller).
        -- intros subValSrc subValDst RelatedSub.
           exact (sg_cast_success_precision _ _ _ _ PRight RelatedSub).
      * eapply sg_bind_precision.
        -- exact (IHexpr _ _ PScr _ _ Envs _ Smaller).
        -- intros scrValSrc scrValDst RelatedScr.
           rewrite <- (sg_value_descriptor_precision _ _ RelatedScr).
           destruct (sg_test (sg_tag scrValSrc) descLeft) eqn:TestLeft.
           ++ eapply sg_bind_precision.
              ** exact (sg_cast_success_precision _ _ _ _
               (sg_precision_refl (sg_lift descLeft)) RelatedScr).
              ** intros checkedSrc checkedDst RelatedChecked.
                 eapply sg_bind_precision.
                 --- exact (IHexpr _ _ PLeft _ _
                   (sgvs_cons _ _ _ _ RelatedChecked Envs) _ Smaller).
                 --- intros branchValSrc branchValDst RelatedBranch.
                 exact (sg_cast_success_precision _ _ _ _ PTarget RelatedBranch).
           ++ destruct (sg_test (sg_tag scrValSrc) descRight) eqn:TestRight.
              ** eapply sg_bind_precision.
                 --- exact (sg_cast_success_precision _ _ _ _
                   (sg_precision_refl (sg_lift descRight)) RelatedScr).
                 --- intros checkedSrc checkedDst RelatedChecked.
                 eapply sg_bind_precision.
                 +++ exact (IHexpr _ _ PRight _ _
                   (sgvs_cons _ _ _ _ RelatedChecked Envs) _ Smaller).
                 +++ intros branchValSrc branchValDst RelatedBranch.
                 exact (sg_cast_success_precision _ _ _ _ PTarget RelatedBranch).
              ** intros answer Run; discriminate Run.
    + intros funSrc funDst Funs argSrc argDst Args budget Bound.
      destruct budget as [| more]; [inversion Bound |].
      assert (Smaller : smaller <= more) by (apply le_S_n; exact Bound).
      destruct Funs as
        [number |
        | descriptor domSrc domDst codSrc codDst bodySrc bodyDst envSrc envDst
            PDom PCod PBody Envs
        | domSrc domDst codSrc codDst innerSrc innerDst PDom PCod RelatedInner
        | domSrc codSrc innerSrc innerDst RelatedInner];
        cbn [sg_apply].
      * intros answer Run; discriminate Run.
      * intros answer Run; discriminate Run.
      * eapply sg_bind_precision.
        -- exact (sg_cast_success_precision _ _ _ _ PDom Args).
        -- intros checkedSrc checkedDst RelatedChecked.
           eapply sg_bind_precision.
           ++ exact (IHexpr _ _ PBody _ _
                (sgvs_cons _ _ _ _ RelatedChecked Envs) _ Smaller).
           ++ intros bodyValSrc bodyValDst RelatedBody.
              exact (sg_cast_success_precision _ _ _ _ PCod RelatedBody).
      * eapply sg_bind_precision.
        -- exact (sg_cast_success_precision _ _ _ _ PDom Args).
        -- intros checkedSrc checkedDst RelatedChecked.
           eapply sg_bind_precision.
           ++ exact (IHapp _ _ RelatedInner _ _ RelatedChecked _ Smaller).
           ++ intros bodyValSrc bodyValDst RelatedBody.
              exact (sg_cast_success_precision _ _ _ _ PCod RelatedBody).
      * intros answer Run.
        destruct (sg_cast domSrc argSrc) as [checkedSrc | |] eqn:CastArg;
          simpl in Run; try discriminate Run.
        destruct (sg_apply smaller innerSrc checkedSrc)
          as [innerAnswer | |] eqn:InnerRun; simpl in Run; try discriminate Run.
        assert (RelatedChecked : sgvalue_precision checkedSrc argDst).
        { exact (sg_cast_forget _ _ _ _ Args CastArg). }
        assert (SkipBound : smaller <= S more) by (apply le_S; exact Smaller).
        destruct (IHapp _ _ RelatedInner _ _ RelatedChecked _ SkipBound _ InnerRun)
          as [target [TargetRun RelatedAnswer]].
        exists target; split; [exact TargetRun |].
        exact (sg_cast_forget _ _ _ _ RelatedAnswer Run).
Qed.

(* Fuel-independent successful expression simulation, for all source terms
   and related runtime environments; no typing or termination premise for the
   less precise program is assumed. The stronger theorem above even permits
   choosing fuel2 = fuel1. *)
Theorem sg_dynamic_gradual_guarantee : forall e e' rho rho' v,
  sgterm_precision e e' -> sgvalues_precision rho rho' ->
  (exists fuel1, sg_eval fuel1 rho e = sg_done v) ->
  exists fuel2 v', sg_eval fuel2 rho' e' = sg_done v' /\
    sgvalue_precision v v'.
Proof.
  intros srcTerm dstTerm envSrc envDst answer Terms Envs [budget Run].
  destruct (proj1 (sg_evaluation_simulation budget)
    _ _ Terms _ _ Envs budget (le_n budget) _ Run)
    as [target [TargetRun Related]].
  exists budget, target; split; assumption.
Qed.

Theorem sg_application_dynamic_guarantee : forall f f' a a' v,
  sgvalue_precision f f' -> sgvalue_precision a a' ->
  (exists fuel1, sg_apply fuel1 f a = sg_done v) ->
  exists fuel2 v', sg_apply fuel2 f' a' = sg_done v' /\
    sgvalue_precision v v'.
Proof.
  intros funSrc funDst argSrc argDst answer Funs Args [budget Run].
  destruct (proj2 (sg_evaluation_simulation budget)
    _ _ Funs _ _ Args budget (le_n budget) _ Run)
    as [target [TargetRun Related]].
  exists budget, target; split; assumption.
Qed.

(* A completed run is stable when its budget grows, including error runs. *)
Definition sg_result_stable (r r' : sgresult) : Prop :=
  r <> sg_timeout -> r' = r.

Lemma sg_bind_stable : forall r r' k k',
  sg_result_stable r r' ->
  (forall v, sg_result_stable (k v) (k' v)) ->
  sg_result_stable (sg_bind r k) (sg_bind r' k').
Proof.
  intros r r' k k' R K H; destruct r; cbn [sg_bind] in *.
  - rewrite (R ltac:(discriminate)); cbn [sg_bind]. apply K; exact H.
  - rewrite (R ltac:(discriminate)); reflexivity.
  - exfalso; apply H; reflexivity.
Qed.

Theorem sg_fuel_monotonicity : forall fuel fuel', fuel <= fuel' ->
  (forall rho e, sg_result_stable (sg_eval fuel rho e) (sg_eval fuel' rho e)) /\
  (forall f a, sg_result_stable (sg_apply fuel f a) (sg_apply fuel' f a)).
Proof.
  induction fuel as [| n IH]; intros budget Bound.
  - split; intros; unfold sg_result_stable; simpl; contradiction.
  - destruct budget as [| m]; [inversion Bound |].
    destruct (IH m (le_S_n _ _ Bound)) as [Eval Apply].
    assert (Refl : forall r, sg_result_stable r r) by (intros r H; reflexivity).
    split.
    + intros rho e; destruct e; cbn [sg_eval]; try apply Refl.
      * apply sg_bind_stable; [apply Eval |].
        intros v; apply sg_bind_stable; [apply Eval | exact (Apply v)].
      * apply sg_bind_stable; [apply Eval | intros; apply Refl].
      * apply sg_bind_stable; [apply Eval | intros; apply Refl].
      * apply sg_bind_stable; [apply Eval | intros; apply Refl].
      * apply sg_bind_stable; [apply Eval |].
        intros v; destruct (sg_test (sg_tag v) t); [| destruct (sg_test (sg_tag v) t0)];
          try apply Refl;
          (apply sg_bind_stable; [apply Refl | intros checked];
           apply sg_bind_stable; [apply Eval | intros; apply Refl]).
    + intros f a; destruct f; cbn [sg_apply]; try apply Refl.
      * apply sg_bind_stable; [apply Refl | intros v].
        apply sg_bind_stable; [apply Eval | intros; apply Refl].
      * apply sg_bind_stable; [apply Refl | intros v].
        apply sg_bind_stable; [apply Apply | intros; apply Refl].
Qed.

(* Independent unbounded operational semantics. A plan specifies the next
   subcomputation and its continuation. Neither plans nor derivations contain
   a budget, and no rule concludes timeout. Missing variables, failed casts,
   non-callable applications and uncovered switches retain their actual errors. *)
Inductive sg_command : Type :=
| sg_evaluate : list sgval -> sgexp -> sg_command
| sg_invoke : sgval -> sgval -> sg_command.

Inductive sg_plan : Type :=
| sg_answer : sgresult -> sg_plan
| sg_request : sg_command -> (sgval -> sg_plan) -> sg_plan.

Definition sg_expand (c : sg_command) : sg_plan :=
  match c with
  | sg_evaluate rho e => match e with
    | sg_var x => sg_answer
        (match nth_error rho x with Some v => sg_done v | None => sg_error end)
    | sg_lit n => sg_answer (sg_done (sg_vint n))
    | sg_null => sg_answer (sg_done sg_vunit)
    | sg_lam D A B body => sg_answer (sg_done (sg_closure D A B body rho))
    | sg_app f a => sg_request (sg_evaluate rho f) (fun v =>
        sg_request (sg_evaluate rho a) (fun w =>
          sg_request (sg_invoke v w) (fun z => sg_answer (sg_done z))))
    | sg_ann e A => sg_request (sg_evaluate rho e) (fun v => sg_answer (sg_cast A v))
    | sg_inl e A B => sg_request (sg_evaluate rho e) (fun v => sg_answer (sg_cast A v))
    | sg_inr e A B => sg_request (sg_evaluate rho e) (fun v => sg_answer (sg_cast B v))
    | sg_switch e D l E r A => sg_request (sg_evaluate rho e) (fun v =>
        if sg_test (sg_tag v) D then match sg_cast (sg_lift D) v with
          | sg_done checked => sg_request (sg_evaluate (checked :: rho) l)
              (fun w => sg_answer (sg_cast A w))
          | result => sg_answer result end
        else if sg_test (sg_tag v) E then match sg_cast (sg_lift E) v with
          | sg_done checked => sg_request (sg_evaluate (checked :: rho) r)
              (fun w => sg_answer (sg_cast A w))
          | result => sg_answer result end
        else sg_answer sg_error)
    end
  | sg_invoke f a => match f with
    | sg_closure D A B body rho => match sg_cast A a with
      | sg_done v => sg_request (sg_evaluate (v :: rho) body)
          (fun w => sg_answer (sg_cast B w))
      | r => sg_answer r end
    | sg_wrapper A B w => match sg_cast A a with
      | sg_done v => sg_request (sg_invoke w v) (fun z => sg_answer (sg_cast B z))
      | r => sg_answer r end
    | _ => sg_answer sg_error end
  end.

Inductive sg_runs : sg_command -> sgresult -> Prop :=
| sg_runs_expand : forall c r, sg_plan_runs (sg_expand c) r -> sg_runs c r
with sg_plan_runs : sg_plan -> sgresult -> Prop :=
| sg_runs_answer : forall r, r <> sg_timeout -> sg_plan_runs (sg_answer r) r
| sg_runs_failure : forall c k, sg_runs c sg_error ->
    sg_plan_runs (sg_request c k) sg_error
| sg_runs_continue : forall c k v r, sg_runs c (sg_done v) ->
    sg_plan_runs (k v) r -> sg_plan_runs (sg_request c k) r.

Scheme sg_runs_ind_mut := Induction for sg_runs Sort Prop
with sg_plan_runs_ind_mut := Induction for sg_plan_runs Sort Prop.
Combined Scheme sg_runs_mutind from sg_runs_ind_mut, sg_plan_runs_ind_mut.

Definition sg_command_eval (fuel : nat) (c : sg_command) : sgresult :=
  match c with sg_evaluate rho e => sg_eval fuel rho e
             | sg_invoke f a => sg_apply fuel f a end.

Fixpoint sg_plan_eval (fuel : nat) (p : sg_plan) : sgresult :=
  match p with
  | sg_answer r => r
  | sg_request c k => sg_bind (sg_command_eval fuel c) (fun v => sg_plan_eval fuel (k v))
  end.

Lemma sg_bind_return : forall r, sg_bind r sg_done = r.
Proof. destruct r; reflexivity. Qed.

Lemma sg_expand_eval : forall fuel c,
  sg_plan_eval fuel (sg_expand c) = sg_command_eval (S fuel) c.
Proof.
  intros fuel [rho e | f a];
    [destruct e | destruct f as [number | | D A B body rho | A B w]];
    cbn [sg_expand sg_plan_eval sg_command_eval sg_eval sg_apply]; try reflexivity.
  - destruct (sg_eval fuel rho e1); cbn [sg_bind]; try reflexivity.
    destruct (sg_eval fuel rho e2); cbn [sg_bind]; try reflexivity.
    apply sg_bind_return.
  - destruct (sg_eval fuel rho e1) as [v | |]; cbn [sg_bind]; try reflexivity.
    destruct (sg_test (sg_tag v) t).
    + destruct (sg_cast (sg_lift t) v); reflexivity.
    + destruct (sg_test (sg_tag v) t0); [| reflexivity].
      destruct (sg_cast (sg_lift t0) v); reflexivity.
  - destruct (sg_cast A a); reflexivity.
  - destruct (sg_cast A a); reflexivity.
Qed.

Lemma sg_command_monotonicity : forall n m c, n <= m ->
  sg_result_stable (sg_command_eval n c) (sg_command_eval m c).
Proof.
  intros n m [rho e | f a] H; unfold sg_command_eval.
  - apply (proj1 (sg_fuel_monotonicity n m H)).
  - apply (proj2 (sg_fuel_monotonicity n m H)).
Qed.

Lemma sg_plan_monotonicity : forall p n m, n <= m ->
  sg_result_stable (sg_plan_eval n p) (sg_plan_eval m p).
Proof.
  induction p as [r | c k IH]; intros n m H; cbn [sg_plan_eval].
  - intros _; reflexivity.
  - apply sg_bind_stable; [apply sg_command_monotonicity; exact H |].
    intros v; apply IH; exact H.
Qed.

Lemma sg_plan_sound : forall fuel,
  (forall c r, sg_command_eval fuel c = r -> r <> sg_timeout -> sg_runs c r) ->
  forall p r, sg_plan_eval fuel p = r -> r <> sg_timeout -> sg_plan_runs p r.
Proof.
  intros fuel Calls p; induction p as [answer | c k IH]; intros r E N;
    cbn [sg_plan_eval] in E.
  - subst; constructor; assumption.
  - destruct (sg_command_eval fuel c) eqn:Call; cbn [sg_bind] in E.
    + eapply sg_runs_continue; [eapply Calls; eauto; discriminate | eapply IH; eauto].
    + subst; apply sg_runs_failure; eapply Calls; eauto; discriminate.
    + subst; contradiction.
Qed.

Theorem sg_fuel_sound : forall fuel c r,
  sg_command_eval fuel c = r -> r <> sg_timeout -> sg_runs c r.
Proof.
  induction fuel as [| n IH]; intros c r E N.
  - destruct c; simpl in E; subst; contradiction.
  - constructor. eapply sg_plan_sound; [exact IH | | exact N].
    rewrite sg_expand_eval; exact E.
Qed.

Lemma sg_runs_no_timeout :
  (forall c r, sg_runs c r -> r <> sg_timeout) /\
  (forall p r, sg_plan_runs p r -> r <> sg_timeout).
Proof. apply sg_runs_mutind; intros; auto; discriminate. Qed.

Theorem sg_unbounded_complete :
  (forall c r, sg_runs c r -> exists fuel, sg_command_eval fuel c = r) /\
  (forall p r, sg_plan_runs p r -> exists fuel, sg_plan_eval fuel p = r).
Proof.
  apply sg_runs_mutind.
  - intros c r Run [n E]; exists (S n); rewrite <- sg_expand_eval; exact E.
  - intros r N; exists 0; reflexivity.
  - intros c k Run [n E]; exists n; cbn [sg_plan_eval]; rewrite E; reflexivity.
  - intros c k v r Run [n E] Cont [m F].
    exists (Nat.max n m); cbn [sg_plan_eval].
    assert (Call : sg_command_eval (Nat.max n m) c = sg_done v).
    { rewrite (sg_command_monotonicity n (Nat.max n m) c (Nat.le_max_l n m));
        rewrite E; try reflexivity; discriminate. }
    rewrite Call; cbn [sg_bind].
    rewrite (sg_plan_monotonicity (k v) m (Nat.max n m) (Nat.le_max_r n m));
      [exact F | rewrite F; exact (proj2 sg_runs_no_timeout _ _ Cont)].
Qed.

Theorem sg_operational_adequacy : forall c r,
  sg_runs c r <-> r <> sg_timeout /\ exists fuel, sg_command_eval fuel c = r.
Proof.
  intros c r; split.
  - intros H; split.
    + exact (proj1 sg_runs_no_timeout _ _ H).
    + exact (proj1 sg_unbounded_complete _ _ H).
  - intros [N [fuel E]]; eapply sg_fuel_sound; eauto.
Qed.

Theorem sg_operational_determinism : forall c r s,
  sg_runs c r -> sg_runs c s -> r = s.
Proof.
  intros c r s R S.
  destruct (proj1 (sg_operational_adequacy c r) R) as [NR [n E]].
  destruct (proj1 (sg_operational_adequacy c s) S) as [NS [m F]].
  assert (ER : sg_command_eval (Nat.max n m) c = r).
  { transitivity (sg_command_eval n c); [| exact E].
    apply sg_command_monotonicity; [apply Nat.le_max_l | rewrite E; exact NR]. }
  assert (ES : sg_command_eval (Nat.max n m) c = s).
  { transitivity (sg_command_eval m c); [| exact F].
    apply sg_command_monotonicity; [apply Nat.le_max_r | rewrite F; exact NS]. }
  congruence.
Qed.

(* Divergence means that every finite budget is exhausted. Adequacy makes
   this equivalent to absence of any finite operational derivation. *)
Definition sg_diverges (c : sg_command) : Prop :=
  forall fuel, sg_command_eval fuel c = sg_timeout.

Theorem sg_divergence_adequacy : forall c,
  sg_diverges c <-> ~ exists r, sg_runs c r.
Proof.
  intros c; split.
  - intros D [r R].
    destruct (proj1 (sg_operational_adequacy c r) R) as [N [n E]].
    rewrite D in E; subst; contradiction.
  - intros N fuel; destruct (sg_command_eval fuel c) eqn:E; try reflexivity;
      exfalso; apply N; eexists; eapply sg_fuel_sound; eauto; discriminate.
Qed.

Theorem sg_termination_classification : forall c,
  (exists v, sg_runs c (sg_done v)) \/ sg_runs c sg_error \/ sg_diverges c.
Proof.
  intros c; destruct (classic (exists r, sg_runs c r)) as [[r R] | N].
  - destruct r.
    + left; eauto.
    + right; left; exact R.
    + exfalso; exact (proj1 sg_runs_no_timeout _ _ R eq_refl).
  - right; right; apply sg_divergence_adequacy; exact N.
Qed.

Theorem sg_unbounded_dynamic_gradual_guarantee : forall e e' rho rho' v,
  sgterm_precision e e' -> sgvalues_precision rho rho' ->
  sg_runs (sg_evaluate rho e) (sg_done v) ->
  exists v', sg_runs (sg_evaluate rho' e') (sg_done v') /\ sgvalue_precision v v'.
Proof.
  intros e e' rho rho' v P Env R.
  destruct (proj1 sg_unbounded_complete _ _ R) as [n E].
  destruct (sg_dynamic_gradual_guarantee e e' rho rho' v P Env (ex_intro _ n E))
    as [m [w [F V]]].
  exists w; split; [eapply sg_fuel_sound; [exact F | discriminate] | exact V].
Qed.

(* Error approximation is oriented backwards: a less precise error rules
   out precise success. The precise computation may instead diverge. *)
Theorem sg_error_approximation : forall e e' rho rho',
  sgterm_precision e e' -> sgvalues_precision rho rho' ->
  sg_runs (sg_evaluate rho' e') sg_error ->
  sg_runs (sg_evaluate rho e) sg_error \/ sg_diverges (sg_evaluate rho e).
Proof.
  intros e e' rho rho' P Env Error.
  destruct (sg_termination_classification (sg_evaluate rho e))
    as [[v R] | [R | D]]; auto.
  destruct (sg_unbounded_dynamic_gradual_guarantee _ _ _ _ _ P Env R)
    as [w [Run V]].
  pose proof (sg_operational_determinism _ _ _ Error Run) as Bad; discriminate.
Qed.

Theorem sg_divergence_approximation : forall e e' rho rho',
  sgterm_precision e e' -> sgvalues_precision rho rho' ->
  sg_diverges (sg_evaluate rho' e') ->
  sg_runs (sg_evaluate rho e) sg_error \/ sg_diverges (sg_evaluate rho e).
Proof.
  intros e e' rho rho' P Env Diverges.
  destruct (sg_termination_classification (sg_evaluate rho e))
    as [[v R] | [R | D]]; auto.
  destruct (sg_unbounded_dynamic_gradual_guarantee _ _ _ _ _ P Env R)
    as [w [Run V]].
  exfalso; apply (proj1 (sg_divergence_adequacy _) Diverges); eauto.
Qed.

(* Runtime shape typing describes the checks actually enforced by casts.
   Arrow membership records the callable's boundary contract; it does not
   certify its captured environment or its separately supplied descriptor. *)
Fixpoint sg_runtime_type (A : sgtyp) (v : sgval) : Prop :=
  match A with
  | sg_any | sg_top => True
  | sg_bot => False
  | sg_int => exists n, v = sg_vint n
  | sg_unit => v = sg_vunit
  | sg_union A B => sg_runtime_type A v \/ sg_runtime_type B v
  | sg_arrow A B =>
      (exists D body rho, v = sg_closure D A B body rho) \/
      (exists w, v = sg_wrapper A B w /\ sg_callable w = true)
  end.

Theorem sg_cast_runtime_type : forall A v w,
  sg_cast A v = sg_done w -> sg_runtime_type A w.
Proof.
  induction A; intros v w E; cbn [sg_cast] in E; cbn [sg_runtime_type];
    try exact I; try discriminate.
  - destruct v; inversion E; subst; eauto.
  - destruct v; inversion E; reflexivity.
  - destruct (sg_callable v) eqn:C; inversion E; subst.
    right; exists v; auto.
  - destruct (sg_cast A1 v) eqn:C.
    + inversion E; subst; left; eauto.
    + right; eauto.
    + right; eauto.
Qed.

Lemma sg_bind_cast_result : forall r A w,
  sg_bind r (sg_cast A) = sg_done w -> sg_runtime_type A w.
Proof.
  intros r A w E; destruct r; cbn [sg_bind] in E; try discriminate.
  eapply sg_cast_runtime_type; eauto.
Qed.

Theorem sg_application_runtime_type : forall fuel f a A B w,
  sg_runtime_type (sg_arrow A B) f ->
  sg_apply fuel f a = sg_done w -> sg_runtime_type B w.
Proof.
  intros fuel f a A B w T E; destruct fuel; [discriminate |].
  destruct T as [[D [body [rho T]]] | [inner [T C]]]; subst f;
    cbn [sg_apply] in E; destruct (sg_cast A a); cbn [sg_bind] in E;
    try discriminate; eapply sg_bind_cast_result; eauto.
Qed.

(* Lambda descriptors retain an observable arrow shape. Switch descriptors
  are arbitrary: branch-entry casts establish their declared binder types. *)
Definition sg_data_descriptor (D : typ) : Prop := D = t_int \/ D = t_unit.

Fixpoint sg_safe_syntax (e : sgexp) : Prop :=
  match e with
  | sg_var _ | sg_lit _ | sg_null => True
  | sg_lam D _ _ body => (exists X Y, D = t_arrow X Y) /\ sg_safe_syntax body
  | sg_app f a => sg_safe_syntax f /\ sg_safe_syntax a
  | sg_ann body _ | sg_inl body _ _ | sg_inr body _ _ => sg_safe_syntax body
    | sg_switch scr _ l _ r _ => sg_safe_syntax scr /\
      sg_safe_syntax l /\ sg_safe_syntax r
  end.

(* Unlike sg_runtime_type, these inductive judgments inspect closure bodies
   and every captured binding. Wrappers retain a valid callable underneath;
   their arbitrary boundary annotations are enforced dynamically. *)
Inductive sg_value_valid : sgval -> Prop :=
| sgvv_int : forall n, sg_value_valid (sg_vint n)
| sgvv_unit : sg_value_valid sg_vunit
| sgvv_closure : forall D A B body rho G C,
    (exists X Y, D = t_arrow X Y) ->
    sg_safe_syntax body -> sgtyping (A :: G) body C -> sgconsistent C B ->
    sg_environment_valid rho G -> sg_value_valid (sg_closure D A B body rho)
| sgvv_wrapper : forall A B inner,
    sg_value_valid inner -> sg_callable inner = true ->
    sg_value_valid (sg_wrapper A B inner)
with sg_environment_valid : list sgval -> list sgtyp -> Prop :=
| sgev_nil : sg_environment_valid nil nil
| sgev_cons : forall v A rho G,
    sg_value_valid v -> sg_runtime_type A v -> sg_environment_valid rho G ->
    sg_environment_valid (v :: rho) (A :: G).

Definition sg_value_typing (v : sgval) (A : sgtyp) : Prop :=
  sg_value_valid v /\ sg_runtime_type A v.

Lemma sg_environment_lookup : forall rho G,
  sg_environment_valid rho G -> forall index A,
  nth_error G index = Some A ->
  exists v, nth_error rho index = Some v /\ sg_value_typing v A.
Proof.
  intros rho G Env; induction Env as [| head Head tail Types Valid Shape Rest IH];
    intros index Target Lookup; destruct index; simpl in Lookup; try discriminate.
  - inversion Lookup; subst Target; exists head; simpl; unfold sg_value_typing; auto.
  - destruct (IH _ _ Lookup) as [found [At Typed]].
    exists found; simpl; auto.
Qed.

Lemma sg_cast_valid : forall A v w,
  sg_value_valid v -> sg_cast A v = sg_done w -> sg_value_valid w.
Proof.
  induction A; intros input output Valid Cast; cbn [sg_cast] in Cast;
    try solve [inversion Cast; subst; assumption | discriminate].
  - destruct input; inversion Cast; subst; assumption.
  - destruct input; inversion Cast; subst; assumption.
  - destruct (sg_callable input) eqn:Callable; inversion Cast; subst.
    apply sgvv_wrapper; assumption.
  - destruct (sg_cast A1 input) eqn:Left.
    + inversion Cast; subst; eapply IHA1; eauto.
    + eapply IHA2; eauto.
    + eapply IHA2; eauto.
Qed.

Theorem sg_cast_logical_preservation : forall A v w,
  sg_value_valid v -> sg_cast A v = sg_done w -> sg_value_typing w A.
Proof.
  intros A v w Valid Cast; split.
  - eapply sg_cast_valid; eauto.
  - eapply sg_cast_runtime_type; eauto.
Qed.

Lemma sg_valid_descriptor_shape : forall v, sg_value_valid v ->
  (exists n, v = sg_vint n) \/ v = sg_vunit \/
  (sg_callable v = true /\ exists X Y, sg_tag v = t_arrow X Y).
Proof.
  intros v Valid; induction Valid.
  - left; eauto.
  - right; left; reflexivity.
  - right; right; simpl; auto.
  - right; right; simpl in *.
    destruct IHValid as [[n Eq] | [Eq | [Call Tag]]]; subst;
      simpl in *; try discriminate; auto.
Qed.

Lemma sg_data_test_refinement : forall v D,
  sg_value_valid v -> sg_data_descriptor D -> sg_test (sg_tag v) D = true ->
  sg_value_typing v (sg_lift D).
Proof.
  intros v D Valid Data Test; split; [exact Valid |].
  assert (Sub : sg_tag v <: D).
  { unfold sg_test in Test; case_if in Test; auto; discriminate. }
  destruct (sg_valid_descriptor_shape _ Valid)
    as [[n Eq] | [Eq | [Call [X [Y Tag]]]]];
    destruct Data as [Data | Data]; subst; simpl in *;
    try solve [eauto | inversion Sub].
  - rewrite Tag in Sub; exfalso; eapply arrow_sub_int_false; eauto.
  - rewrite Tag in Sub; exfalso; eapply arrow_sub_unit_false; eauto.
Qed.

Lemma sg_bind_success : forall r k w,
  sg_bind r k = sg_done w -> exists v, r = sg_done v /\ k v = sg_done w.
Proof.
  intros r k w Run; destruct r; simpl in Run; try discriminate; eauto.
Qed.

Theorem sg_finite_success_preservation : forall fuel,
  (forall G e A rho w, sgtyping G e A -> sg_safe_syntax e ->
    sg_environment_valid rho G -> sg_eval fuel rho e = sg_done w ->
    sg_value_typing w A) /\
  (forall f a w, sg_value_valid f -> sg_value_valid a ->
    sg_apply fuel f a = sg_done w -> sg_value_valid w).
Proof.
  induction fuel as [| fuel [Eval Apply]].
  - split; intros; discriminate.
  - split.
    + intros G e A rho w Typed Safe Env Run.
      destruct Typed as
        [G index A Lookup | G n | G | G D A B body C Body Cons
        | G f a T A B C Fun Match Arg Cons
        | G e A B Body Cons | G e A B C Body Cons
        | G e A B C Body Cons
        | G e D l E r A T B C Scr Disj Left LC Right RC];
        cbn [sg_eval] in Run; cbn [sg_safe_syntax] in Safe.
      * destruct (sg_environment_lookup _ _ Env _ _ Lookup)
          as [v [At VT]]. rewrite At in Run; inversion Run; subst; exact VT.
      * inversion Run; subst; split; [constructor | simpl; eauto].
      * inversion Run; subst; split; [constructor | reflexivity].
      * inversion Run; subst; destruct Safe as [Descriptor Safe].
        split.
        -- eapply sgvv_closure; eauto.
        -- left; eauto.
      * destruct Safe as [SF SA].
        destruct (sg_bind_success _ _ _ Run) as [fv [FR Rest]].
        destruct (sg_bind_success _ _ _ Rest) as [av [AR Call]].
        destruct (Eval _ _ _ _ _ Fun SF Env FR) as [FV FS].
        destruct (Eval _ _ _ _ _ Arg SA Env AR) as [AV AS].
        split; [exact (Apply fv av w FV AV Call) |].
        inversion Match; subst; [exact I |].
        eapply sg_application_runtime_type; eauto.
      * destruct (sg_bind_success _ _ _ Run) as [v [VR Cast]].
        destruct (Eval _ _ _ _ _ Body Safe Env VR) as [Valid Shape].
        exact (sg_cast_logical_preservation A v w Valid Cast).
      * destruct (sg_bind_success _ _ _ Run) as [v [VR Cast]].
        destruct (Eval _ _ _ _ _ Body Safe Env VR) as [Valid Shape].
        destruct (sg_cast_logical_preservation A v w Valid Cast) as [WV WS].
        split; [exact WV | left; exact WS].
      * destruct (sg_bind_success _ _ _ Run) as [v [VR Cast]].
        destruct (Eval _ _ _ _ _ Body Safe Env VR) as [Valid Shape].
        destruct (sg_cast_logical_preservation B v w Valid Cast) as [WV WS].
        split; [exact WV | right; exact WS].
      * destruct Safe as [SS [SL SR]].
        destruct (sg_bind_success _ _ _ Run) as [v [VR Branch]].
        destruct (Eval _ _ _ _ _ Scr SS Env VR) as [Valid Shape].
        destruct (sg_test (sg_tag v) D) eqn:DT.
        -- destruct (sg_bind_success _ _ _ Branch) as [checked [Entry Rest]].
           destruct (sg_cast_logical_preservation (sg_lift D) v checked Valid Entry)
             as [VV VS].
           destruct (sg_bind_success _ _ _ Rest) as [b [BR Cast]].
           assert (Ext : sg_environment_valid (checked :: rho) (sg_lift D :: G)).
           { constructor; assumption. }
           destruct (Eval _ _ _ _ _ Left SL Ext BR) as [BV BS].
           exact (sg_cast_logical_preservation A b w BV Cast).
        -- destruct (sg_test (sg_tag v) E) eqn:ET; [| discriminate].
           destruct (sg_bind_success _ _ _ Branch) as [checked [Entry Rest]].
           destruct (sg_cast_logical_preservation (sg_lift E) v checked Valid Entry)
             as [VV VS].
           destruct (sg_bind_success _ _ _ Rest) as [b [BR Cast]].
           assert (Ext : sg_environment_valid (checked :: rho) (sg_lift E :: G)).
           { constructor; assumption. }
           destruct (Eval _ _ _ _ _ Right SR Ext BR) as [BV BS].
           exact (sg_cast_logical_preservation A b w BV Cast).
    + intros f a w Valid Arg Run.
      inversion Valid as [n | | D A B body rho G C Desc Safe Typed Cons Env
        | A B inner Inner Callable]; subst; cbn [sg_apply] in Run;
        try discriminate.
      * destruct (sg_bind_success _ _ _ Run) as [checked [Cast Rest]].
        destruct (sg_cast_logical_preservation A a checked Arg Cast)
          as [CV CS].
        destruct (sg_bind_success _ _ _ Rest) as [v [Body Result]].
        assert (Ext : sg_environment_valid (checked :: rho) (A :: G)).
        { constructor; assumption. }
        destruct (Eval (A :: G) body C (checked :: rho) v Typed Safe Ext Body)
          as [VV VS].
        exact (sg_cast_valid B v w VV Result).
      * destruct (sg_bind_success _ _ _ Run) as [checked [Cast Rest]].
        pose proof (sg_cast_valid A a checked Arg Cast) as Checked.
        destruct (sg_bind_success _ _ _ Rest) as [v [Call Result]].
        pose proof (Apply inner checked v Inner Checked Call) as Returned.
        exact (sg_cast_valid B v w Returned Result).
Qed.

Corollary sg_evaluation_logical_preservation : forall fuel G e A rho w,
  sgtyping G e A -> sg_safe_syntax e -> sg_environment_valid rho G ->
  sg_eval fuel rho e = sg_done w -> sg_value_typing w A.
Proof.
  intros fuel; exact (proj1 (sg_finite_success_preservation fuel)).
Qed.

Corollary sg_application_logical_preservation : forall fuel f a A B w,
  sg_value_typing f (sg_arrow A B) -> sg_value_valid a ->
  sg_apply fuel f a = sg_done w -> sg_value_typing w B.
Proof.
  intros fuel f a A B w [Valid Shape] Arg Run; split.
  - exact (proj2 (sg_finite_success_preservation fuel) f a w Valid Arg Run).
  - exact (sg_application_runtime_type fuel f a A B w Shape Run).
Qed.

Theorem sg_operational_logical_preservation : forall G e A rho w,
  sgtyping G e A -> sg_safe_syntax e -> sg_environment_valid rho G ->
  sg_runs (sg_evaluate rho e) (sg_done w) -> sg_value_typing w A.
Proof.
  intros G e A rho w Typed Safe Env Run.
  destruct (proj1 sg_unbounded_complete _ _ Run) as [fuel Eval].
  exact (sg_evaluation_logical_preservation fuel G e A rho w Typed Safe Env Eval).
Qed.

Theorem sg_operational_application_preservation : forall f a A B w,
  sg_value_typing f (sg_arrow A B) -> sg_value_valid a ->
  sg_runs (sg_invoke f a) (sg_done w) -> sg_value_typing w B.
Proof.
  intros f a A B w Fun Arg Run.
  destruct (proj1 sg_unbounded_complete _ _ Run) as [fuel Apply].
  exact (sg_application_logical_preservation fuel f a A B w Fun Arg Apply).
Qed.

Theorem sg_evaluation_descriptor_safety : forall fuel G e A rho w D,
  sgtyping G e A -> sg_safe_syntax e -> sg_environment_valid rho G ->
  sg_eval fuel rho e = sg_done w -> sg_data_descriptor D ->
  sg_test (sg_tag w) D = true -> sg_value_typing w (sg_lift D).
Proof.
  intros fuel G e A rho w D Typed Safe Env Run Data Test.
  destruct (sg_evaluation_logical_preservation fuel G e A rho w
    Typed Safe Env Run) as [Valid Shape].
  exact (sg_data_test_refinement w D Valid Data Test).
Qed.

(* Errors are explicit outcomes: consistency casts and partial switches can
   fail even in this fragment. This theorem does not assert their absence. *)
Theorem sg_logical_safety : forall G e A rho,
  sgtyping G e A -> sg_safe_syntax e -> sg_environment_valid rho G ->
  (exists w, sg_runs (sg_evaluate rho e) (sg_done w) /\ sg_value_typing w A) \/
  sg_runs (sg_evaluate rho e) sg_error \/ sg_diverges (sg_evaluate rho e).
Proof.
  intros G e A rho Typed Safe Env.
  destruct (sg_termination_classification (sg_evaluate rho e))
    as [[w Run] | [Error | Diverges]]; eauto.
  left; exists w; split; [exact Run |].
  exact (sg_operational_logical_preservation G e A rho w Typed Safe Env Run).
Qed.

Lemma sg_safe_syntax_precision : forall e e', sgterm_precision e e' ->
  (sg_safe_syntax e <-> sg_safe_syntax e').
Proof.
  induction 1; cbn [sg_safe_syntax] in *; tauto.
Qed.

(* Descriptor precision fixes observable descriptors, so the established
   static guarantee stays inside the descriptor-safe fragment. *)
Corollary sg_safe_static_gradual_guarantee : forall e e' G G' A,
  sgterm_precision e e' -> sg_env_precision G G' ->
  sgtyping G e A -> sg_safe_syntax e ->
  exists A', sgtyping G' e' A' /\ sgprecision A A' /\ sg_safe_syntax e'.
Proof.
  intros e e' G G' A Prec Env Typed Safe.
  destruct (sg_static_gradual_guarantee e e' Prec G G' A Env Typed)
    as [A' [Target Types]].
  exists A'; split; [exact Target | split; [exact Types |]].
  exact (proj1 (sg_safe_syntax_precision e e' Prec) Safe).
Qed.

Definition sg_id := sg_lam (t_arrow t_int t_int) sg_int sg_int (sg_var 0).

(* Elaboration of the ORIGINAL locally nameless source language.
   Delta assigns de Bruijn positions to its free names. Binder premises open
   the original body with a fresh name but elaborate to one fixed target body.
  Alongside the cofinite rules, fresh-name rules select one opening; their
  source soundness uses sg_typing_fresh_open below. Completeness uses these
  rules, not a claimed equivalence with the cofinite-only relation.
  General static subsumption installs a checked target annotation. Union
  injections are also retained as explicit elaboration choices. *)
Inductive sg_exact_elaboration : env -> list (var * typ) ->
    exp -> sgexp -> typ -> Prop :=
| sgee_lit : forall G Delta n, okt G ->
    sg_exact_elaboration G Delta (e_lit n) (sg_lit n) t_int
| sgee_null : forall G Delta, okt G ->
    sg_exact_elaboration G Delta e_null sg_null t_unit
| sgee_var : forall G Delta x A index, okt G -> binds x A G ->
    nth_error Delta index = Some (x, A) ->
    sg_exact_elaboration G Delta (e_var_f x) (sg_var index) A
| sgee_abs : forall L G Delta A B body target, inhabited B ->
    (forall x, x \notin L ->
      sg_exact_elaboration (G & x ~: A) ((x, A) :: Delta)
        (open_exp_wrt_exp body (e_var_f x)) target B) ->
    sg_exact_elaboration G Delta (e_abs A B body)
      (sg_lam (t_arrow A B) (sg_lift A) (sg_lift B) target) (t_arrow A B)
| sgee_app : forall G Delta f a ft argtarget A B,
    sg_exact_elaboration G Delta f ft (t_arrow A B) ->
  sg_exact_elaboration G Delta a argtarget A ->
  sg_exact_elaboration G Delta (e_app f a) (sg_app ft argtarget) B
| sgee_inl : forall G Delta e target A B,
    sg_exact_elaboration G Delta e target A ->
    sg_exact_elaboration G Delta e (sg_inl target (sg_lift A) (sg_lift B))
      (t_union A B)
| sgee_inr : forall G Delta e target A B,
    sg_exact_elaboration G Delta e target B ->
    sg_exact_elaboration G Delta e (sg_inr target (sg_lift A) (sg_lift B))
      (t_union A B)
| sgee_switch : forall L G Delta e et A l lt B r rt C,
    sg_exact_elaboration G Delta e et (t_union A B) ->
    (forall x, x \notin L ->
      sg_exact_elaboration (G & x ~: A) ((x, A) :: Delta)
        (open_exp_wrt_exp l (e_var_f x)) lt C) ->
    (forall x, x \notin L ->
      sg_exact_elaboration (G & x ~: B) ((x, B) :: Delta)
        (open_exp_wrt_exp r (e_var_f x)) rt C) ->
    A *s1 B ->
    sg_exact_elaboration G Delta (e_typeof e A l B r)
      (sg_switch et A lt B rt (sg_lift C)) C
  | sgee_sub : forall G Delta e target A B,
    sg_exact_elaboration G Delta e target A -> A <: B ->
    sg_exact_elaboration G Delta e (sg_ann target (sg_lift B)) B
| sgee_abs_pick : forall G Delta A B body target x,
    inhabited B -> x \notin fv_exp body ->
    sg_exact_elaboration (G & x ~: A) ((x, A) :: Delta)
      (open_exp_wrt_exp body (e_var_f x)) target B ->
    sg_exact_elaboration G Delta (e_abs A B body)
      (sg_lam (t_arrow A B) (sg_lift A) (sg_lift B) target) (t_arrow A B)
| sgee_switch_pick : forall G Delta e et A l lt B r rt C x y,
    sg_exact_elaboration G Delta e et (t_union A B) ->
    x \notin fv_exp l -> y \notin fv_exp r ->
    sg_exact_elaboration (G & x ~: A) ((x, A) :: Delta)
      (open_exp_wrt_exp l (e_var_f x)) lt C ->
    sg_exact_elaboration (G & y ~: B) ((y, B) :: Delta)
      (open_exp_wrt_exp r (e_var_f y)) rt C ->
    A *s1 B ->
    sg_exact_elaboration G Delta (e_typeof e A l B r)
      (sg_switch et A lt B rt (sg_lift C)) C.

Definition sg_elaboration_context (Delta : list (var * typ)) : list sgtyp :=
  map (fun binding => sg_lift (snd binding)) Delta.

Lemma sg_elaboration_lookup : forall Delta index x A,
  nth_error Delta index = Some (x, A) ->
  nth_error (sg_elaboration_context Delta) index = Some (sg_lift A).
Proof.
  induction Delta as [| [y B] Delta IH]; intros index x A Lookup;
    destruct index; simpl in *; try discriminate.
  - inversion Lookup; reflexivity.
  - apply IH with (x := x); exact Lookup.
Qed.

Theorem sg_exact_elaboration_target : forall G Delta e target A,
  sg_exact_elaboration G Delta e target A ->
  sgtyping (sg_elaboration_context Delta) target (sg_lift A) /\
  sg_safe_syntax target.
Proof.
  induction 1.
  - split; [constructor | exact I].
  - split; [constructor | exact I].
  - split; [apply sgt_var; eapply sg_elaboration_lookup; eassumption | exact I].
  - pick_fresh x. destruct (H1 x ltac:(auto)) as [Typed Safe].
    split.
    + eapply sgt_lam; [exact Typed | apply sg_consistent_refl].
    + split; [eauto | exact Safe].
  - destruct IHsg_exact_elaboration1 as [Fun SF].
    destruct IHsg_exact_elaboration2 as [Arg SA].
    split; [| split; assumption].
    eapply sgt_app; [exact Fun | constructor | exact Arg | apply sg_consistent_refl].
  - destruct IHsg_exact_elaboration as [Typed Safe]; split; [| exact Safe].
    eapply sgt_inl; [exact Typed | apply sg_consistent_refl].
  - destruct IHsg_exact_elaboration as [Typed Safe]; split; [| exact Safe].
    eapply sgt_inr; [exact Typed | apply sg_consistent_refl].
  - destruct IHsg_exact_elaboration as [Scr SS].
    pick_fresh x.
    destruct (H1 x ltac:(auto)) as [Left SL].
    destruct (H3 x ltac:(auto)) as [Right SR].
    split; [| split; [exact SS | split; assumption]].
    eapply sgt_switch; [exact Scr | apply Disj_completeness; assumption
      | exact Left | apply sg_consistent_refl | exact Right | apply sg_consistent_refl].
  - destruct IHsg_exact_elaboration as [Typed Safe]; split; [| exact Safe].
    eapply sgt_ann; [exact Typed |].
    eapply sg_con_sub; [eassumption | apply sg_precision_refl | apply sg_precision_refl].
  - destruct IHsg_exact_elaboration as [Typed Safe].
    split.
    + eapply sgt_lam; [exact Typed | apply sg_consistent_refl].
    + split; [eauto | exact Safe].
  - destruct IHsg_exact_elaboration1 as [Scr SS].
    destruct IHsg_exact_elaboration2 as [Left SL].
    destruct IHsg_exact_elaboration3 as [Right SR].
    split; [| split; [exact SS | split; assumption]].
    eapply sgt_switch; [exact Scr | apply Disj_completeness; assumption
      | exact Left | apply sg_consistent_refl | exact Right | apply sg_consistent_refl].
Qed.

Lemma sg_valid_tag_union : forall v A B,
  sg_value_valid v -> sg_tag v <: t_union A B ->
  sg_tag v <: A \/ sg_tag v <: B.
Proof.
  intros v A B Valid Sub.
  destruct (sg_valid_descriptor_shape v Valid)
    as [[n Eq] | [Eq | [Call [X [Y Tag]]]]].
  - subst v; inversion Sub; subst; auto.
  - subst v; inversion Sub; subst; auto.
  - rewrite Tag in *; inversion Sub; subst; auto.
Qed.

(* This is a tag-directed totality theorem, not intrinsic descriptor truth.
   Even a valid closure with an inaccurate arrow descriptor can be wrapped;
   successful future applications still perform the delayed boundary checks. *)
Theorem sg_static_tag_cast_total : forall A v,
  sg_value_valid v -> sg_tag v <: A ->
  exists w, sg_cast (sg_lift A) v = sg_done w /\
    sg_value_typing w (sg_lift A) /\ sg_tag w = sg_tag v.
Proof.
  assert (Total : forall A v, sg_value_valid v -> sg_tag v <: A ->
    exists w, sg_cast (sg_lift A) v = sg_done w).
  { induction A; intros v Valid Sub; cbn [sg_lift sg_cast].
    - exists v; reflexivity.
    - destruct (sg_valid_descriptor_shape v Valid)
        as [[n Eq] | [Eq | [Call [X [Y Tag]]]]].
      + subst v; eauto.
      + subst v; inversion Sub.
      + rewrite Tag in Sub; inversion Sub.
    - destruct (sg_valid_descriptor_shape v Valid)
        as [[n Eq] | [Eq | [Call [X [Y Tag]]]]].
      + subst v; inversion Sub.
      + subst v; inversion Sub.
      + rewrite Tag in Sub; inversion Sub.
    - destruct (sg_valid_descriptor_shape v Valid)
        as [[n Eq] | [Eq | [Call [X [Y Tag]]]]].
      + subst v; inversion Sub.
      + subst v; inversion Sub.
      + rewrite Call; eauto.
    - destruct (sg_valid_tag_union v A1 A2 Valid Sub) as [Left | Right].
      + destruct (IHA1 v Valid Left) as [w Cast]. rewrite Cast; eauto.
      + destruct (sg_cast (sg_lift A1) v) eqn:Cast; eauto.
    - destruct (sg_valid_descriptor_shape v Valid)
        as [[n Eq] | [Eq | [Call [X [Y Tag]]]]].
      + subst v; inversion Sub.
      + subst v; eauto.
      + rewrite Tag in Sub; inversion Sub. }
  intros A v Valid Sub; destruct (Total A v Valid Sub) as [w Cast].
  exists w; split; [exact Cast | split].
  - eapply sg_cast_logical_preservation; eassumption.
  - symmetry; eapply sg_cast_preserves_descriptor; eassumption.
Qed.

Theorem sg_static_subsumption_cast_total : forall A B v,
  sg_value_valid v -> sg_tag v <: A -> A <: B ->
  exists w, sg_cast (sg_lift B) v = sg_done w /\
    sg_value_typing w (sg_lift B) /\ sg_tag w = sg_tag v.
Proof.
  intros A B v Valid Tag Sub; apply sg_static_tag_cast_total; [exact Valid |].
  eapply sub_transitivity; eassumption.
Qed.

(* A checked descriptor is evidence about the boundary actually installed,
   together with the observable test. It is not inferred from an arrow tag. *)
Definition sg_checked_descriptor (v : sgval) (D : typ) : Prop :=
  sg_value_typing v (sg_lift D) /\ sg_tag v <: D.

Theorem sg_descriptor_entry_contract : forall v D checked,
  sg_value_valid v -> sg_test (sg_tag v) D = true ->
  sg_cast (sg_lift D) v = sg_done checked ->
  sg_checked_descriptor checked D /\ sg_tag checked = sg_tag v.
Proof.
  intros v D checked Valid Test Cast.
  pose proof (sg_cast_preserves_descriptor _ _ _ Cast) as Tag.
  assert (Sub : sg_tag v <: D).
  { unfold sg_test in Test; case_if in Test; auto; discriminate. }
  split.
  - split; [eapply sg_cast_logical_preservation; eassumption | rewrite <- Tag; exact Sub].
  - symmetry; exact Tag.
Qed.

Theorem sg_checked_descriptor_application : forall f a A B w,
  sg_checked_descriptor f (t_arrow A B) -> sg_value_valid a ->
  sg_runs (sg_invoke f a) (sg_done w) -> sg_value_typing w (sg_lift B).
Proof.
  intros f a A B w [Typed Tag] Arg Run.
  eapply sg_operational_application_preservation; eassumption.
Qed.

(* Successful descriptor casts to arrows always install the exact wrapper.
   Its call checks the argument before invoking the underlying callable and
   checks the returned value afterwards, even if its descriptor was false. *)
Theorem sg_descriptor_arrow_call_checks : forall v A B checked fuel a w,
  sg_cast (sg_lift (t_arrow A B)) v = sg_done checked ->
  sg_apply (S fuel) checked a = sg_done w ->
  exists argument result,
    sg_cast (sg_lift A) a = sg_done argument /\
    sg_apply fuel v argument = sg_done result /\
    sg_cast (sg_lift B) result = sg_done w.
Proof.
  intros v A B checked fuel a w Entry Run.
  cbn [sg_lift sg_cast] in Entry.
  destruct (sg_callable v); inversion Entry; subst checked.
  cbn [sg_apply] in Run.
  destruct (sg_bind_success _ _ _ Run) as [argument [Arg Rest]].
  destruct (sg_bind_success _ _ _ Rest) as [result [Call Result]].
  exists argument, result; auto.
Qed.

Example sg_open_unknown : sgtyping [sg_any] (sg_ann (sg_var 0) sg_int) sg_int.
Proof.
  eapply sgt_ann with (B := sg_any).
  - apply sgt_var; reflexivity.
  - constructor.
Qed.

Example sg_nested_unknown : sgtyping []
  (sg_lam (t_arrow t_int t_int) sg_any (sg_union sg_any sg_unit)
    (sg_inl (sg_var 0) sg_any sg_unit))
  (sg_arrow sg_any (sg_union sg_any sg_unit)).
Proof.
  eapply sgt_lam; [eapply sgt_inl | apply sg_consistent_refl]; eauto with sg.
  apply sgt_var; reflexivity.
Qed.

Example sg_higher_order_wrapper :
  sg_eval 12 [] (sg_app (sg_ann sg_id (sg_arrow sg_any sg_any)) (sg_lit 7)) =
  sg_done (sg_vint 7).
Proof. reflexivity. Qed.

Example sg_delayed_domain_error :
  sg_eval 12 [] (sg_app (sg_ann sg_id (sg_arrow sg_any sg_any)) sg_null) = sg_error.
Proof. reflexivity. Qed.

Example sg_union_cast_success :
  sg_cast (sg_union sg_unit sg_int) (sg_vint 7) = sg_done (sg_vint 7).
Proof. reflexivity. Qed.

Example sg_union_cast_failure :
  sg_cast (sg_union sg_unit sg_bot) (sg_vint 7) = sg_error.
Proof. reflexivity. Qed.

Example sg_open_evaluation :
  sg_eval 3 [sg_vint 7] (sg_ann (sg_var 0) sg_int) = sg_done (sg_vint 7).
Proof. reflexivity. Qed.

Definition sg_apply_to_seven :=
  sg_lam (t_arrow (t_arrow t_int t_int) t_int)
    (sg_arrow sg_any sg_any) sg_any (sg_app (sg_var 0) (sg_lit 7)).

Example sg_higher_order_argument :
  sg_eval 20 [] (sg_app sg_apply_to_seven sg_id) = sg_done (sg_vint 7).
Proof. reflexivity. Qed.

Example sg_delayed_result_error :
  sg_eval 12 []
    (sg_app (sg_ann sg_id (sg_arrow sg_int sg_unit)) (sg_lit 7)) = sg_error.
Proof. reflexivity. Qed.

Example sg_application_precision :
  sgterm_precision
    (sg_app (sg_ann sg_id (sg_arrow sg_int sg_int)) (sg_lit 7))
    (sg_app (sg_ann sg_id (sg_arrow sg_any sg_any)) (sg_lit 7)).
Proof. unfold sg_id; repeat constructor. Qed.

Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_exp_wrt_exp_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_var_f x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_exp e -> subst_exp u x e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_exp u x (open_exp_wrt_exp t1 t2) =
open_exp_wrt_exp (subst_exp u x t1) (subst_exp u x t2).
Proof.
  intros. unfold open_exp_wrt_exp. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_exp u x e) open_ee_var y = subst_exp u x (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_exp e -> lc_exp u ->
  open_exp_wrt_exp e u = subst_exp u x (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_ee_term : forall e1 Z e2,
lc_exp e1 -> lc_exp e2 -> lc_exp (subst_exp e2 Z e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
 - apply_fresh* lc_e_abs as y.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* lc_e_typeof as y.
   rewrite* subst_ee_open_ee_var.
   rewrite* subst_ee_open_ee_var.
Qed.

#[export]
Hint Resolve subst_ee_term : core.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto.
Qed.

#[export]
Hint Extern 1 (ok _) => apply ok_from_okt : core.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. autos.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
  introv O. induction F using env_ind.
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
  rewrite concat_assoc in *.
  apply okt_push_inv in O.
  destruct O. apply IHF in H.
  apply okt_typ; autos*.
Qed.

(** Automation *)

#[export]
Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ lc_exp e.
Proof.
  induction 1; try splits*.
 - pick_fresh y. specializes H1 y. destructs~ H1.
  apply okt_push_inv in H1. destruct H1. auto.
 - apply lc_e_abs with (L:=L). intros.
  specializes H1 x. destructs~ H1.
 - apply lc_e_typeof with (L:=L); intros. destruct~ IHtyping.
   specialize (H1 x H5). destruct~ H1.
   specialize (H3 x H5). destruct~ H3.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

#[export]
Hint Immediate value_regular : core.

(* ********************************************************************** *)
(** Weakening *)


Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. apply* binds_weaken.
  - apply* typ_app.
  - apply* typ_sub.
  - apply_fresh* typ_abs as x.
    forwards~: (H0 x).
    apply_ih_bind (H1 x); eauto.
  - apply_fresh* typ_typeof as x.
    forwards*: H x. apply_ih_bind (H0 x); eauto.
    forwards*: H1 x. apply_ih_bind (H2 x); eauto.
Qed.

(************************************************************************ *)
(** Term Substitution preserves types *)

Require Import Program.Equality.

Lemma typing_through_subst_ee : forall E F x T e u U,
   typing (E & x ~: U & F) e T ->
   typing E u U ->
   typing (E & F) (subst_exp u x e) T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; introv; simpl.
(*case int*)
 - apply* typ_lit.
 - (*case null*)
   apply* typ_null.
(*case var*)
 - case_var.
  + binds_get H0.
    lets M: (typing_weakening E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H0; apply* typ_var.
(*case app*)
 - eapply typ_app; eauto.
(*case sub*)
 - eapply typ_sub; eauto.
(*case abs*)
 - apply_fresh* typ_abs as y.
   assert (y \notin L) by auto.
   specialize (H0 y H2).
   rewrite* subst_ee_open_ee_var.
   lets : H1 y H2 E (F & y ~: A) x.
   lets : H3 U.
   forwards* : H4.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
(*case typeof*)
 - apply_fresh* typ_typeof as y.
 + assert (y \notin L) by auto.
   rewrite* subst_ee_open_ee_var.
   lets: H y H4.
   lets: H0 y H4 E (F & y ~: A) x.
   lets: H6 U.
   forwards*: H7.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
+ assert (y \notin L) by auto.
   rewrite* subst_ee_open_ee_var.
   lets: H1 y H4.
   lets: H2 y H4 E (F & y ~: B) x.
   lets: H6 U.
   forwards*: H7.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct~ TypU.
Qed.


(* A single fresh opening suffices for static binders. This lemma uses the
   original substitution theorem, independently of target evaluation. *)
Lemma sg_typing_fresh_open : forall G body A B x,
  x \notin fv_exp body ->
  typing (G & x ~: A) (open_exp_wrt_exp body (e_var_f x)) B ->
  forall y, y \notin dom G ->
    typing (G & y ~: A) (open_exp_wrt_exp body (e_var_f y)) B.
Proof.
  intros G body A B x Fresh Typed y FY.
  destruct (classic (x = y)) as [Eq | Neq]; [subst; exact Typed |].
  destruct (typing_regular _ _ _ Typed) as [OK LC].
  destruct (okt_push_inv _ _ _ OK) as [OG FX].
  assert (Extended : okt (G & y ~: A & x ~: A)).
  { apply okt_typ; [apply okt_typ; auto | auto]. }
  pose proof (typing_weakening G (y ~: A) (x ~: A) _ _ Typed Extended) as Weak.
  assert (Var : typing (G & y ~: A) (e_var_f y) A).
  { apply typ_var; [apply okt_typ; auto | apply binds_push_eq]. }
  pose proof (typing_through_subst_ee (G & y ~: A) empty x B
    (open_exp_wrt_exp body (e_var_f x)) (e_var_f y) A) as Rename.
  rewrite concat_empty_r in Rename.
  specialize (Rename Weak Var). rewrite concat_empty_r in Rename.
  rewrite <- (subst_ee_intro x (e_var_f y) body) in Rename; auto.
Qed.

Theorem sg_exact_elaboration_source : forall G Delta e target A,
  sg_exact_elaboration G Delta e target A -> typing G e A.
Proof.
  induction 1.
  - apply typ_lit; assumption.
  - apply typ_null; assumption.
  - apply typ_var; assumption.
  - apply typ_abs with (L := L); assumption.
  - eapply typ_app; eassumption.
  - eapply typ_sub; [eassumption | apply s_orb; apply sub_refl].
  - eapply typ_sub; [eassumption | apply s_orc; apply sub_refl].
  - eapply typ_typeof with (L := L); eassumption.
  - eapply typ_sub; eassumption.
  - apply typ_abs with (L := dom G); [assumption |].
    intros y Fresh. eapply sg_typing_fresh_open; eassumption.
  - apply typ_typeof with (L := dom G); try assumption.
    + intros z Fresh. eapply sg_typing_fresh_open; eassumption.
    + intros z Fresh. eapply sg_typing_fresh_open; eassumption.
Qed.

(* Every named binding has an indexed slot of the same type. Extra slots
   are permitted; no elaboration or target typing is assumed here. *)
Definition sg_context_covers (G : env) (Delta : list (var * typ)) : Prop :=
  forall x A, binds x A G ->
    exists index, nth_error Delta index = Some (x, A).

Lemma sg_context_covers_push : forall G Delta x A,
  sg_context_covers G Delta ->
  sg_context_covers (G & x ~: A) ((x, A) :: Delta).
Proof.
  intros G Delta x A Cover y B Binding.
  destruct (@binds_push_inv typ y B x A G Binding)
    as [[Eq SameType] | [Neq Old]].
  - subst. exists 0; reflexivity.
  - destruct (Cover y B Old) as [index Lookup].
    exists (S index); exact Lookup.
Qed.

Lemma sg_context_covers_canonical : forall G, sg_context_covers G G.
Proof.
  intros G. induction G using env_ind.
  - intros x A Binding. exfalso; eapply binds_empty_inv; eassumption.
  - pose proof (sg_context_covers_push G G x v IHG) as Cover.
    rewrite concat_def, single_def in Cover |- *.
    exact Cover.
Qed.

Theorem sg_exact_elaboration_complete : forall G e A,
  typing G e A -> forall Delta, sg_context_covers G Delta ->
  exists target, sg_exact_elaboration G Delta e target A.
Proof.
  intros G e A Typed. induction Typed; intros Delta Cover.
  - exists (sg_lit i5); apply sgee_lit; assumption.
  - exists sg_null; apply sgee_null; assumption.
  - destruct (Cover x A H0) as [index Lookup].
    exists (sg_var index); apply sgee_var; assumption.
  - destruct (IHTyped1 Delta Cover) as [ft Fun].
    destruct (IHTyped2 Delta Cover) as [argtarget Arg].
    exists (sg_app ft argtarget); eapply sgee_app; eassumption.
  - destruct (IHTyped Delta Cover) as [target Elab].
    exists (sg_ann target (sg_lift A)); eapply sgee_sub; eassumption.
  - pick_fresh x.
    destruct (H1 x ltac:(auto) ((x, A) :: Delta)
      (sg_context_covers_push G Delta x A Cover)) as [target Elab].
    exists (sg_lam (t_arrow A B) (sg_lift A) (sg_lift B) target).
    eapply sgee_abs_pick with (x := x); eauto.
  - destruct (IHTyped Delta Cover) as [et Scr].
    pick_fresh x.
    destruct (H0 x ltac:(auto) ((x, A) :: Delta)
      (sg_context_covers_push G Delta x A Cover)) as [lt Left].
    destruct (H2 x ltac:(auto) ((x, B) :: Delta)
      (sg_context_covers_push G Delta x B Cover)) as [rt Right].
    exists (sg_switch et A lt B rt (sg_lift C)).
    eapply sgee_switch_pick with (x := x) (y := x); eauto.
Qed.

Corollary sg_exact_elaboration_canonical : forall G e A,
  typing G e A -> exists target, sg_exact_elaboration G G e target A.
Proof.
  intros G e A Typed. eapply sg_exact_elaboration_complete;
    [exact Typed | apply sg_context_covers_canonical].
Qed.

Corollary sg_exact_elaboration_closed : forall e A,
  typing empty e A -> exists target,
    sg_exact_elaboration empty [] e target A /\
    sgtyping [] target (sg_lift A) /\ sg_safe_syntax target.
Proof.
  intros e A Typed.
  destruct (sg_exact_elaboration_canonical _ _ _ Typed) as [target Elab].
  rewrite empty_def in Elab.
  rewrite empty_def.
  exists target; split; [exact Elab |].
  exact (sg_exact_elaboration_target _ _ _ _ _ Elab).
Qed.

(* ********************************************************************** *)
(** Typing Inversion Lemmas *)

Lemma inv_int : forall E A i5,
typing E (e_lit i5) A -> typing E (e_lit i5) t_int /\ t_int <: A.
Proof.
  introv Typ.
  inductions Typ. 
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - specialize (IHTyp i5).
  forwards*: IHTyp. destruct H0.
  split*.
  eapply sub_transitivity; eauto.
Qed.

Lemma inv_arrow : forall G A0 B0 e A,
typing G (e_abs A0 B0 e) A ->
typing G (e_abs A0 B0 e) (t_arrow A0 B0) /\
inhabited B0 /\
(exists L, forall x , x \notin  L ->
typing (G & x ~: A0) (e open_ee_var x) B0) /\ (t_arrow A0 B0) <: A.
Proof.
  intros G A0 B0 e A Typ.
  remember (e_abs A0 B0 e) as abs.
  induction Typ; try discriminate.
  - apply IHTyp in Heqabs.
    destruct Heqabs as [TypP [Inh [Hex Sub]]].
    splits*.
    eapply sub_transitivity; eauto.
  - inverts Heqabs.
    splits*.
Qed.

Lemma inv_null : forall E A,
typing E e_null A -> typing E e_null t_unit /\ t_unit <: A.
Proof.
  introv Typ.
  inductions Typ. 
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
Qed.

Lemma check_or_typ : forall E e A B,
   value e ->
   typing E e (t_union A B) ->
   typing E e A \/ typing E e B.
Proof.
  intros.
  inversion H; subst.
  - apply inv_int in H0. destruct H0 as [TypI SubI].
    inversion SubI; subst; [left|right]; eapply typ_sub; eauto.
  - apply inv_arrow in H0.
    destruct H0 as [TypP Rest].
    destruct Rest as [Inh Rest].
    destruct Rest as [Hex Sub].
    inversion Sub; subst; [left|right]; eapply typ_sub; eauto.
  - apply inv_null in H0. destruct H0 as [TypN SubN].
    inversion SubN; subst; [left|right]; eapply typ_sub; eauto.
Qed.

(* Lemma 9 *)

Lemma val_check_disjoint_types : forall E v A B,
A *s1 B ->
value v ->
typing E v A ->
typing E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  unfold DisjSpec1 in Disj. unfold not in Disj.
  inversion Val; subst.
  - apply inv_int in Typ1. destruct Typ1.
    apply inv_int in Typ2. destruct Typ2.
    forwards*: Disj t_int.
  - apply inv_arrow in Typ1.
    destruct Typ1 as [TypP1 Rest1].
    destruct Rest1 as [Inh1 Rest1].
    destruct Rest1 as [Hex1 Sub1].
    apply inv_arrow in Typ2.
    destruct Typ2 as [TypP2 Rest2].
    destruct Rest2 as [Inh2 Rest2].
    destruct Rest2 as [Hex2 Sub2].
    destruct Inh1 as [C [OrdC SubC]].
    assert (Hat : t_arrow t_top C <: t_arrow A0 B0) by auto.
    apply (Disj (t_arrow t_top C)); auto. split.
    eapply sub_transitivity; eauto.
    eapply sub_transitivity; eauto.
  - apply inv_null in Typ1. destruct Typ1.
    apply inv_null in Typ2. destruct Typ2.
    forwards*: Disj t_unit.
Qed.

Lemma findtype_inhabited : forall E e T C,
  typing E e T -> findtype e C -> inhabited C.
Proof.
  introv Typ Find. inductions Find.
  - exists t_int. split*.
  - apply inv_arrow in Typ.
    destruct Typ as [TypP Rest].
    destruct Rest as [Inh Rest].
    apply inhabited_arrow. auto.
  - exists t_unit. split*.
Qed.

Lemma findtype_unique : forall e A B,
  findtype e A -> findtype e B -> A = B.
Proof.
  introv F1 F2. inversion F1; subst; inversion F2; subst; auto.
Qed.

Lemma check_find_type : forall E e A B,
typing E e A ->
findtype e B ->
B <: A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ.
    destruct~ Typ.
  - apply inv_arrow in Typ.
    destruct Typ as [TypP Rest].
    destruct Rest as [Inh Rest].
    destruct Rest as [Hex Sub].
    auto.
  - apply inv_null in Typ. destruct~ Typ.
Qed.

(*******************************)
(****  Preservation Lemma  *****)
(*******************************)

(* Theorem 7 *)

Lemma preservation : forall E e e' T,
  typing E e T ->
  e --> e' ->
  typing E e' T.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inverts* Red ].
  - (* app *)
    inverts* Red.
    (* beta *)
        lets InvA: inv_arrow Typ1.
        destruct InvA as [TypP RestA].
        destruct RestA as [Inh RestA].
        destruct RestA as [Hex Sub].
        destruct Hex as [L Body].
        inverts Sub.
        pick_fresh x.
        forwards* Bodyx: Body x.
        rewrite <- (concat_empty_r G).
        rewrite <- (concat_empty_r (G & x ~: A0)) in Bodyx.
        forwards*: typing_through_subst_ee Bodyx.
        rewrite* (@subst_ee_intro x).
  - (* typeof *)
    inverts* Red.
    + (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*true goal*)
       pick_fresh y. assert (y \notin L) by auto.
       forwards*: H H5.
       assert  (G & y ~: A = G & y ~: A & empty).
       rewrite* concat_empty_r. rewrite H7 in H6.
       assert (G = G & empty).
       rewrite* concat_empty_r.
       rewrite H8.
       forwards*: typing_through_subst_ee.
       rewrite* (@subst_ee_intro y).
     * (*false goal: tag inhabits both A and B*)
       lets temp1: check_find_type G e B C0 H4.
       lets SubB: temp1 H12.
       lets InhC: findtype_inhabited Typ H12.
       destruct InhC as [D [OrdD SubD]].
       unfold DisjSpec1 in H3. unfold not in H3.
       exfalso. apply (H3 D); auto. split.
       eapply sub_transitivity; eauto.
       eapply sub_transitivity; eauto.
    +  (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*false goal: tag inhabits both A and B*)
        lets temp1: check_find_type G e A C0 H4.
        lets SubA: temp1 H12.
        lets InhC: findtype_inhabited Typ H12.
        destruct InhC as [D [OrdD SubD]].
        unfold DisjSpec1 in H3. unfold not in H3.
        exfalso. apply (H3 D); auto. split.
        eapply sub_transitivity; eauto.
        eapply sub_transitivity; eauto.
     * (*true goal*)  
        pick_fresh y. assert (y \notin L) by auto.
        forwards*: H1 H5.
        assert  (G & y ~: B = G & y ~: B & empty).
        rewrite* concat_empty_r. rewrite H7 in H6.
        assert (G = G & empty).
        rewrite* concat_empty_r.
        rewrite H8.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
Qed.


(*******************************)
(******  Progress Lemma  *******)
(*******************************)

(* Theorem 8 *)

Lemma progress : forall e T,
typing empty e T -> (value e) \/ (exists e', e --> e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 (*case null*)
 - left*.
 (*case var*)
 - apply binds_empty_inv in H0. inversion H0.
 (*case typ-app*)
 - right. destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H.
     (*i infers arrow*)
     apply inv_int in Typ1.
     destruct Typ1.
     inverts H1.
     apply inv_null in Typ1.
     destruct Typ1.
     inverts H1.
     (*case step-appl*)
   * destruct H0.
     exists* (e_app e1 x).
   (*case step-appr*)
  + destruct H. 
    exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2.
(*case typ-sub*)
 - destruct~ IHTyp.
(*case typ-abs*)
 - left. forwards*: typing_regular Typ'.
(*case typ-typeof*)
 - right. destruct* IHTyp.
  + apply check_or_typ in Typ; auto.
    destruct Typ.
    (*case typeofl*)
   * inversion H4; subst.
     { (*case e = int*)
      apply inv_int in H5. destruct H5.
      exists (open_exp_wrt_exp e1 (e_lit i5)).
      eapply step_typeofl with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply inv_arrow in H5.
      destruct H5 as [TypP RestA].
      destruct RestA as [Inh RestA].
      destruct RestA as [Hex Sub].
      exists (open_exp_wrt_exp e1 (e_abs A0 B0 e0)).
      eapply step_typeofl with (C:=(t_arrow A0 B0)); eauto.
      forwards*: typing_regular Typ'.
     }
     {
       (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_exp_wrt_exp e1 e_null).
       eapply step_typeofl with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
   * (*case typeofr*)
     inversion H4; subst.
     { (*case e = int*)
      apply inv_int in H5. destruct H5.
      exists (open_exp_wrt_exp e2 (e_lit i5)).
      eapply step_typeofr with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply inv_arrow in H5.
      destruct H5 as [TypP RestA].
      destruct RestA as [Inh RestA].
      destruct RestA as [Hex Sub].
      exists (open_exp_wrt_exp e2 (e_abs A0 B0 e0)).
      eapply step_typeofr with (C:=(t_arrow A0 B0)); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_exp_wrt_exp e2 e_null).
       eapply step_typeofr with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
  + (*case typeof*)
    destruct H4.
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards*: typing_regular Typ'.
Qed.

(*************************************)
(* More typing inversion *)

Lemma inv_app : forall E e1 e2 A,
typing E (e_app e1 e2) A ->
exists A1 B1, typing E e1 (t_arrow A1 B1) /\ typing E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
  exists* A B.
  specialize (IHTyp e1 e2).
  forwards*: IHTyp.
Qed.

Lemma inv_typeof : forall E e e1 e2 A B C,
typing E (e_typeof e A e1 B e2) C ->
exists D, typing E e D /\ A *s1 B.
Proof.
  introv Typ.
  inductions Typ.
  specialize (IHTyp e e1 e2 A B).
  forwards*: IHTyp.
  exists* (t_union A B).
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

(* Theorem 10 *)

Lemma determinism : forall E e e1 e2 A, typing E e A -> 
e --> e1 -> e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A.
  induction He1; introv Typ He2.
  (*case step-appl*)
  - inverts* He2.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1. rewrite* H3.
   + inverts* H2; inverts He1.
   + inverts* He1.
(*case step-appr*)
  - inverts* He2.
   + inverts* H; inverts* H4.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1 H1. rewrite* H3.
   + inverts H4; inverts He1.
(*case step-beta*)
  - inverts* He2.
   + inverts* H5. 
   + inverts H0; inverts H5.
(*case step-typeof*)
 - inverts* He2.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H0.
    forwards*: IHHe1. rewrite* H2.
  + inverts H8; inverts He1.
  + inverts H8; inverts He1.
(*case step-typeofl*)
 - inverts* He2.
  + inverts H0. inverts H10. inverts H10. inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [Hscrut Disj].
    unfold DisjSpec1 in Disj. unfold not in Disj.
    lets InhC: findtype_inhabited Hscrut H1.
    destruct InhC as [D0 [OrdD SubD]].
    forwards* EqT: findtype_unique H1 H11. subst.
    exfalso. apply (Disj D0); auto. split.
    eapply sub_transitivity; eauto.
    eapply sub_transitivity; eauto.
(*case step-typeofr*) 
- inverts* He2.
  + inverts H0; inverts H10. 
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [Hscrut Disj].
    unfold DisjSpec1 in Disj. unfold not in Disj.
    lets InhC: findtype_inhabited Hscrut H1.
    destruct InhC as [D0 [OrdD SubD]].
    forwards* EqT: findtype_unique H1 H11. subst.
    exfalso. apply (Disj D0); auto. split.
    eapply sub_transitivity; eauto.
    eapply sub_transitivity; eauto.
Qed.

Lemma value_tag_typing : forall v A C,
  typing empty v A -> findtype v C -> typing empty v C.
Proof.
  intros v A C T F; inversion F; subst.
  - apply inv_int in T; tauto.
  - apply inv_arrow in T; tauto.
  - apply inv_null in T; tauto.
Qed.

Theorem injection_retains_tag : forall v C C',
  findtype v C -> gstep (g_inject (g_embed v)) (g_pack C' v) -> C = C'.
Proof. intros v C C' F R; inversion R; subst; eauto using findtype_unique. Qed.

Theorem gradual_preservation : forall e T e',
  gtyping e T -> gstep e e' -> gtyping e' T.
Proof.
  intros e T e' Ty; generalize dependent e'.
  induction Ty; intros e' R; inversion R; subst; eauto.
  - constructor. eapply preservation; eauto.
  - inversion Ty; subst. constructor; eauto using value_tag_typing.
  - constructor. eapply successful_projection_typing; eauto.
Qed.

Theorem gradual_progress : forall e T, gtyping e T ->
  gvalue e \/ e = g_error \/ exists e', gstep e e'.
Proof.
  intros e T Ty; induction Ty.
  - destruct (progress e A H) as [V | [e' R]]; eauto.
  - destruct IHTy as [V | [Err | [e' R]]].
    + inversion V; subst; inversion Ty; subst.
      match goal with
      | V : value ?v |- _ => destruct (value_has_tag v V) as [C F]; eauto
      end.
    + subst; eauto.
    + eauto.
  - destruct IHTy as [V | [Err | [e' R]]].
    + inversion V; subst; inversion Ty; subst.
      destruct (classic (subtyping C A)); eauto.
    + subst; eauto.
    + eauto.
  - left. constructor. eauto using tag_is_value.
  - eauto.
Qed.

Theorem gradual_determinism : forall e T e1 e2,
  gtyping e T -> gstep e e1 -> gstep e e2 -> e1 = e2.
Proof.
  intros e T e1 e2 Ty; generalize dependent e2; generalize dependent e1.
  induction Ty; intros e1 e2 R1 R2;
    inversion R1; subst; inversion R2; subst;
    try match goal with H : gstep g_error _ |- _ => inversion H end;
    try match goal with H : gstep (g_pack _ _) _ |- _ => inversion H end;
    try match goal with H : gstep (g_embed _) _ |- _ => inversion H; subst end;
    try solve [exfalso; eapply static_value_no_step; eassumption];
    try solve [f_equal; eauto using determinism, findtype_unique];
    try contradiction; auto.
Qed.

Theorem gradual_preservation_many : forall e e', gsteps e e' ->
  forall T, gtyping e T -> gtyping e' T.
Proof. induction 1; intros; eauto using gradual_preservation. Qed.

Theorem gradual_safety : forall e e' T,
  gtyping e T -> gsteps e e' ->
  gvalue e' \/ e' = g_error \/ exists e'', gstep e' e''.
Proof. eauto using gradual_progress, gradual_preservation_many. Qed.

Theorem boundary_roundtrip : forall v A,
  typing empty v A -> value v ->
  gsteps (g_project A (g_inject (g_embed v))) (g_embed v).
Proof.
  intros v A T V. destruct (value_has_tag v V) as [C F].
  eapply gsteps_cons.
  - apply gs_project_ctx. apply gs_inject_value with (C := C); auto.
  - eapply gsteps_cons; [apply gs_project_ok | constructor].
    eapply check_find_type; eauto.
Qed.

Example int_at_top : gtyping (g_embed (e_lit 7)) (g_static t_top).
Proof. constructor; eauto. Qed.
Example int_injection_tag :
  gstep (g_inject (g_embed (e_lit 7))) (g_pack t_int (e_lit 7)).
Proof. auto. Qed.
Example int_projection_success :
  gsteps (g_project t_int (g_inject (g_embed (e_lit 7)))) (g_embed (e_lit 7)).
Proof. apply boundary_roundtrip; auto. Qed.
Example unit_projection_failure_typed :
  gtyping (g_project t_unit (g_inject (g_embed (e_lit 7)))) (g_static t_unit).
Proof. eauto. Qed.
Example unit_projection_failure :
  gsteps (g_project t_unit (g_inject (g_embed (e_lit 7)))) g_error.
Proof.
  eapply gsteps_cons.
  - apply gs_project_ctx. apply int_injection_tag.
  - eapply gsteps_cons; [apply gs_project_fail | constructor].
    intro H; inversion H.
Qed.
Example unit_roundtrip :
  gsteps (g_project t_unit (g_inject (g_embed e_null))) (g_embed e_null).
Proof. apply boundary_roundtrip; auto. Qed.

Definition switch_example := e_typeof (e_lit 7) t_int (e_lit 1) t_unit (e_lit 0).
Example switch_example_typed : typing empty switch_example t_int.
Proof.
  unfold switch_example. apply typ_typeof with (L := \{}).
  - eauto.
  - intros; unfold open_exp_wrt_exp; simpl. apply typ_lit. apply okt_typ; auto.
  - intros; unfold open_exp_wrt_exp; simpl. apply typ_lit. apply okt_typ; auto.
  - apply Disj_soundness; auto.
Qed.
Example switch_example_step : step switch_example (e_lit 1).
Proof.
  unfold switch_example.
  change (step (e_typeof (e_lit 7) t_int (e_lit 1) t_unit (e_lit 0))
    (open_exp_wrt_exp (e_lit 1) (e_lit 7))).
  eapply step_typeofl with (C := t_int); eauto.
  apply lc_e_typeof with (L := \{}); intros; unfold open_exp_wrt_exp; simpl; auto.
Qed.
Example switch_boundary_typed :
  gtyping (g_project t_int (g_inject (g_embed switch_example))) (g_static t_int).
Proof. eauto using switch_example_typed. Qed.
Example switch_boundary_result :
  gsteps (g_project t_int (g_inject (g_embed switch_example))) (g_embed (e_lit 1)).
Proof.
  eapply gsteps_cons.
  - apply gs_project_ctx. apply gs_inject_ctx. apply gs_static.
    apply switch_example_step.
  - apply boundary_roundtrip; auto.
Qed.

(* Observations relate ORIGINAL values to runtime results independently of
   typing and evaluation. Arrow observations deliberately do not assert a
   logical substitution or an extensional relation between function bodies. *)
Inductive sg_source_value_observation : exp -> sgval -> Prop :=
| sgsvo_int : forall n,
    sg_source_value_observation (e_lit n) (sg_vint n)
| sgsvo_null : sg_source_value_observation e_null sg_vunit
| sgsvo_abs : forall A B body w, sg_tag w = t_arrow A B ->
    sg_source_value_observation (e_abs A B body) w.

Lemma sg_source_value_observation_tag : forall e w C,
  sg_source_value_observation e w -> findtype e C -> sg_tag w = C.
Proof.
  intros e w C Obs Find; inversion Obs; subst; inversion Find; subst; auto.
Qed.

Lemma sg_source_value_observation_cast : forall e v A w,
  sg_source_value_observation e v -> sg_cast A v = sg_done w ->
  sg_source_value_observation e w.
Proof.
  intros e v A w Obs Cast; inversion Obs; subst.
  - assert (Eq : w = sg_vint n).
    { eapply sg_cast_data_identity; [constructor | exact Cast]. }
    subst; constructor.
  - assert (Eq : w = sg_vunit).
    { eapply sg_cast_data_identity; [constructor | exact Cast]. }
    subst; constructor.
  - apply sgsvo_abs.
    rewrite <- (sg_cast_preserves_descriptor _ _ _ Cast); assumption.
Qed.

Lemma sg_source_value_cast_total : forall G e A B v,
  typing G e A -> value e -> sg_source_value_observation e v ->
  sg_value_valid v -> A <: B ->
  exists w, sg_cast (sg_lift B) v = sg_done w /\
    sg_source_value_observation e w.
Proof.
  intros G e A B v Typed Val Obs Valid Sub.
  destruct (value_has_tag e Val) as [C Find].
  assert (Tag : sg_tag v <: A).
  { rewrite (sg_source_value_observation_tag _ _ _ Obs Find).
    eapply check_find_type; eassumption. }
  destruct (sg_static_subsumption_cast_total A B v Valid Tag Sub)
    as [w [Cast Rest]].
  exists w; split; [exact Cast |].
  eapply sg_source_value_observation_cast; eassumption.
Qed.

(* Unlike the observation judgment, this theorem actually evaluates target
   code. It permits all elaboration choices, including repeated subsumption. *)
Theorem sg_exact_elaboration_value_evaluation : forall G Delta e target A,
  sg_exact_elaboration G Delta e target A ->
  forall rho, sg_environment_valid rho (sg_elaboration_context Delta) ->
  value e -> exists fuel w,
    sg_eval fuel rho target = sg_done w /\
    sg_source_value_observation e w.
Proof.
  intros G Delta e target A Elab.
  induction Elab as
    [G Delta n OK | G Delta OK | G Delta x A index OK Binding Lookup
    | L G Delta A B body target Inh Bodies IH
    | G Delta f a ft argtarget A B Fun IFun Arg IArg
    | G Delta e target A B Inner IH
    | G Delta e target A B Inner IH
    | L G Delta e et A l lt B r rt C Scr IScr Left ILeft Right IRight Disj
    | G Delta e target A B Inner IH Sub
    | G Delta A B body target x Inh Fresh Body IH
    | G Delta e et A l lt B r rt C x y Scr IScr FX FY Left ILeft Right IRight Disj];
    intros rho Env Val; try solve [inversion Val].
  - exists 1, (sg_vint n); split; [reflexivity | constructor].
  - exists 1, sg_vunit; split; [reflexivity | constructor].
  - exists 1, (sg_closure (t_arrow A B) (sg_lift A) (sg_lift B) target rho).
    split; [reflexivity | constructor; reflexivity].
  - destruct (IH rho Env Val) as [fuel [v [Run Obs]]].
    destruct (sg_exact_elaboration_target _ _ _ _ _ Inner) as [Typed Safe].
    pose proof (sg_evaluation_logical_preservation fuel _ _ _ _ _
      Typed Safe Env Run) as [Valid Shape].
    destruct (sg_source_value_cast_total G e A A v
      (sg_exact_elaboration_source _ _ _ _ _ Inner) Val Obs Valid (sub_refl A))
      as [w [Cast Observed]].
    exists (S fuel), w; split; [cbn [sg_eval]; rewrite Run; exact Cast | exact Observed].
  - destruct (IH rho Env Val) as [fuel [v [Run Obs]]].
    destruct (sg_exact_elaboration_target _ _ _ _ _ Inner) as [Typed Safe].
    pose proof (sg_evaluation_logical_preservation fuel _ _ _ _ _
      Typed Safe Env Run) as [Valid Shape].
    destruct (sg_source_value_cast_total G e B B v
      (sg_exact_elaboration_source _ _ _ _ _ Inner) Val Obs Valid (sub_refl B))
      as [w [Cast Observed]].
    exists (S fuel), w; split; [cbn [sg_eval]; rewrite Run; exact Cast | exact Observed].
  - destruct (IH rho Env Val) as [fuel [v [Run Obs]]].
    destruct (sg_exact_elaboration_target _ _ _ _ _ Inner) as [Typed Safe].
    pose proof (sg_evaluation_logical_preservation fuel _ _ _ _ _
      Typed Safe Env Run) as [Valid Shape].
    destruct (sg_source_value_cast_total G e A B v
      (sg_exact_elaboration_source _ _ _ _ _ Inner) Val Obs Valid Sub)
      as [w [Cast Observed]].
    exists (S fuel), w; split; [cbn [sg_eval]; rewrite Run; exact Cast | exact Observed].
  - exists 1, (sg_closure (t_arrow A B) (sg_lift A) (sg_lift B) target rho).
    split; [reflexivity | constructor; reflexivity].
Qed.

(* A first-order environment semantics for ORIGINAL syntax. Functions may
   occur in application position as literal lambdas, with arbitrary nesting
   of applications/switches in their bodies. Environments and answers contain
   only original integer/null values. Boundary subtype premises restrict the
   theorem to calls whose declared argument/result boundaries are respected;
   they do not mention target evaluation or casts. *)
Inductive sg_source_data : exp -> Prop :=
| sgsd_int : forall n, sg_source_data (e_lit n)
| sgsd_null : sg_source_data e_null.

Inductive sg_source_data_runs : list exp -> exp -> exp -> Prop :=
| sgsdr_value : forall sigma v, sg_source_data v ->
    sg_source_data_runs sigma v v
| sgsdr_var : forall sigma index v,
    nth_error sigma index = Some v -> sg_source_data v ->
    sg_source_data_runs sigma (e_var_b index) v
| sgsdr_beta : forall sigma A B body arg a v X Y,
    sg_source_data_runs sigma arg a -> findtype a X -> X <: A ->
    sg_source_data_runs (a :: sigma) body v -> findtype v Y -> Y <: B ->
    sg_source_data_runs sigma (e_app (e_abs A B body) arg) v
| sgsdr_left : forall sigma scr D l E r a v X,
    sg_source_data_runs sigma scr a -> findtype a X -> X <: D ->
    sg_source_data_runs (a :: sigma) l v ->
    sg_source_data_runs sigma (e_typeof scr D l E r) v
| sgsdr_right : forall sigma scr D l E r a v X,
    sg_source_data_runs sigma scr a -> findtype a X -> ~ (X <: D) -> X <: E ->
    sg_source_data_runs (a :: sigma) r v ->
    sg_source_data_runs sigma (e_typeof scr D l E r) v.

(* Switch answers use Top, so this compilation does not insert a restrictive
   result boundary. Lambda boundaries are precisely their source annotations.
   This is a separate, restricted compiler, not a new elaboration rule. *)
Fixpoint sg_data_compile (e : exp) : sgexp :=
  match e with
  | e_var_b index => sg_var index
  | e_var_f _ => sg_null
  | e_lit n => sg_lit n
  | e_null => sg_null
  | e_abs A B body =>
      sg_lam (t_arrow A B) (sg_lift A) (sg_lift B) (sg_data_compile body)
  | e_app f a => sg_app (sg_data_compile f) (sg_data_compile a)
  | e_typeof scr D l E r =>
      sg_switch (sg_data_compile scr) D (sg_data_compile l)
        E (sg_data_compile r) sg_top
  end.

Definition sg_data_encode (e : exp) : sgval :=
  match e with e_lit n => sg_vint n | _ => sg_vunit end.

Lemma sg_source_data_runs_answer : forall sigma e v,
  sg_source_data_runs sigma e v -> sg_source_data v.
Proof. induction 1; assumption. Qed.

Lemma sg_data_encode_cast : forall v X A,
  sg_source_data v -> findtype v X -> X <: A ->
  sg_cast (sg_lift A) (sg_data_encode v) = sg_done (sg_data_encode v).
Proof.
  intros v X A Data Tag Sub.
  assert (Valid : sg_value_valid (sg_data_encode v)).
  { inversion Data; subst; constructor. }
  assert (Descriptor : sg_tag (sg_data_encode v) = X).
  { inversion Data; subst; inversion Tag; reflexivity. }
  destruct (sg_static_tag_cast_total A (sg_data_encode v) Valid
    ltac:(rewrite Descriptor; exact Sub)) as [w [Cast Rest]].
  assert (Eq : w = sg_data_encode v).
  { eapply sg_cast_data_identity; [inversion Data; subst; constructor | exact Cast]. }
  subst; exact Cast.
Qed.

Lemma sg_data_encode_tag : forall v X,
  sg_source_data v -> findtype v X -> sg_tag (sg_data_encode v) = X.
Proof. intros v X Data Tag; inversion Data; subst; inversion Tag; reflexivity. Qed.

Lemma sg_eval_success_increase : forall n m rho e v,
  n <= m -> sg_eval n rho e = sg_done v -> sg_eval m rho e = sg_done v.
Proof.
  intros n m rho e v Bound Run.
  pose proof (proj1 (sg_fuel_monotonicity n m Bound) rho e) as Stable.
  unfold sg_result_stable in Stable; rewrite Run in Stable.
  apply Stable; discriminate.
Qed.

Lemma sg_data_environment_lookup : forall sigma index v,
  nth_error sigma index = Some v ->
  nth_error (map sg_data_encode sigma) index = Some (sg_data_encode v).
Proof.
  induction sigma as [| a sigma IH]; intros [| index] v Lookup;
    simpl in *; try discriminate.
  - inversion Lookup; reflexivity.
  - apply IH; exact Lookup.
Qed.

(* Recursive compiler correctness for the independent first-order source
   semantics. The conclusion preserves data exactly, not just descriptors. *)
Theorem sg_data_compile_evaluation : forall sigma e v,
  sg_source_data_runs sigma e v ->
  exists fuel, sg_eval fuel (map sg_data_encode sigma) (sg_data_compile e) =
    sg_done (sg_data_encode v).
Proof.
  intros sigma e v Run.
  induction Run as
    [sigma v Data
    | sigma index v Lookup Data
    | sigma A B body arg a v X Y Arg IHArg TagArg SubArg
        Body IHBody TagBody SubBody
    | sigma scr D l E r a v X Scr IHScr Tag Sub Branch IHBranch
    | sigma scr D l E r a v X Scr IHScr Tag Miss Sub Branch IHBranch].
  - exists 1; inversion Data; reflexivity.
  - exists 1; cbn [sg_data_compile sg_eval].
    rewrite (sg_data_environment_lookup sigma index v Lookup); reflexivity.
  - destruct IHArg as [n RunArg]; destruct IHBody as [m RunBody].
    set (budget := Nat.max n m).
    assert (ArgFuel : sg_eval (S budget) (map sg_data_encode sigma)
      (sg_data_compile arg) = sg_done (sg_data_encode a)).
    { eapply sg_eval_success_increase; [| exact RunArg].
      apply le_S; apply Nat.le_max_l. }
    assert (BodyFuel : sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile body) = sg_done (sg_data_encode v)).
    { eapply sg_eval_success_increase; [| exact RunBody].
      apply Nat.le_max_r. }
    pose proof (sg_data_encode_cast a X A
      (sg_source_data_runs_answer _ _ _ Arg) TagArg SubArg) as CastArg.
    pose proof (sg_data_encode_cast v Y B
      (sg_source_data_runs_answer _ _ _ Body) TagBody SubBody) as CastBody.
    exists (S (S budget)).
    change (sg_bind (sg_done (sg_closure (t_arrow A B) (sg_lift A)
      (sg_lift B) (sg_data_compile body) (map sg_data_encode sigma)))
      (fun f => sg_bind (sg_eval (S budget) (map sg_data_encode sigma)
        (sg_data_compile arg)) (sg_apply (S budget) f)) = sg_done (sg_data_encode v)).
    cbn [sg_bind]; rewrite ArgFuel; cbn [sg_bind sg_apply].
    rewrite CastArg; cbn [sg_bind].
    change (sg_bind (sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile body)) (sg_cast (sg_lift B)) = sg_done (sg_data_encode v)).
    rewrite BodyFuel; exact CastBody.
  - destruct IHScr as [n RunScr]; destruct IHBranch as [m RunBranch].
    set (budget := Nat.max n m).
    assert (ScrFuel : sg_eval budget (map sg_data_encode sigma)
      (sg_data_compile scr) = sg_done (sg_data_encode a)).
    { eapply sg_eval_success_increase; [| exact RunScr]. apply Nat.le_max_l. }
    assert (BranchFuel : sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile l) = sg_done (sg_data_encode v)).
    { eapply sg_eval_success_increase; [| exact RunBranch]. apply Nat.le_max_r. }
    pose proof (sg_source_data_runs_answer _ _ _ Scr) as Data.
    pose proof (sg_data_encode_cast a X D Data Tag Sub) as Cast.
    assert (Test : sg_test (sg_tag (sg_data_encode a)) D = true).
    { rewrite (sg_data_encode_tag a X Data Tag).
      unfold sg_test; case_if; congruence. }
    exists (S budget).
    change (sg_bind (sg_eval budget (map sg_data_encode sigma)
      (sg_data_compile scr)) (fun w =>
      if sg_test (sg_tag w) D then
        sg_bind (sg_cast (sg_lift D) w) (fun checked =>
          sg_bind (sg_eval budget (checked :: map sg_data_encode sigma)
            (sg_data_compile l)) (sg_cast sg_top))
      else if sg_test (sg_tag w) E then
        sg_bind (sg_cast (sg_lift E) w) (fun checked =>
          sg_bind (sg_eval budget (checked :: map sg_data_encode sigma)
            (sg_data_compile r)) (sg_cast sg_top))
      else sg_error) = sg_done (sg_data_encode v)).
    rewrite ScrFuel; cbn [sg_bind]; rewrite Test, Cast; cbn [sg_bind].
    change (sg_bind (sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile l)) (sg_cast sg_top) = sg_done (sg_data_encode v)).
    rewrite BranchFuel; reflexivity.
  - destruct IHScr as [n RunScr]; destruct IHBranch as [m RunBranch].
    set (budget := Nat.max n m).
    assert (ScrFuel : sg_eval budget (map sg_data_encode sigma)
      (sg_data_compile scr) = sg_done (sg_data_encode a)).
    { eapply sg_eval_success_increase; [| exact RunScr]. apply Nat.le_max_l. }
    assert (BranchFuel : sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile r) = sg_done (sg_data_encode v)).
    { eapply sg_eval_success_increase; [| exact RunBranch]. apply Nat.le_max_r. }
    pose proof (sg_source_data_runs_answer _ _ _ Scr) as Data.
    pose proof (sg_data_encode_cast a X E Data Tag Sub) as Cast.
    assert (TestD : sg_test (sg_tag (sg_data_encode a)) D = false).
    { rewrite (sg_data_encode_tag a X Data Tag).
      unfold sg_test; case_if; congruence. }
    assert (TestE : sg_test (sg_tag (sg_data_encode a)) E = true).
    { rewrite (sg_data_encode_tag a X Data Tag).
      unfold sg_test; case_if; congruence. }
    exists (S budget).
    change (sg_bind (sg_eval budget (map sg_data_encode sigma)
      (sg_data_compile scr)) (fun w =>
      if sg_test (sg_tag w) D then
        sg_bind (sg_cast (sg_lift D) w) (fun checked =>
          sg_bind (sg_eval budget (checked :: map sg_data_encode sigma)
            (sg_data_compile l)) (sg_cast sg_top))
      else if sg_test (sg_tag w) E then
        sg_bind (sg_cast (sg_lift E) w) (fun checked =>
          sg_bind (sg_eval budget (checked :: map sg_data_encode sigma)
            (sg_data_compile r)) (sg_cast sg_top))
      else sg_error) = sg_done (sg_data_encode v)).
    rewrite ScrFuel; cbn [sg_bind]; rewrite TestD, TestE, Cast; cbn [sg_bind].
    change (sg_bind (sg_eval budget (map sg_data_encode (a :: sigma))
      (sg_data_compile r)) (sg_cast sg_top) = sg_done (sg_data_encode v)).
    rewrite BranchFuel; reflexivity.
Qed.

Corollary sg_data_compile_operational : forall sigma e v,
  sg_source_data_runs sigma e v ->
  sg_runs (sg_evaluate (map sg_data_encode sigma) (sg_data_compile e))
    (sg_done (sg_data_encode v)).
Proof.
  intros sigma e v Run.
  destruct (sg_data_compile_evaluation sigma e v Run) as [fuel Eval].
  apply (proj2 (sg_operational_adequacy
    (sg_evaluate (map sg_data_encode sigma) (sg_data_compile e))
    (sg_done (sg_data_encode v)))).
  split; [discriminate | exists fuel; exact Eval].
Qed.

(* Simultaneous substitution of the indexed data environment into ORIGINAL
   syntax. Missing slots are closed null values; successful data runs never
   use a missing slot. Bound indices below depth remain under their binders. *)
Fixpoint sg_data_instantiate (depth : nat) (sigma : list exp) (e : exp) : exp :=
  match e with
  | e_var_b index =>
      if Nat.ltb index depth then e_var_b index
      else nth (index - depth) sigma e_null
  | e_var_f x => e_var_f x
  | e_lit n => e_lit n
  | e_null => e_null
  | e_abs A B body => e_abs A B (sg_data_instantiate (S depth) sigma body)
  | e_app f a => e_app (sg_data_instantiate depth sigma f)
      (sg_data_instantiate depth sigma a)
  | e_typeof scr D l E r => e_typeof (sg_data_instantiate depth sigma scr)
      D (sg_data_instantiate (S depth) sigma l)
      E (sg_data_instantiate (S depth) sigma r)
  end.

Lemma sg_source_data_open : forall v, sg_source_data v ->
  forall k a, open_exp_wrt_exp_rec k a v = v.
Proof. intros v Data; inversion Data; reflexivity. Qed.

Lemma sg_source_data_nth : forall sigma, Forall sg_source_data sigma ->
  forall index, sg_source_data (nth index sigma e_null).
Proof.
  induction 1; intros [| index]; simpl; auto using sgsd_null.
Qed.

Lemma sg_data_instantiate_open : forall e k sigma a,
  Forall sg_source_data sigma -> sg_source_data a ->
  sg_data_instantiate k (a :: sigma) e =
    open_exp_wrt_exp_rec k a (sg_data_instantiate (S k) sigma e).
Proof.
  induction e; intros k sigma a Env Data; simpl; try (f_equal; eauto).
  destruct (Nat.ltb n k) eqn:Less.
  - apply Nat.ltb_lt in Less.
    assert (Next : Nat.ltb n (S k) = true).
    { apply Nat.ltb_lt; lia. }
    rewrite Next; simpl; case_if; auto; subst; exfalso.
    exact (Nat.lt_irrefl _ Less).
  - apply Nat.ltb_ge in Less.
    destruct (Nat.eq_dec n k) as [Eq | Neq].
    + subst n.
      assert (Next : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
      rewrite Next, Nat.sub_diag; simpl.
      case_if; congruence.
    + assert (Next : Nat.ltb n (S k) = false).
      { apply Nat.ltb_ge; lia. }
      rewrite Next.
      assert (Index : n - k = S (n - S k)).
      { lia. }
      rewrite Index; simpl.
      symmetry; apply sg_source_data_open; apply sg_source_data_nth; assumption.
Qed.

Lemma sg_data_instantiate_lookup : forall sigma index v,
  nth_error sigma index = Some v -> sg_data_instantiate 0 sigma (e_var_b index) = v.
Proof.
  intros sigma index v Lookup; simpl.
  rewrite Nat.sub_0_r. generalize dependent index.
  induction sigma; intros [| index] Lookup; simpl in *; try discriminate.
  - inversion Lookup; reflexivity.
  - eauto.
Qed.

(* Reflexive transitive closure of the actual Section 3 step relation. *)
Inductive sg_original_steps : exp -> exp -> Prop :=
| sgos_refl : forall e, sg_original_steps e e
| sgos_cons : forall e e' v, step e e' -> sg_original_steps e' v ->
    sg_original_steps e v.

Lemma sg_original_steps_trans : forall e m v,
  sg_original_steps e m -> sg_original_steps m v -> sg_original_steps e v.
Proof. induction 1; eauto using sgos_cons. Qed.

Lemma sg_original_steps_preservation : forall e v,
  sg_original_steps e v -> forall G T, typing G e T -> typing G v T.
Proof. induction 1; eauto using preservation. Qed.

Lemma sg_original_steps_argument : forall a b f,
  sg_original_steps a b -> value f ->
  sg_original_steps (e_app f a) (e_app f b).
Proof. induction 1; eauto using sgos_refl, sgos_cons, step_appr. Qed.

Lemma sg_original_steps_switch : forall scr a,
  sg_original_steps scr a -> forall G T D l E r,
  typing G (e_typeof scr D l E r) T ->
  sg_original_steps (e_typeof scr D l E r) (e_typeof a D l E r).
Proof.
  intros scr a Steps; induction Steps as [e | e e' v Step Steps IH];
    intros G T D l E r Typed; [constructor |].
  assert (LC : lc_exp (e_typeof e D l E r)).
  { exact (proj2 (typing_regular _ _ _ Typed)). }
  eapply sgos_cons; [apply step_typeof; eassumption |].
  eapply IH; eapply preservation; eauto using step_typeof.
Qed.

(* This bridge uses original typing and original beta/switch reduction. The
   recursive source derivation supplies data boundaries, not target runs. *)
Theorem sg_source_data_runs_original : forall sigma e v,
  sg_source_data_runs sigma e v ->
  Forall sg_source_data sigma -> forall G T,
  typing G (sg_data_instantiate 0 sigma e) T ->
  sg_original_steps (sg_data_instantiate 0 sigma e) v.
Proof.
  intros sigma e v Run.
  induction Run as
    [sigma v Data
    | sigma index v Lookup Data
    | sigma A B body arg a v X Y Arg IHArg TagArg SubArg
        Body IHBody TagBody SubBody
    | sigma scr D l E r a v X Scr IHScr Tag Sub Branch IHBranch
    | sigma scr D l E r a v X Scr IHScr Tag Miss Sub Branch IHBranch];
    intros Env G T Typed.
  - inversion Data; subst; constructor.
  - rewrite (sg_data_instantiate_lookup sigma index v Lookup); constructor.
  - change (typing G (e_app (e_abs A B (sg_data_instantiate 1 sigma body))
      (sg_data_instantiate 0 sigma arg)) T) in Typed.
    destruct (inv_app _ _ _ _ Typed) as [U [V [Fun ArgTyped]]].
    assert (LC : lc_exp (e_abs A B (sg_data_instantiate 1 sigma body))).
    { exact (proj2 (typing_regular _ _ _ Fun)). }
    pose proof (sg_source_data_runs_answer _ _ _ Arg) as DataArg.
    assert (Val : value a) by (inversion DataArg; constructor).
    pose proof (sg_original_steps_argument _ _ _
      (IHArg Env G U ArgTyped) (val_abs _ _ _ LC)) as Args.
    assert (Beta : step (e_app (e_abs A B (sg_data_instantiate 1 sigma body)) a)
      (sg_data_instantiate 0 (a :: sigma) body)).
    { rewrite (sg_data_instantiate_open body 0 sigma a Env DataArg).
      apply step_beta; assumption. }
    eapply sg_original_steps_trans; [exact Args |].
    eapply sgos_cons; [exact Beta |].
    eapply IHBody; [constructor; assumption |].
    eapply preservation; [| exact Beta].
    eapply sg_original_steps_preservation; eassumption.
  - pose proof (sg_source_data_runs_answer _ _ _ Scr) as DataScr.
    change (typing G (e_typeof (sg_data_instantiate 0 sigma scr) D
      (sg_data_instantiate 1 sigma l) E (sg_data_instantiate 1 sigma r)) T) in Typed.
    destruct (inv_typeof _ _ _ _ _ _ _ Typed) as [U [ScrTyped Disj]].
    pose proof (sg_original_steps_switch _ _ (IHScr Env G U ScrTyped)
      G T D _ E _ Typed) as Scrs.
    assert (Selected : typing G (e_typeof a D (sg_data_instantiate 1 sigma l)
      E (sg_data_instantiate 1 sigma r)) T).
    { eapply sg_original_steps_preservation; eassumption. }
    assert (Choose : step (e_typeof a D (sg_data_instantiate 1 sigma l)
      E (sg_data_instantiate 1 sigma r)) (sg_data_instantiate 0 (a :: sigma) l)).
    { rewrite (sg_data_instantiate_open l 0 sigma a Env DataScr).
      eapply step_typeofl with (C := X); eauto.
      - exact (proj2 (typing_regular _ _ _ Selected)).
      - inversion DataScr; constructor. }
    eapply sg_original_steps_trans; [exact Scrs |].
    eapply sgos_cons; [exact Choose |].
    eapply IHBranch; [constructor; assumption |].
    eapply preservation; eassumption.
  - pose proof (sg_source_data_runs_answer _ _ _ Scr) as DataScr.
    change (typing G (e_typeof (sg_data_instantiate 0 sigma scr) D
      (sg_data_instantiate 1 sigma l) E (sg_data_instantiate 1 sigma r)) T) in Typed.
    destruct (inv_typeof _ _ _ _ _ _ _ Typed) as [U [ScrTyped Disj]].
    pose proof (sg_original_steps_switch _ _ (IHScr Env G U ScrTyped)
      G T D _ E _ Typed) as Scrs.
    assert (Selected : typing G (e_typeof a D (sg_data_instantiate 1 sigma l)
      E (sg_data_instantiate 1 sigma r)) T).
    { eapply sg_original_steps_preservation; eassumption. }
    assert (Choose : step (e_typeof a D (sg_data_instantiate 1 sigma l)
      E (sg_data_instantiate 1 sigma r)) (sg_data_instantiate 0 (a :: sigma) r)).
    { rewrite (sg_data_instantiate_open r 0 sigma a Env DataScr).
      eapply step_typeofr with (C := X); eauto.
      - exact (proj2 (typing_regular _ _ _ Selected)).
      - inversion DataScr; constructor. }
    eapply sg_original_steps_trans; [exact Scrs |].
    eapply sgos_cons; [exact Choose |].
    eapply IHBranch; [constructor; assumption |].
    eapply preservation; eassumption.
Qed.

Corollary sg_data_compile_original_correspondence : forall sigma e v G T,
  sg_source_data_runs sigma e v -> Forall sg_source_data sigma ->
  typing G (sg_data_instantiate 0 sigma e) T ->
  sg_original_steps (sg_data_instantiate 0 sigma e) v /\
  sg_runs (sg_evaluate (map sg_data_encode sigma) (sg_data_compile e))
    (sg_done (sg_data_encode v)).
Proof.
  intros; split; eauto using sg_source_data_runs_original, sg_data_compile_operational.
Qed.

(* Independent source closures. Checked function boundaries are retained as
   source wrappers; quotation erases them, as the original calculus does. *)
Inductive sg_ho_value : Set :=
| sgh_int : nat -> sg_ho_value
| sgh_unit : sg_ho_value
| sgh_closure : typ -> typ -> exp -> list sg_ho_value -> sg_ho_value
| sgh_boundary : typ -> typ -> sg_ho_value -> sg_ho_value.

Fixpoint sg_ho_tag (v : sg_ho_value) : typ :=
  match v with
  | sgh_int _ => t_int | sgh_unit => t_unit
  | sgh_closure A B _ _ => t_arrow A B
  | sgh_boundary _ _ f => sg_ho_tag f
  end.

Fixpoint sg_ho_callable (v : sg_ho_value) : bool :=
  match v with
  | sgh_closure _ _ _ _ => true
  | sgh_boundary _ _ f => sg_ho_callable f
  | _ => false
  end.

Fixpoint sg_ho_check (A : typ) (v : sg_ho_value) : option sg_ho_value :=
  match A with
  | t_top => Some v
  | t_bot => None
  | t_int => match v with sgh_int _ => Some v | _ => None end
  | t_unit => match v with sgh_unit => Some v | _ => None end
  | t_arrow A B => if sg_ho_callable v then Some (sgh_boundary A B v) else None
  | t_union A B => match sg_ho_check A v with
                   | Some w => Some w | None => sg_ho_check B v end
  end.

Fixpoint sg_ho_encode (v : sg_ho_value) : sgval :=
  match v with
  | sgh_int n => sg_vint n | sgh_unit => sg_vunit
  | sgh_closure A B body sigma => sg_closure (t_arrow A B)
      (sg_lift A) (sg_lift B) (sg_data_compile body) (map sg_ho_encode sigma)
  | sgh_boundary A B f => sg_wrapper (sg_lift A) (sg_lift B) (sg_ho_encode f)
  end.

Fixpoint sg_ho_quote (v : sg_ho_value) : exp :=
  match v with
  | sgh_int n => e_lit n | sgh_unit => e_null
  | sgh_closure A B body sigma =>
      e_abs A B (sg_data_instantiate 1 (map sg_ho_quote sigma) body)
  | sgh_boundary _ _ f => sg_ho_quote f
  end.

(* These judgments mention neither the target interpreter nor its values.
   Boundary premises record source descriptor subtyping separately from the
   structural check. No premise assumes the desired compiler simulation. *)
Inductive sg_ho_runs : list sg_ho_value -> exp -> sg_ho_value -> Prop :=
| sghr_int : forall sigma n, sg_ho_runs sigma (e_lit n) (sgh_int n)
| sghr_unit : forall sigma, sg_ho_runs sigma e_null sgh_unit
| sghr_var : forall sigma i v, nth_error sigma i = Some v ->
    sg_ho_runs sigma (e_var_b i) v
| sghr_lam : forall sigma A B body,
    sg_ho_runs sigma (e_abs A B body) (sgh_closure A B body sigma)
| sghr_app : forall sigma f a vf va v,
    sg_ho_runs sigma f vf -> sg_ho_runs sigma a va ->
    sg_ho_applies vf va v -> sg_ho_runs sigma (e_app f a) v
| sghr_left : forall sigma scr D l E r a checked v,
    sg_ho_runs sigma scr a -> sg_ho_tag a <: D ->
    sg_ho_check D a = Some checked -> sg_ho_runs (checked :: sigma) l v ->
    sg_ho_runs sigma (e_typeof scr D l E r) v
| sghr_right : forall sigma scr D l E r a checked v,
    sg_ho_runs sigma scr a -> ~ (sg_ho_tag a <: D) -> sg_ho_tag a <: E ->
    sg_ho_check E a = Some checked -> sg_ho_runs (checked :: sigma) r v ->
    sg_ho_runs sigma (e_typeof scr D l E r) v
with sg_ho_applies : sg_ho_value -> sg_ho_value -> sg_ho_value -> Prop :=
| sgha_closure : forall A B body sigma a checked raw v,
    sg_ho_tag a <: A -> sg_ho_check A a = Some checked ->
    sg_ho_runs (checked :: sigma) body raw ->
    sg_ho_tag raw <: B -> sg_ho_check B raw = Some v ->
    sg_ho_applies (sgh_closure A B body sigma) a v
| sgha_boundary : forall A B f a checked raw v,
    sg_ho_tag a <: A -> sg_ho_check A a = Some checked ->
    sg_ho_applies f checked raw ->
    sg_ho_tag raw <: B -> sg_ho_check B raw = Some v ->
    sg_ho_applies (sgh_boundary A B f) a v.

Scheme sg_ho_runs_ind_mut := Induction for sg_ho_runs Sort Prop
with sg_ho_applies_ind_mut := Induction for sg_ho_applies Sort Prop.
Combined Scheme sg_ho_semantics_ind from sg_ho_runs_ind_mut, sg_ho_applies_ind_mut.

Lemma sg_ho_encode_tag : forall v, sg_tag (sg_ho_encode v) = sg_ho_tag v.
Proof. induction v; simpl; auto. Qed.

Lemma sg_ho_encode_callable : forall v,
  sg_callable (sg_ho_encode v) = sg_ho_callable v.
Proof. induction v; simpl; auto. Qed.

Lemma sg_ho_check_encoding : forall A v,
  sg_cast (sg_lift A) (sg_ho_encode v) =
    match sg_ho_check A v with
    | Some w => sg_done (sg_ho_encode w) | None => sg_error end.
Proof.
  induction A; intro v; cbn [sg_lift sg_cast sg_ho_check].
  - reflexivity.
  - destruct v; reflexivity.
  - reflexivity.
  - rewrite sg_ho_encode_callable. destruct (sg_ho_callable v); reflexivity.
  - rewrite IHA1. destruct (sg_ho_check A1 v); [reflexivity | apply IHA2].
  - destruct v; reflexivity.
Qed.

Lemma sg_ho_check_encode : forall A v w,
  sg_ho_check A v = Some w ->
  sg_cast (sg_lift A) (sg_ho_encode v) = sg_done (sg_ho_encode w).
Proof. intros A v w H; rewrite sg_ho_check_encoding, H; reflexivity. Qed.

Lemma sg_ho_environment_lookup : forall sigma i v,
  nth_error sigma i = Some v ->
  nth_error (map sg_ho_encode sigma) i = Some (sg_ho_encode v).
Proof.
  induction sigma as [|a sigma IH]; intros [|i] v H;
    simpl in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma sg_apply_success_increase : forall n m f a v,
  n <= m -> sg_apply n f a = sg_done v -> sg_apply m f a = sg_done v.
Proof.
  intros n m f a v Bound Run.
  pose proof (proj2 (sg_fuel_monotonicity n m Bound) f a) as Stable.
  unfold sg_result_stable in Stable; rewrite Run in Stable.
  apply Stable; discriminate.
Qed.

Theorem sg_ho_compile_simulation :
  (forall sigma e v, sg_ho_runs sigma e v ->
    exists fuel, sg_eval fuel (map sg_ho_encode sigma) (sg_data_compile e) =
      sg_done (sg_ho_encode v)) /\
  (forall f a v, sg_ho_applies f a v ->
    exists fuel, sg_apply fuel (sg_ho_encode f) (sg_ho_encode a) =
      sg_done (sg_ho_encode v)).
Proof.
  apply sg_ho_semantics_ind.
  - intros; exists 1; reflexivity.
  - intros; exists 1; reflexivity.
  - intros sigma i v Lookup; exists 1; cbn [sg_eval sg_data_compile].
    rewrite (sg_ho_environment_lookup _ _ _ Lookup); reflexivity.
  - intros; exists 1; reflexivity.
  - intros sigma f a vf va v F [nf RF] A [na RA] Call [nc RC].
    set (k := Nat.max nf (Nat.max na nc)).
    assert (EF : sg_eval k (map sg_ho_encode sigma) (sg_data_compile f) =
      sg_done (sg_ho_encode vf)).
    { eapply sg_eval_success_increase with (n := nf); [apply Nat.le_max_l | exact RF]. }
    assert (EA : sg_eval k (map sg_ho_encode sigma) (sg_data_compile a) =
      sg_done (sg_ho_encode va)).
    { eapply sg_eval_success_increase with (n := na); [| exact RA].
      unfold k; eapply Nat.le_trans with (m := Nat.max na nc);
        [apply Nat.le_max_l | apply Nat.le_max_r]. }
    assert (EC : sg_apply k (sg_ho_encode vf) (sg_ho_encode va) =
      sg_done (sg_ho_encode v)).
    { eapply sg_apply_success_increase with (n := nc); [| exact RC].
      unfold k; eapply Nat.le_trans with (m := Nat.max na nc);
        [apply Nat.le_max_r | apply Nat.le_max_r]. }
    exists (S k); cbn [sg_eval sg_data_compile].
    rewrite EF; cbn [sg_bind]; rewrite EA; exact EC.
  - intros sigma scr D l E r a checked v Scr [n RS] Sub Check Branch [m RB].
    set (k := Nat.max n m).
    assert (ES : sg_eval k (map sg_ho_encode sigma) (sg_data_compile scr) =
      sg_done (sg_ho_encode a)).
    { eapply sg_eval_success_increase; [apply Nat.le_max_l | exact RS]. }
    assert (EB : sg_eval k (map sg_ho_encode (checked :: sigma))
      (sg_data_compile l) = sg_done (sg_ho_encode v)).
    { eapply sg_eval_success_increase; [apply Nat.le_max_r | exact RB]. }
    assert (Test : sg_test (sg_tag (sg_ho_encode a)) D = true).
    { rewrite sg_ho_encode_tag; unfold sg_test; case_if; congruence. }
    exists (S k); cbn [sg_eval sg_data_compile]; rewrite ES; cbn [sg_bind].
    rewrite Test, (sg_ho_check_encode _ _ _ Check); cbn [sg_bind].
    change (sg_bind (sg_eval k (map sg_ho_encode (checked :: sigma))
      (sg_data_compile l)) (sg_cast sg_top) = sg_done (sg_ho_encode v)).
    rewrite EB; reflexivity.
  - intros sigma scr D l E r a checked v Scr [n RS] Miss Sub Check Branch [m RB].
    set (k := Nat.max n m).
    assert (ES : sg_eval k (map sg_ho_encode sigma) (sg_data_compile scr) =
      sg_done (sg_ho_encode a)).
    { eapply sg_eval_success_increase; [apply Nat.le_max_l | exact RS]. }
    assert (EB : sg_eval k (map sg_ho_encode (checked :: sigma))
      (sg_data_compile r) = sg_done (sg_ho_encode v)).
    { eapply sg_eval_success_increase; [apply Nat.le_max_r | exact RB]. }
    assert (T1 : sg_test (sg_tag (sg_ho_encode a)) D = false).
    { rewrite sg_ho_encode_tag; unfold sg_test; case_if; congruence. }
    assert (T2 : sg_test (sg_tag (sg_ho_encode a)) E = true).
    { rewrite sg_ho_encode_tag; unfold sg_test; case_if; congruence. }
    exists (S k); cbn [sg_eval sg_data_compile]; rewrite ES; cbn [sg_bind].
    rewrite T1, T2, (sg_ho_check_encode _ _ _ Check); cbn [sg_bind].
    change (sg_bind (sg_eval k (map sg_ho_encode (checked :: sigma))
      (sg_data_compile r)) (sg_cast sg_top) = sg_done (sg_ho_encode v)).
    rewrite EB; reflexivity.
  - intros A B body sigma a checked raw v SubA CheckA Body [n RB] SubB CheckB.
    exists (S n); cbn [sg_apply sg_ho_encode].
    rewrite (sg_ho_check_encode _ _ _ CheckA); cbn [sg_bind].
    change (sg_bind (sg_eval n (map sg_ho_encode (checked :: sigma))
      (sg_data_compile body)) (sg_cast (sg_lift B)) = sg_done (sg_ho_encode v)).
    rewrite RB; apply sg_ho_check_encode; exact CheckB.
  - intros A B f a checked raw v SubA CheckA Call [n RC] SubB CheckB.
    exists (S n); cbn [sg_apply sg_ho_encode].
    rewrite (sg_ho_check_encode _ _ _ CheckA); cbn [sg_bind].
    rewrite RC; apply sg_ho_check_encode; exact CheckB.
Qed.

Corollary sg_ho_compile_operational : forall sigma e v,
  sg_ho_runs sigma e v ->
  sg_runs (sg_evaluate (map sg_ho_encode sigma) (sg_data_compile e))
    (sg_done (sg_ho_encode v)).
Proof.
  intros sigma e v H.
  destruct (proj1 sg_ho_compile_simulation _ _ _ H) as [n Run].
  eapply sg_fuel_sound; [exact Run | discriminate].
Qed.

Lemma sg_ho_check_quote : forall A v w,
  sg_ho_check A v = Some w -> sg_ho_quote w = sg_ho_quote v.
Proof.
  induction A; intros v w Check; cbn [sg_ho_check] in Check.
  - inversion Check; reflexivity.
  - destruct v; inversion Check; reflexivity.
  - discriminate.
  - destruct (sg_ho_callable v); inversion Check; reflexivity.
  - destruct (sg_ho_check A1 v) eqn:Left.
    + inversion Check; subst; eapply IHA1; exact Left.
    + eapply IHA2; exact Check.
  - destruct v; inversion Check; reflexivity.
Qed.

Lemma sg_lc_environment_nth : forall sigma, Forall lc_exp sigma ->
  forall i, lc_exp (nth i sigma e_null).
Proof.
  induction 1; intros [|i]; simpl; auto using lec_e_null.
Qed.

Lemma sg_instantiate_open_lc : forall e k sigma a,
  Forall lc_exp sigma -> lc_exp a ->
  sg_data_instantiate k (a :: sigma) e =
    open_exp_wrt_exp_rec k a (sg_data_instantiate (S k) sigma e).
Proof.
  induction e; intros k sigma a Env Closed; simpl; try (f_equal; eauto).
  destruct (Nat.ltb n k) eqn:Less.
  - apply Nat.ltb_lt in Less.
    assert (Next : Nat.ltb n (S k) = true).
    { apply Nat.ltb_lt; lia. }
    rewrite Next; simpl; case_if; auto; subst; exfalso.
    exact (Nat.lt_irrefl _ Less).
  - apply Nat.ltb_ge in Less.
    destruct (Nat.eq_dec n k) as [Eq | Neq].
    + subst n.
      assert (Next : Nat.ltb k (S k) = true) by (apply Nat.ltb_lt; lia).
      rewrite Next, Nat.sub_diag; simpl; case_if; congruence.
    + assert (Next : Nat.ltb n (S k) = false).
      { apply Nat.ltb_ge; lia. }
      rewrite Next.
      assert (Index : n - k = S (n - S k)) by lia.
      rewrite Index; simpl.
      apply open_ee_rec_term; apply sg_lc_environment_nth; assumption.
Qed.

(* Structural well-formedness concerns original quotation, not evaluation.
   It excludes dangling captured values and malformed lambda quotations. *)
Inductive sg_ho_wf : sg_ho_value -> Prop :=
| sghw_int : forall n, sg_ho_wf (sgh_int n)
| sghw_unit : sg_ho_wf sgh_unit
| sghw_closure : forall A B body sigma,
    Forall sg_ho_wf sigma -> lc_exp (sg_ho_quote (sgh_closure A B body sigma)) ->
    sg_ho_wf (sgh_closure A B body sigma)
| sghw_boundary : forall A B f, sg_ho_wf f -> sg_ho_wf (sgh_boundary A B f).

Lemma sg_ho_wf_quote : forall v, sg_ho_wf v ->
  value (sg_ho_quote v) /\ findtype (sg_ho_quote v) (sg_ho_tag v).
Proof. induction 1; simpl in *; split; intuition eauto. Qed.

Lemma sg_ho_wf_closed : forall v, sg_ho_wf v -> lc_exp (sg_ho_quote v).
Proof.
  intros v H; destruct (sg_ho_wf_quote v H) as [V _].
  inversion V; subst; auto.
Qed.

Lemma sg_ho_environment_closed : forall sigma, Forall sg_ho_wf sigma ->
  Forall lc_exp (map sg_ho_quote sigma).
Proof. induction 1; simpl; constructor; auto using sg_ho_wf_closed. Qed.

Lemma sg_ho_check_wf : forall A v w, sg_ho_check A v = Some w ->
  sg_ho_wf v -> sg_ho_wf w.
Proof.
  induction A; intros v w Check WF; cbn [sg_ho_check] in Check.
  - inversion Check; subst; assumption.
  - destruct v; inversion Check; subst; assumption.
  - discriminate.
  - destruct (sg_ho_callable v); inversion Check; subst; constructor; assumption.
  - destruct (sg_ho_check A1 v) eqn:Left.
    + inversion Check; subst; eapply IHA1; eauto.
    + eapply IHA2; eauto.
  - destruct v; inversion Check; subst; assumption.
Qed.

Lemma sg_original_steps_function : forall f g a,
  sg_original_steps f g -> lc_exp a ->
  sg_original_steps (e_app f a) (e_app g a).
Proof. induction 1; eauto using sgos_refl, sgos_cons, step_appl. Qed.

Lemma sg_ho_quote_lookup : forall sigma i v,
  nth_error sigma i = Some v ->
  nth_error (map sg_ho_quote sigma) i = Some (sg_ho_quote v).
Proof.
  induction sigma as [|a sigma IH]; intros [|i] v H;
    simpl in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma sg_ho_wf_lookup : forall sigma, Forall sg_ho_wf sigma ->
  forall i v, nth_error sigma i = Some v -> sg_ho_wf v.
Proof.
  induction 1; intros [|i] v Lookup; simpl in Lookup; try discriminate.
  - inversion Lookup; subst; assumption.
  - eapply IHForall; eauto.
Qed.

Theorem sg_ho_original_simulation :
  (forall sigma e v, sg_ho_runs sigma e v ->
    Forall sg_ho_wf sigma -> forall G T,
    typing G (sg_data_instantiate 0 (map sg_ho_quote sigma) e) T ->
    sg_ho_wf v /\ sg_original_steps
      (sg_data_instantiate 0 (map sg_ho_quote sigma) e) (sg_ho_quote v)) /\
  (forall f a v, sg_ho_applies f a v ->
    sg_ho_wf f -> sg_ho_wf a -> forall G T,
    typing G (e_app (sg_ho_quote f) (sg_ho_quote a)) T ->
    sg_ho_wf v /\ sg_original_steps
      (e_app (sg_ho_quote f) (sg_ho_quote a)) (sg_ho_quote v)).
Proof.
  apply sg_ho_semantics_ind.
  - intros; split; constructor.
  - intros; split; constructor.
  - intros sigma i v Lookup Env G T Typed.
    split.
    + eapply sg_ho_wf_lookup; eauto.
    + rewrite (sg_data_instantiate_lookup _ _ _ (sg_ho_quote_lookup _ _ _ Lookup)).
      constructor.
  - intros sigma A B body Env G T Typed.
    split; [constructor; [assumption |] | constructor].
    exact (proj2 (typing_regular _ _ _ Typed)).
  - intros sigma f a vf va v F IHF A IHA Call IHC Env G T Typed.
    destruct (inv_app _ _ _ _ Typed) as [U [V [TF TA]]].
    destruct (IHF Env G (t_arrow U V) TF) as [WF SF].
    destruct (IHA Env G U TA) as [WA SA].
    pose proof (sg_original_steps_function _ _ _ SF
      (proj2 (typing_regular _ _ _ TA))) as FS.
    pose proof (sg_original_steps_argument _ _ _ SA
      (proj1 (sg_ho_wf_quote _ WF))) as AS.
    pose proof (sg_original_steps_trans _ _ _ FS AS) as Steps.
    destruct (IHC WF WA G T
      (sg_original_steps_preservation _ _ Steps G T Typed)) as [WV SV].
    split; [exact WV | eapply sg_original_steps_trans; eassumption].
  - intros sigma scr D l E r a checked v Scr IHS Sub Check Branch IHB Env G T Typed.
    destruct (inv_typeof _ _ _ _ _ _ _ Typed) as [U [TS Disj]].
    destruct (IHS Env G U TS) as [WA SA].
    pose proof (sg_original_steps_switch _ _ SA G T D _ E _ Typed) as Steps.
    pose proof (sg_original_steps_preservation _ _ Steps G T Typed) as Selected.
    assert (Choose : step (e_typeof (sg_ho_quote a) D
      (sg_data_instantiate 1 (map sg_ho_quote sigma) l) E
      (sg_data_instantiate 1 (map sg_ho_quote sigma) r))
      (sg_data_instantiate 0 (map sg_ho_quote (checked :: sigma)) l)).
    { simpl; rewrite (sg_ho_check_quote _ _ _ Check).
      rewrite sg_instantiate_open_lc; auto using sg_ho_environment_closed, sg_ho_wf_closed.
      eapply step_typeofl with (C := sg_ho_tag a).
      - exact (proj2 (typing_regular _ _ _ Selected)).
      - exact (proj1 (sg_ho_wf_quote _ WA)).
      - exact (proj2 (sg_ho_wf_quote _ WA)).
      - exact Sub. }
    destruct (IHB (Forall_cons checked (sg_ho_check_wf _ _ _ Check WA) Env)
      G T (preservation _ _ _ _ Selected Choose)) as [WV SV].
    split; [exact WV | eapply sg_original_steps_trans; [exact Steps |]].
    eapply sgos_cons; eassumption.
  - intros sigma scr D l E r a checked v Scr IHS Miss Sub Check Branch IHB Env G T Typed.
    destruct (inv_typeof _ _ _ _ _ _ _ Typed) as [U [TS Disj]].
    destruct (IHS Env G U TS) as [WA SA].
    pose proof (sg_original_steps_switch _ _ SA G T D _ E _ Typed) as Steps.
    pose proof (sg_original_steps_preservation _ _ Steps G T Typed) as Selected.
    assert (Choose : step (e_typeof (sg_ho_quote a) D
      (sg_data_instantiate 1 (map sg_ho_quote sigma) l) E
      (sg_data_instantiate 1 (map sg_ho_quote sigma) r))
      (sg_data_instantiate 0 (map sg_ho_quote (checked :: sigma)) r)).
    { simpl; rewrite (sg_ho_check_quote _ _ _ Check).
      rewrite sg_instantiate_open_lc; auto using sg_ho_environment_closed, sg_ho_wf_closed.
      eapply step_typeofr with (C := sg_ho_tag a).
      - exact (proj2 (typing_regular _ _ _ Selected)).
      - exact (proj1 (sg_ho_wf_quote _ WA)).
      - exact (proj2 (sg_ho_wf_quote _ WA)).
      - exact Sub. }
    destruct (IHB (Forall_cons checked (sg_ho_check_wf _ _ _ Check WA) Env)
      G T (preservation _ _ _ _ Selected Choose)) as [WV SV].
    split; [exact WV | eapply sg_original_steps_trans; [exact Steps |]].
    eapply sgos_cons; eassumption.
  - intros A B body sigma a checked raw v SubA CheckA Body IHB SubB CheckB
      WF WA G T Typed.
    inversion WF; subst.
    assert (Beta : step (e_app (sg_ho_quote (sgh_closure A B body sigma)) (sg_ho_quote a))
      (sg_data_instantiate 0 (map sg_ho_quote (checked :: sigma)) body)).
    { simpl; rewrite (sg_ho_check_quote _ _ _ CheckA).
      rewrite sg_instantiate_open_lc; auto using sg_ho_environment_closed, sg_ho_wf_closed.
      apply step_beta; [assumption | exact (proj1 (sg_ho_wf_quote _ WA))]. }
    destruct (IHB ltac:(constructor; eauto using sg_ho_check_wf) G T
      (preservation _ _ _ _ Typed Beta)) as [WR SR].
    split; [eapply sg_ho_check_wf; eauto |].
    rewrite (sg_ho_check_quote _ _ _ CheckB); eapply sgos_cons; eassumption.
  - intros A B f a checked raw v SubA CheckA Call IHC SubB CheckB
      WF WA G T Typed.
    inversion WF; subst.
    assert (TC : typing G (e_app (sg_ho_quote f) (sg_ho_quote checked)) T).
    { rewrite (sg_ho_check_quote _ _ _ CheckA); exact Typed. }
    destruct (IHC ltac:(assumption) (sg_ho_check_wf _ _ _ CheckA WA) G T TC)
      as [WR SR].
    split; [eapply sg_ho_check_wf; eauto |].
    cbn [sg_ho_quote]; rewrite (sg_ho_check_quote _ _ _ CheckB).
    rewrite (sg_ho_check_quote _ _ _ CheckA) in SR; exact SR.
Qed.

Corollary sg_ho_compile_original_correspondence : forall sigma e v G T,
  sg_ho_runs sigma e v -> Forall sg_ho_wf sigma ->
  typing G (sg_data_instantiate 0 (map sg_ho_quote sigma) e) T ->
  sg_original_steps (sg_data_instantiate 0 (map sg_ho_quote sigma) e)
    (sg_ho_quote v) /\
  sg_runs (sg_evaluate (map sg_ho_encode sigma) (sg_data_compile e))
    (sg_done (sg_ho_encode v)).
Proof.
  intros sigma e v G T Run Env Typed; split.
  - exact (proj2 (proj1 sg_ho_original_simulation sigma e v Run Env G T Typed)).
  - apply sg_ho_compile_operational; exact Run.
Qed.













