Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               rulesb_inf
               Typing_b
               Infrastructure_b
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.


Lemma lc_lcb: forall E e t dir A,
 ttyping E e dir A t ->
 lc_exp e ->
 lc_term t.
Proof.
  introv typ H. 
  inductions typ; eauto. 
  -
    inverts H1. 
    pick fresh x.
    forwards*: H.
  - inverts* H.
  - inverts* H.
Qed.



(* Common Lemmas *)
Lemma ttyping_regular_1 : forall e G dir A t,
    ttyping G e dir A t -> lc_exp e.
Proof.
  intros e G dir A t H.
  induction H;
    eauto.
Qed.

Lemma ttyping_regular_2 : forall G e dir T t,
    ttyping G e dir T t -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.


Lemma ttyping_weaken : forall G E F e dir T t,
    ttyping (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    ttyping (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply ttyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma ttyping_weakening : forall (E F : ctx) e dir T t,
    ttyping E e dir T t ->
    uniq (F ++ E) ->
    ttyping (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ ttyping_weaken.
Qed.


(** Typing is preserved by substitution. *)

Lemma ttfv_in_dom: forall G e dir T t,
    ttyping G e dir T t -> fv_exp e [<=] dom G.
Proof.
  intros G e dir T t H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (open_exp_wrt_exp e (e_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (open_exp_wrt_exp e (e_var_f x))) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma ttvalue_no_fv : forall v dir T t,
    ttyping [] v dir T t -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_dom [] v).
  intuition eauto.
Qed.

Lemma ttsubst_value : forall v dir T t z u,
    ttyping [] v dir T t -> subst_exp u z v = v.
Proof.
  intros v dir T t z u Typ.
  lets* Fv: ttvalue_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma ttyping_subst_1 : forall (E F : ctx) e u uu dir S T (z : atom) t,
    ttyping (F ++ [(z,S)] ++ E) e dir T t ->
    ttyping E u Inf S uu ->
    ttyping (F ++ E) ([z ~> u] e) dir T ([z ~> uu]' t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ ttyping_weakening.
    solve_uniq.
  -
    pick fresh x and apply ttyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
    forwards*: lc_lcb H0.
Qed.

Lemma ttyping_c_subst_simpl : forall E e u uu t dir S T z,
  ttyping ([(z,S)] ++ E) e dir T t ->
  ttyping E u Inf S uu ->
  ttyping E ([z ~> u] e) dir T ([z ~> uu]' t).
Proof.
  intros E e u uu t dir S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply ttyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.


Lemma ttinference_unique : forall G e t A1 A2,
    ttyping G e Inf A1 t ->
    ttyping G e Inf A2 t->
    A1 = A2.
Proof.
  introv Ty1.
  gen A2.
  inductions Ty1; introv Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H.
Qed.

Lemma elaboration_soundness : forall G e t dir A,
    ttyping G e dir A t ->
    Btyping G t A.
Proof.
  introv Ty1.
  inductions Ty1; intros; eauto.
Qed.