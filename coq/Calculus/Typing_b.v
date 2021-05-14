Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntaxb_ott
               rulesb_inf
               Infrastructure
               Infrastructure_b.

Require Import List. Import ListNotations.
Require Import Strings.String.


(* Common Lemmas *)
Lemma Btyping_regular_1 : forall e G A,
    Btyping G e A -> lc_term e.
Proof.
  intros e G A H.
  induction H;
    eauto.
Qed.

Lemma Btyping_regular_2 : forall G e T,
    Btyping G e T -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.


Lemma Btyping_weaken : forall G E F e T,
    Btyping (E ++ G) e T ->
    uniq (E ++ F ++ G) ->
    Btyping (E ++ F ++ G) e T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply Btyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma Btyping_weakening : forall (E F : ctx) e T,
    Btyping E e T ->
    uniq (F ++ E) ->
    Btyping (F ++ E) e T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Btyping_weaken.
Qed.


(** Typing is preserved by substitution. *)

Lemma fvb_in_dom: forall G t T,
    Btyping G t T -> fv_term t [<=] dom G.
Proof.
  intros G t T H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_term (open_term_wrt_term t (trm_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_term t [<=] fv_term (open_term_wrt_term t (trm_var_f x))) by
        eapply fv_term_open_term_wrt_term_lower.
    fsetdec.
Qed.

Lemma valueb_no_fv : forall v T,
    Btyping [] v T -> fv_term v [<=] empty.
Proof.
  intro v.
  pose proof (fvb_in_dom [] v).
  intuition eauto.
Qed.

Lemma substb_value : forall v T z u,
    Btyping [] v T -> subst_term u z v = v.
Proof.
  intros v T z u Typ.
  lets* Fv: valueb_no_fv Typ.
  forwards*: subst_term_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma Btyping_subst_1 : forall (E F : ctx) e u S T (z : atom),
    Btyping (F ++ [(z,S)] ++ E) e T ->
    Btyping E u S ->
    Btyping (F ++ E) ([z ~> u]' e) T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : Btyping_regular_1 H0;
    lets Uni : Btyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ Btyping_weakening.
    solve_uniq.
  -
    pick fresh x and apply Btyp_abs; eauto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.

Lemma Btyping_c_subst_simpl : forall E e u S T z,
  Btyping ([(z,S)] ++ E) e T ->
  Btyping E u S ->
  Btyping E ([z ~> u]' e) T.
Proof.
  intros E e u S T z H1 H2.
  rewrite_env (nil ++ E).
  eapply Btyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.

