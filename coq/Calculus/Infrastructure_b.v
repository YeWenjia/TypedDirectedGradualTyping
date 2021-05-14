Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntaxb_ott
               rulesb_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.

Notation "Γ ⊢ E A" := (Btyping Γ E A) (at level 45).
Notation "[ z ~> u ]' t" := (subst_term u z t) (at level 0).
Notation "t ^^' u"       := (open_term_wrt_term t u) (at level 67).

Notation "t ->* r" := (bsteps t r) (at level 68).


Lemma star_one:
forall a b, bstep a (t_term b) -> bsteps a (t_term b).
Proof.
eauto using bsteps.
Qed.

Lemma star_trans:
forall a b, bsteps a (t_term b) -> forall c, bsteps b (t_term c) -> bsteps a (t_term c).
Proof.
  introv H.
  inductions H; eauto using bsteps.
Qed.


Hint Resolve star_one star_trans : core.

Lemma valueb_lc : forall v,
    valueb v -> lc_term v.
Proof.
  intros v H.
  induction* H. 
Qed.


Lemma multi_red_app : forall v t t',
    valueb v -> t ->* (t_term t') -> (trm_app v t) ->* (t_term (trm_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: do_stepb H1 H.
Qed.

Lemma multi_blame_app : forall v t,
    valueb v -> t ->* (t_blame) -> (trm_app v t) ->* (t_blame).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: do_stepb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: blame_stepb H0 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_term t2 -> t1 ->* (t_term t1') -> (trm_app t1 t2) ->* (t_term (trm_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: do_stepb H0 H.
Qed.


Lemma multi_blame_app2 : forall t1 t2 ,
    lc_term t2 -> t1 ->* t_blame -> (trm_app t1 t2) ->* t_blame.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: do_stepb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: blame_stepb H0 H.
Qed.

Lemma multi_red_cast : forall t t' A B,
    t ->* (t_term t') -> (trm_cast t A B) ->* (t_term (trm_cast t' A B)).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformedb (castCtxb A B)). eauto.
  forwards*: do_stepb H0 H.
Qed.

Lemma multi_blame_cast : forall t A B,
    t ->* t_blame -> (trm_cast t A B) ->* t_blame.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (castCtxb A B)). eauto.
  forwards*: do_stepb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (castCtxb A B)). eauto.
  forwards*: blame_stepb H0 H.
Qed.

