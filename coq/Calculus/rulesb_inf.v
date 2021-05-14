Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntaxb_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme term_ind' := Induction for term Sort Prop.

Definition term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme term_rec' := Induction for term Sort Set.

Definition term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  term_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_term_wrt_term_rec (n1 : nat) (x1 : var) (t1 : term) {struct t1} : term :=
  match t1 with
    | trm_var_f x2 => if (x1 == x2) then (trm_var_b n1) else (trm_var_f x2)
    | trm_var_b n2 => if (lt_ge_dec n2 n1) then (trm_var_b n2) else (trm_var_b (S n2))
    | trm_lit i1 => trm_lit i1
    | trm_abs A1 t2 => trm_abs A1 (close_term_wrt_term_rec (S n1) x1 t2)
    | trm_app t2 t3 => trm_app (close_term_wrt_term_rec n1 x1 t2) (close_term_wrt_term_rec n1 x1 t3)
    | trm_cast t2 A1 B1 => trm_cast (close_term_wrt_term_rec n1 x1 t2) A1 B1
    | trm_add => trm_add
    | trm_addl i1 => trm_addl i1
  end.

Definition close_term_wrt_term x1 t1 := close_term_wrt_term_rec 0 x1 t1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_dyn => 1
  end.

Fixpoint size_term (t1 : term) {struct t1} : nat :=
  match t1 with
    | trm_var_f x1 => 1
    | trm_var_b n1 => 1
    | trm_lit i1 => 1
    | trm_abs A1 t2 => 1 + (size_typ A1) + (size_term t2)
    | trm_app t2 t3 => 1 + (size_term t2) + (size_term t3)
    | trm_cast t2 A1 B1 => 1 + (size_term t2) + (size_typ A1) + (size_typ B1)
    | trm_add => 1
    | trm_addl i1 => 1
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_term_wrt_term : nat -> term -> Prop :=
  | degree_wrt_term_trm_var_f : forall n1 x1,
    degree_term_wrt_term n1 (trm_var_f x1)
  | degree_wrt_term_trm_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_term_wrt_term n1 (trm_var_b n2)
  | degree_wrt_term_trm_lit : forall n1 i1,
    degree_term_wrt_term n1 (trm_lit i1)
  | degree_wrt_term_trm_abs : forall n1 A1 t1,
    degree_term_wrt_term (S n1) t1 ->
    degree_term_wrt_term n1 (trm_abs A1 t1)
  | degree_wrt_term_trm_app : forall n1 t1 t2,
    degree_term_wrt_term n1 t1 ->
    degree_term_wrt_term n1 t2 ->
    degree_term_wrt_term n1 (trm_app t1 t2)
  | degree_wrt_term_trm_cast : forall n1 t1 A1 B1,
    degree_term_wrt_term n1 t1 ->
    degree_term_wrt_term n1 (trm_cast t1 A1 B1)
  | degree_wrt_term_trm_add : forall n1,
    degree_term_wrt_term n1 (trm_add)
  | degree_wrt_term_trm_addl : forall n1 i1,
    degree_term_wrt_term n1 (trm_addl i1).

Scheme degree_term_wrt_term_ind' := Induction for degree_term_wrt_term Sort Prop.

Definition degree_term_wrt_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_term_wrt_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_term_wrt_term : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_term : term -> Set :=
  | lc_set_trm_var_f : forall x1,
    lc_set_term (trm_var_f x1)
  | lc_set_trm_lit : forall i1,
    lc_set_term (trm_lit i1)
  | lc_set_trm_abs : forall A1 t1,
    (forall x1 : var, lc_set_term (open_term_wrt_term t1 (trm_var_f x1))) ->
    lc_set_term (trm_abs A1 t1)
  | lc_set_trm_app : forall t1 t2,
    lc_set_term t1 ->
    lc_set_term t2 ->
    lc_set_term (trm_app t1 t2)
  | lc_set_trm_cast : forall t1 A1 B1,
    lc_set_term t1 ->
    lc_set_term (trm_cast t1 A1 B1)
  | lc_set_trm_add :
    lc_set_term (trm_add)
  | lc_set_trm_addl : forall i1,
    lc_set_term (trm_addl i1).

Scheme lc_term_ind' := Induction for lc_term Sort Prop.

Definition lc_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_term_ind' := Induction for lc_set_term Sort Prop.

Definition lc_set_term_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_term_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme lc_set_term_rec' := Induction for lc_set_term Sort Set.

Definition lc_set_term_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_set_term_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors lc_term : core lngen.

Hint Constructors lc_set_term : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_term_wrt_term t1 := forall x1, lc_term (open_term_wrt_term t1 (trm_var_f x1)).

Hint Unfold body_term_wrt_term : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_term_min_mutual :
(forall t1, 1 <= size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_term_min :
forall t1, 1 <= size_term t1.
Proof.
pose proof size_term_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_min : lngen.

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 t1) = size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_close_term_wrt_term_rec :
forall t1 x1 n1,
  size_term (close_term_wrt_term_rec n1 x1 t1) = size_term t1.
Proof.
pose proof size_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_close_term_wrt_term_rec : lngen.
Hint Rewrite size_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_term_close_term_wrt_term :
forall t1 x1,
  size_term (close_term_wrt_term x1 t1) = size_term t1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_close_term_wrt_term : lngen.
Hint Rewrite size_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_mutual :
(forall t1 t2 n1,
  size_term t1 <= size_term (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec :
forall t1 t2 n1,
  size_term t1 <= size_term (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof size_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma size_term_open_term_wrt_term :
forall t1 t2,
  size_term t1 <= size_term (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term : lngen.

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var_mutual :
(forall t1 x1 n1,
  size_term (open_term_wrt_term_rec n1 (trm_var_f x1) t1) = size_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_term_open_term_wrt_term_rec_var :
forall t1 x1 n1,
  size_term (open_term_wrt_term_rec n1 (trm_var_f x1) t1) = size_term t1.
Proof.
pose proof size_term_open_term_wrt_term_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_term_open_term_wrt_term_rec_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_term_open_term_wrt_term_var :
forall t1 x1,
  size_term (open_term_wrt_term t1 (trm_var_f x1)) = size_term t1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve size_term_open_term_wrt_term_var : lngen.
Hint Rewrite size_term_open_term_wrt_term_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_term_wrt_term_S_mutual :
(forall n1 t1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term (S n1) t1).
Proof.
apply_mutual_ind degree_term_wrt_term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_S :
forall n1 t1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term (S n1) t1.
Proof.
pose proof degree_term_wrt_term_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_S : lngen.

Lemma degree_term_wrt_term_O :
forall n1 t1,
  degree_term_wrt_term O t1 ->
  degree_term_wrt_term n1 t1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_O : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec :
forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 t1).
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_term_rec : lngen.

(* end hide *)

Lemma degree_term_wrt_term_close_term_wrt_term :
forall t1 x1,
  degree_term_wrt_term 0 t1 ->
  degree_term_wrt_term 1 (close_term_wrt_term x1 t1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_close_term_wrt_term : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual :
(forall t1 x1 n1,
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 t1) ->
  degree_term_wrt_term n1 t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_rec_inv :
forall t1 x1 n1,
  degree_term_wrt_term (S n1) (close_term_wrt_term_rec n1 x1 t1) ->
  degree_term_wrt_term n1 t1.
Proof.
pose proof degree_term_wrt_term_close_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_rec_inv : lngen.

(* end hide *)

Lemma degree_term_wrt_term_close_term_wrt_term_inv :
forall t1 x1,
  degree_term_wrt_term 1 (close_term_wrt_term x1 t1) ->
  degree_term_wrt_term 0 t1.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_close_term_wrt_term_inv : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_mutual :
(forall t1 t2 n1,
  degree_term_wrt_term (S n1) t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec :
forall t1 t2 n1,
  degree_term_wrt_term (S n1) t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma degree_term_wrt_term_open_term_wrt_term :
forall t1 t2,
  degree_term_wrt_term 1 t1 ->
  degree_term_wrt_term 0 t2 ->
  degree_term_wrt_term 0 (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve degree_term_wrt_term_open_term_wrt_term : lngen.

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual :
(forall t1 t2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1) ->
  degree_term_wrt_term (S n1) t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_rec_inv :
forall t1 t2 n1,
  degree_term_wrt_term n1 (open_term_wrt_term_rec n1 t2 t1) ->
  degree_term_wrt_term (S n1) t1.
Proof.
pose proof degree_term_wrt_term_open_term_wrt_term_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_rec_inv : lngen.

(* end hide *)

Lemma degree_term_wrt_term_open_term_wrt_term_inv :
forall t1 t2,
  degree_term_wrt_term 0 (open_term_wrt_term t1 t2) ->
  degree_term_wrt_term 1 t1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate degree_term_wrt_term_open_term_wrt_term_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_term_wrt_term_rec_inj_mutual :
(forall t1 t2 x1 n1,
  close_term_wrt_term_rec n1 x1 t1 = close_term_wrt_term_rec n1 x1 t2 ->
  t1 = t2).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_inj :
forall t1 t2 x1 n1,
  close_term_wrt_term_rec n1 x1 t1 = close_term_wrt_term_rec n1 x1 t2 ->
  t1 = t2.
Proof.
pose proof close_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_term_wrt_term_rec_inj : lngen.

(* end hide *)

Lemma close_term_wrt_term_inj :
forall t1 t2 x1,
  close_term_wrt_term x1 t1 = close_term_wrt_term x1 t2 ->
  t1 = t2.
Proof.
unfold close_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate close_term_wrt_term_inj : lngen.

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (trm_var_f x1) t1) = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_open_term_wrt_term_rec :
forall t1 x1 n1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 (open_term_wrt_term_rec n1 (trm_var_f x1) t1) = t1.
Proof.
pose proof close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.
Hint Rewrite close_term_wrt_term_rec_open_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_term_wrt_term_open_term_wrt_term :
forall t1 x1,
  x1 `notin` fv_term t1 ->
  close_term_wrt_term x1 (open_term_wrt_term t1 (trm_var_f x1)) = t1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_open_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_open_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  open_term_wrt_term_rec n1 (trm_var_f x1) (close_term_wrt_term_rec n1 x1 t1) = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_close_term_wrt_term_rec :
forall t1 x1 n1,
  open_term_wrt_term_rec n1 (trm_var_f x1) (close_term_wrt_term_rec n1 x1 t1) = t1.
Proof.
pose proof open_term_wrt_term_rec_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_close_term_wrt_term_rec : lngen.
Hint Rewrite open_term_wrt_term_rec_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_term_wrt_term_close_term_wrt_term :
forall t1 x1,
  open_term_wrt_term (close_term_wrt_term x1 t1) (trm_var_f x1) = t1.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_close_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_inj_mutual :
(forall t2 t1 x1 n1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 (trm_var_f x1) t2 = open_term_wrt_term_rec n1 (trm_var_f x1) t1 ->
  t2 = t1).
Proof.
apply_mutual_ind term_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_inj :
forall t2 t1 x1 n1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 (trm_var_f x1) t2 = open_term_wrt_term_rec n1 (trm_var_f x1) t1 ->
  t2 = t1.
Proof.
pose proof open_term_wrt_term_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_term_wrt_term_rec_inj : lngen.

(* end hide *)

Lemma open_term_wrt_term_inj :
forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  open_term_wrt_term t2 (trm_var_f x1) = open_term_wrt_term t1 (trm_var_f x1) ->
  t2 = t1.
Proof.
unfold open_term_wrt_term; eauto with lngen.
Qed.

Hint Immediate open_term_wrt_term_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_term_wrt_term_of_lc_term_mutual :
(forall t1,
  lc_term t1 ->
  degree_term_wrt_term 0 t1).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_term_wrt_term_of_lc_term :
forall t1,
  lc_term t1 ->
  degree_term_wrt_term 0 t1.
Proof.
pose proof degree_term_wrt_term_of_lc_term_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_term_wrt_term_of_lc_term : lngen.

(* begin hide *)

Lemma lc_term_of_degree_size_mutual :
forall i1,
(forall t1,
  size_term t1 = i1 ->
  degree_term_wrt_term 0 t1 ->
  lc_term t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_degree :
forall t1,
  degree_term_wrt_term 0 t1 ->
  lc_term t1.
Proof.
intros t1; intros;
pose proof (lc_term_of_degree_size_mutual (size_term t1));
intuition eauto.
Qed.

Hint Resolve lc_term_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac term_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_term_wrt_term_of_lc_term in J1; clear H
          end).

Lemma lc_trm_abs_exists :
forall x1 A1 t1,
  lc_term (open_term_wrt_term t1 (trm_var_f x1)) ->
  lc_term (trm_abs A1 t1).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_term (trm_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_trm_abs_exists x1) : core.

Lemma lc_body_term_wrt_term :
forall t1 t2,
  body_term_wrt_term t1 ->
  lc_term t2 ->
  lc_term (open_term_wrt_term t1 t2).
Proof.
unfold body_term_wrt_term;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
term_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_term_wrt_term : lngen.

Lemma lc_body_trm_abs_2 :
forall A1 t1,
  lc_term (trm_abs A1 t1) ->
  body_term_wrt_term t1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_trm_abs_2 : lngen.

(* begin hide *)

Lemma lc_term_unique_mutual :
(forall t1 (proof2 proof3 : lc_term t1), proof2 = proof3).
Proof.
apply_mutual_ind lc_term_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_term_unique :
forall t1 (proof2 proof3 : lc_term t1), proof2 = proof3.
Proof.
pose proof lc_term_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_unique : lngen.

(* begin hide *)

Lemma lc_term_of_lc_set_term_mutual :
(forall t1, lc_set_term t1 -> lc_term t1).
Proof.
apply_mutual_ind lc_set_term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_term_of_lc_set_term :
forall t1, lc_set_term t1 -> lc_term t1.
Proof.
pose proof lc_term_of_lc_set_term_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_term_of_lc_set_term : lngen.

(* begin hide *)

Lemma lc_set_term_of_lc_term_size_mutual :
forall i1,
(forall t1,
  size_term t1 = i1 ->
  lc_term t1 ->
  lc_set_term t1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind term_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_term_of_lc_term];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_term_of_lc_term :
forall t1,
  lc_term t1 ->
  lc_set_term t1.
Proof.
intros t1; intros;
pose proof (lc_set_term_of_lc_term_size_mutual (size_term t1));
intuition eauto.
Qed.

Hint Resolve lc_set_term_of_lc_term : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 t1 = t1).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_term_wrt_term_rec_degree_term_wrt_term :
forall t1 x1 n1,
  degree_term_wrt_term n1 t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term_rec n1 x1 t1 = t1.
Proof.
pose proof close_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve close_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite close_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

Lemma close_term_wrt_term_lc_term :
forall t1 x1,
  lc_term t1 ->
  x1 `notin` fv_term t1 ->
  close_term_wrt_term x1 t1 = t1.
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve close_term_wrt_term_lc_term : lngen.
Hint Rewrite close_term_wrt_term_lc_term using solve [auto] : lngen.

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term_mutual :
(forall t2 t1 n1,
  degree_term_wrt_term n1 t2 ->
  open_term_wrt_term_rec n1 t1 t2 = t2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_term_wrt_term_rec_degree_term_wrt_term :
forall t2 t1 n1,
  degree_term_wrt_term n1 t2 ->
  open_term_wrt_term_rec n1 t1 t2 = t2.
Proof.
pose proof open_term_wrt_term_rec_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve open_term_wrt_term_rec_degree_term_wrt_term : lngen.
Hint Rewrite open_term_wrt_term_rec_degree_term_wrt_term using solve [auto] : lngen.

(* end hide *)

Lemma open_term_wrt_term_lc_term :
forall t2 t1,
  lc_term t2 ->
  open_term_wrt_term t2 t1 = t2.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve open_term_wrt_term_lc_term : lngen.
Hint Rewrite open_term_wrt_term_lc_term using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec_mutual :
(forall t1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 t1) [=] remove x1 (fv_term t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_close_term_wrt_term_rec :
forall t1 x1 n1,
  fv_term (close_term_wrt_term_rec n1 x1 t1) [=] remove x1 (fv_term t1).
Proof.
pose proof fv_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_close_term_wrt_term_rec : lngen.
Hint Rewrite fv_term_close_term_wrt_term_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_term_close_term_wrt_term :
forall t1 x1,
  fv_term (close_term_wrt_term x1 t1) [=] remove x1 (fv_term t1).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_close_term_wrt_term : lngen.
Hint Rewrite fv_term_close_term_wrt_term using solve [auto] : lngen.

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower_mutual :
(forall t1 t2 n1,
  fv_term t1 [<=] fv_term (open_term_wrt_term_rec n1 t2 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_lower :
forall t1 t2 n1,
  fv_term t1 [<=] fv_term (open_term_wrt_term_rec n1 t2 t1).
Proof.
pose proof fv_term_open_term_wrt_term_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_lower : lngen.

(* end hide *)

Lemma fv_term_open_term_wrt_term_lower :
forall t1 t2,
  fv_term t1 [<=] fv_term (open_term_wrt_term t1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_lower : lngen.

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper_mutual :
(forall t1 t2 n1,
  fv_term (open_term_wrt_term_rec n1 t2 t1) [<=] fv_term t2 `union` fv_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_term_open_term_wrt_term_rec_upper :
forall t1 t2 n1,
  fv_term (open_term_wrt_term_rec n1 t2 t1) [<=] fv_term t2 `union` fv_term t1.
Proof.
pose proof fv_term_open_term_wrt_term_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_open_term_wrt_term_rec_upper : lngen.

(* end hide *)

Lemma fv_term_open_term_wrt_term_upper :
forall t1 t2,
  fv_term (open_term_wrt_term t1 t2) [<=] fv_term t2 `union` fv_term t1.
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve fv_term_open_term_wrt_term_upper : lngen.

(* begin hide *)

Lemma fv_term_subst_term_fresh_mutual :
(forall t1 t2 x1,
  x1 `notin` fv_term t1 ->
  fv_term (subst_term t2 x1 t1) [=] fv_term t1).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_fresh :
forall t1 t2 x1,
  x1 `notin` fv_term t1 ->
  fv_term (subst_term t2 x1 t1) [=] fv_term t1.
Proof.
pose proof fv_term_subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_fresh : lngen.
Hint Rewrite fv_term_subst_term_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_term_subst_term_lower_mutual :
(forall t1 t2 x1,
  remove x1 (fv_term t1) [<=] fv_term (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_lower :
forall t1 t2 x1,
  remove x1 (fv_term t1) [<=] fv_term (subst_term t2 x1 t1).
Proof.
pose proof fv_term_subst_term_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_lower : lngen.

(* begin hide *)

Lemma fv_term_subst_term_notin_mutual :
(forall t1 t2 x1 x2,
  x2 `notin` fv_term t1 ->
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_notin :
forall t1 t2 x1 x2,
  x2 `notin` fv_term t1 ->
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term (subst_term t2 x1 t1).
Proof.
pose proof fv_term_subst_term_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_notin : lngen.

(* begin hide *)

Lemma fv_term_subst_term_upper_mutual :
(forall t1 t2 x1,
  fv_term (subst_term t2 x1 t1) [<=] fv_term t2 `union` remove x1 (fv_term t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_term_subst_term_upper :
forall t1 t2 x1,
  fv_term (subst_term t2 x1 t1) [<=] fv_term t2 `union` remove x1 (fv_term t1).
Proof.
pose proof fv_term_subst_term_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_term_subst_term_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_mutual :
(forall t2 t1 x1 x2 n1,
  degree_term_wrt_term n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term_rec n1 x2 t2) = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_close_term_wrt_term_rec :
forall t2 t1 x1 x2 n1,
  degree_term_wrt_term n1 t1 ->
  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term_rec n1 x2 t2) = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 t2).
Proof.
pose proof subst_term_close_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec : lngen.

Lemma subst_term_close_term_wrt_term :
forall t2 t1 x1 x2,
  lc_term t1 ->  x1 <> x2 ->
  x2 `notin` fv_term t1 ->
  subst_term t1 x1 (close_term_wrt_term x2 t2) = close_term_wrt_term x2 (subst_term t1 x1 t2).
Proof.
unfold close_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term : lngen.

(* begin hide *)

Lemma subst_term_degree_term_wrt_term_mutual :
(forall t1 t2 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_degree_term_wrt_term :
forall t1 t2 x1 n1,
  degree_term_wrt_term n1 t1 ->
  degree_term_wrt_term n1 t2 ->
  degree_term_wrt_term n1 (subst_term t2 x1 t1).
Proof.
pose proof subst_term_degree_term_wrt_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_degree_term_wrt_term : lngen.

(* begin hide *)

Lemma subst_term_fresh_eq_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  subst_term t1 x1 t2 = t2).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_eq :
forall t2 t1 x1,
  x1 `notin` fv_term t2 ->
  subst_term t1 x1 t2 = t2.
Proof.
pose proof subst_term_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_eq : lngen.
Hint Rewrite subst_term_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_term_fresh_same_mutual :
(forall t2 t1 x1,
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x1 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh_same :
forall t2 t1 x1,
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x1 t2).
Proof.
pose proof subst_term_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh_same : lngen.

(* begin hide *)

Lemma subst_term_fresh_mutual :
(forall t2 t1 x1 x2,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x2 t2)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_fresh :
forall t2 t1 x1 x2,
  x1 `notin` fv_term t2 ->
  x1 `notin` fv_term t1 ->
  x1 `notin` fv_term (subst_term t1 x2 t2).
Proof.
pose proof subst_term_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_fresh : lngen.

Lemma subst_term_lc_term :
forall t1 t2 x1,
  lc_term t1 ->
  lc_term t2 ->
  lc_term (subst_term t2 x1 t1).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_lc_term : lngen.

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term_rec n1 t2 t3) = open_term_wrt_term_rec n1 (subst_term t1 x1 t2) (subst_term t1 x1 t3)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_open_term_wrt_term_rec :
forall t3 t1 t2 x1 n1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term_rec n1 t2 t3) = open_term_wrt_term_rec n1 (subst_term t1 x1 t2) (subst_term t1 x1 t3).
Proof.
pose proof subst_term_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma subst_term_open_term_wrt_term :
forall t3 t1 t2 x1,
  lc_term t1 ->
  subst_term t1 x1 (open_term_wrt_term t3 t2) = open_term_wrt_term (subst_term t1 x1 t3) (subst_term t1 x1 t2).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term : lngen.

Lemma subst_term_open_term_wrt_term_var :
forall t2 t1 x1 x2,
  x1 <> x2 ->
  lc_term t1 ->
  open_term_wrt_term (subst_term t1 x1 t2) (trm_var_f x2) = subst_term t1 x1 (open_term_wrt_term t2 (trm_var_f x2)).
Proof.
intros; rewrite subst_term_open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_open_term_wrt_term_var : lngen.

(* begin hide *)

Lemma subst_term_spec_rec_mutual :
(forall t1 t2 x1 n1,
  subst_term t2 x1 t1 = open_term_wrt_term_rec n1 t2 (close_term_wrt_term_rec n1 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_spec_rec :
forall t1 t2 x1 n1,
  subst_term t2 x1 t1 = open_term_wrt_term_rec n1 t2 (close_term_wrt_term_rec n1 x1 t1).
Proof.
pose proof subst_term_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_spec_rec : lngen.

(* end hide *)

Lemma subst_term_spec :
forall t1 t2 x1,
  subst_term t2 x1 t1 = open_term_wrt_term (close_term_wrt_term x1 t1) t2.
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_spec : lngen.

(* begin hide *)

Lemma subst_term_subst_term_mutual :
(forall t1 t2 t3 x2 x1,
  x2 `notin` fv_term t2 ->
  x2 <> x1 ->
  subst_term t2 x1 (subst_term t3 x2 t1) = subst_term (subst_term t2 x1 t3) x2 (subst_term t2 x1 t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_subst_term :
forall t1 t2 t3 x2 x1,
  x2 `notin` fv_term t2 ->
  x2 <> x1 ->
  subst_term t2 x1 (subst_term t3 x2 t1) = subst_term (subst_term t2 x1 t3) x2 (subst_term t2 x1 t1).
Proof.
pose proof subst_term_subst_term_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_subst_term : lngen.

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual :
(forall t2 t1 x1 x2 n1,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 (open_term_wrt_term_rec n1 (trm_var_f x2) t2))).
Proof.
apply_mutual_ind term_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec :
forall t2 t1 x1 x2 n1,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  degree_term_wrt_term n1 t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term_rec n1 x2 (subst_term t1 x1 (open_term_wrt_term_rec n1 (trm_var_f x2) t2)).
Proof.
pose proof subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_close_term_wrt_term_rec_open_term_wrt_term_rec : lngen.

(* end hide *)

Lemma subst_term_close_term_wrt_term_open_term_wrt_term :
forall t2 t1 x1 x2,
  x2 `notin` fv_term t2 ->
  x2 `notin` fv_term t1 ->
  x2 <> x1 ->
  lc_term t1 ->
  subst_term t1 x1 t2 = close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term t2 (trm_var_f x2))).
Proof.
unfold close_term_wrt_term; unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_close_term_wrt_term_open_term_wrt_term : lngen.

Lemma subst_term_trm_abs :
forall x2 A1 t2 t1 x1,
  lc_term t1 ->
  x2 `notin` fv_term t1 `union` fv_term t2 `union` singleton x1 ->
  subst_term t1 x1 (trm_abs A1 t2) = trm_abs (A1) (close_term_wrt_term x2 (subst_term t1 x1 (open_term_wrt_term t2 (trm_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_term_trm_abs : lngen.

(* begin hide *)

Lemma subst_term_intro_rec_mutual :
(forall t1 x1 t2 n1,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 t2 t1 = subst_term t2 x1 (open_term_wrt_term_rec n1 (trm_var_f x1) t1)).
Proof.
apply_mutual_ind term_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_term_intro_rec :
forall t1 x1 t2 n1,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term_rec n1 t2 t1 = subst_term t2 x1 (open_term_wrt_term_rec n1 (trm_var_f x1) t1).
Proof.
pose proof subst_term_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_term_intro_rec : lngen.
Hint Rewrite subst_term_intro_rec using solve [auto] : lngen.

Lemma subst_term_intro :
forall x1 t1 t2,
  x1 `notin` fv_term t1 ->
  open_term_wrt_term t1 t2 = subst_term t2 x1 (open_term_wrt_term t1 (trm_var_f x1)).
Proof.
unfold open_term_wrt_term; default_simp.
Qed.

Hint Resolve subst_term_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
