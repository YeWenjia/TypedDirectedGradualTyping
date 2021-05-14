Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  introv.
  induction* A.
Qed.

Lemma TypedReduce_unique: forall v r1 r2 (A: typ),
    value v -> (exists B, Typing nil v Inf B) -> TypedReduce v A r1 -> TypedReduce v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
  - inverts* R2.
    inverts* H1.
    inverts* H1.
    inverts* H1.
  - inverts* R2.
    inverts* H0.
    inverts* Val; inverts* H0; inverts* H1.
    inverts* H2.
    inverts* H3.
    inverts* H1.
    inverts* H0.
    inverts* H0.
  - inverts* R2.
    inverts* H1.
    inverts* Val; inverts* H0; inverts* H1.
    inverts* Val.
    rewrite H3 in H2.
    inverts* H2.
    exfalso.
    apply H2.
    eauto.
  - inverts* R2.
    inverts* Val; inverts* H0; inverts* H1.
    inverts* H3.
    inverts* H1.
    inverts* H0.
    inverts* H1.
    inverts* Val.
    rewrite H3 in H2.
    inverts* H2.
    exfalso.
    apply H1.
    eauto.
  - inverts* R2.
    simpl in H0.
    inverts* H3.
    inverts* H2.
    inverts* H2.
    inverts* Val.
    inverts* H4; inverts* H3;inverts* H0.
    inverts* H3.
    inverts* H4.
    exfalso.
    apply H3.
    apply BA_AB.
    auto.
  - inverts* R2.
    simpl in H3.
    inverts* H3.
    inverts* H2.
    inverts* Val.
    rewrite <- H1 in H3.
    inverts* H3.
    inverts* H2.
    inverts* Val.
    inverts* H4; inverts* H3;inverts* H1.
    inverts* H3.
    inverts* H4.
    exfalso.
    apply H1.
    inverts* Val.
    inverts* H3; inverts* H2.
    simpl; eauto.
    simpl; eauto.
  - inverts* R2.
    inverts* H1.
    inverts* H2.
    exfalso.
    apply H0.
    eauto.
    exfalso.
    apply H0.
    apply BA_AB.
    auto.
    inverts* Val.
    exfalso.
    apply H0.
    inverts* H3; inverts* H2.
    simpl; eauto.
    simpl; eauto.
    exfalso.
    apply H0.
    apply BA_AB.
    auto.
    exfalso.
    apply H0.
    inverts* Val.
    inverts* H3; inverts* H2.
    simpl; eauto.
    simpl; eauto.
Qed.


Lemma fill_auxi: forall E1 E0 e0 e1 r2 r1,
 fill E0 e0 = fill E1 e1 ->
 wellformed E0 ->
 wellformed E1 ->
 step e0 r1 ->
 step e1 r2 ->
 (E1 = E0)/\ (e0 = e1).
Proof.
  introv eq wf1 wf2 red1 red2. gen E1 e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros. 
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red1.
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red2.
  - inductions E1; unfold fill in *; inverts* eq.    
Qed.

Lemma fill_typ: forall E e1 A,
 wellformed E ->
 Typing nil (fill E e1) Chk A ->
 exists B, Typing nil e1 Chk B.
Proof.
  introv wf Typ. gen e1 A. 
  inductions E; intros.
  - simpl in *.
    inverts Typ. inverts H.
    exists.
    apply Typ_sim with (A:= t_arrow A1 A0).
    apply H4.
    apply sim_refl.
  - unfold fill in *.
    inverts Typ.
    inverts H.
    exists. apply H5.
  - unfold fill in *.
    inverts Typ.
    inverts H.
    exists. apply H3.
Qed.


Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1].
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence. 
  - inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1].
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H1 H9.
    congruence.
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H1 H9.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H1 H9.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H9.
    forwards*: TypedReduce_unique H0 H5.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H3.
    congruence.
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H3.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H3.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H5.
    congruence.
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H5.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    inverts Typ.
    inverts H1.
    inverts H9.
    forwards*: TypedReduce_unique H0 H5.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H0 H8.
    congruence.
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H0 H8.
    congruence.
  - inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ.
    inverts H2.
    inverts H11.
    forwards*: TypedReduce_unique H0 H8.
    congruence.
Qed.


