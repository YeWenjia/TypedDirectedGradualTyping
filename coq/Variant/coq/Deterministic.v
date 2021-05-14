Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  intros.
  inductions A; eauto.
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
    inverts H1.
  - inverts* R2.
    inverts* H1.
  - inverts* R2.
    inverts* H4. 
  - inverts* R2.
    inverts* H5.
Qed.


Lemma TypedReduce_prv_value2: forall v A v',
    value v -> TypedReduce v A (Expr v') -> value v'.
Proof.
  intros v A v' Val Red.
  inductions Red; eauto.
  - inverts* Val.
  - inverts Val.
    inverts H1.
    eapply value_abs; auto.
  - inverts* Val.
Qed.

Lemma principle_inf: forall v A,
  sval v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed. 

Lemma TypedReduce_preservation2: forall v A v' B,
    value v -> TypedReduce v A (Expr v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  + inverts* Typ. inverts H1. inverts H5.
    eapply Typ_anno; eauto.
    inverts Val.
    inverts H1. inverts H0.
    eapply Typ_sim; eauto.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H1.
    rewrite H4 in H0. 
    eapply Typ_sim; eauto.
  + inverts* Typ.
    inverts* H2. inverts H6.
    eapply Typ_save; eauto.
    forwards*: principle_inf H2.
    rewrite H5 in H1. auto.
  + inverts* Val.
    inverts Typ. inverts H0.
    eapply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    forwards*: principle_inf H9.
    rewrite H0 in H. auto.
  + inverts* Typ.
    inverts* H0.
    eapply Typ_save; eauto.
    forwards*: principle_inf H7.
    rewrite H0 in H. auto.
Qed.

Lemma  TypeLists_unique: forall v r1 r2 (A: list typ),
    value v -> (exists B, Typing nil v Inf B) ->  TypeLists v A r1 ->  TypeLists v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  induction R1; introv R2;
    try solve [inverts* R2].
  - inverts* R2.
    forwards*: TypedReduce_unique H1 H5.
    forwards*: TypedReduce_unique H1 H5. inverts H8.
    forwards*: TypedReduce_unique H1 H7.
  - inverts* R2.
    forwards*: TypedReduce_unique H1 H5. inverts H8.
  - inverts* R2. inverts R1. inverts R1.
    forwards*: TypedReduce_unique H1 H6. inverts H2.
    forwards*: TypedReduce_prv_value2 Val H1.
    inverts H.
    forwards*: TypedReduce_preservation2 H1.
    forwards*: TypedReduce_unique H1 H7. inverts H2.
  - inverts* R2.
    forwards*: TypedReduce_unique H1 H7.
    forwards*: TypedReduce_unique H1 H6. inverts H2.
Qed.


Lemma vval_val: forall v,
  vvalue v -> value v.
Proof.
  introv val.
  inductions val; eauto.
Qed.

Lemma sfill_eq: forall E0 e0 E e1 r1 r2,
  simpl_fill E0 e0 = simpl_fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  simpl_wf E ->
  simpl_wf E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold simpl_fill in *;  intros.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red2.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red2.
Qed.


Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - inverts* Red2. destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
  - inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence. inverts H3.
      forwards*: IHRed1 Red1 H8. congruence.
      inverts H3.
      forwards*: IHRed1 Red1 H9. congruence.
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H8. congruence.
      inverts H3.
      forwards*: IHRed1 Red1 H9. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
      destruct H3. subst. inverts Typ.
      destruct E0; unfold simpl_fill in H3. inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H2. congruence.
      inverts H3. 
      forwards*: IHRed1 Red1 H8. congruence.
      inverts H3.
      forwards*: IHRed1 Red1 H9. congruence.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
      forwards*: step_not_value Red1.
      forwards*: step_not_value Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: step_not_value H2 Red1.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0];
    try solve [inverts Typ; inverts H0; forwards*: IHRed1 H2; congruence].
    forwards*: step_not_value H2 Red1.
  - inverts* Red2.
    destruct E; unfold simpl_fill in H2; inverts* H2; simpl in *.
    forwards*: step_not_value H4.
    forwards*: step_not_value H4.
    destruct E; unfold simpl_fill in H2; inverts* H2.
    inverts* H4.
    destruct E; unfold simpl_fill in H2; inverts* H2.
    exfalso. apply H7. eauto. inverts H8.
    forwards*: step_not_value H4. inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
    inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
  - inverts Red2.
    destruct E; unfold simpl_fill in H2; inverts* H2;
    try solve [
    forwards*: step_not_value H4]; eauto.
    destruct E; unfold simpl_fill in H2; inverts* H2;
    try solve [
    forwards*: step_not_value H4]; eauto.
    inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
    auto.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    forwards*: step_not_value H3. forwards*: step_not_value H3.
    inverts* Typ. inverts* H1. inverts* H7.
    forwards*:  TypedReduce_unique H0 H5.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2].
    destruct E; unfold simpl_fill in H2; inverts* H2.
    forwards*: step_not_value H4. forwards*: step_not_value H4.
    destruct E; unfold simpl_fill in H2; inverts* H2.
    forwards*: step_not_value H4. forwards*: step_not_value H4.
    inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
    inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2].
    destruct E; unfold simpl_fill in H2; inverts* H2.
    forwards*: step_not_value H4. forwards*: step_not_value H4.
    inverts Typ. inverts H2. inverts H8.
    forwards*: TypeLists_unique H1 H11. congruence.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H2; inverts* H2].
    destruct E; unfold simpl_fill in H2; inverts* H2.
    forwards*: step_not_value H4. forwards*: step_not_value H4.
    inverts* H1.
    exfalso. apply H5; eauto.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    destruct E; unfold simpl_fill in H1; inverts* H1.
    forwards*: step_not_value H3. forwards*: step_not_value H3.
    inverts* H0.
    exfalso. apply H4; eauto.
  - inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H; inverts* H].
    destruct E; unfold simpl_fill in H; inverts* H.
    forwards*: step_not_value H1. forwards*: step_not_value H1.
    destruct E; unfold simpl_fill in H; inverts* H.
    forwards*: step_not_value H1.
    forwards*: step_not_value H1.  
    inverts* H4.
    exfalso. apply H5; eauto.
    inverts* H4.
    exfalso. apply H2; eauto.
Qed.


