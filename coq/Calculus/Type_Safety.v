Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


Lemma eq_type: forall A,
 (A = t_dyn) \/ ~(A = t_dyn).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H].
Qed.

Lemma Tred_value: forall v v' A,
  value v->
  TypedReduce v A (e_exp v') ->
  value v'.
Proof.
  introv Val Red.
  inductions Red; eauto.
  - apply value_dyn; eauto.
    inverts H.
    inverts H1.
    inverts Val; inverts* H2.
    eapply value_fanno; eauto.
    reflexivity.
    eapply value_fanno; eauto.
    reflexivity.
    eapply value_fanno; eauto.
    reflexivity.
    eapply value_fanno; eauto.
    reflexivity.
  - inverts Val.
    inverts H.
    inverts H4.
    inverts* H5.
    inverts* H0.
    rewrite <- H5 in H2.
    inverts H2.
  - inverts* Val.
Qed.


Theorem tred_progress: forall v A,
 value v -> Typing nil v Chk A -> (exists v', (TypedReduce v A (e_exp v'))) \/ (TypedReduce v A (e_blame)). 
Proof.
  introv val sim. gen A.
  inductions val; intros.
  - inverts sim. inverts H. 
    inductions A; simpl in H0; inverts H0.
    left.
    exists*.
    left.
    exists*.
  - inverts sim. inverts H. 
    inductions A; simpl in H0; inverts H0.
    left.
    exists.
    eapply TReduce_abs.
    apply S_arr.
    apply H4.
    apply H6.
    reflexivity.
    left.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H.
    split.
    simpl; unfold not; intros.
    inverts H.
    simpl; eauto. 
  - inverts sim. inverts H. 
    inductions A; simpl in H0; inverts H0.
    left.
    exists.
    eapply TReduce_abs.
    apply S_arr.
    apply H4.
    apply H6.
    reflexivity.
    left.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H.
    split.
    simpl; unfold not; intros.
    inverts H.
    simpl; eauto.
  - inverts sim. inverts H0. 
    inductions A0; simpl in H1; inverts H1.
    left.
    exists.
    eapply TReduce_abs.
    apply S_arr.
    apply H4.
    apply H6.
    reflexivity.
    left.
    destruct (eq_type A).
    destruct (eq_type B).
    subst*.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H2.
    split.
    simpl; unfold not; intros.
    inverts H2.
    simpl; eauto.
    eauto.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H1.
    split.
    simpl; unfold not; intros.
    inverts H1.
    simpl; eauto.
    eauto.
  - inverts sim. inverts H0. 
    inductions A0; simpl in H1; inverts H1.
    left.
    exists.
    eapply TReduce_abs.
    apply S_arr.
    apply H5.
    apply H7.
    reflexivity.
    destruct (eq_type A).
    destruct (eq_type B).
    subst*.
    left.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H2.
    split.
    simpl; unfold not; intros.
    inverts H2.
    simpl; eauto.
    eauto.
    left.
    exists.
    eapply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    simpl; unfold not; intros.
    inverts H1.
    split.
    simpl; unfold not; intros.
    inverts H1.
    simpl; eauto.
    eauto.
  - inductions A.
    + inverts val; inverts H.
      left.
      exists.
      eapply TReduce_vany; eauto.
      right.
      eapply TReduce_blame; eauto.
      simpl. unfold not; intros.
      inverts H.
      right.
      eapply TReduce_blame; eauto.
      simpl. unfold not; intros.
      inverts H.
    + destruct (eq_type A1).
      destruct (eq_type A2).
      subst.
      inverts val; inverts H.
      right.
      eapply TReduce_blame; eauto.
      simpl. unfold not; intros.
      inverts H.
      left.
      exists.
      eapply TReduce_vany; eauto.
      left.
      exists.
      eapply TReduce_vany; eauto.
      inverts val; inverts H.
      right.
      eapply TReduce_blame; eauto.
      simpl. unfold not; intros.
      inverts H.
      left.
      exists.
      eapply TReduce_dyna; eauto.
      unfold FLike.
     split.
     simpl; unfold not; intros.
     inverts H.
     split.
     simpl; unfold not; intros.
     inverts H.
     simpl; eauto.
     simpl; eauto.
     simpl. eauto.
      left.
      exists.
      eapply TReduce_dyna; eauto.
      unfold FLike.
     split.
     simpl; unfold not; intros.
     inverts H.
     split.
     simpl; unfold not; intros.
     inverts H.
     simpl; eauto.
     simpl; eauto.
     simpl. eauto.
      inverts H.
      right.
      eapply TReduce_blame; eauto.
      simpl. unfold not; intros.
      inverts H.
      rewrite <- H4 in H2.
      inverts* H2.
      rewrite <- H4 in H2.
      inverts* H2.
      left.
      exists.
      eapply TReduce_dyna; eauto.
      unfold FLike.
     split.
     simpl; unfold not; intros.
     inverts H.
     split.
     simpl; unfold not; intros.
     inverts H.
     apply H0. reflexivity.
     eauto.
     rewrite <- H2.
     eauto.
    + left. exists.
      eapply TReduce_dd; eauto.
      apply value_lc; eauto.
Qed.

Lemma TypedReduce_sim: forall v A r B,
    value v -> TypedReduce v A r -> Typing nil v Inf B -> sim B A.
Proof with auto.
  introv Val Red Typ.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  forwards*: principle_inf Typ.
  rewrite H1 in H0.
  rewrite H0.
  auto.
Qed.

Lemma TypedReduce_preservation: forall v A v' B,
    value v -> TypedReduce v A (e_exp v') -> Typing nil v Chk B -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  + apply Typ_anno; eauto.
    inverts* Typ.
    forwards*: principle_inf H1.
    rewrite H0 in H3.
    rewrite <- H3 in H1.
    eapply Typ_sim.
    apply H1.
    auto.
  + apply Typ_anno; eauto.
    inverts* Typ.
    inverts* H0.
  + inverts* Typ.
    apply Typ_anno; eauto.
    forwards*: principle_inf H0.
    rewrite H2 in H.
    eapply Typ_sim; eauto.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    inverts* H.
  + inverts* Typ.
    inverts* H1.
    inverts* H5.
    inverts Val.
    forwards*: principle_inf H1.
    apply Typ_anno; eauto.
    eapply Typ_sim; eauto.
    rewrite H4 in H0.
    auto.
  + inverts* Typ.
    inverts* H.
    inverts* Val.
    inverts* H3.
    forwards*: principle_inf H.
    rewrite H3.
    auto.
Qed.

Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (e_exp e') ->
    Typing nil e' dir A.
Proof.
  introv Typ Red. gen A dir.
  inductions Red; intros.
  - inductions E; unfold fill in *.
  + inverts Typ.
    forwards*: IHRed H3.
    inverts H0.
    forwards*: IHRed H5.
  + inverts Typ.
    forwards*: IHRed H6.
    inverts H0.
    forwards*: IHRed H6.
  + inverts Typ.
    forwards*: IHRed H5.
    inverts H0.
    forwards*: IHRed H4.
  - inverts Typ.
    inverts H5.
    pick fresh y.
    apply Typ_anno.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: TypedReduce_preservation H1.
    inverts H2. inverts H7.
    pick fresh x.
    eapply Typ_sim.
    apply Typ_anno.
    rewrite (subst_exp_intro x); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: TypedReduce_preservation H1.
    auto.
  - inverts Typ.
    forwards*: TypedReduce_preservation H0.
    inverts H2.
    forwards*: TypedReduce_preservation H0.
  - inverts Typ.
    forwards*: TypedReduce_preservation H7.
    inverts H4.
    apply Typ_addl; eauto.
    inverts H1.
    inverts H6.
    eapply Typ_sim.
    apply Typ_addl; eauto.
    auto.
  - inverts Typ.
    forwards*: TypedReduce_preservation H0.
    inverts H4.
    apply Typ_lit; eauto.
    inverts H1.
    inverts H6.
    eapply Typ_sim.
    apply Typ_lit; eauto.
    auto.
  - inverts Typ.
    forwards*: TypedReduce_preservation H0.
    inverts H5.
    inverts H9.
    inverts H. 
    inverts H4.
    apply Typ_anno; eauto.
    apply Typ_sim with (A:= B); eauto.
    apply Typ_app with (A := A2); eauto.
    apply Typ_sim with (A := A1); eauto.
    apply BA_AB; auto.
    forwards*: principle_inf H3.
    rewrite H in H10.
    inverts H10.
    inverts H2.
    forwards*: TypedReduce_preservation H0.
    inverts H.
    inverts H7.
    inverts H11.
    inverts H4.
    apply Typ_sim with (A:= A1); eauto.
    apply Typ_anno; eauto.
    apply Typ_sim with (A:= B); eauto.
    apply Typ_app with (A := A3); eauto.
    apply Typ_sim with (A := A2); eauto.
    apply BA_AB; auto.
    forwards*: principle_inf H.
    rewrite H4 in H10.
    inverts H10.
Qed.

Theorem preservation_multi_step : forall t t' dir  T,
    Typing nil t dir T ->
    t ->** (e_exp t') ->
    Typing nil t' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
Qed.



Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto.
    right.
    unfold not; 
    intros.
    inverts* H.
  - inductions A; eauto.
    right.
    unfold not; 
    intros.
    inverts* H.
    forwards*: IHB1 A1.
    forwards*: IHB2 A2.
    destruct H.
    destruct H0.
    left.
    eauto.
    right.
    unfold not; 
    intros.
    inverts* H1.
    destruct H0.
    right.
    unfold not; 
    intros.
    inverts* H1.
    right.
    unfold not; 
    intros.
    inverts* H1.
Qed.

Lemma TypedReduce_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - inverts Typ.
    inverts H.
    inductions A; inverts H0; eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros H;
    inverts* H.
    split.
    unfold not; intros H;
    inverts* H.
    eauto.
  - inverts Typ.
    inverts H0.
    inductions A0; inverts H1; eauto.
    destruct (eq_type A).
    destruct (eq_type B).
    subst*.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H2.
    split.
    unfold not; intros H2;
    inverts* H2.
    eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H1.
    split.
    unfold not; intros H2;
    inverts* H2.
    eauto.
  - inverts Typ.
    inverts H0.
    inductions A0; inverts H1; eauto.
    destruct (eq_type A).
    destruct (eq_type B).
    subst*.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H2.
    split.
    unfold not; intros H2;
    inverts* H2.
    eauto.
    exists.
    apply TReduce_anyd; eauto.
    simpl.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H1.
    split.
    unfold not; intros H2;
    inverts* H2.
    eauto.
  - inverts Typ.
    inverts H0.
    inverts H4.
    inductions A; eauto.
    inverts* Val; inverts* H.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    inverts* Val; inverts* H.
    exists.
    apply TReduce_blame; eauto.
    simpl.
    unfold not; intros.
    inverts H.
    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H5.
    split.
    unfold not; intros;
    inverts* H5.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H4.
    split.
    unfold not; intros;
    inverts* H4.
    eauto.
    simpl. eauto.
    destruct (eq_type A1).
    destruct (eq_type A2).
    subst.
    exists.
    apply TReduce_vany; eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H6.
    split.
    unfold not; intros;
    inverts* H6.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dyna; eauto.
    unfold FLike.
    split.
    unfold not; intros.
    inverts* H5.
    split.
    unfold not; intros;
    inverts* H5.
    eauto.
    simpl. eauto.
    exists.
    apply TReduce_dd; eauto.
    apply value_lc; auto. 
Qed.
  
Theorem progress : forall e dir T,
    Typing nil e dir T ->
    value e \/ (exists r, step e r).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].
  - Case "var".
    inverts* H0.
  - right. inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts Val1 ].
    +
      forwards*: TypedReduce_progress Typ2.
      destruct H.
      inductions x.
      exists.
      apply Step_beta; eauto.
      exists. apply Step_betap; eauto.
    + forwards*: TypedReduce_progress Typ2.
      destruct H.
      inductions x.
      inverts Typ2.
      inverts Val2;
      inverts H0; inverts H3. 
      exists. apply Step_add; eauto. inverts H. inverts H7.
      inverts H0. inverts H7.
      inverts H6 ; inverts H7.
      exists. apply Step_add; eauto.
      apply TReduce_vany; eauto.
      exists. apply Step_addp; eauto.
    + forwards*: TypedReduce_progress Typ2.
      destruct H.
      inductions x.
      inverts Typ2.
      inverts Val2;
      inverts H0; inverts H3. 
      exists. apply Step_addl; eauto. inverts H. inverts H7.
      inverts H0. inverts H7.
      inverts H6 ; inverts H7.
      exists. apply Step_addl; eauto.
      apply TReduce_vany; eauto.
      exists. apply Step_addlp; eauto.
    + forwards*: TypedReduce_progress Typ2.
      destruct H0.
      inductions x.
      exists. apply Step_abeta; eauto.
      exists. apply Step_abetap; eauto.
    + inductions e2'.
      assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
      rewrite <- H.
      exists. apply do_step; eauto.
      assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
      rewrite <- H.
      exists. apply blame_step; eauto.
    + inductions e1'.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H.
      exists. apply do_step; eauto.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H.
      exists. apply blame_step; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress Typ.
      destruct H.
      inverts* H.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
        inverts* H2.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
        inverts* H1.
        inverts* H4.
        inverts* H5.
        rewrite <- H4 in H2.
        inverts H2.
        rewrite <- H4 in H1.
        exfalso.
        apply H1.
        reflexivity.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
        inverts* H5.
        inverts* H4.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
        inverts* H3.
        inverts* H2.
      * right. exists.
        apply Step_annov; eauto.
        unfold not; intros nt;
        inverts* nt.
        inverts* H4.
    + right.
      induction t'.
      * 
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply do_step; eauto.
      *
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply blame_step; eauto.
  - forwards*: IHTyp Typ.
Qed.
