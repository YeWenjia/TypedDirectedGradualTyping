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

Lemma value_decidable: forall v,
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc. inductions v; eauto;
  try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. forwards*: IHv. inverts H.
    + inverts H1;try solve [right; unfold not; intros nt; inverts nt].
    + inductions v; eauto;
      try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. forwards*: IHv. inverts H.
    + inverts H1;try solve [right; unfold not; intros nt; inverts nt].
      right. unfold not;intros. inverts H. inverts H2.
      right. unfold not;intros. inverts H1. inverts H3.
      right. unfold not;intros. inverts H1. inverts H3.
    + inductions v; eauto;
      try solve [right; unfold not; intros nt; inverts nt; inverts H2].
Qed.



Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto. right. unfold not;  intros. inverts* H.
  - inductions A; eauto. right. unfold not; intros.
    inverts* H.
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H.  destruct H0. left.  eauto. right.
    unfold not; intros. inverts* H1. destruct H0.
    right. unfold not; intros. inverts* H1.
    right. unfold not; intros. inverts* H1.
Qed.

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

Lemma TypedReduce_trans : forall v v1 v2 A B,
    value v -> TypedReduce v A (Expr v1) -> TypedReduce v1 B (Expr v2) -> TypedReduce v B (Expr v2).
Proof.
  introv Val Red1 Red2.
  lets Lc: value_lc Val.
  gen B v2.
  inductions Red1;
    introv Red2; eauto.
  - inverts* Red2. 
  - inverts* Red2.
  - inverts* Red2.
  - inverts* Red2.
Qed.

Lemma TypedReduce_prv_value: forall v A v',
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


Lemma principle_inf2: forall v A,
  value v -> Typing nil v Inf A -> (principal_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

Lemma TypedReduce_preservation: forall v A v' B,
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

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma TypeLists_preservation3: forall v A1 A2 v' B,
value v -> TypeLists v (cons A2 (cons t_dyn (cons A1 nil))) (Expr v') 
     -> Typing nil v Chk B -> Typing nil v' Inf A1.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  - inverts Red.
    inverts H7.
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_preservation H5.
    forwards*: TypedReduce_prv_value H5.
    forwards*: TypedReduce_preservation H8.
    inverts H10.
Qed.

Lemma TypeLists_preservation2: forall v A1 A2 v' B,
value v -> TypeLists v (cons A2 (cons A1 nil)) (Expr v') 
     -> Typing nil v Chk B -> Typing nil v' Inf A1.
Proof with auto.
  introv Val Red Typ'.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*].
  - inverts Red.
    forwards*: TypedReduce_preservation H0.
    forwards*: TypedReduce_prv_value H0.
    forwards*: TypedReduce_preservation H5.
    inverts H7.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (Expr e') ->
    Typing nil e' dir A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J]; introv J.
  - inverts J.
    apply Typ_anno; eauto.
    destruct E; unfold simpl_fill in H0; inverts H0.
  - inverts H0.
  - inverts* J.
    + eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      apply sim_refl.
    + destruct E; unfold simpl_fill in H1; inverts H1.
  - Case "typing_app".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    + inverts Typ1.
      inverts* H6.
      inverts* H.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H9.
      inverts H.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_preservation2 H4.
      auto.
      inverts* H0. 
    + inverts Typ1.
      inverts* H10.
      pick fresh x.
      rewrite (subst_exp_intro x); eauto.
      forwards*: H7.
      inverts H.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply Typ_anno.
      eapply Typ_sim.
      eapply typing_c_subst_simpl; eauto.
      forwards*: TypeLists_preservation3 H4. 
      auto. eauto. eauto.
  - Case "typing_anno".
    inverts* J.
    + destruct E; unfold simpl_fill in *; inverts H.
    + eapply TypedReduce_preservation; eauto.
  - inverts* J.
    destruct E; unfold simpl_fill in *; inverts H.
    forwards*: IHTyp1 Typ1.
    forwards*: IHTyp2 Typ2.
  - inverts* J.
    destruct E; unfold simpl_fill in H2; inverts H2.
Qed.

Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (Expr e') ->
    Typing nil e' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
Qed.

Lemma sfill_appl : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addl : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_addr : forall e1 e2,
  (e_add e1 e2) = (simpl_fill (saddCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma TypedReduce_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, TypedReduce v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - inverts Typ. inverts H. inverts H3. inverts H. 
    destruct (sim_decidable t_int  A0).
    exists.
    apply TReduce_sim; eauto.  
    exists.
    apply TReduce_i; eauto.
  - inverts Typ. inverts H0. inverts H4. inverts H0. 
    destruct (sim_decidable (t_arrow A B)  A0).
    exists.
    apply TReduce_sim; eauto.
    destruct A0.
    exists.
    apply TReduce_p; eauto.
    exists.
    apply TReduce_simp; eauto.  
    exfalso. apply H0. eauto.
  - inverts Typ. inverts H0.
    inverts H1.  
    forwards*: principle_inf H8.
    destruct (sim_decidable C  (t_arrow C0 D)).
    exists.
    apply TReduce_savep; eauto.
    rewrite H0. auto.  
    exists.
    apply TReduce_save; eauto.
    rewrite H0. auto.
    forwards*: principle_inf H8.
Qed.


(* Lemma TypeLists_progress: forall v B (A: typ),
    value v -> Typing [] v Chk A -> 
    exists r, TypeLists v (cons B (cons A nil)) r.
Proof.
  introv Val Typ. 
  inductions Val; intros.  
  - inverts Typ. inverts H. inverts H3. inverts H.
    destruct (sim_decidable t_int  B). 
    destruct (sim_decidable t_int A). 
    exists.
    eapply TLists_cons; eauto. 
    apply TLists_base; eauto.
    exists Blame.
    eapply TLists_cons; eauto.
    apply TLists_baseb; eauto.
    exists.
    eapply TLists_consb; eauto.
  - inverts Typ. inverts H0. inverts H4. inverts H0. 
    destruct (sim_decidable (t_arrow A B)  B).
    exists.
    apply TReduce_sim; eauto.
    destruct A0.
    exists.
    apply TReduce_p; eauto.
    exists.
    apply TReduce_simp; eauto.  
    exfalso. apply H0. eauto.
  - inverts Typ. inverts H0.
    inverts H1.  
    forwards*: principle_inf H8.
    destruct (sim_decidable C  (t_arrow C0 D)).
    exists.
    apply TReduce_savep; eauto.
    rewrite H0. auto.  
    exists.
    apply TReduce_save; eauto.
    rewrite H0. auto.
    forwards*: principle_inf H8.
Qed. *)

Lemma vval_dec: forall v,
  value v -> 
  (vvalue v) \/ ~(vvalue v).
Proof.
  introv val.
  inductions val; eauto.
  right. unfold not; intros.
  inverts* H0.
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
    + inverts* Val1; inverts* H.
      inverts* H0; inverts* H3. inverts* H0; inverts* H4.
      forwards*: TypedReduce_progress Typ2. inverts H.
      destruct x.
      forwards*: TypedReduce_preservation H0.
      forwards*: TypedReduce_prv_value H0.
      assert([] ⊢ e ⇐ A0). eapply Typ_sim; eauto. apply BA_AB; auto. 
      forwards*: TypedReduce_progress H4. inverts H7. 
      destruct x.
      exists. apply Step_beta; eauto.
      eapply TLists_cons; eauto. eapply TLists_base; eauto.
      forwards*: value_lc H4. 
      exists. apply Step_betap; eauto.
      eapply TLists_cons; eauto. eapply TLists_consb; eauto.
      forwards*: value_lc H4.
      exists. apply Step_betap; eauto.
    + inverts H4. 
      inverts* H7.
      forwards*: TypedReduce_progress Typ2. inverts H0.
      destruct x.
      forwards*: TypedReduce_preservation H4.
      forwards*: TypedReduce_prv_value H4.
      assert([] ⊢ e ⇐ t_dyn). eapply Typ_sim; eauto.  
      forwards*: TypedReduce_progress H6. inverts H7. 
      destruct x.
      forwards*: TypedReduce_preservation H9.
      forwards*: TypedReduce_prv_value H9.
      assert([] ⊢ e1 ⇐ A0).  eapply Typ_sim; eauto.
      forwards*: TypedReduce_progress H12. inverts H13. 
      forwards*: value_lc H11. forwards*: value_lc H5.
      destruct x.
      exists. apply Step_appv; eauto.
      exists. apply Step_appvp; eauto.
      forwards*: value_lc H5. 
      exists. apply Step_appvp; eauto.
    + 
      rewrite sfill_appr.  destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
    + rewrite sfill_appl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  -  Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: TypedReduce_progress Val.
      inverts H.
      right. 
      exists. apply Step_annov; eauto. 
    + assert (lc_exp (e_anno e A)); eauto.
      forwards*: value_decidable H. inverts H1.
      left. auto.
      right. inductions t'. 
      exists. apply Step_anno; eauto. 
      exists. apply Step_annob; eauto.
  - right. inverts Lc. 
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts Val1 ].
    + inverts Typ2.
      inverts Val1; inverts H; inverts* H0.
      inverts Val2; inverts H3; inverts* H4.
      inverts Val2; inverts H3; inverts* H4.
    + rewrite sfill_addr.  destruct e2'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
    + rewrite sfill_addl. destruct e1'. exists.
      apply do_step; eauto. exists. apply blame_step; eauto.
  - forwards*: IHTyp Typ.
Qed.
    
      