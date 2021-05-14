Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        rulesb_inf
        Infrastructure
        Infrastructure_b
        Deterministic
        Typing_b
        Type_Safety
        ttyping.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Require Import Omega.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try omega ;
    try eauto ).

Lemma principle_if: forall v A t,
    value v -> ttyping nil v Inf A t -> principal_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.


Lemma value_valueb: forall e t A,
 ttyping nil e Inf A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ.
    pick fresh x.
    forwards*: H6.
    forwards*: lc_lcb H.
  - inverts typ.
    inverts* H3.
    forwards*: IHvalue.
    inverts* H; inverts H1; inverts H2; simpl in H0; inverts H0.
    eapply valueb_fanno; eauto.
    eapply valueb_fanno; eauto.
    eapply valueb_fanno; eauto.
    eapply valueb_fanno; eauto.
  - inverts typ.
    inverts* H3.
    forwards*: IHvalue.
    forwards*: principle_if H1.
    rewrite H4 in H.
    apply valueb_dyn; eauto.
Qed.

Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma fillb_cast: forall v A B,
  (trm_cast v A B) = (fillb (castCtxb A B)  v).
Proof.
  introv.
  eauto.
Qed.



Lemma Tred_soundness: forall v t v' A,
  ttyping nil (e_anno v A) Inf A t->
  value v ->
  TypedReduce v A (e_exp v') ->
  exists t', t ->* (t_term t') /\ ttyping nil v' Inf A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - inverts Typ.
    inverts H3.
    forwards*: principle_if H1.
  - inverts Typ.
    inverts H2.
    forwards*: principle_if H0.
  - inverts Typ.
    inverts H1.
    inverts H.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply ttyp_lit; eauto.
  - inverts Typ.
    inverts H2.
    inverts H0.
    inverts H4.
    inverts val.
    exists. split.
    apply star_one.
    apply bStep_dd; eauto.
    apply valueb_dyn; eauto.
    forwards*: value_valueb H5.
    forwards*: principle_if H0.
    rewrite H3 in H4.
    auto.
    simpl.
    apply ttyp_anno; eauto.
  - inverts Typ.
    inverts H2.
    forwards*: principle_if H0.
    rewrite H2 in H.
    inverts* H.
    inverts H4.
    inverts H5.
    rewrite <- TEMP in H.
    rewrite <- TEMP in H3.
    exists. split.
    apply star_one.
    apply bStep_anyd; eauto.
    forwards*: value_valueb val.
    simpl.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto.
    apply ttyp_sim; eauto.
    rewrite <- TEMP in H0. auto.
    rewrite <- TEMP in H3.
    exfalso. apply H3. reflexivity.
  - inverts Typ. inverts val.
    inverts H3. inverts H1. inverts H8.
    forwards*: principle_if H1.
    rewrite H7 in H0.
    rewrite H7 in H2.
    exists. split.
    eapply bstep_n.
    apply bStep_dyna; eauto.
    apply valueb_dyn; eauto.
    forwards*: value_valueb H4.
    inverts* H. inverts* H. inverts* H.
    rewrite fillb_cast.
    eapply bstep_n.
    apply do_stepb; eauto.
    inverts H. inverts H9. inverts* H10.
    inverts H0. rewrite <- TEMP in H2. inverts H2.
    apply bStep_vany; eauto.
    forwards*: value_valueb H4.
    rewrite <- TEMP in H2. inverts H2.
    apply bstep_refl.
    apply ttyp_anno; eauto.
    inverts H. inverts H9. inverts* H10.
    inverts H0. rewrite <- TEMP in H2. inverts H2.
    rewrite <- TEMP in H1.
    apply ttyp_sim; eauto. 
    rewrite <- TEMP in H2. inverts H2.
  - inverts Typ. inverts val.
    inverts H1.
    inverts H. inverts H5.
    forwards*: principle_if H.
    exists. split.
    apply star_one.
    rewrite H4. rewrite H4 in H0.
    apply bStep_vany; eauto.
    forwards*: value_valueb H2.
    rewrite H4. auto.
Qed.

Lemma soundness_mul_two: forall e t e' A dir ,
  ttyping nil e dir A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ ttyping nil e' dir A t' .
Proof.
  introv Typ Red. gen A t dir.
  inductions Red; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H3. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H4.
      eapply ttyp_app; eauto.
      inverts H0.
      forwards*: IHRed H5. inverts H0. inverts H2.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app x t2) A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app2; auto.
      inverts H.
      forwards*: lc_lcb H6. 
      apply bstep_refl.
      apply ttyp_sim; eauto.
    + inverts Typ. inverts H7.
      forwards*: IHRed H0. inverts H2. inverts H4.
      exists. split.
      apply star_trans with (b:= trm_app t1 (trm_cast x A1 A0)).
      apply multi_red_app; auto.
      inverts H.
      forwards*: value_valueb H3.
      apply multi_red_cast; auto.
      apply bstep_refl.
      eapply ttyp_app; eauto.
      inverts H0.
      forwards*: IHRed H6. inverts H0. inverts H2.
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app t1 x) A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app; auto.
      inverts H.
      forwards*: value_valueb H5.
      apply multi_red_cast; auto.
      eapply ttyp_sim; eauto.
    + inverts Typ. inverts H6.
      forwards*: IHRed H0. inverts H2. inverts H3.
      exists. split.
      apply multi_red_cast.
      apply H2.
      apply ttyp_anno; eauto.
      inverts H0.
      forwards*: IHRed H4. inverts H0. inverts H2.
      exists. split.
      apply multi_red_cast.
      apply H0.
      apply ttyp_sim; eauto.
  - inverts* Typ.
    * inverts H5. 
    assert(ttyping nil (e_anno v A1) Inf A1 t2).
    apply ttyp_anno; auto. inverts H9.
    forwards*: value_valueb H3.
    forwards*: Tred_soundness H1.
    destruct H6. destruct H6.
    exists. split.
    apply star_trans with (b:= (trm_app (trm_abs A1 t) x)).
    apply multi_red_app; eauto. forwards*: lc_lcb H.
    apply star_one. 
    apply bStep_beta; eauto.
    forwards*: lc_lcb H.
    forwards*: Tred_value H1.
    forwards*: value_valueb H7.
    apply ttyp_anno; eauto.
    pick fresh y.
    forwards*: H11.
    rewrite (subst_exp_intro y); auto.
    rewrite (subst_term_intro y); auto.
    eapply ttyping_c_subst_simpl; auto.
    apply H8. auto.
    * inverts H2. inverts H7.
    assert(ttyping nil (e_anno v A2) Inf A2 t2).
    apply ttyp_anno; auto. inverts H8.
    forwards*: value_valueb H4.
    forwards*: Tred_soundness H1.
    destruct H7. destruct H7.
    exists. split.
    apply star_trans with (b:= trm_cast (trm_app (trm_abs A2 t) x) A1 A0).
    apply multi_red_cast; eauto.
    apply multi_red_app; eauto. forwards*: lc_lcb H.
    apply star_trans with (b := trm_cast (t ^^' x) A1 A0).
    apply multi_red_cast; auto.
    apply star_one. 
    apply bStep_beta; eauto.
    forwards*: lc_lcb H.
    forwards*: Tred_value H1.
    forwards*: value_valueb H8.
    apply bstep_refl.
    apply ttyp_sim; eauto.
    apply ttyp_anno; eauto.
    pick fresh y.
    forwards*: H12.
    rewrite (subst_exp_intro y); auto.
    rewrite (subst_term_intro y); auto.
    eapply ttyping_c_subst_simpl; auto.
    apply H9. auto.
  - inverts Typ.
    assert (ttyping nil (e_anno v A0) Inf A0 t).
    eauto.
    forwards*: Tred_soundness H2.
    inverts H2.
    assert (ttyping nil (e_anno v A1) Inf A1 t0).
    eauto.
    forwards*: Tred_soundness H0.
    inverts H4. inverts H5.
    exists. split.
    apply multi_red_cast; eauto.
    apply ttyp_sim;eauto.
  - inverts Typ. 
    * inverts H4.
    inverts H8. 
    assert(ttyping nil (e_anno v1 t_int) Inf t_int (trm_cast t A t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H1.  
    forwards*: Tred_soundness H3. inverts* H6. inverts H7. inverts H8.
     exists. split.
    apply star_trans with (b := (trm_app trm_add (trm_lit i1))).
    apply multi_red_app; eauto. apply star_one.
    apply bStep_add; eauto. 
    eapply ttyp_addl; eauto.
    * inverts H1. inverts H6. inverts H7. 
    assert(ttyping nil (e_anno v1 t_int) Inf t_int (trm_cast t A0 t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H.  
    forwards*: Tred_soundness H4. inverts* H7. inverts H8. inverts H9.
     exists. split.
    apply star_trans with (b := trm_cast (trm_app trm_add (trm_lit i1)) (t_arrow t_int t_int) A).
    apply multi_red_cast; eauto.
    apply multi_red_app; eauto.
    apply star_trans with (b := trm_cast ((trm_addl i1)) (t_arrow t_int t_int) A).
    apply multi_red_cast; auto.
    apply bstep_refl.
    apply ttyp_sim; eauto.
  - inverts Typ.
    *
    inverts H4. inverts H8.
    assert(ttyping nil (e_anno v2 t_int) Inf t_int (trm_cast t A t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H1.  
    forwards*: Tred_soundness H3. inverts* H5. inverts H7. 
    exists. split.
    apply star_trans with (b := (trm_app (trm_addl i1) x)).
    apply multi_red_app; eauto. apply star_one. inverts H8.
    apply bStep_addl; eauto. 
    eapply ttyp_lit; eauto.
    *
    inverts H1. inverts H6. inverts H7.
    assert(ttyping nil (e_anno v2 t_int) Inf t_int (trm_cast t A0 t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H.  
    forwards*: Tred_soundness H4. inverts* H6. inverts H7. 
    exists. split. 
    apply star_trans with (b := (trm_cast (trm_app (trm_addl i1) x) t_int A)).
    apply multi_red_cast; eauto.
    apply multi_red_app; eauto.
    apply star_trans with (b:= (trm_cast (trm_lit (i1 + i2)) t_int A)).
    apply multi_red_cast; eauto. inverts H9.
    apply star_one.
    apply bStep_addl; eauto. apply bstep_refl.
    apply ttyp_sim; eauto. 
  - inverts Typ. 
    * inverts H5. 
    assert(ttyping nil (e_anno v2 A1) Inf A1 t2).
    apply ttyp_anno; auto. inverts H9.
    inverts H. 
    inverts H10. inverts H5.
    forwards*: value_valueb H3.
    forwards*: Tred_soundness H2.
    destruct H6. destruct H6.
    exists. split.
    apply star_trans with (b:= (trm_app (trm_cast t0 (t_arrow A3 B) (t_arrow A1 A0)) x)).
    apply multi_red_app; eauto.  
    forwards*: value_valueb H.
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H. 
    forwards*: Tred_value H0.
    forwards*: value_valueb H8.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: principle_if H. rewrite H5 in H9. inverts* H9.
    * inverts H2. inverts H7. 
    assert(ttyping nil (e_anno v2 A2) Inf A2 t2).
    apply ttyp_anno; auto. inverts H8.
    inverts H. 
    inverts H11. inverts H6.
    forwards*: value_valueb H4.
    forwards*: Tred_soundness H2.
    destruct H7. destruct H7.
    exists. split.
    apply star_trans with (b:= (trm_cast (trm_app (trm_cast t0 (t_arrow A4 B) (t_arrow A2 A1)) x) A1 A0)).
    apply multi_red_cast; eauto.
    apply multi_red_app; eauto.  
    forwards*: value_valueb H.
    apply star_trans with (b := trm_cast (trm_cast (trm_app t0 (trm_cast x A2 A4)) B A1) A1 A0).
    apply multi_red_cast; auto.
    apply star_one; eauto.
    apply bStep_abeta; eauto. forwards*: value_valueb H. 
    forwards*: Tred_value H0.
    forwards*: value_valueb H11.
    apply bstep_refl. apply ttyp_sim; eauto.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: principle_if H. rewrite H6 in H10. inverts* H10.
Qed. 

  



Lemma soundness_mul: forall e t e' A,
  ttyping nil e Inf A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ ttyping nil e' Inf A t' .
Proof.
  introv Typ Red. gen A t.
  inductions Red; intros.
  - destruct E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H3. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H5.
      eapply ttyp_app; eauto.
    + inverts Typ. inverts H4.
      forwards*: IHRed H0. inverts H2. inverts H4.
      exists. split.
      apply star_trans with (b:= trm_app t1 (trm_cast x A1 A0)).
      apply multi_red_app; auto.
      inverts H.
      forwards*: value_valueb H3.
      apply multi_red_cast; auto.
      apply bstep_refl.
      eapply ttyp_app; eauto.
    + inverts Typ. inverts H2.
      forwards*: IHRed H0. inverts H2. inverts H3.
      exists. split.
      apply multi_red_cast.
      apply H2.
      apply ttyp_anno; eauto.
  - inverts* Typ.
    inverts H5. 
    assert(ttyping nil (e_anno v A1) Inf A1 t2).
    apply ttyp_anno; auto. inverts H6.
    forwards*: value_valueb H3.
    forwards*: Tred_soundness H2.
    destruct H6. destruct H6.
    exists. split.
    apply star_trans with (b:= (trm_app (trm_abs A1 t) x)).
    apply multi_red_app; eauto. forwards*: lc_lcb H.
    apply star_one. 
    apply bStep_beta; eauto.
    forwards*: lc_lcb H.
    forwards*: Tred_value H1.
    forwards*: value_valueb H7.
    apply ttyp_anno; eauto.
    pick fresh y.
    forwards*: H11.
    rewrite (subst_exp_intro y); auto.
    rewrite (subst_term_intro y); auto.
    eapply ttyping_c_subst_simpl; auto.
    apply H8. auto.   
  - inverts Typ.
    assert (ttyping nil (e_anno v A0) Inf A0 t).
    eauto.
    forwards*: Tred_soundness H2.
  - inverts Typ. inverts H4.
    inverts H5. 
    assert(ttyping nil (e_anno v1 t_int) Inf t_int (trm_cast t A t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H1.  
    forwards*: Tred_soundness H3. inverts* H5. inverts H7. inverts H8.
     exists. split.
    apply star_trans with (b := (trm_app trm_add (trm_lit i1))).
    apply multi_red_app; eauto. apply star_one.
    apply bStep_add; eauto. 
    eapply ttyp_addl; eauto.
  - inverts Typ.
    inverts H4. inverts H5.
    assert(ttyping nil (e_anno v2 t_int) Inf t_int (trm_cast t A t_int)).
    apply ttyp_anno; auto. 
    forwards*: value_valueb H1.  
    forwards*: Tred_soundness H3. inverts* H5. inverts H6. exists. split.
    apply star_trans with (b := (trm_app (trm_addl i1) x)).
    apply multi_red_app; eauto. apply star_one. inverts H8.
    apply bStep_addl; eauto. 
    eapply ttyp_lit; eauto.
  - inverts Typ. inverts H5. 
    assert(ttyping nil (e_anno v2 A1) Inf A1 t2).
    apply ttyp_anno; auto. inverts H6.
    inverts H. inverts H10. inverts H5.
    forwards*: value_valueb H3.
    forwards*: Tred_soundness H2.
    destruct H6. destruct H6.
    exists. split.
    apply star_trans with (b:= (trm_app (trm_cast t0 (t_arrow A3 B) (t_arrow A1 A0)) x)).
    apply multi_red_app; eauto.  
    forwards*: value_valueb H.
    apply star_one. 
    apply bStep_abeta; eauto. forwards*: value_valueb H. 
    forwards*: Tred_value H0.
    forwards*: value_valueb H8.
    apply ttyp_anno; eauto. apply ttyp_sim; eauto. eapply ttyp_app; eauto.
    apply ttyp_sim; eauto. apply BA_AB; auto.
    forwards*: principle_if H. rewrite H5 in H9. inverts* H9.
Qed. 
