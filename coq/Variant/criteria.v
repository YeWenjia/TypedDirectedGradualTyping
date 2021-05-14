Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Bool.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.

Lemma tpre_refl: forall A,
  tpre A A.
Proof.
   inductions A; eauto.
Qed.


Lemma sim_refl: forall A,
 sim A A.
Proof.
  introv.
  inductions A; eauto.
Qed.

Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. gen e2.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
  inverts* ep.
  apply lc_e_anno.
  assert(epre (e_anno e1 t_dyn) (e_anno e0 t_dyn)). eauto.
  forwards*: IHlc H. inverts* H0.
  apply lc_e_save.
  assert(epre (e_anno e1 t_dyn) (e_anno e0 t_dyn)). eauto.
  forwards*: IHlc H. inverts* H0.
Qed.

Lemma epre_lc2: forall e1 e2,
 epre e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. gen e1.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 epre [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - inductions H; simpl; eauto.
    + destruct (x == x0); eauto.
    + 
      apply ep_abs with (L := (singleton x)); intros; auto.
      forwards*: H0 x0 ep2 x.
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
      apply tpre_refl. apply tpre_refl.
    + apply ep_anno; eauto.
      apply tpre_refl.
    + apply ep_save; eauto.
      apply tpre_refl.
      apply tpre_refl.
  - 
    apply ep_abs with (L := (union L (singleton x))); intros; auto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed. 


Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
  Case "x <> y".
    assert (J : uniq (((x , T1) :: E))).
      eapply Typing_regular_2; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , T1) :: E)).
    apply Typing_subst_1 with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply Typing_weaken. eauto. auto.
    SCase "y is well-typed". eauto.
Qed.

Theorem precise_type: forall e e' T T',
   epre e e' ->  
   Typing nil e Inf T ->
   Typing nil e' Inf T'->
   tpre T T'.
Proof.
    introv ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - forwards*: inference_unique Typ1 Typ2. subst.
      apply tpre_refl.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H2 H4.
      inverts* H.
Qed.


Lemma vval_pre: forall e1 e2,
  epre e1 e2 ->
  vvalue e1 ->
  vvalue e2.
Proof.
  introv ep vval1. gen e2.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto.
  - inverts ep. eauto. inverts* H4. 
    assert (epre (e_abs A e B) (e_abs A2 e2 B2)).
    eauto. 
    forwards*: epre_lc H0.
Qed.

Lemma val_prel: forall e1 e2,
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv ep vval1. gen e2.
  inductions vval1; intros; eauto.
  - inverts ep. eauto. inverts H3. eauto. 
  - inverts ep. eauto. inverts* H4.  
    assert(epre ((e_abs A e B)) ((e_abs A2 e2 B2))). eauto. 
    forwards*: epre_lc H0.
  - inverts ep. inverts* H. inverts* H. inverts* H6. 
     assert(epre ((e_abs A0 e1 B0)) ((e_abs A2 e3 B2))). eauto. 
    forwards*: epre_lc H.
    inverts* H.
    inverts* H5. 
     pick fresh x.
    forwards*: H3.
    assert(epre ((e_abs A0 e1 B0)) ((e_abs A2 e3 B2))). eauto.
    forwards*: epre_lc H1. 
Qed.

Lemma epre_sim : forall A1 B1 A2 B2,
  sim A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  sim A2 B2.
Proof.
  introv s1 tp1 tp2. gen A2 B2.
  inductions s1; intros; eauto.
  - inverts tp1. inverts* tp2. inverts* tp2.
  - inverts* tp1.
    inverts* tp2.
  - inverts* tp1.
  - inverts* tp2. 
Qed.


Lemma tdynamic_guarantee: forall e1 e2 e1' A B,
 epre e1 e2 ->  
 tpre A B ->
 value e1 ->
 Typing nil e1 Chk A ->
 Typing nil e2 Chk B -> 
 TypedReduce e1 A (Expr e1') ->
 exists e2', TypedReduce e2 B (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep tp val typ1 typ2 red. gen e2 B .
  inductions red; intros; eauto.
  - forwards*: val_prel ep. 
    inverts val.
    + destruct B.
      * inverts tp. inverts ep. inverts typ2. inverts H3.
        inverts H7. inverts H3. inverts H4.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto. inverts H6.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto. inverts ep.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto. inverts H6.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
      * inverts* H0.
      * inverts tp. inverts typ2.
        inverts ep.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto. inverts H8.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
    + destruct B.
      * inverts tp. inverts ep. inverts typ2. inverts H4.
        inverts H8. inverts H4. inverts H6. inverts H5.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts H7.  inverts typ2. inverts H4.
        inverts H9. inverts H4. inverts H7. inverts H6. inverts H0.
        inverts H0. inverts H0.
      * inverts tp. inverts ep.  inverts typ2. inverts H4.
         exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        forwards*: value_lc H1. inverts H2.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts ep.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A0 B1)). apply tpre_refl.
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H4 H6.
        exists. split.
        apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        inverts H9.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A0 B1)). apply tpre_refl.
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H4 H8.
        exists. split.
        apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        simpl in H0. 
        assert(tpre (t_arrow A0 B1) (t_arrow A2 B4)). eauto. 
        assert (tpre (t_arrow B2 B3) (t_arrow C D)). eauto.
        forwards*: epre_sim H0 H2 H4.
        exists. split. 
        assert (epre (e_abs A0 e0 B1) (e_abs A2 e2 B4)).
        eauto. forwards*: epre_lc H9.
        apply ep_anno; eauto.
      * inverts tp. inverts typ2.
        inverts ep.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        forwards*: value_lc H1. inverts H5.
        exists. split. apply TReduce_sim; eauto.
        apply ep_anno; eauto.
  -
   inverts ep. inverts typ2. inverts H3.
    + destruct(sim_decidable (principal_type e) B0).
      exists. split. apply TReduce_sim; eauto.
      apply ep_sa; eauto.
      inverts val. inverts H0.
      destruct B0. inverts tp.
      exists. split. apply TReduce_simp; eauto.
      apply ep_save; eauto. inverts* tp. inverts* tp.
      exfalso. apply H3. simpl; eauto.
    + destruct(sim_decidable (principal_type e0) B0).
      exists. split. apply TReduce_sim; eauto.
      forwards*: epre_lc H6.
      apply ep_sa; eauto.
      destruct B0. inverts tp.
      exists. split. apply TReduce_simp; eauto.
      forwards*: epre_lc H6.
      inverts* H0; inverts* H6. 
      assert(epre (e_abs A0 e1 B0) (e_abs A2 e3 B3)). eauto.
      forwards*: epre_lc H0.
      apply ep_save; eauto. inverts* tp. inverts* tp.
      exfalso. apply H2. eauto. 
    + inverts H0.
    + inverts H0.
  - inverts* ep. inverts typ2. inverts H1.
    + destruct B0.
      * inverts tp.
       exists. split. apply TReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
      * inverts tp.
        exists. split. apply TReduce_savep; eauto.
        inverts H8. simpl in *.
        assert(tpre (t_arrow A1 B1) (t_arrow A1 B1)). apply tpre_refl. 
        assert (tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)). eauto.
        forwards*: epre_sim H H3 H4.
        apply ep_anno; eauto. apply ep_refl. inverts* H0.
      * inverts tp.
        exists. split. apply TReduce_savep; eauto.
        apply ep_anno; eauto. inverts* H0.
    + destruct B0.
      * inverts val. inverts tp. inverts H1. inverts H.
      * inverts tp.
         exists. split. apply TReduce_savep; eauto.
         inverts val. inverts H1. inverts H6.
        simpl in *. 
        assert(tpre (t_arrow A1 B1) (t_arrow A1 B1)). apply tpre_refl. 
        assert (tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)). eauto.
        forwards*: epre_sim H H2 H6.
        simpl in *.
        assert(tpre (t_arrow A1 B1) (t_arrow A3 B3)). eauto. 
        assert (tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)). eauto.
        forwards*: epre_sim H H1 H2.
        apply ep_anno; eauto.
      * inverts tp.
        exists. split. apply TReduce_savep; eauto.
        apply ep_anno; eauto.
    + destruct B0.
      * inverts val. inverts tp. inverts H1. inverts H.
      * inverts tp. inverts val. inverts H1. 
        inverts H4.
         exists. split. 
        apply TReduce_sim; eauto.
        forwards*: epre_lc H5.
        inverts H5. simpl in *.
        
        assert(tpre (t_arrow A1 B1) (t_arrow A1 B1)).
        apply tpre_refl.
        assert(tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)). eauto.
        forwards*: epre_sim H2 H4.
        simpl in *.

        assert(tpre (t_arrow A1 B1) (t_arrow A3 B3)); eauto.
        assert(tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)).
        eauto.
        forwards*: epre_sim H1 H2.
        apply ep_anno; eauto.
        exists. split.
        apply TReduce_sim; eauto.
        forwards*: epre_lc H5. inverts H5. simpl in *.

        assert(tpre (t_arrow A1 B1) (t_arrow A1 B1)).
        apply tpre_refl.
        assert(tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)). eauto.
        forwards*: epre_sim H2 H4.
        simpl in *.

        assert(tpre (t_arrow A1 B1) (t_arrow A3 B3)); eauto.
        assert(tpre (t_arrow A0 B0) (t_arrow B0_1 B0_2)).
        eauto.
        forwards*: epre_sim H1 H2.
        apply ep_anno; eauto.
      * inverts tp. inverts val. inverts H1. 
        inverts H5.
         exists. split. 
        apply TReduce_sim; eauto.
        apply ep_anno; eauto.
        exists. split.
        pick fresh x.
        forwards*: H6.
        assert(epre (e_abs A0 e1 B0) (e_abs A2 e3 B2)). eauto. 
        apply TReduce_sim; eauto. forwards*: epre_lc H2.
        apply ep_anno; eauto.
  -
    inverts ep. inverts typ2. inverts H1.
    + destruct(sim_decidable (principal_type e) B0).
      exists. split. apply TReduce_savep; eauto.
      apply ep_sa; eauto. apply ep_refl. inverts* H0.
      destruct B0. inverts H2.
      exists. split. apply TReduce_save; eauto.
      apply ep_save; eauto. 
      inverts* tp. inverts* tp. apply ep_refl. inverts* H0.
      exfalso. apply H1. eauto.
    + destruct(sim_decidable (principal_type e0) B0).
      exists. split. apply TReduce_savep; eauto.
      apply ep_sa; eauto. 
      destruct B0. inverts tp.
      exists. split. apply TReduce_save; eauto.
      apply ep_save; eauto. 
      inverts* tp. inverts* tp. 
      exfalso. apply H0. eauto.
    + destruct(sim_decidable (principal_type e0) B0).
      exists. split. apply TReduce_sim; eauto. forwards*: value_lc val.
      inverts H1. forwards*: epre_lc H5.
      apply ep_sa; eauto. 
      destruct B0. inverts tp.
      forwards*: value_lc val.
      inverts H1. 
      exists. split. apply TReduce_simp; eauto.
      forwards*: epre_lc H5.
      inverts val. inverts H2. inverts* H5.
      assert(epre (e_abs A0 e1 B0) (e_abs A2 e3 B2)); eauto.
      forwards*: epre_lc H2.
      apply ep_save; eauto. 
      inverts* tp. inverts* tp. 
      exfalso. apply H0. eauto.  
Qed.


Lemma dynamic_guarantee_dir_test: forall e1 e2 e1' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e1 (Expr e1') ->
 exists e2', e2 ->*(Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' dir T1 T2.
  inductions ep; intros; eauto.
  - exists. split. apply star_one. apply red. apply ep_refl.
    forwards*: preservation typ1. 
    forwards*: Typing_regular_1 H0.
  - inverts red. exists. split. assert (epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)).
    eauto. apply star_one; eauto. apply Step_abs; auto. forwards*: epre_lc H3. apply ep_anno; eauto.
    destruct E; unfold simpl_fill in H3; inverts* H3. 
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. 
      forwards*: IHep1 H2. inverts H. inverts H0.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H3. inverts H.
      forwards*: IHep1 H2. inverts H. inverts H3.
      exists. split. inverts H1. apply multi_red_app2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. 
      forwards*: IHep2 H2. inverts H. inverts H0.
      exists. split. inverts H1. apply multi_red_app.
      forwards*: val_prel ep1. apply H.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H. inverts H3.
      forwards*: IHep2 H2. inverts H. inverts H3.
      exists. split. inverts H1. apply multi_red_app.
      forwards*: val_prel ep1. apply H.
      unfold simpl_fill. eauto.
    + inverts* ep1.
      forwards*: val_prel ep2. inverts H4. inverts H10.
      inverts typ1. inverts H10. inverts typ2. inverts H10. 
      forwards*: tdynamic_guarantee ep2 H13 H11 H8. apply tpre_refl.
      inverts H1. inverts H4. 
      forwards*: TypedReduce_prv_value H8. forwards*: TypedReduce_prv_value H1.
      forwards*: TypedReduce_preservation H8. forwards*: TypedReduce_preservation H1.
      inverts H12. inverts H17; inverts H18. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A1). apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H5 H12 H17 H9. apply tpre_refl.
      inverts H18. inverts H19.
      forwards*: TypedReduce_prv_value H9. forwards*: TypedReduce_prv_value H18.
      forwards*: value_lc H19. forwards*: value_lc H24.       
      forwards*: value_lc H0. forwards*: value_lc H10.              
      assert(TypeLists e2' [A0; A1] (Expr x0)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto.
      apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x0) = [xx ~> x0] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H30.
      inverts H2. forwards*: H32 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H31 H21.

      inverts* H1. inverts H12. 
      inverts typ2. inverts* H1. inverts H15. 
      forwards*: val_prel ep2. forwards*: tdynamic_guarantee ep2 H13 H16. apply tpre_refl.
      inverts H10. inverts H11. 
      forwards*: TypedReduce_prv_value H8. forwards*: TypedReduce_prv_value H10.
      forwards*: TypedReduce_preservation H8. forwards*: TypedReduce_preservation H10.
      inverts H14. inverts H20; inverts H21. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A3); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A1). apply Typ_sim with (A := A3); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H12 H14 H20. apply tpre_refl.
      inverts H21. inverts H22.
      forwards*: TypedReduce_prv_value H21. forwards*: TypedReduce_prv_value H9.
      forwards*: value_lc H22. forwards*: value_lc H27.       
      forwards*: value_lc H0. forwards*: value_lc H11. forwards*: value_lc H15.           
      assert(TypeLists e2' [A3; A1] (Expr x0)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_anno; eauto. apply tpre_refl. apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x0) = [xx ~> x0] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H34.
      inverts H2. forwards*: H36 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H35 H24. inverts H12.

      inverts typ2. inverts H6; inverts H1; inverts H7. 
      inverts H4. inverts H13. inverts typ1. inverts H13.
      forwards*: val_prel ep2. forwards*: tdynamic_guarantee ep2 H14 H10. 
      inverts H1. inverts H4.
      forwards*: TypedReduce_prv_value H8. forwards*: TypedReduce_prv_value H1.
      forwards*: TypedReduce_preservation H8. forwards*: TypedReduce_preservation H1.
      inverts H11. inverts H19; inverts H20. inverts H16. inverts H11; inverts H19. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A1). apply Typ_sim with (A := A); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H13 H11 H16. apply tpre_refl.
      inverts H19. inverts H20.
      forwards*: TypedReduce_prv_value H12. forwards*: TypedReduce_prv_value H19.
      forwards*: value_lc H15. forwards*: value_lc H20. 
      forwards*: value_lc H28. forwards*: value_lc H0. 
      assert(TypeLists e2' [A; A1] (Expr x0)). eapply TLists_cons; eauto.    
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_anno; eauto.  apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x0) = [xx ~> x0] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H34.
      inverts H2. forwards*: H36 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H35 H23. inverts H15.
      
      inverts typ1. inverts H6. inverts H4. inverts H17.
      forwards*: val_prel ep2. forwards*: tdynamic_guarantee ep2 H7 H10. 
      inverts H0. inverts H4.
      forwards*: TypedReduce_prv_value H14. forwards*: TypedReduce_prv_value H0.
      forwards*: TypedReduce_preservation H14. forwards*: TypedReduce_preservation H0.
      inverts H13. inverts H21; inverts H22. inverts H15. inverts H13; inverts H21. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A3). apply Typ_sim with (A := A); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H17 H13 H15. 
      inverts H21. inverts H22.
      forwards*: TypedReduce_prv_value H16. forwards*: TypedReduce_prv_value H21.
      forwards*: value_lc H. forwards*: value_lc H22. 
      forwards*: value_lc H18. forwards*: value_lc H30. 
      assert(TypeLists e2' [A; A3] (Expr x0)). eapply TLists_cons; eauto.    
      exists. split. apply star_one. apply Step_beta; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H36.
      pick fresh xx.
      assert((e3 ^^ x0) = [xx ~> x0] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H36.
      forwards*: H8 xx.
      assert(epre (e^xx) (e3^xx)); eauto.
      forwards*: epre_open H37 H25. inverts H19.

      inverts H. inverts H6; inverts H1; inverts H9. inverts H4. inverts H14.
      inverts typ1. inverts H1. inverts H16.
      forwards*: val_prel ep2. forwards*: tdynamic_guarantee ep2 H17 H10. 
      inverts H5. inverts H14.
      forwards*: TypedReduce_prv_value H9. forwards*: TypedReduce_prv_value H5.
      forwards*: TypedReduce_preservation H9. forwards*: TypedReduce_preservation H5.
      inverts H12. inverts H21; inverts H22. inverts H18. inverts H12; inverts H21. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A4); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A1). apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H15 H12 H18. apply tpre_refl.
      inverts H21. inverts H22.
      forwards*: TypedReduce_prv_value H13. forwards*: TypedReduce_prv_value H21.
      forwards*: value_lc H22. forwards*: value_lc H1. 
      forwards*: value_lc H16. forwards*: value_lc H30. 
      assert(TypeLists e2' [A0; A1] (Expr x0)). eapply TLists_cons; eauto.    
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_anno; eauto.  apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x0) = [xx ~> x0] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H36.
      inverts H2. forwards*: H38 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H37 H25. inverts H16.
      
      inverts typ1. inverts H. inverts H15. inverts H4. inverts H19.
      forwards*: val_prel ep2. forwards*: tdynamic_guarantee ep2 H16 H10. 
      inverts H4. inverts H5.
      forwards*: TypedReduce_prv_value H15. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H15. forwards*: TypedReduce_preservation H4.
      inverts H14. inverts H23; inverts H24. inverts H17. inverts H14; inverts H23. 
      assert ([] ⊢ v2 ⇐ A1).  apply Typ_sim with (A := A5); auto. apply BA_AB; auto.
      assert ([] ⊢ x ⇐ A4). apply Typ_sim with (A := A0); auto. apply BA_AB; auto.
      forwards*: tdynamic_guarantee H19 H14 H17. 
      inverts H23. inverts H24.
      forwards*: TypedReduce_prv_value H18. forwards*: TypedReduce_prv_value H23.
      forwards*: value_lc H. forwards*: value_lc H24. 
      forwards*: value_lc H20. forwards*: value_lc H32. 
      assert(TypeLists e2' [A0; A4] (Expr x0)). eapply TLists_cons; eauto.    
      exists. split. apply star_one. apply Step_beta; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A4 e3 B3)); eauto. forwards*: epre_lc H38.
      pick fresh xx.
      assert((e3 ^^ x0) = [xx ~> x0] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H38.
      forwards*: H8 xx.
      assert(epre (e^xx) (e3^xx)); eauto.
      forwards*: epre_open H39 H27. inverts H21.
    + 
      inverts* ep1. inverts typ1. inverts typ2. inverts H6. inverts H7. 
      inverts H4. inverts H11. inverts H21.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H9 H8. apply tpre_refl.
      inverts H1. inverts H6. 
      forwards*: TypedReduce_prv_value H7. forwards*: TypedReduce_prv_value H1.
      forwards*: TypedReduce_preservation H7. forwards*: TypedReduce_preservation H1.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      forwards*: tdynamic_guarantee H21 H25 H26 H10. inverts H27. inverts H28.
      forwards*: TypedReduce_prv_value H10. forwards*: TypedReduce_prv_value H27.
      forwards*: TypedReduce_preservation H10. forwards*: TypedReduce_preservation H27.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H29 H33 H34 H20. apply tpre_refl.
      inverts H35. inverts H36.
      forwards*: TypedReduce_prv_value H20. forwards*: TypedReduce_prv_value H35.
      forwards*: value_lc H36. forwards*: value_lc H0.       
      forwards*: value_lc H22. forwards*: value_lc H30. forwards*: value_lc H38.                          
      assert(TypeLists e2' [A0;t_dyn; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H45.
      inverts H3. forwards*: H47 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H46 H37. inverts H23.

      inverts H0. inverts H8. inverts typ2. inverts H0. inverts H10. 
      inverts H4. inverts H17. inverts H23.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H9 H11. apply tpre_refl.
      inverts H4. inverts H8. 
      forwards*: TypedReduce_prv_value H10. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H10. forwards*: TypedReduce_preservation H4.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A3); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A3); auto.
      forwards*: tdynamic_guarantee H23 H27 H28. inverts H29. inverts H30.
      forwards*: TypedReduce_prv_value H16. forwards*: TypedReduce_prv_value H29.
      forwards*: TypedReduce_preservation H16. forwards*: TypedReduce_preservation H29.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H31 H35 H36. apply tpre_refl.
      inverts H37. inverts H38.
      forwards*: TypedReduce_prv_value H22. forwards*: TypedReduce_prv_value H37.
      forwards*: value_lc H38. forwards*: value_lc H0.       
      forwards*: value_lc H24. forwards*: value_lc H32. forwards*: value_lc H40.                          
      assert(TypeLists e2' [A3;t_dyn; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      apply ep_anno; eauto. apply tpre_refl.
      apply ep_anno; eauto. apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H47.
      inverts H3. forwards*: H49 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H48 H39. inverts H25.

      inverts* H8. inverts typ1. inverts typ2. inverts H8. inverts H9. 
      inverts H4. inverts H13. inverts H23.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H11 H10. 
      inverts H1. inverts H8. 
      forwards*: TypedReduce_prv_value H9. forwards*: TypedReduce_prv_value H1.
      forwards*: TypedReduce_preservation H9. forwards*: TypedReduce_preservation H1.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      forwards*: tdynamic_guarantee H23 H27 H28. inverts H29. inverts H30.
      forwards*: TypedReduce_prv_value H12. forwards*: TypedReduce_prv_value H29.
      forwards*: TypedReduce_preservation H12. forwards*: TypedReduce_preservation H29.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H31 H35 H36. apply tpre_refl.
      inverts H37. inverts H38.
      forwards*: TypedReduce_prv_value H22. forwards*: TypedReduce_prv_value H37.
      forwards*: value_lc H38. forwards*: value_lc H0.       
      forwards*: value_lc H24. forwards*: value_lc H32. forwards*: value_lc H40.                          
      assert(TypeLists e2' [A0;t_dyn; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H47.
      inverts H3. forwards*: H49 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H48 H39. inverts H25.

      inverts H0. inverts H10. inverts typ2. inverts H0. inverts H12. 
      inverts H4. inverts H19. inverts H25.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H11 H13. 
      inverts H4. inverts H10. 
      forwards*: TypedReduce_prv_value H12. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H12. forwards*: TypedReduce_preservation H4.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A3); auto.
      forwards*: tdynamic_guarantee H25 H29 H30. inverts H31. inverts H32.
      forwards*: TypedReduce_prv_value H18. forwards*: TypedReduce_prv_value H31.
      forwards*: TypedReduce_preservation H18. forwards*: TypedReduce_preservation H31.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H33 H37 H38. apply tpre_refl.
      inverts H39. inverts H40.
      forwards*: TypedReduce_prv_value H24. forwards*: TypedReduce_prv_value H39.
      forwards*: value_lc H40. forwards*: value_lc H0.       
      forwards*: value_lc H26. forwards*: value_lc H34. forwards*: value_lc H42.                          
      assert(TypeLists e2' [A3;t_dyn; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply ep_anno; eauto. apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H49.
      inverts H3. forwards*: H51 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H50 H41. inverts H27.

      inverts typ1. inverts typ2. inverts H8. inverts H9. 
      inverts H4. inverts H15. inverts H25.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H13 H12. 
      inverts H0. inverts H8. 
      forwards*: TypedReduce_prv_value H9. forwards*: TypedReduce_prv_value H0.
      forwards*: TypedReduce_preservation H9. forwards*: TypedReduce_preservation H0.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      forwards*: tdynamic_guarantee H25 H29 H30. inverts H31. inverts H32.
      forwards*: TypedReduce_prv_value H14. forwards*: TypedReduce_prv_value H31.
      forwards*: TypedReduce_preservation H14. forwards*: TypedReduce_preservation H31.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A3).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H33 H37 H38.
      inverts H39. inverts H40.
      forwards*: TypedReduce_prv_value H24. forwards*: TypedReduce_prv_value H39.
      forwards*: value_lc H40. forwards*: value_lc H.       
      forwards*: value_lc H26. forwards*: value_lc H34. forwards*: value_lc H42.                          
      assert(TypeLists e2' [A0;t_dyn; A3] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H49.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply ep_anno; eauto. 
      pick fresh xx.
      assert((e3 ^^ x1) = [xx ~> x1] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H49.
      forwards*: H6 xx.
      assert(epre (e^xx) (e3^xx)); eauto.
      forwards*: epre_open H50 H41. inverts H27.

      inverts H. inverts H12. inverts typ2. inverts H. inverts H14.
      inverts H4. inverts H21. inverts H27.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H13 H15. 
      inverts H4. inverts H12. 
      forwards*: TypedReduce_prv_value H14. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H14. forwards*: TypedReduce_preservation H4.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A4); auto.
      forwards*: tdynamic_guarantee H27 H31 H32. inverts H33. inverts H34.
      forwards*: TypedReduce_prv_value H20. forwards*: TypedReduce_prv_value H33.
      forwards*: TypedReduce_preservation H20. forwards*: TypedReduce_preservation H33.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A3).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H35 H39 H40. 
      inverts H41. inverts H42.
      forwards*: TypedReduce_prv_value H26. forwards*: TypedReduce_prv_value H41.
      forwards*: value_lc H42. forwards*: value_lc H.       
      forwards*: value_lc H28. forwards*: value_lc H36. forwards*: value_lc H44.                          
      assert(TypeLists e2' [A4;t_dyn; A3] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_appv; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H51.
      apply ep_anno; eauto. 
      apply ep_anno; eauto. apply ep_anno; eauto. 
      pick fresh xx.
      assert((e3 ^^ x1) = [xx ~> x1] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H51.
      forwards*: H6 xx.
      forwards*: epre_open H52 H43. inverts H29.  

      inverts typ1. inverts typ2. inverts H5. inverts H8. inverts H6. inverts H7. 
      inverts H4. inverts H18. inverts H20.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H10 H9.
      inverts H4. inverts H7. 
      forwards*: TypedReduce_prv_value H11. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H11. forwards*: TypedReduce_preservation H4.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      forwards*: tdynamic_guarantee H20 H24 H25. inverts H26. inverts H27.
      forwards*: TypedReduce_prv_value H13. forwards*: TypedReduce_prv_value H26.
      forwards*: TypedReduce_preservation H13. forwards*: TypedReduce_preservation H26.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H28 H32 H33. apply tpre_refl.
      inverts H34. inverts H35.
      forwards*: TypedReduce_prv_value H19. forwards*: TypedReduce_prv_value H34.
      forwards*: value_lc H35. forwards*: value_lc H0.       
      forwards*: value_lc H21. forwards*: value_lc H29. forwards*: value_lc H37.
      forwards*: TypedReduce_trans H26 H34.                          
      assert(TypeLists e2' [A0; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_annol; eauto. 
      apply ep_anno; eauto.  apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H45.
      inverts H3. forwards*: H47 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H46 H36. inverts H22.

      inverts H1. inverts H; inverts H0.
      inverts H4. inverts H22. inverts H24.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H10 H9.
      inverts H0. inverts H5. 
      forwards*: TypedReduce_prv_value H11. forwards*: TypedReduce_prv_value H0.
      forwards*: TypedReduce_preservation H11. forwards*: TypedReduce_preservation H0.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      forwards*: tdynamic_guarantee H24 H28 H29. inverts H30. inverts H31.
      forwards*: TypedReduce_prv_value H21. forwards*: TypedReduce_prv_value H30.
      forwards*: TypedReduce_preservation H21. forwards*: TypedReduce_preservation H30.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A3).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H32 H36 H37. 
      inverts H38. inverts H39.
      forwards*: TypedReduce_prv_value H23. forwards*: TypedReduce_prv_value H38.
      forwards*: value_lc H41. forwards*: value_lc H.       
      forwards*: value_lc H25. forwards*: value_lc H33. forwards*: value_lc H39.
      forwards*: TypedReduce_trans H30 H38.                          
      assert(TypeLists e2' [A0; A3] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A3 e3 B2)); eauto. forwards*: epre_lc H49.
      apply ep_annol; eauto. 
      apply ep_anno; eauto.  
      pick fresh xx.
      assert((e3 ^^ x1) = [xx ~> x1] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H49.
      forwards*: H6 xx.
      forwards*: epre_open H50 H40. inverts H26.

      inverts H. inverts H9. inverts typ2. inverts H. inverts H7. inverts H11.
      inverts H8. inverts H5; inverts H7.
      inverts H4. inverts H21. inverts H23. inverts H6.
      forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H10 H12.
      inverts H5. inverts H6. 
      forwards*: TypedReduce_prv_value H17. forwards*: TypedReduce_prv_value H5.
      forwards*: TypedReduce_preservation H17. forwards*: TypedReduce_preservation H5.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A3); auto.
      forwards*: tdynamic_guarantee H9 H28 H29. inverts H30. inverts H31.
      forwards*: TypedReduce_prv_value H20. forwards*: TypedReduce_prv_value H30.
      forwards*: TypedReduce_preservation H20. forwards*: TypedReduce_preservation H30.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H32 H36 H37. apply tpre_refl.
      inverts H38. inverts H39.
      forwards*: TypedReduce_prv_value H22. forwards*: TypedReduce_prv_value H38.
      forwards*: value_lc H39. forwards*: value_lc H4.       
      forwards*: value_lc H24. forwards*: value_lc H33. forwards*: value_lc H41.
      forwards*: TypedReduce_trans H30 H38.                          
      assert(TypeLists e2' [A3; A1] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      apply ep_annol; eauto. 
      apply ep_anno; eauto.  apply tpre_refl.
      pick fresh xx.
      assert((e ^^ x1) = [xx ~> x1] (e ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H49.
      inverts H3. forwards*: H51 xx.
      assert(epre (e^xx) (e^xx)); eauto.
      forwards*: epre_open H50 H40. inverts H25.
      
     inverts H11. inverts H7. inverts H; inverts H5. inverts H6.
     inverts H4. inverts H24. inverts H26. 
     forwards*: val_prel ep2.
      forwards*: tdynamic_guarantee ep2 H10 H12.
      inverts H4. inverts H7. 
      forwards*: TypedReduce_prv_value H17. forwards*: TypedReduce_prv_value H4.
      forwards*: TypedReduce_preservation H17. forwards*: TypedReduce_preservation H4.
      assert ([] ⊢ v2 ⇐ t_dyn).  apply Typ_sim with (A := A0); auto.
      assert ([] ⊢ x ⇐ t_dyn).  apply Typ_sim with (A := A3); auto.
      forwards*: tdynamic_guarantee H26 H30 H31. inverts H32. inverts H33.
      forwards*: TypedReduce_prv_value H23. forwards*: TypedReduce_prv_value H32.
      forwards*: TypedReduce_preservation H23. forwards*: TypedReduce_preservation H32.
      assert ([] ⊢ v0 ⇐ A1).  apply Typ_sim with (A := t_dyn); auto.
      assert ([] ⊢ x0 ⇐ A5).  apply Typ_sim with (A := t_dyn); auto.
      forwards*: tdynamic_guarantee H34 H38 H39. 
      inverts H40. inverts H41.
      forwards*: TypedReduce_prv_value H25. forwards*: TypedReduce_prv_value H40.
      forwards*: value_lc H41. forwards*: value_lc H.       
      forwards*: value_lc H27. forwards*: value_lc H35. forwards*: value_lc H43.
      forwards*: TypedReduce_trans H32 H40.                          
      assert(TypeLists e2' [A3; A5] (Expr x1)). eapply TLists_cons; eauto.
      exists. split. apply star_one. apply Step_beta; eauto.
      assert(epre (e_abs A1 e B1) (e_abs A5 e3 B2)); eauto. forwards*: epre_lc H51.
      apply ep_annol; eauto. 
      apply ep_anno; eauto.  
      pick fresh xx.
      assert((e3 ^^ x1) = [xx ~> x1] (e3 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H51.
      forwards*: H9 xx.
      forwards*: epre_open H52 H42. inverts H28.
  - inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      inverts typ1. inverts typ2. 
      forwards*: IHep1 H2. inverts H. inverts H0.
      exists. split. inverts H1. apply multi_red_add2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H3. inverts H.
      forwards*: IHep1 H2. inverts H. inverts H3.
      exists. split. inverts H1. apply multi_red_add2.
      forwards*: epre_lc ep2. apply H.
      unfold simpl_fill. eauto.
      inverts typ1. inverts typ2. 
      forwards*: IHep2 H2. inverts H. inverts H0.
      exists. split. inverts H1. apply multi_red_add.
      forwards*: val_prel ep1. apply H.
      unfold simpl_fill. eauto.
      inverts typ2. inverts H. inverts H3.
      forwards*: IHep2 H2. inverts H. inverts H3.
      exists. split. inverts H1. apply multi_red_add.
      forwards*: val_prel ep1. apply H.
      unfold simpl_fill. eauto.
    + inverts typ2. inverts ep1. inverts ep2.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H6. exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H4. inverts ep2.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H7. exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H. inverts ep1. inverts ep2.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H7. exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H6. inverts ep2.
      exists. split. apply star_one. apply Step_addb; eauto. eauto.
      inverts H8. exists. split. apply star_one. apply Step_addb; eauto. eauto.
  - inverts red.
    destruct E; unfold simpl_fill in H0; inverts* H0.
    assert (not (value (e_anno e2 A))).
    unfold not; intros.
    apply H4. inverts H0.
    inverts* ep. inverts* ep.
    assert (epre (e_abs A1 e0 B1) (e_abs A0 e B0)).
    eauto. forwards*: epre_lc2 H0.
    inverts typ1.  inverts typ2. 
    forwards*: IHep H3. inverts H1. inverts H2.
    exists. split. apply multi_red_anno. 
    unfold not; intro. inverts H2.
    apply H0. eauto. apply H0. eauto.
    apply H1.
    apply ep_anno; eauto.
    inverts typ2. inverts H1.  inverts H5.
    forwards*: IHep H3. inverts H1. inverts H5.
    exists. split. apply multi_red_anno. 
    unfold not; intro. inverts H5.
    apply H0. eauto. apply H0. eauto.
    apply H1.
    apply ep_anno; eauto.
    inverts typ1. inverts typ2.
    forwards*: tdynamic_guarantee H7 H3 H4. inverts H0.
    inverts H1. exists. split. apply star_one. apply Step_annov; eauto.
    forwards*: val_prel ep.  auto.
    inverts typ2. inverts H0.  inverts H3.
    forwards*: tdynamic_guarantee H8 H7 H4. inverts H0.
    inverts H3. exists. split. apply star_one. apply Step_annov; eauto.
    forwards*: val_prel ep.  auto.
  - forwards*: step_not_value red. inverts typ1.
    eauto. inverts H1.
    eauto.
  - forwards*: step_not_value red. inverts typ1.
    eauto. inverts H0.
    eauto.
  - inverts* red.
    + destruct E; unfold simpl_fill in H0; inverts* H0.
    + inverts* H3.
      * destruct E; unfold simpl_fill in H0; inverts* H0.
      * inverts typ2. inverts typ1. inverts H2. inverts H0.
        forwards*: IHep H5. inverts H0. inverts H2.
        exists. split. apply multi_red_anno.
        unfold not; intros nt; inverts nt.
        inverts ep. apply H6; eauto.
        inverts ep. apply H6; eauto.
        apply H6; eauto. apply value_abs; auto.
        assert(epre (e_abs A1 e0 B1) (e_abs A e B)); eauto.
        forwards*: epre_lc2 H2. apply H0. 
        apply ep_annol; eauto.
        inverts typ1. inverts H2. inverts H9. inverts H2.
        inverts H0.
        forwards*: IHep H5. inverts H0. inverts H2.
        exists. split. apply multi_red_anno.
        unfold not; intros nt; inverts nt.
        inverts ep. apply H6; eauto.
        inverts ep. apply H6; eauto.
        apply H6; eauto. apply value_abs; auto.
        assert(epre (e_abs A2 e0 B1) (e_abs A e B)); eauto.
        forwards*: epre_lc2 H2. apply H0. 
        apply ep_annol; eauto.
      * inverts* H6. 
      inverts* H2. inverts ep. 
      inverts typ2. inverts H9. inverts H2. inverts H8.
      inverts H2. inverts H5; inverts H3. inverts H.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      inverts H2. inverts H8. inverts H2. inverts H9.
      inverts H2; inverts H6. inverts H5. inverts H.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      inverts H6.
      inverts typ2. inverts H10. inverts H2. inverts H9.
      inverts H2. inverts H6; inverts H5. inverts H.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      inverts H2. inverts H9. inverts H2. inverts H10.
      inverts H2; inverts H8. inverts H6. inverts H.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto. 
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto. 
      inverts ep.
      inverts typ2. inverts H10. inverts H2. inverts H9.
      inverts H2. inverts H6; inverts H5; inverts H.
      destruct(sim_decidable (t_arrow A1 B0) (t_arrow C0 D0)).
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      inverts H2. inverts H9. inverts H2. inverts H10. inverts H2.
      inverts H8; inverts H6; inverts H.
      destruct(sim_decidable (t_arrow A1 B0) (t_arrow C0 D0)).
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      inverts H8. 
      inverts typ2. inverts H11. inverts H2. inverts H10.
      inverts H2. inverts H8; inverts H6. inverts H.
      destruct(sim_decidable (t_arrow A1 B0) (t_arrow C0 D0)).
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      inverts H2. inverts H10. inverts H2. inverts H11.
      inverts H2. inverts H9; inverts H8; inverts H.
      destruct(sim_decidable (t_arrow A1 B0) (t_arrow C0 D0)).
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      inverts typ2. inverts H13. inverts H0. inverts H10.
      inverts H0. inverts H6; inverts H2. inverts H.
      destruct(sim_decidable (t_arrow A3 B3) (t_arrow C0 D0)).
      exists. split. apply star_one. 
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H0.
      apply ep_annol; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H0.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H0.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      inverts H0. inverts H10. inverts H0. inverts H13.
      inverts H0. inverts H8; inverts H6; inverts H.
      destruct(sim_decidable (t_arrow A3 B3) (t_arrow C0 D0)).
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H0.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H0.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_saver; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H.
      exists. split. apply star_one. apply Step_annov; eauto.
      apply ep_annol; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      forwards*: epre_lc H.
      exists. split. apply step_refl; eauto.
      apply ep_anno; eauto.
      assert(epre (e_abs A1 e0 B0) (e_abs A3 e2 B3)); eauto.
      inverts ep. inverts typ2. inverts H9. inverts H1. inverts H3;inverts H.
      inverts H11. inverts H12.
      destruct(sim_decidable (t_arrow A B1) (t_arrow C0 D)).
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      inverts H11. inverts H12.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts H1. inverts H8. inverts H1. inverts H12. inverts H13. inverts H6.
      destruct(sim_decidable (t_arrow A2 B) (t_arrow C D)).
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. inverts H. apply ep_saver; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts typ2. inverts H11. inverts H0. inverts H13;inverts H14.
      inverts H1. inverts H.
      destruct(sim_decidable (t_arrow A1 B) (t_arrow C0 D0)).
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts H0. inverts H10. inverts H0. inverts H14. inverts H15. inverts H3. inverts H.
      destruct(sim_decidable (t_arrow A2 B) (t_arrow C0 D0)).
      forwards*: value_lc H2.  forwards*: value_lc H2. inverts H3.
      forwards*: epre_lc H9. exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      forwards*: value_lc H2. inverts H3. forwards*: epre_lc H9.
      exists. split. apply star_one.  apply Step_annov; eauto.  apply ep_saver; eauto.
      forwards*: value_lc H2. inverts H3. forwards*: epre_lc H9.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts typ1. inverts H10. inverts H0. inverts H9. inverts H0. inverts H13;inverts H14.
      inverts H8. inverts H7. 
      exists. split. apply step_refl; eauto. apply ep_anno; eauto.
      inverts typ2. inverts H9. inverts H7. inverts H8. inverts H.
      destruct(sim_decidable (t_arrow A B1) (t_arrow C D0)).
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts H7. inverts typ2. 
      assert(epre (e_abs A e1 B1) (e_abs A2 e3 B3)); eauto.
      inverts typ2. inverts H8. inverts H6. inverts H7. inverts H.
      destruct(sim_decidable (t_arrow A2 B3) (t_arrow C D0)).
      assert(epre (e_abs A e1 B1) (e_abs A2 e3 B3)); eauto. forwards*: epre_lc H6.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      assert(epre (e_abs A e1 B1) (e_abs A2 e3 B3)); eauto. forwards*: epre_lc H6.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      assert(epre (e_abs A e1 B1) (e_abs A2 e3 B3)); eauto. forwards*: epre_lc H6.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts H0. inverts H9. inverts H0. inverts H10. inverts H0. inverts H14; inverts H15.
      inverts H8. inverts H7. 
      exists. split. apply step_refl; eauto. apply ep_anno; eauto.
      inverts typ2. inverts H7. inverts H15. inverts H7. inverts H10; inverts H.
      destruct(sim_decidable (t_arrow A B1) (t_arrow C D0)).
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      inverts H7. exists. split. apply step_refl; eauto. apply ep_anno; eauto.
      inverts typ2. inverts H7. inverts H19. inverts H7.
      inverts H9; inverts H.
      destruct(sim_decidable (t_arrow A3 B3) (t_arrow C D0)).
      assert(epre (e_abs A e1 B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H7.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
      assert(epre (e_abs A e1 B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H7.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_saver; eauto.
      assert(epre (e_abs A e1 B1) (e_abs A3 e3 B3)); eauto. forwards*: epre_lc H.
      exists. split. apply star_one.  apply Step_annov; eauto. apply ep_annol; eauto.
    + inverts* H4.
  - inverts* red.
    + destruct E; unfold simpl_fill in H1; inverts* H1.
    + inverts typ2. inverts H8; inverts ep.
      forwards*: step_not_value H4.
      assert(epre (e_abs A1 e0 B1) (e_abs A0 e B0)); eauto. forwards*: epre_lc2 H2.
      forwards*: step_not_value H4.
      inverts H1.
      inverts H10; inverts ep.
      forwards*: step_not_value H4.
      forwards*: step_not_value H4.
      assert(epre (e_abs A1 e0 B1) (e_abs A0 e B0)); eauto. forwards*: epre_lc2 H3.
    + inverts* typ2. inverts H8. inverts ep.
      inverts H5. inverts H11. simpl in H13.
      assert(tpre (t_arrow A0 B0) (t_arrow A0 B0)). apply tpre_refl.
      assert(tpre (t_arrow A B) (t_arrow C D)). eauto.
      forwards*: epre_sim H13 H4 H5.
      exists. split. apply step_refl; eauto. apply ep_save; eauto.
      inverts H5. inverts H11.
      simpl in H15.
      assert(tpre (t_arrow A1 B1) (t_arrow A0 B0)). eauto.
      assert(tpre (t_arrow A B) (t_arrow C D)). eauto.
      forwards*: epre_sim H15 H2 H4.
      exists. split. apply step_refl; eauto. apply ep_save; eauto.
      inverts H1. inverts H10.
      inverts ep.
      inverts H5. inverts H11.
      simpl in H14.
      assert(tpre (t_arrow A0 B0) (t_arrow A0 B0)). apply tpre_refl.
      assert(tpre (t_arrow A B) (t_arrow C D)). eauto.
      forwards*: epre_sim H14 H5 H6.
      exists. split. apply step_refl; eauto. apply ep_save; eauto.
      inverts H5. inverts H11.
      simpl in H16.
      assert(tpre (t_arrow A1 B1) (t_arrow A0 B0)). eauto.
      assert(tpre (t_arrow A B) (t_arrow C D)). eauto.
      forwards*: epre_sim H16 H4 H5.
      exists. split. apply step_refl; eauto. apply ep_save; eauto.
Qed.

Lemma dynamic_guarantees_test: forall e1 e2 dir m1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value m1 ->
 e1 ->* (Expr m1) ->
 exists m2, value m2 /\ e2 ->* (Expr m2) /\ epre m1 m2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  - forwards*: val_prel ep.
  - forwards*: dynamic_guarantee_dir_test ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: preservation H.
    forwards*: preservation_multi_step H0.
    forwards*: IHred val H2 H1 H3.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    apply star_trans with (b := x).
    apply H0.
    apply H5. auto.
Qed.


