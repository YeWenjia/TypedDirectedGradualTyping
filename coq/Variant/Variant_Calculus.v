Require Import LibTactics.
Require Import Metalib.Metatheory.

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


Lemma fill_appl : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma fill_anno : forall e A,
  (e_anno e A) = (fill (annoCtx A) e).
Proof.
  intros. eauto.
Qed.



Theorem variant_calculus: forall e dir A,
 gtyping nil (trans e) dir A -> step e Blame 
 -> (trans e) ->** Blame.
Proof with eauto.
  introv Typ Red. gen dir A.
    inductions Red; intros; eauto; unfold trans; simpl;
    forwards*: gtyping_regular_1 Typ; fold trans.
  - destruct E; unfold simpl_fill in *; inverts* Typ.
    + forwards*: IHRed H4. inverts H0.
      apply multi_blame_app2...
    + inverts* H0. inverts H1. forwards*: IHRed H7. inverts H. 
      apply multi_blame_app2 ...
    + forwards*: IHRed H7. inverts H.
      inverts* H3.
      * inverts H4. inverts H3. inverts H; inverts H2.
      * inverts H4. inverts H5. inverts H2; inverts H3. inverts H0.
        inverts H4.
        apply multi_blame_app ...
        eapply gvalue_fanno ... simpl ...
      * inverts H4. inverts H8. inverts H2. unfold trans; simpl.
        inverts H0. inverts H5. inverts H2. inverts H.
        fold trans. unfold trans in H4. fold trans in H4.
        apply multi_blame_app ...
        eapply gvalue_fanno ... eapply gvalue_fanno ...
        simpl; eauto. simpl ...
    + inverts* H0. inverts H1. forwards*: IHRed H8. inverts H.
      unfold trans. fold trans.
      inverts* H3.
      * inverts H7. inverts H3. inverts H; inverts H1.
      * inverts H7. inverts H4. inverts H1; inverts H3.
        unfold trans in H5.  fold trans in H5. inverts H5.
        apply multi_blame_app; eauto. 
        eapply gvalue_fanno; eauto. simpl; eauto.
      * inverts H7. inverts H10. inverts H1. unfold trans; simpl.
        inverts H5. inverts H4.  inverts H.
        fold trans. unfold trans in H5. fold trans in H5.
        apply multi_blame_app; eauto.
        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto.
        simpl; eauto. simpl; eauto.
    + inverts* H1.
    + inverts* H1.
  - inverts* Typ. forwards*: IHRed H6. 
    + apply multi_blame_anno; eauto.
    + inverts H1. forwards*: IHRed H5. 
      apply multi_blame_anno; eauto.
  - inverts H1. 
    + inverts H9.
      * lets Typ': Typ. inverts Typ. 
        ** inverts H12.
           inverts H6. inverts H7.
           *** inverts H1. inverts H10. inverts H1. inverts H6.
               inverts H14. inverts H9. inverts H12. inverts H1.
               inverts H6. exfalso. apply H8. apply BA_AB. auto.
               eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. inverts H9.
               forwards*: gtyping_regular_1 H12.
               eapply gvalue_fanno; eauto. reflexivity.
               unfold trans. apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H9. forwards*: gtyping_regular_1 H12.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_v; auto. eapply gstep_b. rewrite fill_anno.
               apply gblame_step; eauto.  apply gStep_betap; eauto. inverts H9.
               forwards*: gtyping_regular_1 H12. apply gTReduce_blame; eauto.
               simpl. unfold not; intros. apply H8. apply BA_AB; auto.
               unfold trans; simpl; fold trans. inverts H14.
               inverts H9. inverts H12. inverts H1. inverts H6.
               exfalso. apply H8. apply BA_AB; auto.
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H9. forwards*: gtyping_regular_1 H12.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_dd ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H9. forwards*: gtyping_regular_1 H12.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H8.
               apply BA_AB ...
           *** inverts H0. inverts H7.
           *** inverts H7. unfold trans. fold trans. inverts H13.
               inverts H9. inverts H14. inverts H6; inverts H7. inverts H13.
               inverts H9. forwards*: gtyping_regular_1 H11. 
               inverts H1. inverts H9. forwards*: gtyping_regular_1 H1. 
               inverts H1; inverts H7.
               destruct (eq_type C). destruct (eq_type D). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_v; eauto.  eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  reflexivity. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

               destruct (eq_type A4). destruct (eq_type B). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_dd; eauto.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H7. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H1. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               unfold trans in *; simpl; fold trans in *.

               inverts H9. inverts H1.  inverts H4.
               inverts H12. inverts H1. inverts H4. inverts H12.  
               forwards*: gtyping_regular_1 H12. inverts H1.
               destruct (eq_type A1). destruct (eq_type B0). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               forwards*: gtyping_regular_1 H8. inverts H1.
               eapply gTReduce_v; eauto. forwards*: gtyping_regular_1 H8. inverts H1.
               eapply gvalue_fanno ... eapply gvalue_fanno ...
               reflexivity. reflexivity.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn ...
               forwards*: gtyping_regular_1 H8. inverts H1.
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               forwards*: gtyping_regular_1 H12. eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H4. reflexivity.
               forwards*: gtyping_regular_1 H8. inverts H7.
               simpl. eauto. forwards*: gtyping_regular_1 H8. inverts H7.
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... forwards*: gtyping_regular_1 H8. inverts H7.
               eapply gvalue_fanno ... forwards*: gtyping_regular_1 H8. inverts H7.
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               forwards*: gtyping_regular_1 H12. eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
               forwards*: gtyping_regular_1 H8. inverts H4.
               simpl. eauto. forwards*: gtyping_regular_1 H8. inverts H4.
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... forwards*: gtyping_regular_1 H8. inverts H4.
               eapply gvalue_fanno ... forwards*: gtyping_regular_1 H8. inverts H4.
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.  
        ** inverts H6. inverts H7.
           *** inverts H1. inverts H11. inverts H1. inverts H11.
               inverts H1. inverts H7. inverts H6. inverts H13.
               inverts H10. inverts H11. inverts H1. inverts H6. exfalso. apply H8. apply BA_AB. auto.
               eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. inverts H10. 
               apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. 
               apply gTReduce_v; auto. eapply gstep_b. rewrite fill_anno.
               apply gblame_step; eauto.  apply gStep_betap; eauto. inverts H10.
               apply gTReduce_blame; eauto.
               simpl. unfold not; intros. apply H8. apply BA_AB; auto.
               unfold trans; simpl; fold trans. inverts H13.
               inverts H10.  eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. inverts H10.
               forwards*: gtyping_regular_1 H11. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. forwards*: gtyping_regular_1 H11.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_v ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H10. forwards*: gtyping_regular_1 H11.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H8.
               apply BA_AB ...
               unfold trans; simpl; fold trans. inverts H13.
               inverts H10.  inverts H13. inverts H1; inverts H7. 
               exfalso. apply H8. apply BA_AB; auto.
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. forwards*: gtyping_regular_1 H13.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_dd ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H10. forwards*: gtyping_regular_1 H13.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H8.
               apply BA_AB ...
           *** inverts H0. inverts H7.
           *** inverts H7. inverts H1. inverts H9. inverts H13.
               forwards*: gtyping_regular_1 H1. inverts H10. inverts H8.
               forwards*: gtyping_regular_1 H14. 
               inverts H1. inverts H12. inverts H6. inverts H15.
               inverts H14. inverts H1. inverts H10. 
               destruct (eq_type C). destruct (eq_type D). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_v; eauto.  eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  reflexivity. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

               destruct (eq_type A3). destruct (eq_type B). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_dd; eauto. unfold trans. apply gvalue_dyn; eauto.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H13. apply H10. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H12.  apply H1. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               unfold trans in *; simpl; fold trans in *.

               inverts H10. inverts H1.  inverts H10.
               inverts H12. inverts H1. inverts H10. inverts H1. inverts H13.
               inverts H1; inverts H9. inverts H14. inverts H1. inverts H10.
               inverts H9. inverts H1. inverts H9. inverts H1.   
               forwards*: gtyping_regular_1 H12. forwards*: gtyping_regular_1 H10.
               destruct (eq_type A1). destruct (eq_type B0). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_v; eauto.  
               eapply gvalue_fanno ... eapply gvalue_fanno ...
               reflexivity. reflexivity.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn ...
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H11. reflexivity.
               simpl. eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... 
               eapply gvalue_fanno ... 
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               forwards*: gtyping_regular_1 H12. eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H9. reflexivity.
               simpl. eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... 
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt. 
      * inverts H11.
      * inverts Typ.  
        ** inverts H12.
           inverts H8. inverts H7.
           *** inverts H9. inverts H12. 
               inverts H1. inverts H11. inverts H1. inverts H9. 
               forwards*: gtyping_regular_1 H7.
               inverts H3; inverts H7.
                inverts H8. exfalso. apply H4. apply BA_AB; auto. 
               eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno ... reflexivity.
               apply gTReduce_v; auto. eapply gstep_b. rewrite fill_anno.
               apply gblame_step; eauto.  apply gStep_betap; eauto. 
               apply gTReduce_blame; eauto.
               simpl. unfold not; intros. apply H4. apply BA_AB; auto.
               unfold trans; simpl; fold trans. inverts H7. inverts H14.
               inverts H8. exfalso. apply H4. apply BA_AB; auto.
               eapply gstep_nb. apply gStep_abeta; eauto. inverts H2. inverts H9.
               eapply gvalue_fanno ... reflexivity.
               apply gTReduce_dd ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H2. inverts H9.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H4.
               apply BA_AB ...
          *** inverts H0. inverts H8.
          *** inverts H7. inverts H1. inverts H9. inverts H13.
              forwards*: gtyping_regular_1 H8. inverts H11. inverts H4. inverts H9.
              inverts H14.
              forwards*: gtyping_regular_1 H11. forwards*: gtyping_regular_1 H8.  
              inverts H8. inverts H7. inverts H9. inverts H11.
              inverts H7. inverts H8.  
              destruct (eq_type C). destruct (eq_type D). subst.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. simpl. reflexivity.
              eapply gTReduce_v; eauto.  eapply gvalue_fanno; eauto. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ...  reflexivity. 
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. simpl. reflexivity.
              eapply gTReduce_anyd; eauto. unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
              simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. simpl. reflexivity.
              eapply gTReduce_anyd; eauto. unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
              simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

              destruct (eq_type A4). destruct (eq_type B). subst.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. simpl. reflexivity.
              eapply gTReduce_dd; eauto. unfold trans. apply gvalue_dyn; eauto.  
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. 
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
              apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H8. reflexivity. 
              eapply gstep_nb ... simpl.
              apply gStep_abeta; eauto.
              eapply gvalue_fanno ... simpl. reflexivity.
              eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
              eapply gvalue_fanno ... simpl. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ... reflexivity.  
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
              apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H7. reflexivity. 
              eapply gstep_nb ... simpl.
              apply gStep_abeta; eauto.
              eapply gvalue_fanno ... simpl. reflexivity.
              eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
              eapply gvalue_fanno ... simpl. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ... reflexivity.  
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              unfold trans in *; simpl; fold trans in *.

              inverts H9. inverts H1.  inverts H8.
              inverts H12. inverts H1. inverts H12. 
              forwards*: gtyping_regular_1 H7. forwards*: gtyping_regular_1 H1.
              inverts H7. inverts H11. inverts H8. inverts H15.
              inverts H1; inverts H9. 
              destruct (eq_type A1). destruct (eq_type B0). subst.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. simpl. reflexivity.
              eapply gTReduce_v; eauto.  
              eapply gvalue_fanno ... eapply gvalue_fanno ...
              reflexivity. reflexivity.  
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn ...
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. reflexivity.
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H7. reflexivity.
              simpl. eauto. 
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ... 
              eapply gvalue_fanno ... 
              eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gstep_nb. apply gStep_abeta; eauto.
              eapply gvalue_fanno; eauto. reflexivity.
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
              simpl. eauto. 
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
              apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
              eapply gvalue_fanno ... eapply gvalue_fanno ... 
              eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
         ** inverts H8. inverts H7.
           *** inverts H1. inverts H11. inverts H1. inverts H11.
               inverts H1. inverts H8. inverts H7. inverts H13.
               inverts H10. inverts H11. inverts H1. inverts H7. exfalso. apply H4. apply BA_AB. auto.
               eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. inverts H10. 
               apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. 
               apply gTReduce_v; auto. eapply gstep_b. rewrite fill_anno.
               apply gblame_step; eauto.  apply gStep_betap; eauto. inverts H10.
               apply gTReduce_blame; eauto.
               simpl. unfold not; intros. apply H4. apply BA_AB; auto.
               unfold trans; simpl; fold trans. inverts H13.
               inverts H10.  eapply gstep_nb. rewrite fill_appr. 
               apply gdo_step. apply wf_appCtxR. inverts H10.
               forwards*: gtyping_regular_1 H11. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov; eauto.
               apply gTReduce_lit. unfold not; intros nt; inverts nt. simpl. 
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. forwards*: gtyping_regular_1 H11.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_v ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H10. forwards*: gtyping_regular_1 H11.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H4.
               apply BA_AB ...
               unfold trans; simpl; fold trans. inverts H13.
               inverts H10.  inverts H13. inverts H1; inverts H8. 
               exfalso. apply H4. apply BA_AB; auto.
               eapply gstep_nb. apply gStep_abeta; eauto.
               inverts H10. forwards*: gtyping_regular_1 H13.
               eapply gvalue_fanno; eauto. reflexivity.
               apply gTReduce_dd ... 
               eapply gstep_b. rewrite fill_anno. 
               apply gblame_step ...
               inverts H10. forwards*: gtyping_regular_1 H13.
               apply gStep_betap ... apply gTReduce_blame ...
               simpl. unfold not; intros. apply H4.
               apply BA_AB ...
           *** inverts H0. inverts H8.
           *** inverts H7. inverts H1. inverts H9. inverts H13.
               forwards*: gtyping_regular_1 H1. inverts H10. inverts H8.
               forwards*: gtyping_regular_1 H14. 
               inverts H1. inverts H12. inverts H4. inverts H15.
               inverts H14. inverts H1. inverts H10. 
               destruct (eq_type C). destruct (eq_type D). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_v; eauto.  eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  reflexivity. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_anyd; eauto. unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. eapply gvalue_fanno; eauto. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

               destruct (eq_type A3). destruct (eq_type B). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_dd; eauto. unfold trans. apply gvalue_dyn; eauto.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. 
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H13. apply H10. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H12.  apply H1. reflexivity. 
               eapply gstep_nb ... simpl.
               apply gStep_abeta; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gTReduce_dd; eauto. apply gvalue_dyn. eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... reflexivity.  
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               unfold trans in *; simpl; fold trans in *.

               inverts H10. inverts H1.  inverts H10.
               inverts H12. inverts H1. inverts H10. inverts H1. inverts H13.
               inverts H1; inverts H9. inverts H14. inverts H1. inverts H10.
               inverts H9. inverts H1. inverts H9. inverts H1.   
               forwards*: gtyping_regular_1 H12. forwards*: gtyping_regular_1 H10.
               destruct (eq_type A1). destruct (eq_type B0). subst.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_v; eauto.  
               eapply gvalue_fanno ... eapply gvalue_fanno ...
               reflexivity. reflexivity.  
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn ...
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H11. reflexivity.
               simpl. eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... 
               eapply gvalue_fanno ... 
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gstep_nb. apply gStep_abeta; eauto.
               forwards*: gtyping_regular_1 H12. eapply gvalue_fanno; eauto. reflexivity.
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H9. reflexivity.
               simpl. eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
               eapply gstep_b. rewrite fill_anno. apply gblame_step; eauto.
               apply gStep_betap; eauto. eapply gvalue_dyn; eauto. 
               eapply gvalue_fanno ... eapply gvalue_fanno ... 
               eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.   
    + inverts Typ.  
      ** inverts H10.
         inverts* H7.
          *** inverts H5. inverts H11. 
              inverts H1. inverts H10. inverts H1. inverts H8. 
              forwards*: gtyping_regular_1 H5. forwards*: gtyping_regular_1 H5.
              inverts H5; inverts H7.
              eapply gstep_b. unfold trans. fold trans. 
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... reflexivity.
              apply gTReduce_blame; eauto.
              simpl. unfold not; intros. apply H4. apply BA_AB; auto.
          *** inverts H1. forwards*: gtyping_regular_1 H8. inverts H5. 
               forwards*: gtyping_regular_1 H11. 
               inverts H11. inverts H5. inverts H8. inverts H5.
               inverts H9; inverts H3. 
               destruct (eq_type A4). destruct (eq_type B). subst.
               eapply gstep_b. apply gStep_abetap; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.   
               unfold trans. apply gvalue_dyn; eauto.  
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H5. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H5. reflexivity.
               fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gvalue_dyn; eauto.  
               eapply gvalue_fanno ... reflexivity.  
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H3. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H3. reflexivity.
               fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                eapply gvalue_dyn; eauto.  
               eapply gvalue_fanno ... reflexivity.   
      ** inverts* H7.
          *** inverts H1. inverts H10. inverts H1. inverts H9. 
              forwards*: gtyping_regular_1 H12. 
              inverts H10; inverts H5. exfalso. apply H4. eauto.
              inverts H7; inverts H8. 
              eapply gstep_b. unfold trans. fold trans. 
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... reflexivity.
              apply gTReduce_blame; eauto.
              simpl. unfold not; intros. apply H4. apply BA_AB; auto.
              exfalso. apply H4. eauto.
          *** inverts H1. inverts H8. forwards*: gtyping_regular_1 H10. 
              inverts H9. inverts H4. forwards*: gtyping_regular_1 H9. 
               inverts H10. inverts H7. inverts H8. inverts H9.
               inverts H7; inverts H8. inverts H5. 
               destruct (eq_type A3). destruct (eq_type B). subst.
               eapply gstep_b. apply gStep_abetap; eauto.
               eapply gvalue_fanno; eauto. simpl. reflexivity.
               eapply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.   
               unfold trans. apply gvalue_dyn; eauto.  
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H8. reflexivity.
               fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               eapply gvalue_dyn; eauto.  
               eapply gvalue_fanno ... reflexivity.  
               eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
               apply wf_appCtxR. eapply gvalue_fanno ... reflexivity.
               apply gStep_annov ...  
               eapply gTReduce_anyd ... unfold FLike. 
               split. unfold not; intros nt; inverts nt.
               split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
               simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H7. reflexivity.
               fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... simpl. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                eapply gvalue_dyn; eauto.  
               eapply gvalue_fanno ... reflexivity.
  - inverts* Typ. 
    * inverts* H0. 
      ** inverts H7. inverts H0. inverts H6. inverts H0.
         inverts H4.
         inductions A0.
         exfalso. apply H2; eauto. inverts H3.
         exfalso. apply H2; eauto.
         inductions A0.
         exfalso. apply H2; eauto. unfold trans. 
         eapply gstep_b.  apply gStep_annov; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt. inverts H8.
         exfalso. apply H2; eauto.
      ** inverts H7. inverts H0. inverts H5. inverts H0.
         inverts H3. inverts H2.
         destruct(eq_type A);  destruct(eq_type B); subst.
        unfold trans.
         inverts H1. inverts H3. 
         eapply gstep_b.  apply gStep_annov; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         unfold trans.
         inverts H1. inverts H4. 
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H3. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H4.
         simpl. inverts H1. inverts H4.
         apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         inverts H1. inverts H4.  
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H0. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H4.
         inverts H1. inverts H4.  
         simpl. apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         inverts H1. inverts H5.  
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H0. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H5.
         inverts H1. inverts H5.  
         simpl. apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
    * inverts H2. inverts* H0.
      ** inverts H6. inverts H0. inverts H7. inverts H0.
         inverts H5.
         inductions A1.
         exfalso. apply H2; eauto. inverts H4.
         exfalso. apply H2; eauto.
         inductions A1.
         exfalso. apply H2; eauto. unfold trans. 
         eapply gstep_b.  apply gStep_annov; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt. inverts H9.
         exfalso. apply H2; eauto.
      ** inverts H6. inverts H0. inverts H6. inverts H0.
         inverts H4. inverts H2.
         destruct(eq_type A);  destruct(eq_type B); subst.
         unfold trans.
         inverts H1. inverts H4. 
         eapply gstep_b.  apply gStep_annov; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         unfold trans.
         inverts H1. inverts H5. 
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H4. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H5.
         simpl. inverts H1. inverts H5.
         apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         inverts H1. inverts H5.  
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H0. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H5.
         inverts H1. inverts H5.  
         simpl. apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
         eapply gstep_nb. rewrite fill_anno.
         apply gdo_step; eauto.
         inverts H1. inverts H6.  
         apply gStep_annov; eauto.
         apply gTReduce_anyd. simpl. unfold FLike.
         split. unfold not; intros nt1; inverts nt1.
         split. unfold not; intros nt1; inverts nt1.
         apply H0. eauto. eauto.
         unfold not; intros nt1; inverts nt1. inverts* H6.
         inverts H1. inverts H6.  
         simpl. apply gstep_b. apply gStep_annov; eauto.
         apply gvalue_dyn; eauto. eapply gvalue_fanno; eauto.
         simpl; eauto.
         apply gTReduce_blame. 
         unfold not; intros nt; inverts nt.
         unfold not; intros nt; inverts nt.
  -  inverts H1.
      + inverts H9.
        * inverts H11.
          ** forwards*: TypedReduce_trans H7 H8.
             inverts Typ. inverts H15.
             *** inverts H12. inverts H16. inverts H11.
                 forwards*: gtyping_regular_1 H15.
                 inverts H9. inverts H1.
                 **** inverts H6. inverts H14. inverts H1; inverts H6. inverts H10.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_lit.  eauto.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_v ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_v.  eauto. eauto. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_dd ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      inverts H8; inverts H7; inverts H21.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_vany ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_v ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_dd ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_dd ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                 **** inverts H. inverts H9.
                 **** inverts H1. inverts H6. inverts H13. inverts H1; inverts H6; inverts H10.
                      -- unfold trans in *. fold trans in *. eapply gstep_nb. apply gStep_abeta ...
                          eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_abs ... eapply gvalue_fanno ... inverts H2. inverts H14. auto. reflexivity.
                          destruct (eq_type C0). destruct (eq_type D0). subst.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step... 
                          apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity. 
                          eapply gTReduce_v ... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                          reflexivity.  reflexivity.  eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. rewrite fill_anno.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                          simpl. eauto. inverts H2. inverts H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H22.
                          eapply gvalue_fanno... reflexivity.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. rewrite fill_anno.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts H21. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H21.
                          eapply gvalue_fanno... reflexivity.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                      -- destruct (eq_type C). destruct (eq_type D). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          eapply gTReduce_v ... inverts H2. inverts H10. eapply gvalue_fanno... 
                          reflexivity.  eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H10.
                          reflexivity. eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H10. reflexivity.
                          apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                          simpl. eauto. inverts H2. inverts H19. eapply gvalue_fanno... reflexivity.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H19.
                          reflexivity. reflexivity.  apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts H14. eapply gvalue_fanno... reflexivity.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H14. eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                          reflexivity. reflexivity.  apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                      -- inverts H8;  inverts H7; inverts H16.
                         ++ destruct (eq_type A2). destruct (eq_type B). subst.
                            destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H16.  eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H16.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H16. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt. 
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H21.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H21. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H19.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H21. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H16. apply H7. reflexivity.
                            simpl. destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H19.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H16. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H16. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H19. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H1. reflexivity.
                            simpl. destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H19.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            ++ destruct (eq_type A2). destruct (eq_type B). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H9. apply gvalue_dyn; eauto.  inverts H2. inverts* H9.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H9. apply gvalue_dyn; eauto.  inverts H2. inverts* H9.
                            eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H9. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. apply gStep_annov ... inverts H2. inverts* H16.  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H7. reflexivity. 
                            eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  inverts H2. inverts* H16.
                            eapply gvalue_fanno ... reflexivity.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  inverts H2. inverts* H16.
                            eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. apply gstep_b...  
                            apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity.
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. apply gStep_annov ... inverts H2. inverts* H10.  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H1. reflexivity. 
                            eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  inverts H2. inverts* H10.
                            eapply gvalue_fanno ... reflexivity.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  inverts H2. inverts* H10.
                            eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. apply gstep_b...  
                            apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H10. eapply gvalue_fanno ... reflexivity.
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                        ++ destruct (eq_type A2). destruct (eq_type B). subst.
                          destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H9.  eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H9.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H9. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H16.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H16. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H13.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H13. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H16. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H7. reflexivity.
                          simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H13.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H13. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H1. reflexivity.
                          simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H13.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                      -- destruct (eq_type A2). destruct (eq_type B). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H10.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H10.
                          eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. 
                          inverts H2. inverts* H10. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H14.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H6. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H14. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H14.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H14. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H14.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H14. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H13.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H1. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                          inverts H2. inverts* H13.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H13.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                      -- inverts H6; inverts H10.
                         ++ unfold trans in *. fold trans in *.
                            eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            reflexivity. reflexivity. eapply gTReduce_abs ... eapply gvalue_fanno ... 
                            inverts H2. inverts* H14. inverts H2.  eapply gvalue_fanno ...  reflexivity. reflexivity.
                            rewrite fill_anno. destruct (eq_type C). destruct (eq_type D). subst.  
                            eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                            eapply gTReduce_v ... eapply gvalue_fanno ... eapply gvalue_fanno ... 
                            inverts H2. inverts H14. 
                            inverts H2. eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                            rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                            apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            eapply gvalue_fanno ...  inverts H2. inverts H14.  inverts* H2. reflexivity. reflexivity. reflexivity.
                            apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                            eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                            eapply gTReduce_anyd... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                            simpl. eauto.  
                            inverts H2. inverts H19. 
                            inverts H10. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                            rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                            apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            eapply gvalue_fanno ...  inverts H2. inverts H19.  inverts* H10. eapply gvalue_fanno ...
                            reflexivity. reflexivity. reflexivity. reflexivity.
                            apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                            eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                            eapply gTReduce_anyd... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto.  
                            inverts H2. inverts H18. 
                            inverts H6. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                            rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                            apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            eapply gvalue_fanno ...  inverts H2. inverts H18.  inverts* H6. eapply gvalue_fanno ...
                            reflexivity. reflexivity. reflexivity. reflexivity.
                            apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                         ++ unfold trans in *. fold trans in *.
                            destruct (eq_type A1). destruct (eq_type B0). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_v; eauto. eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H10. inverts* H2. reflexivity. reflexivity. 
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                            apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                            inverts H2. inverts H10. inverts* H2.  eapply gvalue_fanno ... reflexivity. reflexivity.
                            rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                            apply gStep_betap; eauto.
                            eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H10. inverts* H2. reflexivity. reflexivity. 
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H6. reflexivity.
                            simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H17. inverts* H9. reflexivity. reflexivity. 
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                            apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                            inverts H2. inverts H17. inverts* H9.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                            rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                            apply gStep_betap; eauto.
                            eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H17. inverts* H9. reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
                            simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H14. inverts* H6. reflexivity. reflexivity. 
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                            apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                            inverts H2. inverts H14. inverts* H6.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                            rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                            apply gStep_betap; eauto.
                            eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                            inverts H2. inverts H14. inverts* H6. reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.  
             *** inverts H6. inverts H14. inverts H16. inverts H6.
                 forwards*: gtyping_regular_1 H14.
                 inverts H9. inverts H1.
                 **** inverts H15. inverts H1. inverts H16. inverts H1; inverts H13. inverts H9. 
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_lit.  eauto.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_v ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_v.  eauto. eauto. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_dd ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      inverts H8; inverts H7; inverts H22.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_vany ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_v ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_dd ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_dd ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                 **** inverts H. inverts H9.
                 **** inverts H1. inverts H15. inverts H1. inverts H15. inverts H1; inverts H12; inverts H9.
                      --  unfold trans in *. fold trans in *. eapply gstep_nb. apply gStep_abeta ...
                          eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_abs ... eapply gvalue_fanno ... 
                          inverts H2. inverts* H16.  reflexivity.
                          destruct (eq_type C0). destruct (eq_type D0). subst.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step... 
                          apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity. 
                          eapply gTReduce_v ... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H16.
                          reflexivity.  reflexivity.  eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H16.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. rewrite fill_anno.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto. inverts H2. inverts H23. eapply gvalue_fanno... eapply gvalue_fanno... 
                          reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H23.
                          eapply gvalue_fanno... reflexivity.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. rewrite fill_anno.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H22.
                          eapply gvalue_fanno... reflexivity.
                          reflexivity. reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                      -- 
                          destruct (eq_type C). destruct (eq_type D). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          eapply gTReduce_v ... inverts H2. inverts H13. eapply gvalue_fanno... 
                          reflexivity.  eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H13.
                          reflexivity. eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H13. reflexivity.
                          apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto. inverts H2. inverts H20. eapply gvalue_fanno... reflexivity.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... 
                          inverts H2. inverts* H20. eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H20.
                          reflexivity. reflexivity.  apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts H16. eapply gvalue_fanno... reflexivity.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                          eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H16. eapply gvalue_fanno... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                          inverts H2. inverts* H16.
                          reflexivity. reflexivity.  apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                      -- 
                          inverts H8;  inverts H7; inverts H19.
                          ++ destruct (eq_type A2). destruct (eq_type B). subst.
                            destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H19.  eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                            inverts H2. inverts* H19.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt. 
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H22.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H22. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H20.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H20. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H22. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H19. apply H7. reflexivity.
                            simpl. destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H20.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H19. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H24. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H19. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H24. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H24. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H20. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H1. reflexivity.
                            simpl. destruct (eq_type C). destruct (eq_type D). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H20.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            ++ destruct (eq_type A2). destruct (eq_type B). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H12. apply gvalue_dyn; eauto.  
                            inverts H2. inverts* H12.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H12. apply gvalue_dyn; eauto.  
                            inverts H2. inverts* H12.
                            eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H12. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. apply gStep_annov ... inverts H2. inverts* H19.  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt.
                             inverts H12. apply H7. reflexivity. 
                            eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H19. apply gvalue_dyn; eauto. 
                             inverts H2. inverts* H19.
                            eapply gvalue_fanno ... reflexivity.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H19. apply gvalue_dyn; eauto.  
                            inverts H2. inverts* H19.
                            eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. apply gstep_b...  
                            apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. apply gStep_annov ... inverts H2. inverts* H13.  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H1. reflexivity. 
                            eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                             inverts H2. inverts* H13.
                            eapply gvalue_fanno ... reflexivity.
                            eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                             inverts H2. inverts* H13.
                            eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. apply gstep_b...  
                            apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                            eapply gvalue_dyn; eauto. inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                            apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                        ++ destruct (eq_type A2). destruct (eq_type B). subst.
                            destruct (eq_type A1). destruct (eq_type B0). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H12.  eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                            inverts H2. inverts* H12.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H12. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt. 
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... 
                            inverts H2. inverts* H19.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H15.
                            eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. inverts H2. inverts* H15. eapply gvalue_fanno... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                            apply gTReduce_blame. unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H19. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H8. reflexivity.
                            simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H15.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                            inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                            apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                            reflexivity. inverts H2. inverts H15. apply gStep_annov ...  
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                            simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H1. reflexivity.
                            simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            unfold trans in *. fold trans in *.
                            apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                            inverts H2. inverts* H15.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                            apply gdo_step; eauto. apply gStep_abeta ... 
                            eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.  
                            
                            eapply gstep_nb. apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                            eapply gTReduce_dyna ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                            simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. 
                            rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                            eapply gvalue_fanno; eauto. reflexivity. 
                            eapply gTReduce_anyd ... unfold FLike. 
                            split. unfold not; intros nt; inverts nt.
                            split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                            simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. reflexivity.
                            eapply gstep_b. rewrite fill_anno.
                            apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                            apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                            apply gTReduce_blame.
                            unfold not; intros nt; inverts nt.
                      -- destruct (eq_type A2). destruct (eq_type B). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H13.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H13.
                          eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. 
                          inverts H2. inverts* H13. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H16.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. 
                          inverts H13. apply H9. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H16.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H16.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H15.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H1. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H15. apply gvalue_dyn; eauto. 
                          inverts H2. inverts* H15.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H15. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H15.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                      -- inverts H15. inverts H1; inverts H9.
                         ++ 
                          unfold trans in *. fold trans in *.
                          eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          reflexivity. reflexivity. eapply gTReduce_abs ... eapply gvalue_fanno ... 
                          inverts H2. inverts* H17. inverts H2.  eapply gvalue_fanno ...  reflexivity. reflexivity.
                          rewrite fill_anno. destruct (eq_type C). destruct (eq_type D). subst.  
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_v ... eapply gvalue_fanno ... eapply gvalue_fanno ... 
                          inverts H2. inverts H17. 
                          inverts H2. eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H17.  inverts* H2. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H20. 
                          inverts H12. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H20.  inverts* H12. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H19. 
                          inverts H9. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H19.  inverts* H9. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                       ++ 
                          unfold trans in *. fold trans in *.
                          destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_v; eauto. eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2.  eapply gvalue_fanno ... reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H9. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H9. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H9.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H9. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt. 
          ** inverts H13.
          ** forwards*: TypedReduce_trans H7 H8.
             inverts Typ. inverts H15.
             *** inverts H12. inverts H16. inverts H11.
                 forwards*: gtyping_regular_1 H15.
                 inverts H10. inverts H1.
                 **** inverts H3. inverts H14. inverts H1; inverts H3. inverts H6.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_lit.  eauto.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_v ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_v.  eauto. eauto. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_dd ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      inverts H8; inverts H7; inverts H21.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_vany ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_v ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_dd ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_dd ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H13. apply BA_AB; auto.
                 **** inverts H. inverts H10.
                 **** inverts H1. inverts H3. inverts H13. inverts H1; inverts H3; inverts H6.
                      -- unfold trans in *. fold trans in *. eapply gstep_nb. apply gStep_abeta ...
                      eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      eapply gTReduce_abs ... eapply gvalue_fanno ... inverts H2. inverts H14. auto. reflexivity.
                      destruct (eq_type C0). destruct (eq_type D0). subst.
                      eapply gstep_nb. rewrite fill_anno. apply gdo_step... 
                      apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity. 
                      eapply gTReduce_v ... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                      reflexivity.  reflexivity.  eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                      reflexivity. reflexivity. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt. rewrite fill_anno.
                      eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H3. reflexivity. 
                      simpl. eauto. inverts H2. inverts H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H22.
                      eapply gvalue_fanno... reflexivity.
                      reflexivity. reflexivity. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt. rewrite fill_anno.
                      eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                      simpl. eauto. inverts H2. inverts H21. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H21.
                      eapply gvalue_fanno... reflexivity.
                      reflexivity. reflexivity. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.
                      -- destruct (eq_type C). destruct (eq_type D). subst.
                      eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                      eapply gTReduce_v ... inverts H2. inverts H10. eapply gvalue_fanno... 
                      reflexivity.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                      eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H10.
                      reflexivity. eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H10. reflexivity.
                      apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                      eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H3. reflexivity. 
                      simpl. eauto. inverts H2. inverts H19. eapply gvalue_fanno... reflexivity.
                      eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                      eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H19.
                      reflexivity. reflexivity.  apply gTReduce_blame.
                      unfold not; intros nt; inverts nt. 
                      eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                      simpl. eauto. inverts H2. inverts H14. eapply gvalue_fanno... reflexivity.
                      eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                      eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H14. eapply gvalue_fanno... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... inverts H2. inverts* H14.
                      reflexivity. reflexivity.  apply gTReduce_blame.
                      unfold not; intros nt; inverts nt. 
                      -- inverts H8;  inverts H7; inverts H16.
                      ++ destruct (eq_type A2). destruct (eq_type B). subst.
                      destruct (eq_type C). destruct (eq_type D). subst.
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      unfold trans in *. fold trans in *.
                      apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                      inverts H2. inverts* H16.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H16.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H16. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt. 
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      unfold trans in *. fold trans in *.
                      apply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                      simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H21.
                      eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                      simpl. eauto. inverts H2. inverts* H21. eapply gvalue_fanno... reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                      apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                      
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      unfold trans in *. fold trans in *.
                      apply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                      simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H19.
                      eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                      simpl. eauto. inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                      apply gTReduce_blame. unfold not; intros nt; inverts nt.
                      
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                      reflexivity. inverts H2. inverts H21. apply gStep_annov ...  
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                      simpl. eauto. unfold not; intros nt; inverts nt. inverts H16. apply H6. reflexivity.
                      simpl. destruct (eq_type C). destruct (eq_type D). subst.
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      unfold trans in *. fold trans in *.
                      apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                      inverts H2. inverts* H19.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.  
                      
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      eapply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H16. reflexivity. 
                      simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                      rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. reflexivity. 
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H16. reflexivity. 
                      simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                      apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.  
                      
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      eapply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                      simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                      rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. reflexivity. 
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                      simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                      apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.
                      
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                      reflexivity. inverts H2. inverts H19. apply gStep_annov ...  
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                      simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H1. reflexivity.
                      simpl. destruct (eq_type C). destruct (eq_type D). subst.
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      unfold trans in *. fold trans in *.
                      apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                      inverts H2. inverts* H19.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step; eauto. apply gStep_abeta ... 
                      eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.
                      
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      eapply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                      simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                      rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. reflexivity. 
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                      simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                      apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.  
                      
                      eapply gstep_nb. apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                      eapply gTReduce_dyna ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                      simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                      rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                      eapply gvalue_fanno; eauto. reflexivity. 
                      eapply gTReduce_anyd ... unfold FLike. 
                      split. unfold not; intros nt; inverts nt.
                      split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                      simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                      eapply gstep_b. rewrite fill_anno.
                      apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                      apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                      apply gTReduce_blame.
                      unfold not; intros nt; inverts nt.
                      ++ destruct (eq_type A2). destruct (eq_type B). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H8. apply gvalue_dyn; eauto.  inverts H2. inverts* H8.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H8. apply gvalue_dyn; eauto.  inverts H2. inverts* H8.
                        eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H8. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H16.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H6. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  inverts H2. inverts* H16.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  inverts H2. inverts* H16.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H10.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H7. apply H1. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  inverts H2. inverts* H10.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  inverts H2. inverts* H10.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H10. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                        ++ destruct (eq_type A2). destruct (eq_type B). subst.
                        destruct (eq_type A1). destruct (eq_type B0). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        unfold trans in *. fold trans in *.
                        apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                        inverts H2. inverts* H8.  eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H8.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H8. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt. 
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        unfold trans in *. fold trans in *.
                        apply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H16.
                        eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto. inverts H2. inverts* H16. eapply gvalue_fanno... reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                        apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                        
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        unfold trans in *. fold trans in *.
                        apply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H13.
                        eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. inverts H2. inverts* H13. eapply gvalue_fanno... reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                        apply gTReduce_blame. unfold not; intros nt; inverts nt.
                        
                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. inverts H2. inverts H16. apply gStep_annov ...  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H6. reflexivity.
                        simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        unfold trans in *. fold trans in *.
                        apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                        inverts H2. inverts* H13.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.  
                        
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                        simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                        simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                        apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.  
                        
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                        simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                        simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                        apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.
                        
                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. inverts H2. inverts H13. apply gStep_annov ...  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H7. apply H1. reflexivity.
                        simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        unfold trans in *. fold trans in *.
                        apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                        inverts H2. inverts* H13.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.
                        
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                        simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                        simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H21. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H21. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                        apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.  
                        
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dyna ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H6. reflexivity. 
                        simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... inverts H2. inverts* H16. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                        apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.
                        -- destruct (eq_type A2). destruct (eq_type B). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H10.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H10. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H10.
                        eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. 
                        inverts H2. inverts* H10. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
  
                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H14.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H3. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H3. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H14. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H14.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H14. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H14.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H14. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
  
                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H13.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H6. apply H1. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                         inverts H2. inverts* H13.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H13.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                      -- inverts H3; inverts H6.
                          ++ unfold trans in *. fold trans in *.
                          eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          reflexivity. reflexivity. eapply gTReduce_abs ... eapply gvalue_fanno ... 
                          inverts H2. inverts* H14. inverts H2.  eapply gvalue_fanno ...  reflexivity. reflexivity.
                          rewrite fill_anno. destruct (eq_type C). destruct (eq_type D). subst.  
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_v ... eapply gvalue_fanno ... eapply gvalue_fanno ... 
                          inverts H2. inverts H14. 
                          inverts H2. eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H14.  inverts* H2. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H3. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H19. 
                          inverts H6. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H19.  inverts* H6. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H18. 
                          inverts H3. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H18.  inverts* H3. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          ++ unfold trans in *. fold trans in *.
                          destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_v; eauto. eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H10. inverts* H2. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H10. inverts* H2.  eapply gvalue_fanno ... reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H10. inverts* H2. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H3. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H6. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H6.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H6. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H14. inverts* H3. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H14. inverts* H3.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H14. inverts* H3. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt. 
             *** inverts H3. inverts H14. inverts H16. inverts H3.
                 forwards*: gtyping_regular_1 H14.
                 inverts H10. inverts H1.
                 **** inverts H15. inverts H1. inverts H16. inverts H1; inverts H13. inverts H10.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_lit.  eauto.  eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_v ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      eapply gstep_nb. rewrite fill_appr. apply gdo_step.
                      apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gStep_annov ... apply gTReduce_lit. unfold not; intros nt; inverts nt.
                      simpl. eapply gstep_nb. apply gStep_abeta. eapply gvalue_fanno ... eapply gvalue_fanno ...
                      reflexivity. reflexivity. apply gTReduce_v.  eauto. eauto. eapply gstep_nb. rewrite fill_anno.
                      apply gdo_step ... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                      apply gTReduce_dd ... rewrite fill_anno. apply gstep_b. apply gblame_step ...
                      apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      inverts H8; inverts H7; inverts H22.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_vany ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_v ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                      eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                      apply gTReduce_dd ... apply gvalue_dyn ... rewrite fill_anno. eapply gstep_nb. apply gdo_step ...
                      apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. apply gTReduce_dd ...
                      rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ... apply gStep_betap ... apply gTReduce_blame.
                      unfold not; intros nt. apply H12. apply BA_AB; auto.
                 **** inverts H. inverts H10.
                 **** inverts H1. inverts H15. inverts H1. inverts H15. inverts H1; inverts H12; inverts H10.
                      --  
                        unfold trans in *. fold trans in *. eapply gstep_nb. apply gStep_abeta ...
                        eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_abs ... eapply gvalue_fanno ... 
                        inverts H2. inverts* H16.  reflexivity.
                        destruct (eq_type C0). destruct (eq_type D0). subst.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step... 
                        apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity. 
                        eapply gTReduce_v ... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H16.
                        reflexivity.  reflexivity.  eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H16.
                        reflexivity. reflexivity. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt. rewrite fill_anno.
                        eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                        simpl. eauto. inverts H2. inverts H23. eapply gvalue_fanno... eapply gvalue_fanno... 
                        reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H23.
                        eapply gvalue_fanno... reflexivity.
                        reflexivity. reflexivity. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt. rewrite fill_anno.
                        eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto. eapply gvalue_fanno... reflexivity.
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. inverts H2. inverts H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H22.
                        eapply gvalue_fanno... reflexivity.
                        reflexivity. reflexivity. apply gTReduce_blame.
                        unfold not; intros nt; inverts nt.
                     -- 
                        destruct (eq_type C). destruct (eq_type D). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                        eapply gTReduce_v ... inverts H2. inverts H13. eapply gvalue_fanno... 
                        reflexivity.  eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                        eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H13.
                        reflexivity. eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H13. reflexivity.
                        apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                        eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                        simpl. eauto. inverts H2. inverts H20. eapply gvalue_fanno... reflexivity.
                        eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                        eapply gvalue_dyn... eapply gvalue_fanno... 
                        inverts H2. inverts* H20. eapply gvalue_fanno... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H20.
                        reflexivity. reflexivity.  apply gTReduce_blame.
                        unfold not; intros nt; inverts nt. 
                        eapply gstep_nb. apply gStep_abeta; eauto. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity.
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. inverts H2. inverts H16. eapply gvalue_fanno... reflexivity.
                        eapply gstep_nb. rewrite fill_anno.
                        apply gdo_step; eauto. apply gStep_abeta ... 
                        eapply gvalue_fanno... reflexivity. inverts H2. eapply gTReduce_dd ...
                        eapply gvalue_dyn... eapply gvalue_fanno... inverts H2. inverts* H16. eapply gvalue_fanno... reflexivity. reflexivity.
                        eapply gstep_b. rewrite fill_anno.
                        apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                        apply gvalue_dyn... eapply gvalue_fanno... eapply gvalue_fanno... 
                        inverts H2. inverts* H16.
                        reflexivity. reflexivity.  apply gTReduce_blame.
                        unfold not; intros nt; inverts nt. 
                     -- 
                        inverts H8;  inverts H7; inverts H19.
                        ++ destruct (eq_type A2). destruct (eq_type B). subst.
                          destruct (eq_type C). destruct (eq_type D). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H19.  eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                          inverts H2. inverts* H19.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H19. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H22.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H22. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H20.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H20. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H22. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H19. apply H7. reflexivity.
                          simpl. destruct (eq_type C). destruct (eq_type D). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H20.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H19. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H24. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H19. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H24. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H24. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H20. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H1. reflexivity.
                          simpl. destruct (eq_type C). destruct (eq_type D). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H20.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H20. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          ++ destruct (eq_type A2). destruct (eq_type B). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H12. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H12.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H12. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H12.
                          eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H12. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H19.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H7. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt.
                            inverts H12. apply H7. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H19. apply gvalue_dyn; eauto. 
                            inverts H2. inverts* H19.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H19. apply gvalue_dyn; eauto.  
                          inverts H2. inverts* H19.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. apply gStep_annov ... inverts H2. inverts* H13.  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H8. apply H1. reflexivity. 
                          eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                            inverts H2. inverts* H13.
                          eapply gvalue_fanno ... reflexivity.
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto. 
                            inverts H2. inverts* H13.
                          eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. apply gstep_b...  
                          apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                          eapply gvalue_dyn; eauto. inverts H2. inverts* H13. eapply gvalue_fanno ... reflexivity.
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                      ++ destruct (eq_type A2). destruct (eq_type B). subst.
                          destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H12.  eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                          inverts H2. inverts* H12.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H12. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt. 
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... 
                          inverts H2. inverts* H19.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H19. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt. 
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. simpl ... apply gvalue_dyn ... inverts H2. inverts* H15.
                          eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. inverts H2. inverts* H15. eapply gvalue_fanno... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno... eapply gvalue_fanno... reflexivity. reflexivity. 
                          apply gTReduce_blame. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H19. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H8. reflexivity.
                          simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H15.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... 
                          inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H12. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H23. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H23. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                          apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                          reflexivity. inverts H2. inverts H15. apply gStep_annov ...  
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto. unfold not; intros nt; inverts nt. inverts H10. apply H1. reflexivity.
                          simpl. destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          unfold trans in *. fold trans in *.
                          apply gTReduce_vany ... unfold trans in *. apply gvalue_dyn ...
                          inverts H2. inverts* H15.  eapply gvalue_fanno ... reflexivity. eapply gstep_nb. rewrite fill_anno.
                          apply gdo_step; eauto. apply gStep_abeta ... 
                          eapply gvalue_fanno... reflexivity.  eapply gTReduce_v ... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity. apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H22. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H22. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.  
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_dyna ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. 
                          rewrite fill_anno. eapply gstep_nb. apply gdo_step... apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
                          simpl. eauto.  simpl. eauto. eapply gvalue_fanno...  inverts H2. inverts* H19. eapply gvalue_fanno ... reflexivity. reflexivity.
                          eapply gstep_b. rewrite fill_anno.
                          apply gblame_step; eauto. apply gblame_step; eauto. apply gStep_betap ... 
                          apply gvalue_dyn... inverts H2. inverts* H19. eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame.
                          unfold not; intros nt; inverts nt.
                     -- 
                        destruct (eq_type A2). destruct (eq_type B). subst.
                        eapply gstep_nb. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H13.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H13. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H13.
                        eapply gstep_b. rewrite fill_anno. apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. 
                        inverts H2. inverts* H13. apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H16.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. 
                        inverts H13. apply H10. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H16.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H16. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H16.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H16. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                        eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
                        apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
                        reflexivity. apply gStep_annov ... inverts H2. inverts* H15.  
                        eapply gTReduce_anyd ... unfold FLike. 
                        split. unfold not; intros nt; inverts nt.
                        split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                        simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H1. reflexivity. 
                        eapply gstep_nb. simpl. apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. eapply gvalue_fanno ... reflexivity. reflexivity.
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H15. apply gvalue_dyn; eauto. 
                        inverts H2. inverts* H15.
                        eapply gvalue_fanno ... reflexivity.
                        eapply gstep_nb. rewrite fill_anno. apply gdo_step ... apply gStep_abeta; eauto.
                        eapply gvalue_fanno; eauto. reflexivity. 
                        eapply gTReduce_dd; eauto. inverts H2. inverts* H15. apply gvalue_dyn; eauto.  
                        inverts H2. inverts* H15.
                        eapply gvalue_fanno ... reflexivity. 
                        rewrite fill_anno. apply gstep_b...  
                        apply gblame_step ... apply gblame_step ... apply gStep_betap; eauto.
                        eapply gvalue_dyn; eauto. inverts H2. inverts* H15. eapply gvalue_fanno ... reflexivity.
                        apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                     -- inverts H15. inverts H1; inverts H10.
                        ++ 
                          unfold trans in *. fold trans in *.
                          eapply gstep_nb. apply gStep_abeta ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          reflexivity. reflexivity. eapply gTReduce_abs ... eapply gvalue_fanno ... 
                          inverts H2. inverts* H17. inverts H2.  eapply gvalue_fanno ...  reflexivity. reflexivity.
                          rewrite fill_anno. destruct (eq_type C). destruct (eq_type D). subst.  
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_v ... eapply gvalue_fanno ... eapply gvalue_fanno ... 
                          inverts H2. inverts H17. 
                          inverts H2. eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H17.  inverts* H2. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H20. 
                          inverts H12. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H20.  inverts* H12. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                          eapply gstep_nb. apply gdo_step... apply gStep_abeta ... eapply gvalue_fanno ... reflexivity. 
                          eapply gTReduce_anyd... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity. 
                          simpl. eauto.  
                          inverts H2. inverts H19. 
                          inverts H10. eapply gvalue_fanno ...   eapply gvalue_fanno ...  eapply gvalue_fanno ... reflexivity. reflexivity.  reflexivity. 
                          rewrite fill_anno. apply gstep_b. apply gblame_step ... apply gblame_step ...
                          apply gStep_betap ... eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          eapply gvalue_fanno ...  inverts H2. inverts H19.  inverts* H10. eapply gvalue_fanno ...
                          reflexivity. reflexivity. reflexivity. reflexivity.
                          apply gTReduce_blame ... unfold not;intros nt; inverts nt.
                        ++ 
                          unfold trans in *. fold trans in *.
                          destruct (eq_type A1). destruct (eq_type B0). subst.
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_v; eauto. eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2.  eapply gvalue_fanno ... reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H13. inverts* H2. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
                          
                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H10. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H18. inverts* H12. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.

                          eapply gstep_nb. apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
                          eapply gTReduce_anyd ... unfold FLike. 
                          split. unfold not; intros nt; inverts nt.
                          split. unfold not; intros nt; inverts nt. apply H1. reflexivity.
                          simpl; eauto.  eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H10. reflexivity. reflexivity. 
                          eapply gstep_nb. rewrite fill_anno. apply gdo_step; eauto.
                          apply gStep_abeta; eauto.
                          eapply gvalue_fanno; eauto. reflexivity. 
                          eapply gTReduce_dd; eauto. inverts* H2. eapply gvalue_dyn ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H10.  eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity. reflexivity.
                          rewrite fill_anno. eapply gstep_b ... apply gblame_step ...  apply gblame_step ...
                          apply gStep_betap; eauto.
                          eapply gvalue_dyn ... eapply gvalue_fanno ... eapply gvalue_fanno ... eapply gvalue_fanno ...
                          inverts H2. inverts H17. inverts* H10. reflexivity. reflexivity. reflexivity. 
                          apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt. 
        * inverts H8. exfalso. apply H1. eauto.
      + inverts H7.
        * inverts Typ. 
          ** inverts H10. inverts H3. inverts H9. 
             inverts H7. inverts H12. inverts H7.
             forwards*: gtyping_regular_1 H11. 
             inverts H3; inverts H5.
             ***  exfalso. apply H1. auto.
             *** fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... eapply gvalue_fanno ...  reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               apply H1; auto. apply H1; eauto.
          ** inverts H3. inverts H10. inverts H3. inverts H10. inverts H3.
             inverts H9. inverts H7. exfalso. apply H1. auto. inverts H2.
             inverts H8. inverts H3.
             fold trans in *.  
               eapply gstep_b ... simpl.
               apply gStep_abetap; eauto.
               eapply gvalue_fanno ... eapply gvalue_fanno ...  reflexivity. reflexivity.
               apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
               apply H1; auto. apply H1; eauto.
        * inverts Typ. 
          ** inverts H9. inverts H1. forwards*: gtyping_regular_1 H8. inverts H8.
             inverts H5. inverts H12. inverts H5. inverts H4. 
             inverts H7; inverts H3.
             forwards*: gtyping_regular_1 H11. 
             destruct (eq_type A0). destruct (eq_type B). subst.
              eapply gstep_b. apply gStep_abetap; eauto.
              eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
              eapply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.   
              unfold trans. apply gvalue_dyn; eauto.  
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
              reflexivity. apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H5. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H5. reflexivity.
              fold trans in *.  
              eapply gstep_b ... simpl.
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gvalue_dyn; eauto.  
              eapply gvalue_fanno ... reflexivity.  
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H4. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H7. apply H4. reflexivity.
              fold trans in *.  
              eapply gstep_b ... simpl.
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gvalue_dyn; eauto.  
              eapply gvalue_fanno ... reflexivity.
          ** inverts H1. inverts H8. inverts H9. inverts H10. inverts H5.
             inverts H1.  forwards*: gtyping_regular_1 H9. forwards*: gtyping_regular_1 H10.
             inverts H9. inverts H8; inverts H4. inverts H11. 
             destruct (eq_type A0). destruct (eq_type B). subst.
              eapply gstep_b. apply gStep_abetap; eauto.
              eapply gvalue_fanno; eauto. eapply gvalue_fanno; eauto. reflexivity. reflexivity.
              eapply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.   
              unfold trans. apply gvalue_dyn; eauto.  
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity.
              reflexivity. apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H8. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H12. apply H8. reflexivity.
              fold trans in *.  
              eapply gstep_b ... simpl.
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gvalue_dyn; eauto.  
              eapply gvalue_fanno ... reflexivity.  
              eapply gstep_nb. rewrite fill_appr. apply gdo_step; eauto.
              apply wf_appCtxR. eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gStep_annov ...  
              eapply gTReduce_anyd ... unfold FLike. 
              split. unfold not; intros nt; inverts nt.
              split. unfold not; intros nt; inverts nt. apply H4. reflexivity. 
              simpl. eauto. unfold not; intros nt; inverts nt. inverts H9. apply H4. reflexivity.
              fold trans in *.  
              eapply gstep_b ... simpl.
              apply gStep_abetap; eauto.
              eapply gvalue_fanno ... eapply gvalue_fanno ... reflexivity. reflexivity.
              apply gTReduce_blame; eauto. unfold not; intros nt; inverts nt.
              eapply gvalue_dyn; eauto.  
              eapply gvalue_fanno ... reflexivity.
  - inverts* Typ. inverts* H3. 
  - inverts* Typ. inverts* H2. 
Qed.
