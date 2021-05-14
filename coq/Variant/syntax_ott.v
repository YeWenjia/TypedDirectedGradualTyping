Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition i : Set := nat.
Definition b : Set := bool.

Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_dyn : typ (*r dynamic type *).

Inductive st : Set :=  (*r input type or projection label *)
 | st_ty (A:typ).

 Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (A:typ) (e:exp) (B:typ) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_add (e1:exp) (e2:exp) (*r additions *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_save (e:exp) (A:typ) (B:typ) (*r save *).

 Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

 Definition ctx : Set := list ( atom * typ ).

 Definition ls : Set := list st.
 
 (* EXPERIMENTAL *)
 (** auxiliary functions on the new list types *)
 (** library functions *)
 (** subrules *)
 (** arities *)
 (** opening up abstractions *)
 Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
    match e__6 with
    | (e_var_b nat) => 
        match lt_eq_lt_dec nat k with
          | inleft (left _) => e_var_b nat
          | inleft (right _) => e_5
          | inright _ => e_var_b (nat - 1)
        end
    | (e_var_f x) => e_var_f x
    | (e_lit i5) => e_lit i5
    | (e_abs A e B) => e_abs A (open_exp_wrt_exp_rec (S k) e_5 e) B
    | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
    | (e_add e1 e2) => e_add (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
    | (e_save e A B) => e_save (open_exp_wrt_exp_rec k e_5 e) A B
  end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (A:typ) (e:exp) (B:typ),
      ( forall x , lc_exp  (open_exp_wrt_exp e (e_var_f x))  )  ->
     (lc_exp (e_abs A e B))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_add : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_add e1 e2))
 | lc_e_save : forall (e:exp) (A:typ) B,
     (lc_exp e) ->
     (lc_exp (e_save e A B)).


(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs A e B) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | (e_add e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_save e A B) => (fv_exp e)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs A e B) => e_abs A (subst_exp e_5 x5 e) B
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_add e1 e2) => e_add (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_save e A B) => e_save (subst_exp e_5 x5 e) A B
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_abs A e B) => (t_arrow A B)
  | (e_anno e A) => A
  | (e_save e A B) => (t_arrow A B)
  | _ => t_dyn
  end.

Fixpoint trans (e:exp) : exp :=
    match e with
    | (e_var_b nat) => e_var_b nat
    | (e_var_f x) => (e_var_f x)
    | (e_lit i5) => e_lit i5
    | (e_abs A e B) => e_abs A (trans (e)) B
    | (e_anno e A) => e_anno (trans e) A
    | (e_save e A B) => e_anno (e_anno (trans e) (t_arrow t_dyn t_dyn)) (t_arrow A B)
    | (e_app e1 e2) => e_app (trans e1) (trans e2)
    | (e_add e1 e2) => e_add (trans e1) (trans e2)
    end.

    
Inductive sval : exp -> Prop :=    (* defn fval *)
 | sval_abs : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     sval  ( (e_abs A e B) ).

(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_lit : forall (i5:i) (A: typ),
     value (e_anno (e_lit i5) A)
 | value_abs : forall (A:typ) (e:exp) (B C:typ),
     lc_exp (e_abs A e B) ->
     value  ( (e_anno  ( (e_abs A e B) )  C) ) 
 | value_save : forall (e:exp) (A B:typ),
     sval e ->
     value  ( (e_save e A B) ) .

(* defns vValues *)
Inductive vvalue : exp -> Prop :=    (* defn value *)
 | vvalue_lit : forall (i5:i) (A: typ),
     vvalue (e_anno (e_lit i5) A)
 | vvalue_abs : forall (A:typ) (e:exp) (B C:typ),
     lc_exp (e_abs A e B) ->
     vvalue  ( (e_anno  ( (e_abs A e B) )  C) ).

Inductive ival : exp -> Prop :=    (* defn value *)
 | ival_lit : forall (i5:i) (A: typ),
     ival (e_anno (e_lit i5) A).



(* defns Consistency *)
Inductive sim : typ -> typ -> Prop :=    (* defn sim *)
 | S_i : 
     sim t_int t_int
 | S_arr : forall (A B C D:typ),
     sim A C ->
     sim B D ->
     sim (t_arrow A B) (t_arrow C D)
 | S_dynl : forall (A:typ),
     sim t_dyn A
 | S_dynr : forall (A:typ),
     sim A t_dyn.


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs A e B) Inf (t_arrow A B)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     Typing G e1 Inf (t_arrow A B) ->
     Typing G e2 Chk A ->
     Typing G (e_app e1 e2) Inf B
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_add : forall (G:ctx) (e1 e2:exp),
     Typing G e1 Chk t_int ->
     Typing G e2 Chk t_int ->
     Typing G (e_add e1 e2) Inf t_int
 | Typ_save : forall (G:ctx) (e:exp) (A B C:typ),
      uniq  G  ->
     sval e ->
     Typing  nil  e Inf C ->
      not (  sim C (t_arrow A B) )  ->
     Typing G  ( (e_save e A B) )  Inf (t_arrow A B)
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     Typing G e Chk B.


Inductive gtyping : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | gtyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
      gtyping G (e_lit i5) Inf t_int
 | gtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      gtyping G (e_var_f x) Inf A
 | gtyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> gtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      gtyping G (e_abs A e B) Inf (t_arrow A B)
 | gtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     gtyping G e1 Inf (t_arrow A B) ->
     gtyping G e2 Chk A ->
     gtyping G (e_app e1 e2) Inf B
 | gtyp_anno : forall (G:ctx) (e:exp) (A:typ),
     gtyping G e Chk A ->
     gtyping G  ( (e_anno e A) )  Inf A
 | gtyp_sim : forall (G:ctx) (e:exp) (B A:typ),
     gtyping G e Inf A ->
     sim A B ->
     gtyping G e Chk B.


Inductive simpl_item : Type :=
     | sappCtxL : exp -> simpl_item
     | sappCtxR : exp -> simpl_item
     | saddCtxL : exp -> simpl_item
     | saddCtxR : exp -> simpl_item.

   
Inductive ctx_item : Type :=
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | annoCtx : typ -> ctx_item.
   

Inductive simpl_wf : simpl_item -> Prop :=
     | swf_appl : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (sappCtxL e)
     | swf_appr : forall (v : exp),
                    value v ->
                    simpl_wf (sappCtxR v)
     | swf_addl : forall (e : exp),
                     lc_exp e ->
                    simpl_wf (saddCtxL e)
     | swf_addr : forall (v : exp),
                    value v ->
                    simpl_wf (saddCtxR v).

Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)).

Inductive Ground : typ -> Prop :=    (* defn Ground *)
 | Ground_lit : 
     Ground t_int
 | Ground_dyn : 
     Ground  (t_arrow t_dyn t_dyn) .


(* defns Values *)
Inductive gvalue : exp -> Prop :=    (* defn value *)
 | gvalue_lit : forall (i5:i),
     gvalue (e_lit i5)
 | gvalue_anno : forall (A:typ) (e:exp) (B:typ),
     lc_exp (e_abs A e B) ->
     gvalue (e_abs A e B)
 | gvalue_fanno : forall (v:exp) (A B C D:typ),
     gvalue v ->
      (t_arrow C D)  =   (principal_type   ( v )  )   ->
     gvalue (e_anno v (t_arrow A B))
 | gvalue_dyn : forall (v:exp),
     Ground   (principal_type  v )   ->
     gvalue v ->
     gvalue  ( (e_anno v t_dyn) ) .

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    gvalue v ->
                    wellformed (appCtxR v)
     | wf_annoCtx : forall (A : typ),
                    wellformed (annoCtx A).

Definition simpl_fill (EE : simpl_item) (e : exp) : exp :=
     match EE with
     | sappCtxL e2 => e_app e e2
     | sappCtxR v1 => e_app v1 e
     | saddCtxL e2 => e_add e e2
     | saddCtxR v1 => e_add v1 e
     end.

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | annoCtx A => e_anno e A
     end.

Inductive res : Type :=
     | Expr  : exp -> res
     | Blame :  res.

(* defns Semantics *)


Inductive TypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | TReduce_sim : forall (e:exp) (A:typ) (B:typ),
     lc_exp e ->
     sim (principal_type e) B ->
     TypedReduce  ( (e_anno e A) ) B  (Expr (e_anno e B) )
 | TReduce_simp : forall (A:typ) (e:exp) (B C:typ),
     lc_exp e ->
     sval e ->
      not (  sim (principal_type e) (t_arrow B C)  )  ->
     TypedReduce  ( (e_anno e A) ) (t_arrow B C)  (Expr (e_save e B C))
 | TReduce_i : forall (A:typ) (B:typ) i,
      not (  sim t_int B  )  ->
     TypedReduce  ( (e_anno (e_lit i) A) ) B  Blame
 | TReduce_savep : forall (e:exp) (A B C:typ),
     sim   (principal_type  e )   C ->
     TypedReduce  ( (e_save e A B) )  C  (Expr (e_anno e C))
 | TReduce_save : forall (e:exp) (A B C D:typ),
      not (  sim   (principal_type  e )  (t_arrow C D)  )  ->
     TypedReduce  ( (e_save e A B) )  (t_arrow C D)  (Expr (e_save e C D))
 | TReduce_p : forall (e:exp) (A B C:typ),
     TypedReduce  (e_anno (e_abs A e B) C)  t_int Blame.


Inductive TypeLists : exp -> list typ -> res -> Prop :=    (* defn TypeLists *)
 | TLists_base : forall (v v':exp) (A:typ),
     lc_exp v ->
     TypedReduce v A (Expr v') ->
     TypeLists  v (cons A nil)  (Expr v')
 | TLists_baseb : forall (A:typ) (v:exp),
     lc_exp v ->
     TypedReduce v A Blame ->
     TypeLists  v (cons A nil) Blame
 | TLists_cons : forall (A:typ) (B: list typ) v1 v2 r,
     lc_exp v1 ->
     TypedReduce v1 A (Expr v2) ->
     TypeLists  v2 B r ->
     TypeLists  v1 (cons A B) r 
 | TLists_consb : forall (A:typ) (B: list typ) v1,
     lc_exp v1 ->
     TypedReduce v1 A Blame ->
     TypeLists  v1 (cons A B) Blame.

Inductive gTypedReduce : exp -> typ -> res -> Prop :=    (* defn TypedReduce *)
 | gTReduce_abs: forall v A B C D,
   sim (t_arrow C D) (t_arrow A B) ->
   principal_type v = (t_arrow C D) ->
   gTypedReduce v (t_arrow A B) (Expr (e_anno v (t_arrow A B)))
  | gTReduce_v : forall (v:exp),
   Ground(principal_type v) ->
   gTypedReduce v t_dyn (Expr (e_anno v t_dyn))
 | gTReduce_lit : forall (i5:i),
     gTypedReduce (e_lit i5) t_int (Expr (e_lit i5))
 | gTReduce_dd : forall (v:exp),
     lc_exp v ->
     gTypedReduce  ( (e_anno v t_dyn) )  t_dyn  (Expr  (e_anno v t_dyn) ) 
 | gTReduce_anyd : forall (v:exp),
      FLike (principal_type  v )  ->
     gTypedReduce v t_dyn  (Expr (e_anno  ( (e_anno v (t_arrow t_dyn t_dyn)) )  t_dyn) ) 
 | gTReduce_dyna : forall (v:exp) (A:typ),
      FLike A ->
     sim (principal_type v) A ->
    gTypedReduce  ( (e_anno v t_dyn) )  A  (Expr (e_anno v A) ) 
 | gTReduce_vany : forall (v:exp),
   gTypedReduce (e_anno v t_dyn) (principal_type  v) (Expr v)
 | gTReduce_blame : forall (v:exp) (A:typ),
      not (sim A (principal_type  v ))  ->
     gTypedReduce (e_anno v t_dyn) A Blame.


Inductive step : exp -> res -> Prop :=
   | Step_abs : forall (A:typ) (e:exp) (B:typ),
      lc_exp (e_abs A e B) ->
      step (e_abs A e B) (Expr (e_anno (e_abs A e B) (t_arrow A B)))
   | Step_i : forall (i5:i),
      step (e_lit i5) (Expr (e_anno (e_lit i5) t_int))
   | do_step E e1 e2 :
    simpl_wf E ->
    step e1 ( Expr e2 ) ->
    step (simpl_fill E e1) (Expr (simpl_fill E e2))
  | blame_step E e1 :
    simpl_wf E ->
    step e1 Blame ->
    step (simpl_fill E e1) Blame
   | Step_anno : forall (e e':exp ) (A: typ),
     step e (Expr e') ->
     not (value (e_anno e A)) -> 
     step (e_anno e A) (Expr (e_anno e' A))
   | Step_annob : forall (e:exp ) (A: typ),
     step e Blame ->
     not (value (e_anno e A)) -> 
     step (e_anno e A) Blame
   | Step_beta : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v v': exp),
     lc_exp (e_abs A1 e B1) ->
     value v ->
     TypeLists v (cons A2 (cons A1 nil)) (Expr v') ->
     step (e_app  (e_anno (e_abs A1 e B1) (t_arrow A2 B2))  v)  (Expr (e_anno (e_anno (open_exp_wrt_exp  e v' ) B1) B2) )
   | Step_betap : forall (A1 A2:typ) (e:exp) (B1 B2:typ) (v: exp),
     lc_exp (e_abs A1 e B1) ->
     value v ->
     TypeLists v (cons A2 (cons A1 nil)) Blame ->
     step (e_app  (e_anno (e_abs A1 e B1) (t_arrow A2 B2))  v)  Blame
  | Step_annov : forall (v:exp) (A:typ) r,
     value v ->
     TypedReduce v A r ->
     step (e_anno v A) r
  | Step_appv : forall (e v v':exp) (A1 B1 A2 B2:typ),
     value v ->
     lc_exp (e_abs A1 e B1) -> 
     TypeLists v (cons A2 (cons t_dyn (cons A1 nil))) (Expr v') ->
     step (e_app (e_save (e_abs A1 e B1) A2 B2) v) (Expr (e_anno (e_anno (e_anno (open_exp_wrt_exp  e v' ) B1) t_dyn) B2) ) 
  | Step_appvp : forall (e v :exp) (A1 B1 A2 B2:typ),
     value v ->
     lc_exp (e_abs A1 e B1) -> 
     TypeLists v (cons A2 (cons t_dyn (cons A1 nil))) Blame ->
     step (e_app (e_save (e_abs A1 e B1) A2 B2) v) Blame
  | Step_addl : forall v1 v2,
     value v1 ->
     value v2 ->
     TypedReduce v1 t_int Blame ->
     step (e_add v1 v2) Blame 
   | Step_addr : forall i5 v2 A,
     value v2 ->
     TypedReduce v2 t_int Blame ->
     step (e_add (e_anno (e_lit i5) A) v2) Blame
  | Step_addb : forall i1 i2 A B,
     step (e_add (e_anno (e_lit i1) A) (e_anno (e_lit i2) B)) (Expr (e_anno (e_lit (i1 + i2)) t_int)).

Inductive gstep : exp -> res -> Prop :=    (* defn step *)
  | gdo_step E e1 e2 :
       wellformed E ->
       gstep e1 (Expr e2 ) ->
      gstep (fill E e1) (Expr (fill E e2))
  | gblame_step E e1:
      wellformed E ->
      gstep e1 Blame ->
      gstep (fill E e1) Blame
 | gStep_beta : forall (A:typ) (e:exp) (B:typ) (v v' : exp),
    lc_exp (e_abs A e B) ->
    gvalue v ->
    gTypedReduce v A (Expr v') ->
    gstep (e_app  ( (e_abs A e B) )  v)  (Expr (e_anno  (  (open_exp_wrt_exp  e v' )  )  B) ) 
 | gStep_betap : forall (A:typ) (e:exp) (B:typ) (v v':exp),
    lc_exp (e_abs A e B) ->
    gvalue v ->
    gTypedReduce v A Blame ->
    gstep (e_app  ( (e_abs A e B) )  v)  Blame
 | gStep_annov : forall (v:exp) (A:typ) (v':res),
     gvalue v ->
     gTypedReduce v A v' ->
     not (gvalue (e_anno v A)) -> 
     gstep (e_anno v A) v'
 | gStep_abeta : forall (v1:exp) (A B:typ) (v2 v2':exp),
     gvalue  ( (e_anno v1 (t_arrow A B)) )  ->
     gTypedReduce v2 A (Expr v2') ->
     gvalue v2 ->
     gstep (e_app  ( (e_anno v1 (t_arrow A B)) )  v2) (Expr (e_anno  ( (e_app v1 v2') )  B))
 | gStep_abetap : forall (v1:exp) (A B:typ) (v2 v2':exp),
     gvalue  ( (e_anno v1 (t_arrow A B)) )  ->
     gTypedReduce v2 A Blame ->
     gvalue v2 ->
     gstep (e_app  ( (e_anno v1 (t_arrow A B)) )  v2) Blame.


(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    (* defn sim *)
 | tp_i : 
     tpre t_int t_int
 | tp_dyn : forall (A:typ),
     tpre A t_dyn
 | tp_abs : forall (A B C D:typ),
     tpre A C ->
     tpre B D ->
     tpre (t_arrow A B) (t_arrow C D).

(* defns expression precision *)
Inductive epre : exp -> exp -> Prop :=    (* defn sim *)
 | ep_refl e:
    lc_exp e ->
    epre e e 
 | ep_abs : forall (A1 A2:typ) (e1 e2:exp) (B1 B2:typ) (L:vars),
     ( forall x , x \notin  L  -> 
      epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
     tpre A1 A2 ->
     tpre B1 B2 ->
     epre (e_abs A1 e1 B1) (e_abs A2 e2 B2)
 | ep_app : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_add : forall (e1 e2 e1' e2':exp),
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_add e1 e2) (e_add e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_save : forall (A B C D:typ) (e1 e2:exp),
     tpre A C ->
     tpre B D ->
     epre e1 e2 ->
     epre (e_save e1 A B) (e_save e2 C D)
 | ep_sa : forall (A B C:typ) (e1 e2:exp),
     tpre (t_arrow A B) C ->
     epre e1 e2 ->
     epre (e_save e1 A B) (e_anno e2 C)
 | ep_annol : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno (e_anno e1 t_dyn) A) (e_anno e2 B)
 | ep_saver : forall (A B C D:typ) (e1 e2:exp),
     tpre A C ->
     tpre B D ->
     epre e1 e2 ->
     epre (e_anno (e_anno e1 t_dyn) (t_arrow A B)) (e_save e2 C D).

Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (Expr e)

  | step_n e t' e':   
    step e (Expr e') ->
    steps e' (Expr t') ->
    steps e  (Expr t')
  | step_nb e e':
    step e (Expr e') ->
    steps e' Blame ->
    steps e  Blame

  | step_b e:
    step e (Blame) ->
    steps e (Blame).

Inductive gsteps : exp -> res -> Prop :=
  | gstep_refl e:
    gsteps e (Expr e)

  | gstep_n e t' e':   
    gstep e (Expr e') ->
    gsteps e' (Expr t') ->
    gsteps e  (Expr t')

  | gstep_nb e e':
    gstep e (Expr e') ->
    gsteps e' Blame ->
    gsteps e  Blame

  | gstep_b e:
    gstep e (Blame) ->
    gsteps e (Blame).

(** infrastructure *)
Hint Constructors value Ground gvalue sval vvalue ival sim TypedReduce TypeLists wellformed simpl_wf step steps gsteps tpre epre Typing gtyping lc_exp : core.


