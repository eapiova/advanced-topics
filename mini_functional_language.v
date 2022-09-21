From pv Require Export library.


(* 1.2 Syntax *)


Inductive term :=
  | Const : nat -> term
  | true : term
  | false : term
  | Fun : string -> type -> term -> term
  | unit : term
  | Var : string -> term
  | Plus : term -> term -> term
  | If : term -> term -> term -> term
  | App : term -> term -> term
  | RNil : term
  | RCons : string -> term -> term -> term
  | Sel : term -> string -> term
with type :=
  | TBool : type
  | TNat : type
  | TFun : type -> type -> type
  | TUnit : type
  | TRNil : type
  | TRCons : string -> type -> type -> type.
  (*
  | TTop : type
  | TBot : type.
  *)


Inductive val : term -> Prop :=
  | VConst n : val (Const n)
  | Vtrue : val true
  | Vfalse : val false
  | VFun x T M : val (Fun x T M)
  | Vunit : val unit
  | VRNil : val RNil
  | VRCons l v1 vr: 
    val v1 ->
    val vr ->
    val (RCons l v1 vr).


Inductive rec_term : term -> Prop :=
  | RMNil :
    rec_term RNil
  | RMCons l M MR : 
    rec_term (RCons l M MR).


Inductive rec_type : type -> Prop :=
  | RTNil :
    rec_type TRNil
  | RTCons l T TR :
    rec_type (TRCons l T TR).


Inductive wf_type : type -> Prop :=
  | wfTBool : wf_type TBool
  | wfTNat : wf_type TNat
  | wfTFun T1 T2 : 
    wf_type T1 ->
    wf_type T2 ->
    wf_type (TFun T1 T2)
  | wfTUnit : wf_type TUnit
  | wfTRNil : wf_type TRNil
  | wfTRCons l T TR : 
    wf_type T ->
    wf_type TR ->
    rec_type TR ->
    wf_type (TRCons l T TR).


Fixpoint rec_term_lookup (l : string) (MR : term) : option term :=
  match MR with
  | RCons l' M MR' => if String.eq_dec l l' then Some M else rec_term_lookup l MR'
  | _ => None
  end.


Fixpoint rec_type_lookup (l : string) (TR : type) : option type :=
  match TR with
  | TRCons l' T TR' => if String.eq_dec l l' then Some T else rec_type_lookup l TR'
  | _ => None
  end.


Fixpoint subst (x : string) (N : term) (M : term) : term :=
  match M with
  | Var y => if String.eq_dec x y then N else M
  | Plus M1 M2 => Plus (subst x N M1) (subst x N M2)
  | If M1 M2 M3 => If (subst x N M1) (subst x N M2) (subst x N M3)
  | Fun y T M' => if String.eq_dec x y then M else Fun y T (subst x N M')
  | App M1 M2 => App (subst x N M1) (subst x N M2)
  | RCons l M' MR => RCons l (subst x N M') (subst x N MR)
  | Sel M' l => Sel (subst x N M') l 
  | _ => M
  end.


(* 1.3 Operational Semantics *)


Inductive step : term -> term -> Prop :=
  | Sum n1 n2 n :
    n1 + n2 = n ->
    step (Plus (Const n1) (Const n2)) (Const n)
  | Sum_left M N M' :
    step M M' -> 
    step (Plus M N) (Plus M' N)
  | Sum_right M v M' :
    val v ->
    step M M' -> 
    step (Plus v M) (Plus v M')
  | If_true M N :
    step (If true M N) M
  | If_false M N :
    step (If false M N) N
  | If_step M1 M1' M2 M3 :
    step M1 M1' -> step (If M1 M2 M3) (If M1' M2 M3)
  | Beta x T M v :
    val v ->
    step (App (Fun x T M) v) (subst x v M)
  | App1 M N M' :
    step M M' -> 
    step (App M N) (App M' N)
  | App2 v M M' :
    val v ->
    step M M' -> 
    step (App v M) (App v M')
  | Select l vr v :
    val vr ->
    rec_term_lookup l vr = Some v ->
    step (Sel vr l) v
  | Eval_Select M M' l :
    step M M' -> step (Sel M l) (Sel M' l)
  | Eval_Record_Head l M M' MR :
    step M M' ->
    step (RCons l M MR) (RCons l M' MR)
  | Eval_Record_Tail l v MR MR' :
    val v ->
    step MR MR' ->
    step (RCons l v MR) (RCons l v MR').


Inductive steps : term -> term -> Prop :=
  | steps_refl M :
     steps M M
  | steps_step M1 M2 M3 :
     step M1 M2 ->
     steps M2 M3 ->
     steps M1 M3.


(* Subtyping *)

(*
Inductive subtype : type -> type -> Prop :=
  | Reflex T :
      subtype T T
  | Trans S U T :
      subtype S U ->
      subtype U T ->
      subtype S T 
  | Sub_Width l T TR :
    wf_type (TRCons l T TR) ->
    subtype (TRCons l T TR) TRNil
  | Sub_Depth l S T SR TR :
    subtype S T ->
    subtype SR TR ->
    rec_type SR ->
    rec_type TR ->
    subtype (TRCons l S SR) (TRCons l T TR)
  | Sub_Perm l1 l2 T1 T2 TR :
    wf_type (TRCons l1 T1 (TRCons l2 T2 TR)) ->
    ~ (l1 = l2) ->
    subtype (TRCons l1 T1 (TRCons l2 T2 TR)) (TRCons l2 T2 (TRCons l1 T1 TR))
  | Arrow S1 S2 T1 T2 :
      subtype T1 S1 ->
      subtype S2 T2 ->
      subtype (TFun S1 S2) (TFun T1 T2).
*)



(* 3 Simple types *)


Inductive typed : stringmap type -> term -> type -> Prop :=
  | T_True Gamma :
    typed Gamma true TBool
  | T_False Gamma :
    typed Gamma false TBool
  | T_Int Gamma n :
    typed Gamma (Const n) TNat
  | T_Fun Gamma x M T1 T2 :
    wf_type T1 ->
    StringMap.lookup Gamma x = None ->
    typed (StringMap.insert x T1 Gamma) M T2 ->
    typed Gamma (Fun x T1 M) (TFun T1 T2)
  | T_Var Gamma x T :
     StringMap.lookup Gamma x = Some T ->
     wf_type T ->
     typed Gamma (Var x) T
  | T_Sum Gamma M N :
     typed Gamma M TNat ->
     typed Gamma N TNat ->
     typed Gamma (Plus M N) TNat
  | T_IfThenElse Gamma M1 M2 M3 T :
     typed Gamma M1 TBool->
     typed Gamma M2 T ->
     typed Gamma M3 T ->
     typed Gamma (If M1 M2 M3) T
  | T_App Gamma M N T1 T2 :
     typed Gamma M (TFun T1 T2) ->
     typed Gamma N T1 ->
     typed Gamma (App M N) T2
  | T_Unit Gamma :
    typed Gamma unit TUnit
  | T_RNil Gamma :
    typed Gamma RNil TRNil
  | T_RCons Gamma l M T MR TR :
    typed Gamma M T ->
    typed Gamma MR TR ->
    rec_term MR ->
    rec_type TR ->
    typed Gamma (RCons l M MR) (TRCons l T TR)
  | T_Select Gamma M l T TR :
    typed Gamma M TR -> 
    rec_type_lookup l TR = Some T ->
    typed Gamma (Sel M l) T.
  (*
  | Subsumption Gamma M S T :
    typed Gamma M S ->
    subtype S T ->
    typed Gamma M T.
  *)


Definition well_typed (M : term) : Prop :=
  exists T, exists Gamma, typed Gamma M T.

Definition stuck M :=
  ~(val M) /\ ~(exists M', step M M').


(* Exercises *)


Definition term_1_1 : term :=
  Fun "f" (TFun TBool TBool) (Fun "x" TBool true).

Lemma exercise_1_1 :
  typed StringMap.empty term_1_1 (TFun (TFun TBool TBool) (TFun TBool TBool)).
Proof.
  apply T_Fun.
  - apply wfTFun; apply wfTBool.
  - apply StringMap.lookup_empty.
  - apply T_Fun.
    + apply wfTBool.
    + rewrite StringMap.lookup_insert.
      apply String.eq_dec_neq.
      congruence.
    + apply T_True.
Qed.


Definition term_1_2 : term :=
  Fun "f" (TFun TBool TNat) (Fun "x" TBool (Const 0)).

Lemma exercise_1_2 :
  typed StringMap.empty term_1_2 (TFun (TFun TBool TNat) (TFun TBool TNat)).
Proof.
  apply T_Fun.
  - apply wfTFun.
    + apply wfTBool.
    + apply wfTNat.
  - apply StringMap.lookup_empty.
  - apply T_Fun.
    + apply wfTBool.
    + rewrite StringMap.lookup_insert.
      apply String.eq_dec_neq.
      congruence.
    + apply T_Int.
Qed.


Definition term_2 : term :=
  App (Fun "x" TNat true) false.

Lemma exercise_2 :
  ~ well_typed term_2.
Proof.
  unfold well_typed.
  intros H.
  inv H.
  inv H0.
  inv H.
  inv H3.
  inv H5.
Qed.


Definition term_3 : term :=
  App (App (Var "z") (Var "x")) (Var "y").

Lemma exercise_3 :
  exists Gamma, typed Gamma term_3 TBool.
Proof.
  exists (StringMap.insert "z" (TFun TBool (TFun TBool TBool)) (StringMap.insert "y" TBool (StringMap.singleton "x" TBool))).
  eapply T_App.
  - eapply T_App.
    + apply T_Var.
      * rewrite StringMap.lookup_insert. 
        apply String.eq_dec_eq.
      * apply wfTFun.
        -- apply wfTBool.
        -- apply wfTFun.
          ++ apply wfTBool.
          ++ apply wfTBool.
    + apply T_Var.
      * rewrite StringMap.lookup_insert. 
        rewrite String.eq_dec_neq; try congruence.
        rewrite StringMap.lookup_insert. 
        rewrite String.eq_dec_neq; try congruence.
        rewrite StringMap.lookup_singleton.
        apply String.eq_dec_eq.
      * apply wfTBool.
  - eapply T_Var.
    + rewrite StringMap.lookup_insert. 
      rewrite String.eq_dec_neq; try congruence.
      rewrite StringMap.lookup_insert. 
      apply String.eq_dec_eq.
    + apply wfTBool.
Qed.


Definition term_4 : term :=
  App (Var "x") (Var "x").

Lemma exercise_4 :
  ~ well_typed term_4.
Proof.
  unfold well_typed.
  intros H.
  inv H.
  destruct H0 as [Gamma H0].
  inv H0.
  inv H3.
  inv H5.
  induction T1; try inv H.
  - apply IHT1_1.
    + rewrite <-H3 in H0.
      apply H0.
    + apply H4.
    + inv H4.
      apply H5.
    + apply H3.
Qed.


Definition term_5 : term :=
  Fun "x" (TFun TBool TNat) (Fun "y" TBool (If (Var "y") (Const 1) (Plus (Var "x") (Var "y")))).

Lemma exercise_5 :
  ~ well_typed term_5.
Proof.
  unfold well_typed.
  intros H.
  inv H.
  inv H0.
  inv H.
  inv H7.
  inv H9.
  inv H11.
  inv H9.
  rewrite StringMap.lookup_insert in H0.
  rewrite String.eq_dec_eq in H0.
  inv H0.
Qed.


Definition term_15_1 T1 T2 :=
  Fun "x" T1 (Fun "y" T2 (If (Var "y") (Var "x") true)).

Lemma exercise_15_1 :
  exists T1, exists T2, well_typed (term_15_1 T1 T2).
Proof.
  eexists.
  eexists.
  eexists.
  exists StringMap.empty.
  apply T_Fun.
  - constructor.
  - apply StringMap.lookup_empty.
  - apply T_Fun.
    + constructor.
    + rewrite StringMap.lookup_insert.
      apply String.eq_dec_neq.
      congruence.
    + apply T_IfThenElse.
      * apply T_Var; constructor. 
      * apply T_Var; constructor.
      * apply T_True.
Qed.


Definition term_15_2 :=
  Fun "x" (TFun TNat TBool) (Var "x").

Lemma exercise_15_2 :
  well_typed term_15_2.
Proof.
  eexists.
  exists StringMap.empty.
  apply T_Fun; repeat constructor.
Qed.





(* 3.1 Properties of the type system *)


(* Inversion for Typing *)

(*
Lemma inversion_plus Gamma M N T :
  typed Gamma (Plus M N) T ->
  T = TNat /\ typed Gamma M TNat /\ typed Gamma N TNat.
Proof.
Admitted.

Lemma inversion_if Gamma M1 M2 M3 T :
  typed Gamma (If M1 M2 M3) T ->
  typed Gamma M1 TBool /\ typed Gamma M2 T /\ typed Gamma M3 T.
Proof.
Admitted.
  
Lemma inversion_fun Gamma x S1 M T :
  typed Gamma (Fun x S1 M) T ->
  exists T1, exists T2, T = (TFun T1 T2) /\ subtype T1 S1 /\ typed (StringMap.insert x S1 Gamma) M T2.
Proof.
Admitted.
  
Lemma inversion_app Gamma M N T :
  typed Gamma (App M N) T ->
  exists T1, typed Gamma M (TFun T1 T) /\ typed Gamma N T1.
Proof.
Admitted.
*)


(* Canonical forms *)

(*
Lemma canonical_forms_bool Gamma v :
  val v ->
  typed Gamma v TBool ->
  v = true \/ v = false.
Proof.
Admitted.

Lemma canonical_forms_nat Gamma v :
  val v ->
  typed Gamma v TNat ->
  exists n, v = Const n.
Proof.
Admitted.

Lemma canonical_forms_fun Gamma v T1 T2 :
  val v ->
  typed Gamma v (TFun T1 T2) ->
  exists x S1 M, v = Fun x S1 M.
Proof with eauto.
Admitted.
*)


Lemma lookup_field_in_value Gamma vr TR l T :
  val vr ->
  typed Gamma vr TR ->
  rec_type_lookup l TR = Some T ->
  exists v, rec_term_lookup l vr = Some v /\ typed Gamma v T.
Proof.
  intros Hval Htyp Hget.
  induction Htyp; simpl in *; try congruence; try inv Hval.
  destruct (String.eq_dec l l0).
  - injection Hget as Hget. subst.
    exists M.
    split.
    + reflexivity.
    + apply Htyp1.
  - destruct IHHtyp2 as [vi [Hgeti Htypi]].
    + apply H5.
    + apply Hget.
    + exists vi.
      split.
      * apply Hgeti.
      * apply Htypi.
Qed. 


Theorem progress M T :
  typed StringMap.empty M T ->
  (val M) \/ (exists M', step M M').
Proof.
  intros.
  remember StringMap.empty as Gamma' eqn:HGamma'.
  induction H; intros.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - rewrite HGamma' in H.
    rewrite StringMap.lookup_empty in H.
    discriminate.
  - destruct IHtyped1.
    + apply HGamma'.
    + inv H; inv H1.
      destruct IHtyped2.
      * reflexivity.
      * inv H; inv H0.
        right. 
        exists (Const (n + n0)). 
        eapply Sum. 
        reflexivity.
      * right. 
        destruct H as [N' H]. 
        exists (Plus (Const n) N').  
        apply Sum_right.
        -- constructor.
        -- apply H. 
    + right.
      destruct H1 as [M' H1].
      exists (Plus M' N).
      apply Sum_left.
      apply H1.  
  - destruct IHtyped1.
    + apply HGamma'.
    + inv H2;
      inv H.
      * right. 
        exists M2.
        apply If_true.
      * right. 
        exists M3.
        apply If_false.
    + right.
      destruct H2 as [M1' H2].
      exists (If M1' M2 M3).
      apply If_step.
      apply H2.
  - destruct IHtyped1.
    + apply HGamma'.
    + inv H1;
      inv H.
      destruct IHtyped2.
      * reflexivity.
      * right.
        eexists.
        apply Beta.
        apply H.
      * right.
        destruct H as [N' H].
        eexists.
        apply App2.
        ++ constructor.
        ++ apply H.
    + right.
      destruct H1 as [M' H1].
      exists (App M' N).
      apply App1.
      apply H1.
  - left. constructor.
  - left. constructor.
  - destruct IHtyped1.
    + apply HGamma'.
    + destruct IHtyped2.
      * apply HGamma'.
      * left. constructor.
        -- apply H3.
        -- apply H4.
      * right.
        destruct H4 as [MR' H4].
        eexists.
        apply Eval_Record_Tail.
        -- apply H3.
        -- apply H4.
    + right.
      destruct H3 as [M' H3].
      eexists.
      apply Eval_Record_Head.
      apply H3.
  - right. 
    destruct IHtyped.
    + apply HGamma'.
    + inv H1;
      inv H.
      destruct (String.eq_dec l l0).
      * eexists. 
        apply Select. 
        -- constructor.
          ++ apply H2.
          ++ apply H3.
        -- simpl.
           subst.
           rewrite String.eq_dec_eq.
           reflexivity.
      * destruct (lookup_field_in_value StringMap.empty vr TR0 l T) as [vi [Hlkup _] ].
        -- apply H3.
        -- apply H8.
        -- apply H0.
        -- exists vi.
           apply Select.
           ++ constructor.
              ** apply H2.
              ** apply H3.
           ++ simpl.
              rewrite String.eq_dec_neq.
              ** apply Hlkup.
              ** apply n.
    + destruct H1 as [M' H1].
      exists (Sel M' l).
      apply Eval_Select.
      apply H1.
Qed.


(*
Definition alpha_equivalence x y T M :=
  Fun x T M = Fun y T (subst x (Var y) M).
*)


Lemma weakening Gamma x M S T :
  typed Gamma M T ->
  StringMap.lookup Gamma x = None ->
  typed (StringMap.insert x S Gamma) M T.
Proof.
  intros.
  induction H; intros.
  - apply T_True.
  - apply T_False.
  - apply T_Int.
  - admit.
  - apply T_Var.
    + rewrite StringMap.lookup_insert.
      destruct String.eq_dec.
      * rewrite e in H.
        rewrite H in H0.
        discriminate.
      * apply H.
    + apply H1.
  - apply T_Sum.
    + apply IHtyped1.
      apply H0.
    + apply IHtyped2.
      apply H0.
  - apply T_IfThenElse.
    + apply IHtyped1.
      apply H0.
    + apply IHtyped2.
      apply H0.
    + apply IHtyped3.
    apply H0.
  - eapply T_App.
    + apply IHtyped1.
      apply H0.
    + apply IHtyped2.
      apply H0.
  - apply T_Unit.
  - apply T_RNil.
  - apply T_RCons.
    + apply IHtyped1.
      apply H0.
    + apply IHtyped2.
      apply H0.
    + apply H2.
    + apply H3.
  - eapply T_Select.
    + apply IHtyped.
      apply H0.
    + apply H1.
Admitted.


Lemma substitution Gamma x M N S T :
  typed (StringMap.insert x S Gamma) M T ->
  typed Gamma N S ->
  typed Gamma (subst x N M) T.
Proof.
  intros.
  remember (StringMap.insert x S Gamma) as Gamma' eqn:HGamma'.
  revert H0.
  revert Gamma HGamma'.
  induction H; intros.
  - apply T_True.
  - apply T_False.
  - apply T_Int.
  - rewrite HGamma' in H0.
      rewrite StringMap.lookup_insert in H0.
      simpl.
      destruct (String.eq_dec); subst.
      -- inv H0.
      -- rewrite String.eq_dec_neq.
        ++ apply T_Fun.
          ** apply H.
          ** apply H0.
          ** eapply weakening in H2. 
            * apply IHtyped in H2.
            { apply H2. }
              { rewrite StringMap.insert_insert.
              rewrite String.eq_dec_neq.
              { reflexivity. }
              { congruence. }}
            * apply H0.
        ++ congruence.
  - simpl.
    rewrite HGamma' in H. 
    rewrite StringMap.lookup_insert in H.
    destruct (String.eq_dec x x0); destruct (String.eq_dec x0 x); try congruence.
    apply T_Var.
    + apply H. 
    + apply H0.
  - simpl. 
    apply IHtyped1 in HGamma' as H2.
    + apply IHtyped2 in HGamma' as H3.
      * apply T_Sum.
        -- apply H2.
        -- apply H3.
      * apply H1.
    + apply H1.
  - simpl. 
    apply IHtyped1 in HGamma' as H3; 
    apply IHtyped2 in HGamma' as H4;
    apply IHtyped3 in HGamma' as H5; 
    try apply H2.
    apply T_IfThenElse.
    + apply H3.
    + apply H4.
    + apply H5.
  - simpl.
    apply IHtyped1 in HGamma' as H3; 
    apply IHtyped2 in HGamma' as H4;
    try apply H1.
    eapply T_App.
    + apply H3.
    + apply H4.
  - apply T_Unit.
  - apply T_RNil.
  - simpl.
    apply T_RCons.
    + apply IHtyped1.
      * apply HGamma'.
      * apply H3.
    + apply IHtyped2.
      * apply HGamma'.
      * apply H3.
    + inv H1; constructor.
    + inv H2; constructor.
  - simpl.
    eapply T_Select.
    + apply IHtyped.
      * apply HGamma'.
      * apply H1.
    + apply H0.
Qed.


Lemma step_preserves_record_term TR TR' :
  rec_term TR ->
  step TR TR' ->
  rec_term TR'.
Proof.
  intros Hrt Hstp.
  inv Hrt.
  - inv Hstp.
  - inv Hstp.
    + constructor.
    + constructor.
Qed.


Theorem type_preservation Gamma M M' T :
  typed Gamma M T ->
  step M M' ->
  typed Gamma M' T.
Proof.
  intros.
  revert H.
  revert T.
  induction H0; intros.
  - inv H.
    inv H0.
    apply T_Int.
  - inv H.
    apply IHstep in H4.
    apply T_Sum.
    + apply H4.
    + apply H6.
  - inv H1.
    apply IHstep in H7.
    apply T_Sum.
    + apply H5.
    + apply H7.
  - inv H.
    apply H6.
  - inv H.
    apply H7.
  - inv H.
    apply IHstep in H5.
    apply T_IfThenElse.
    + apply H5.
    + apply H7.
    + apply H8.
  - inv H0.
    inv H4.
    eapply substitution.
    + apply H10.
    + apply H6.
  - inv H.
    apply IHstep in H4.
    eapply T_App.
    + apply H4.
    + apply H6.
  - inv H1.
    apply IHstep in H7.
    eapply T_App.
    + apply H5.
    + apply H7.
  - inv H1.
    destruct (lookup_field_in_value Gamma vr TR l T) as [vi [Hget Htyp] ].
    + apply H.
    + apply H5.
    + apply H7.
    + rewrite H0 in Hget. injection Hget as Hget. subst.
      apply Htyp.
  - inv H.
    apply IHstep in H4.
    eapply T_Select.
    + apply H4.
    + apply H6.
  - inv H.
    apply IHstep in H4.
    apply T_RCons.
    + apply H4.
    + apply H6.
    + apply H8.
    + apply H9.
  - inv H1.
    apply IHstep in H7.
    apply T_RCons.
    + apply H5.
    + apply H7.
    + eapply step_preserves_record_term.
      * apply H9.
      * apply H0.
    + apply H10.
Qed.


Corollary extended_type_preservation M M' T :
  typed StringMap.empty M T ->
  steps M M' ->
  typed StringMap.empty M' T.
Proof.
  intros.
  induction H0.
  - apply H.
  - apply IHsteps.
    eapply type_preservation.
    + apply H.
    + apply H0.
Qed.


Theorem safety M M' T :
  typed StringMap.empty M T ->
  steps M M' ->
  ~(stuck M').
Proof.
  intros H H1 H2.
  destruct H2.
  apply (extended_type_preservation M M' T) in H.
  - apply progress in H.
    destruct H; tauto.
  - apply H1.
Qed.

