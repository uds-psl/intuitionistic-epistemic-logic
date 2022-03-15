Require Import decidabilityK forms. 

Require Import Coq.Classes.CRelationClasses.
Require Import PslBase.Base.
Require Import PslBase.Lists.BaseLists. 
Require Import  decidability decidabilityK nd forms toolbox.

Section Models.
    Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            acc: world -> world -> Prop;
                            val: world -> valuation;
                            }.

   Fixpoint evalK {M: KripkeModel} (s: form) : (world) -> Prop := 
    match s with 
    | (K x)  => (fun y => forall r, ((acc y r) -> evalK x r))
    | Bot    => (fun x => False)
    | Var y  => (fun x => val x y)
    | x ⊃ y  => (fun z => (evalK y z) \/ ~(evalK x z))
    | s ∨ t  => (fun y => evalK s y \/ evalK t y)
    | s ∧ t  => (fun y => evalK s y /\  evalK t y)  
    end.

    Definition evalK' {M: KripkeModel} (Γ: context) :=
    fun w => forall s, (s el Γ) -> @evalK M s w.  

    Definition entails Γ φ := 
      forall (M : KripkeModel), ((forall w,evalK' Γ w -> @evalK M φ w)).
  Context {M: (@KripkeModel)}.

End Models.


Definition hil Γ A := gk3c Γ [A]. 

Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
  Variable A0 : context.
  Variable s0 : form.
  Definition U' := scl (s0::A0).
  Record mcTheory := mkmcTheory {
                         T: list form;
                         Tsubs: (T el (power U')) ;
                         Tcons: ~(hil T ⊥);
                         Tdedclos: forall A, A el U' ->  hil T A -> A el T; 
                       }.
  Definition single_extend (Ω: context) (A: form) (a: form) :=
      if (@gk3c_dec (a::Ω) [A]) then Ω else (a::Ω). 

      Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
  Proof. 
    intros a Ha.  unfold single_extend. destruct (gk3c_dec (B :: Ω) [A]); eauto.
  Qed.  

    Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
    match Γ with
      nil => Ω
    | (a::Γ') =>
      single_extend (extend Ω A Γ') A a  end.
    
  Lemma extend_two_possibilites Γ A B:
    ((single_extend Γ A B) === Γ /\ hil (B::Γ) A) \/   (single_extend Γ A B) === (B::Γ) /\ ~(hil (B::Γ) A). 
  Proof.
    destruct (gk3c_dec (B::Γ) [A]) eqn:id.
    - left. split; try tauto.
      split.
      + intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      + unfold single_extend. rewrite id; auto.
    - right.      split; auto. split.
      +  intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      +  unfold single_extend. rewrite id; auto.
  Qed.        

  Lemma extend_does_not_derive Ω A Γ: ~(hil Ω A) -> ~(hil (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (gk3c_dec (a :: extend Ω A Γ) [A]) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di. apply IHΓ.  auto. 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

  Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (gk3c_dec (a :: extend Ω A Γ) [A]); eauto.                          
  Qed.

  Lemma extend_does_not_derive_imp Ω Γ A B:
    ~(hil Ω A) -> B el Γ -> ~(hil (extend Ω A Γ) B) -> (hil (extend Ω A Γ) (B ⊃ A)).
  Proof.
    intros H H1. revert H. revert Ω.
    induction Γ.
    - intros.  eauto.
    - intros.  destruct H1.
      + subst a. simpl.
        destruct (extend_two_possibilites (extend Ω A Γ) A B) as [(E1 & E2) | (E1 & E2)].
        * apply gk3cW with (extend Ω A Γ) [(B ⊃ A)]. apply gk3cIR with B A. auto. apply gk3cW with (B::extend Ω A Γ) [A]; eauto.     destruct E1; auto. auto.
        * exfalso.   apply H0. simpl extend; fold extend. apply gk3cW with ( B :: extend Ω A Γ) [B].  apply gk3cA with B; auto. destruct E1; auto. auto. 
      + assert (~ hil (extend Ω A Γ) B).  intro. apply H0. apply gk3cW with (extend Ω A Γ) [B]. auto. apply single_extend_subcontext.  auto. 
        specialize (IHΓ H1 (Ω) H H2). 
        simpl extend.  apply gk3cW with (extend Ω A Γ) [B ⊃ A]; auto.  auto.  apply single_extend_subcontext. 
  Qed.   

  Lemma ImpAgree (Γ: context) (a b: form) :
    (hil Γ (a ⊃ b)) <-> (hil (a::Γ) b).  
  Proof.
    split.
    - intro H. admit. 
    -  intros.  apply gk3cIR with a b.  eauto. apply gk3cW with (a :: Γ) [b]; firstorder eauto.
  Admitted.      

  Lemma extend_locally_dclosed Γ Ω A B: ~(hil Ω A) -> (hil (extend Ω A Γ) (B)) -> B el Γ ->  B el (extend Ω A Γ).
  Proof.
    revert Ω B.  induction Γ.
    - intros.   inversion H1.
    - intros. destruct H1.
      + simpl extend; fold extend. destruct (extend_two_possibilites  (extend Ω A Γ) A a).  
        *  destruct H2. apply extend_does_not_derive with Ω A (a::Γ) in H.
           exfalso. apply H. subst a.  (*apply ndIE with B.  apply ndII. apply ndW with ((B :: extend Ω A Γ)). auto.
           unfold extend at 2.  fold extend. enough ((extend Ω A Γ ) <<= (single_extend (extend Ω A Γ) A B)).
           eauto.  apply single_extend_subcontext. auto. 
        *    subst a.  destruct H2. rewrite H1.  auto. 
      + 
        simpl extend. unfold single_extend. simpl extend in H0. unfold single_extend in H0.  destruct (ielg_dec (a :: extend Ω A Γ) A d) eqn:di.
        *  apply IHΓ; auto. 
        *  enough (B el (extend Ω A (a::Γ))). simpl extend in H2. unfold single_extend in H2. rewrite di in H2.   auto. simpl extend. unfold single_extend.   rewrite di.  right.   apply IHΓ. auto.  2: auto.  destruct (ielg_dec (extend Ω A Γ) B d); auto. exfalso.
           apply ImpAgree in H0.
           assert (HA := n0). 
           apply (extend_does_not_derive_imp H H1) in HA. apply n. apply ndIE with B.
           apply ndW with (extend Ω A Γ). auto.  auto. apply ndIE with a.  apply ndW with (extend Ω A Γ). auto.  auto.  apply ndA. auto. *) 
  Admitted.


  
  

Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
    Variable A0 : context.
  Variable s0 : form.
  Definition U' := scl (s0::(K ⊥)::A0).

   Record mcTheory := mkmcTheory {
                         T: list form;
                         B: form;
                         Tgood: ~(hil T B); 
                         Tsubs: T <<= U' ;
                         Tlcons: forall A, A el U' -> A el T \/ (hil (A::T) B) ;
    }.

    Definition single_extend (Ω: context) (A: form) (a: form) :=
      if (@gk3c_dec (a::Ω) [A]) then Ω else (a::Ω). 

      Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
  Proof. 
    intros a Ha.  unfold single_extend. destruct (gk3c_dec (B :: Ω) [A]); eauto.
  Qed.  

    Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
    match Γ with
      nil => Ω
    | (a::Γ') =>
      single_extend (extend Ω A Γ') A a  end.

      Lemma extend_does_not_derive Ω A Γ: ~(hil Ω A) -> ~(hil (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (gk3c_dec (a :: extend Ω A Γ) [A]) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di. apply IHΓ.  auto. 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

  
  Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (gk3c_dec (a :: extend Ω A Γ) [A]); eauto.                          
  Qed.

    Lemma extend_disjunction  Γ Ω A B: ~(hil Ω A) -> B el Γ ->  B el (extend Ω A Γ) \/ (hil (B::(extend Ω A Γ)) (A)).
  Proof.
    intros H H0. induction Γ.
    - inversion H0.
    -  destruct H0.
       + subst a. simpl extend. unfold single_extend. destruct (gk3c_dec (B :: extend Ω A Γ) [A]).  tauto.   left. auto.
       + specialize (IHΓ H0).   destruct IHΓ. left.   simpl extend. unfold single_extend. destruct (gk3c_dec (a :: extend Ω A Γ) [A]); eauto.
         * right. unfold hil. apply gk3cW with ((B :: extend Ω A Γ)) [A] ; auto.  intros x Hx. destruct Hx.
           -- subst x. eauto.
           --  right.   simpl extend. unfold single_extend. destruct (gk3c_dec (a :: extend Ω A Γ) [A]); auto.
  Qed.              

    Lemma extend_locally_prime Γ Ω A B C:  ~(hil Ω A) -> (B ∨ C) el (extend Ω A Γ)  -> B el Γ -> C el Γ -> B el (extend Ω A Γ) \/ C el (extend Ω A Γ).
  Proof.
    intros. destruct (extend_disjunction H H1); try tauto.  destruct (extend_disjunction H H2); try tauto. exfalso.
    specialize (@extend_does_not_derive Ω A Γ H). intro. apply H5. apply gk3cOL with B C.  auto. auto. auto. 
   Qed. 

    Lemma extend_locally_easy_subset Ω A Γ: (extend Ω A Γ) <<= (Ω ++ Γ).
  Proof.
    revert Ω. induction Γ. eauto. intros.  simpl extend. unfold single_extend. destruct (gk3c_dec (a :: extend Ω A Γ) [A]); auto.
    specialize (IHΓ Ω). intros b Hb.  apply  IHΓ in Hb. apply in_app_iff. apply in_app_iff in Hb. destruct Hb. tauto. right. right. assumption.
    intros b Hb.  destruct Hb; eauto. subst b; eauto. apply IHΓ in H.  apply in_app_iff in H; destruct H; apply in_app_iff; try tauto. right. right. auto. 
  Qed.

    
  Lemma extend_locally_subset Γ A Ω: Ω <<= Γ -> (extend Ω A Γ) <<= Γ.
  Proof.
    intros. enough (extend Ω A Γ <<= Γ ++ Γ).  intros a Ha. specialize (H0 a Ha). apply in_app_iff in H0; destruct H0; assumption.
    enough (extend Ω A Γ <<= Ω ++ Γ). intros a Ha. specialize (H0 a Ha).  apply in_app_iff in H0. destruct H0; eauto.  apply extend_locally_easy_subset. 
  Qed.   


  Definition valuationMKT (A: mcTheory) (a: nat) := (Var a) el (T A).
  Definition subsetVerif (A B:mcTheory) := (remNotK (T A)) <<= (T B). 

    Instance canonical: (KripkeModel).
  Proof.
    eapply mkKripkeModel.
    apply subsetVerif. 
    apply valuationMKT. 

   Defined. 

  Definition Lindenbaum (Γ : list form) (A: form) (H: Γ <<= U') (H'': A el U') (H': ~(hil Γ A)) : mcTheory.
  Proof.
    eapply mkmcTheory. 
        - apply extend_does_not_derive.  apply H'.
    - apply extend_locally_subset.     auto. 
    - intro. 
      intro. 
      specialize (@extend_does_not_derive Γ A U' H'). intro.
      specialize (extend_disjunction H' H0). intro. destruct H2. 
      +  left.  apply H2.
      +  right.   auto. 
  Defined.
  Definition U'_sfc : sf_closed U' := @scl_closed _.

    Lemma mctheory_conjucntion (Δ: mcTheory) A B: (A ∧ B) el (T Δ) -> (A el (T Δ)) /\  (B el (T Δ)).
  Proof.
    intros.
    split.
    - destruct Δ. simpl.  cbn in H.  specialize (  Tlcons0 A). destruct Tlcons0. enough ((A ∧ B) el U'). apply U'_sfc in H0; tauto.  eauto.   auto. exfalso. apply Tgood0. apply gk3cAL with A B.  auto.  apply gk3cW with ((A :: T0)) [B0]. auto.  firstorder eauto. auto. 
    - destruct Δ. simpl.  cbn in H.  specialize (  Tlcons0 B). destruct Tlcons0. enough ((A ∧ B) el U'). apply U'_sfc in H0; tauto.  eauto.   auto. exfalso. apply Tgood0. apply gk3cAL with A B.  auto.  apply gk3cW with ((B :: T0)) [B0]. auto.  firstorder eauto.   eauto. 
  Qed.

    Lemma mctheory_disjunction (Δ: mcTheory) A B: (A ∨ B) el (T Δ) -> (A el (T Δ)) \/  (B el (T Δ)).
  Proof.
    destruct Δ. intros. 
    intros. decide (A el (T0)); decide (B el (T0)). all: try tauto.
    cbn in H. cbn. enough (A el U'). enough (B el U'). pose proof (Tlcons0 A H0) as Ha.   pose proof (Tlcons0 B H1) as Hb.  destruct Ha; destruct Hb; try tauto.
    exfalso. apply Tgood0. apply gk3cOL with  A B. auto. auto. auto. all: apply Tsubs0 in H;   apply U'_sfc in H; tauto.
  Qed.

  Print unK. 
  Print remNotK. 
    Lemma truth_lemma : forall (x: form), In x U' -> forall (t: (@world  canonical)), ( (x el (T t) -> (evalK x t))  /\( ~(hil (T t) x) -> ~(evalK x t))).
  Proof.
    intro x. intro Hx. induction x.
        - intros w. split.
      + intros H w' v.  apply IHx. apply U'_sfc in Hx. auto.   apply v. admit. 
      + intros D D1.   assert (~(hil (remNotK (T w)) x)).   intro. apply D. apply gk3cKI with x. auto.  apply H.  
        assert (exists Δ: mcTheory, (remNotK (T w)) <<= (T Δ)
                                   /\ ~(hil (T Δ) (x))).
        {
          assert ((remNotK (T w)) <<= U'). { destruct w.  intros a Ha. admit.  }
          apply U'_sfc in Hx.                                 
          eexists (@Lindenbaum  (remNotK (T w)) x H0 Hx H). split.
          - simpl. apply extend_subset.    
          - simpl. apply extend_does_not_derive.  auto. 
        }
        
        destruct H0 as (w' & Hw').
        specialize (IHx (U'_sfc Hx) w').  destruct IHx. destruct Hw'.  specialize (H1 H3). specialize (D1 w').   apply H1. apply D1. auto.
    -  intros w.  split.
      + intro H. simpl evalK. assert (x2 el (T w) \/ ~(hil (T w) x1)).
        {
          decide (x2 el (T w)); try tauto.
          right. intro.
           cbn in H0. destruct w. destruct (Tlcons0 x2). apply U'_sfc in Hx.  tauto. cbn in n. congruence.
          cbn in n. apply Tgood0. apply gk3cIL with x1 x2.  auto. auto. apply gk3cW with T0 [x1]; auto.   auto.            
        }
        destruct H0.
        * left.   apply IHx2. apply U'_sfc in Hx; tauto. auto.
        * right.  apply IHx1 in H0.   congruence. apply U'_sfc in Hx; tauto.  
      + intro. decide (x2 el (T w)). exfalso. apply H.  apply gk3cIR with x1 x2.  auto. apply gk3cA with x2.   right.  exact i.  auto.
        intro.  simpl evalK in H0. destruct H0.
        *    assert (~ hil (x1::(T w)) x2). {
          intro. apply H. apply gk3cIR with x1 x2. auto. apply gk3cW with (x1 :: T w) [x2]; auto. 
        }
         pose proof (U'_sfc Hx). simpl in H2.  destruct H2 as [sf1 sf2].
        
         enough (exists w' : mcTheory, (x1::(T w)) <<= (T w') /\ ~(hil (T w') x2)).
         
         destruct H2 as (w' & Hw' & Hw'2). pose proof (IHx2 sf2 w').  destruct H2.  apply H3.  auto. 
         admit.  admit. 
        *    pose proof (U'_sfc Hx). simpl in H1.  destruct H1 as [sf1 sf2]. clear H0.  specialize (IHx1 sf1). specialize (IHx2 sf2). clear sf1 sf2.
             decide (x1 el T w). 
         apply Hw'2. apply gk3cIL with x1 x2. 
        apply U'_sfc in Hx. destruct Hx as (Hx1 & Hx2). pose proof (IHx2 Hx2 w'). pose proof (IHx1 Hx1 w').    destruct H2.  destruct H3. 
        destruct H0.
        * apply H4. auto.  (* Idea: Use monotnicity -> evalK x2 w should suffice *)
            admit. 
        *   apply H5.  2: auto. intro. 
           
          apply H5; auto. intro.   apply H0.   apply IHx1.  auto.  destruct (Tlcons w sf1). auto. assert (~ hil (T w') (B w')).   
          
          apply H3. apply gk3cW with  (x1 :: T w) [x2]. 
       (* apply H2.  apply Hw'. intros a Ha.  apply Hw'.  auto.  apply IHx1.  apply Hw'.  auto. *)
        * assert ((x1::(T w)) <<= U'). {  intros a Ha. destruct Ha.  subst a. apply U'_sfc in Hx; tauto.  destruct w; eauto. }
                                    apply U'_sfc in Hx; destruct Hx. 
         eexists (@Lindenbaum  (x1::(T w)) x2 H2 sf2 H1). split.
          ** simpl. apply extend_subset.    
          **
            simpl. apply extend_does_not_derive.  auto. 

    - intros w.  split.
      + intro. apply mctheory_conjucntion in H.  split.
        * apply IHx1. apply U'_sfc in Hx.  tauto.  tauto.
        * apply IHx2.  apply U'_sfc in Hx.  tauto.  tauto.
      + intro.    intro.  destruct H0.
        assert (~(hil (T w) x1) \/ ~(hil (T w) x2)). {
          destruct (gk3c_dec (T w) [x1]).  destruct (gk3c_dec (T w) [x2]).  exfalso. apply H. apply gk3cAR with x1 x2; auto. apply gk3cW with (T w) [x1]; eauto.
           apply gk3cW with (T w) [x2]; eauto. eauto.  eauto. 
        }
        apply U'_sfc in Hx.  destruct Hx as (Hx1 & Hx2). specialize (IHx1 Hx1 w). specialize (IHx2 Hx2 w). destruct IHx1, IHx2.   destruct H2.
        * specialize (H4 H2). congruence.
        * specialize (H6 H2). congruence.
    - intros w. split.
      + intro. apply mctheory_disjunction in H.  destruct H.
        * simpl evalK. left. apply IHx1. apply U'_sfc in Hx; tauto.  auto.
        * right. apply IHx2. apply U'_sfc in Hx; tauto.  auto.
      +  apply U'_sfc in Hx.  destruct Hx as (Hx1 & Hx2).
         intro. intro. apply H.   destruct H0.
         * apply gk3cOR with x1 x2. auto.  apply gk3cW with (T w) [x1]; auto.  destruct (gk3c_dec (T w) [x1]); try tauto.   apply IHx1 in n.  congruence.  tauto.
         * apply gk3cOR  with x1 x2. auto. apply gk3cW with (T w) [x2]; auto.  destruct (gk3c_dec (T w) [x2]); try tauto.   apply IHx2 in n.  congruence.  tauto.
    -  intros w. split.
       + intro.  simpl evalK. destruct w. apply Tgood0. apply gk3cF. auto.
       + intro. intro.  unfold evalK in H0. auto.
    -  intros w. split.
       + intro. apply H.
       + intro.   intro. apply H. apply gk3cA with (Var n). apply H0. auto. 
Qed. 
