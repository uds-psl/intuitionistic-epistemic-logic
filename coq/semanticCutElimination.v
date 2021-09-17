(** * Semantic Cut-Elimination (following Su & Sano ) *)

Require Import models nd forms decidability toolbox.
Require Import PslBase.Base.

Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
  Context {d : DerivationType}.
    Variable A0 : context.
  Variable s0 : form.
  Definition U' := scl (s0::(K ⊥)::A0).

  Record mcTheory := mkmcTheory {
                         T: list form;
                         B: form;
                         Tgood: ~(gen T B); 
                         Tsubs: T <<= U' ;
                         Tlcons: forall A, A el U' -> A el T \/ (gen (A::T) B) ;
                       }.

  (** Define extension operator on theories  **)

  Definition single_extend (Ω: context) (A: form) (a: form) :=
    if (@gen_dec (a::Ω) A d) then Ω else (a::Ω). 

  Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
  Proof. 
    intros a Ha.  unfold single_extend. destruct (gen_dec (B :: Ω) A d); eauto.
  Qed.  
  Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
    match Γ with
      nil => Ω
    | (a::Γ') =>
      single_extend (extend Ω A Γ') A a  end.

  Lemma extend_does_not_derive Ω A Γ: ~(gen Ω A) -> ~(gen (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (gen_dec (a :: extend Ω A Γ) A d) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di. apply IHΓ.  auto. 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

  Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (gen_dec (a :: extend Ω A Γ) A d); eauto.                          
  Qed.

  Lemma extend_disjunction  Γ Ω A B: ~(gen Ω A) -> B el Γ ->  B el (extend Ω A Γ) \/ (gen (B::(extend Ω A Γ)) (A)).
  Proof.
    intros H H0. induction Γ.
    - inversion H0.
    -  destruct H0.
       + subst a. simpl extend. unfold single_extend. destruct (gen_dec (B :: extend Ω A Γ) A d).  tauto.   left. auto.
       + specialize (IHΓ H0).   destruct IHΓ. left.   simpl extend. unfold single_extend. destruct (gen_dec (a :: extend Ω A Γ) A d); eauto.
         * right. apply genW with ((B :: extend Ω A Γ)); auto.  intros x Hx. destruct Hx.
           -- subst x. eauto.
           --  right.   simpl extend. unfold single_extend. destruct (gen_dec (a :: extend Ω A Γ) A d); auto.
  Qed.              

  Lemma extend_locally_prime Γ Ω A B C:  ~(gen Ω A) -> (B ∨ C) el (extend Ω A Γ)  -> B el Γ -> C el Γ -> B el (extend Ω A Γ) \/ C el (extend Ω A Γ).
  Proof.
    intros. destruct (extend_disjunction H H1); try tauto.  destruct (extend_disjunction H H2); try tauto. exfalso.
    specialize (@extend_does_not_derive Ω A Γ H). intro. apply H5. apply genOL with B C.  auto. auto. auto. 
   Qed. 

  Lemma extend_locally_easy_subset Ω A Γ: (extend Ω A Γ) <<= (Ω ++ Γ).
  Proof.
    revert Ω. induction Γ. eauto. intros.  simpl extend. unfold single_extend. destruct (gen_dec (a :: extend Ω A Γ) A d); auto.
    specialize (IHΓ Ω). intros b Hb.  apply  IHΓ in Hb. apply in_app_iff. apply in_app_iff in Hb. destruct Hb. tauto. right. right. assumption.
    intros b Hb.  destruct Hb; eauto. subst b; eauto. apply IHΓ in H.  apply in_app_iff in H; destruct H; apply in_app_iff; try tauto. right. right. auto. 
  Qed.
  
  Lemma extend_locally_subset Γ A Ω: Ω <<= Γ -> (extend Ω A Γ) <<= Γ.
  Proof.
    intros. enough (extend Ω A Γ <<= Γ ++ Γ).  intros a Ha. specialize (H0 a Ha). apply in_app_iff in H0; destruct H0; assumption.
    enough (extend Ω A Γ <<= Ω ++ Γ). intros a Ha. specialize (H0 a Ha).  apply in_app_iff in H0. destruct H0; eauto.  apply extend_locally_easy_subset. 
  Qed.   
  (* Not deriven implies adding it causes us to derive A *)
  Definition U'_sfc : sf_closed U' := @scl_closed _.

  Definition subsetMKT (A B: mcTheory) :=  (T A) <<= (T B).
  Definition valuationMKT (A: mcTheory) (a: nat) := (Var a) el (T A).
  Definition subsetVerif (A B:mcTheory) := (unK (T A)) <<= (T B). 

  Instance canonical: (KripkeModel).
  Proof.
    apply mkKripkeModel with (world := mcTheory) (cogn := subsetMKT) (val := valuationMKT) (verif := subsetVerif).
    firstorder.  firstorder.
    + intros A B c d' E. unfold subsetVerif in c.  apply c.  apply unK_in_iff.  eauto.
    +   intros x y z H H0. intros a Ha.  apply unK_in_iff in Ha. destruct Ha; auto.  apply H0. apply unK_in_iff. left. apply H. auto. apply H0. apply unK_in_iff. right. apply H.  auto.
  Defined.     

  Definition Lindenbaum (Γ : list form) (A: form) (H: Γ <<= U') (H'': A el U') (H': ~(gen Γ A)) : mcTheory.  
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

  Lemma mctheory_conjucntion (Δ: mcTheory) A B: (A ∧ B) el (T Δ) -> (A el (T Δ)) /\  (B el (T Δ)).
  Proof.
    intros.
    split.
    - destruct Δ. simpl.  cbn in H.  specialize (  Tlcons0 A). destruct Tlcons0. enough ((A ∧ B) el U'). apply U'_sfc in H0; tauto.  eauto.   auto. exfalso. apply Tgood0. apply genAL with A B.  auto.  apply genW with ((A :: T0)). auto.  firstorder eauto.
    - destruct Δ. simpl.  cbn in H.  specialize (  Tlcons0 B). destruct Tlcons0. enough ((A ∧ B) el U'). apply U'_sfc in H0; tauto.  eauto.   auto. exfalso. apply Tgood0. apply genAL with A B.  auto.  apply genW with ((B :: T0)). auto.  firstorder eauto.  
  Qed.

  Lemma mctheory_disjunction (Δ: mcTheory) A B: (A ∨ B) el (T Δ) -> (A el (T Δ)) \/  (B el (T Δ)).
  Proof.
    destruct Δ. intros. 
    intros. decide (A el (T0)); decide (B el (T0)). all: try tauto.
    cbn in H. cbn. enough (A el U'). enough (B el U'). pose proof (Tlcons0 A H0) as Ha.   pose proof (Tlcons0 B H1) as Hb.  destruct Ha; destruct Hb; try tauto.
    exfalso. apply Tgood0. apply genOL with  A B. auto. auto. auto. all: apply Tsubs0 in H;   apply U'_sfc in H; tauto.
  Qed.


  
  Lemma truth_lemma : forall (x: form), In x U' -> forall (t: (@world  canonical)), ( (x el (T t) -> (evalK x t))  /\( ~(gen (T t) x) -> ~(evalK x t))).
  Proof.
    intro x. intro Hx. induction x.
    - intros w. split.
      + intros H w' v.  apply IHx. apply U'_sfc in Hx. auto.   apply v. apply unK_in_iff. tauto. 
      + intros D D1.   assert (~(gen (unK (T w)) x)).   intro. apply D. apply genKI. auto. apply U'_sfc in Hx.  specialize (IHx Hx). 
        assert (exists Δ: mcTheory, (unK (T w)) <<= (T Δ)
                                   /\ ~(gen (T Δ) (x))).
        {
          assert ((unK (T w)) <<= U'). { destruct w.  intros a Ha. apply unK_in_iff in Ha.  destruct Ha; auto.  assert (K a el U') by auto.  apply U'_sfc in H1.  assumption. }
          eexists (@Lindenbaum  (unK (T w)) x H0 Hx H). split.
          - simpl. apply extend_subset.    
          - simpl. apply extend_does_not_derive.  auto. 
        }
        
        destruct H0 as (w' & Hw').
        specialize (IHx w').  destruct IHx. destruct Hw'.  specialize (H1 H3). specialize (D1 w').   apply H1. apply D1. auto.

    - intros w.  split.
      + intro H. apply U'_sfc in Hx. intros w' Hw' c. assert (x2 el (T w') \/ ~(gen (T w') x1)).
        {
          decide (x2 el (T w')); try tauto.
          right. intro.
          destruct w'. cbn in H0. destruct (Tlcons0 x2).  tauto. cbn in n. congruence.
          cbn in n. apply Tgood0. apply genIL with x1 x2.  auto. auto.  auto.            
        }
        destruct H0.
        *  apply IHx2. tauto. auto.
        *  apply IHx1 in H0.   congruence. tauto. 
      + intro. intro. assert (~ gen (x1::(T w)) x2). {
          intro. apply H. apply genIR. auto. 
        }
        enough (exists w' : mcTheory, (x1::(T w)) <<= (T w') /\ ~(gen (T w') x2)).
        destruct H2 as (w' & Hw' & Hw'2).
        apply U'_sfc in Hx. destruct Hx as (Hx1 & Hx2). specialize (IHx2 Hx2 w'). specialize (IHx1 Hx1 w').    destruct IHx2. apply H3.  auto.
        apply H0. intros a Ha.  apply Hw'.  auto.  apply IHx1.  apply Hw'.  auto.
        assert ((x1::(T w)) <<= U'). {  intros a Ha. destruct Ha.  subst a. apply U'_sfc in Hx; tauto.  destruct w; eauto. }
                                    apply U'_sfc in Hx; destruct Hx. 
          eexists (@Lindenbaum  (x1::(T w)) x2 H2 H4 H1). split.
          * simpl. apply extend_subset.    
          * simpl. apply extend_does_not_derive.  auto. 

    - intros w.  split.
      + intro. apply mctheory_conjucntion in H.  split.
        * apply IHx1. apply U'_sfc in Hx.  tauto.  tauto.
        * apply IHx2.  apply U'_sfc in Hx.  tauto.  tauto.
      + intro.    intro.  destruct H0.
        assert (~(gen (T w) x1) \/ ~(gen (T w) x2)). {
          destruct (gen_dec (T w) x1 d).  destruct (gen_dec (T w) x2 d).  exfalso. apply H. apply genAR; auto. tauto.  tauto. 
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
         * apply genOR1. destruct (gen_dec (T w) x1 d); try tauto.   apply IHx1 in n.  congruence.  tauto.
         * apply genOR2. destruct (gen_dec (T w) x2 d); try tauto.   apply IHx2 in n.  congruence.  tauto.
    -  intros w. split.
       + intro.  simpl evalK. destruct w. apply Tgood0. apply genF. auto.
       + intro. intro.  unfold evalK in H0. auto.
    -  intros w. split.
       + intro. apply H.
       + intro.   intro. apply H. apply genV. apply H0.
  Qed.

  Lemma are_iel_models: d = normal -> forall w, exists u, verif w u. 
  Proof.
    intros. 
    assert (exists Δ: mcTheory, (unK (T w)) <<= (T Δ)).
    {
      destruct w.
      assert (~(gen (unK T0) (⊥))).
      intro. apply Tgood0. rewrite H.   apply genKB. apply genKI. subst d.   eapply H0.
      
      enough (unK (T0) <<= U').
      assert (⊥ el U'). {
        unfold U'. simpl.  firstorder eauto. 
      }
      exists (Lindenbaum  H1 H2 H0).
      simpl T. enough (unK (T0) <<= (extend (unK T0) (⊥) U')).
      intros a Ha. apply H3. assumption.
      apply extend_subset; auto.
      intros a Ha.   apply unK_in_iff in Ha; destruct Ha; eauto.
      apply Tsubs0 in H1.  apply U'_sfc in H1.  auto. 
    }
    destruct H0.  exists x.  firstorder eauto. 
  Qed.  


    Lemma completeness' Ω A: A el U' -> Ω <<= U' -> entails Ω A -> gen Ω A. 
  Proof.
    intros Au U H. destruct (gen_dec Ω A d); auto.  exfalso. 
    unfold entails in H.
    specialize (H (@canonical)).
     assert (exists Δ: mcTheory, ~(gen (T Δ) A) /\ (Ω <<= (T Δ))).
     {
       eexists (Lindenbaum  U Au n). split.
       - simpl.  apply extend_does_not_derive.   auto.
       - simpl.   apply extend_subset. 
     }
     assert (model_constraint canonical). {
       destruct d eqn:dn; simpl; auto. unfold isIEL.  apply are_iel_models. auto. 
       
     }
     specialize (H H1). 
     destruct (H0) as [Δ H2].
     specialize (H Δ). destruct H2.
     decide (A el (T Δ)).
    + apply H2. apply genA.  auto.
    +
      pose proof (truth_lemma Au Δ).

      destruct H4. specialize (H5 H2).   apply H5.  apply H.   unfold evalK'.   intros s H6.
      apply truth_lemma.  auto.  auto. 
  Qed.   

End Canonical. 


Lemma completeness Ω A (D: DerivationType): entails Ω A -> gen Ω A.
Proof.
  intro. apply completeness' with Ω A. unfold U'. apply scl_incl'. auto. intros a Ha. apply scl_incl'. auto. auto.
Qed.


Lemma soundnessGen (Γ: context) (A: form) {D: DerivationType}:
  gen Γ A -> entails Γ A.
Proof. 
  intros H % gen2nd.  eapply soundness.  auto.
Qed.   

(**
   ** Semantic Cut-Elimination 
 **)

Lemma semaCut Γ A (D: DerivationType):
  nd Γ A -> gen Γ A. 
Proof.
  intro. apply soundness in H. apply completeness.  assumption.
Qed.   
(** Soundness w.r.t gen used by using nd soundness **)
Lemma semaCut' Γ A B (D: DerivationType):
  gen Γ A -> gen (A::Γ) B -> gen Γ B.
Proof.
  intros H1 % gen2nd H2 % gen2nd.
  apply semaCut.
  eauto. 
Qed.
