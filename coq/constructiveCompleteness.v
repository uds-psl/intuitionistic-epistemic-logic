(** * Constructive Completeness *)

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
                         Tsubs: (T el (power U')) ;
                         Tcons: ~(nd T ⊥);
                         TUPrime: forall A B,  (A ∨ B) el T -> A el T \/ B el T;
                         Tdedclos: forall A, A el U' ->  nd T A -> A el T; 
                       }.


  (** Define extension operator on theories  **)

  Definition single_extend (Ω: context) (A: form) (a: form) :=
    if (@ielg_dec (a::Ω) A d) then Ω else (a::Ω). 

  Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
  Proof. 
    intros a Ha.  unfold single_extend. destruct (ielg_dec (B :: Ω) A d); eauto.
  Qed.

  Lemma extend_two_possibilites Γ A B:
    ((single_extend Γ A B) === Γ /\ (B::Γ) ⊢ A) \/   (single_extend Γ A B) === (B::Γ) /\ ~((B::Γ) ⊢ A). 
  Proof.
    destruct (ielg_dec (B::Γ) A d) eqn:id.
    - left. split; try tauto.
      split.
      + intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      + unfold single_extend. rewrite id; auto.
    - right.      split; auto. split.
      +  intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      +  unfold single_extend. rewrite id; auto.
  Qed.        
  Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
    match Γ with
      nil => Ω
    | (a::Γ') =>
      single_extend (extend Ω A Γ') A a  end.

  Lemma extend_does_not_derive Ω A Γ: ~(nd Ω A) -> ~(nd (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (ielg_dec (a :: extend Ω A Γ) A d) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di. apply IHΓ.  auto. 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

  Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (ielg_dec (a :: extend Ω A Γ) A d); eauto.                          
  Qed.

  Lemma extend_does_not_derive_imp Ω Γ A B:
    ~(nd Ω A) -> B el Γ -> ~(nd (extend Ω A Γ) B) -> (nd (extend Ω A Γ) (B ⊃ A)).
  Proof.
    intros H H1. revert H. revert Ω.
    induction Γ.
    - intros.  eauto.
    - intros.  destruct H1.
      + subst a. simpl.
        destruct (extend_two_possibilites (extend Ω A Γ) A B) as [(E1 & E2) | (E1 & E2)].
        * apply ndW with (extend Ω A Γ). eauto.  destruct E1; auto.
        * exfalso.   apply H0. simpl extend; fold extend. apply ndW with ( B :: extend Ω A Γ).  apply ndA. auto. destruct E1; auto. 
      + assert (~extend Ω A Γ ⊢ B).  intro. apply H0. apply ndW with (extend Ω A Γ). auto. apply single_extend_subcontext. 
        specialize (IHΓ H1 (Ω) H H2). 
        simpl extend.  apply ndW with (extend Ω A Γ). auto.  apply single_extend_subcontext. 
  Qed.   

  Lemma ImpAgree (Γ: context) (a b: form) :
    Γ ⊢ (a ⊃ b) <-> ((a::Γ) ⊢ b).  
  Proof.
    split.
    - intro H.  apply ndIE with a; auto. apply ndW with Γ; firstorder eauto.
    -  intros.  apply ndII. firstorder eauto.
  Qed.      

  Lemma extend_locally_dclosed Γ Ω A B: ~(nd Ω A) -> (nd (extend Ω A Γ) (B)) -> B el Γ ->  B el (extend Ω A Γ).
  Proof.
    revert Ω B.  induction Γ.
    - intros.   inversion H1.
    - intros. destruct H1.
      + simpl extend; fold extend. destruct (extend_two_possibilites  (extend Ω A Γ) A a).  
        *  destruct H2. apply extend_does_not_derive with Ω A (a::Γ) in H.
           exfalso. apply H. subst a. apply ndIE with B.  apply ndII. apply ndW with ((B :: extend Ω A Γ)). auto.
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
           apply ndW with (extend Ω A Γ). auto.  auto. apply ndIE with a.  apply ndW with (extend Ω A Γ). auto.  auto.  apply ndA. auto. 
  Qed.

  Lemma extend_locally_prime Γ Ω A B C:  ~(nd Ω A) -> (nd (extend Ω A Γ) (B ∨ C)) -> B el Γ -> C el Γ -> B el (extend Ω A Γ) \/ C el (extend Ω A Γ).
  Proof.
    intros. decide (B el (extend Ω A Γ)).  auto. decide (C el (extend Ω A Γ)).  auto. assert (~(extend Ω A Γ ⊢ (B ∨ C))).
    assert (~(extend Ω A Γ ⊢ B)). intro. apply (extend_locally_dclosed H) in H3. congruence. auto.
    assert (~(extend Ω A Γ ⊢ C)). intro. apply (extend_locally_dclosed H) in H4. congruence. auto. intro. specialize (@extend_does_not_derive Ω A Γ  H ). intro.  apply H6. apply ndDE with B C. auto.
    apply extend_does_not_derive_imp. auto.  auto.  auto.   apply extend_does_not_derive_imp; auto.   congruence. 
  Qed.


  Lemma extend_locally_easy_subset Ω A Γ: (extend Ω A Γ) <<= (Ω ++ Γ).
  Proof.
    revert Ω. induction Γ. eauto. intros.  simpl extend. unfold single_extend. destruct (ielg_dec (a :: extend Ω A Γ) A d); auto.
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
  
  Definition Lindenbaum (Γ : list form) (A: form) (H: Γ <<= U') (H': ~(nd Γ A)) : mcTheory.  
  Proof.
    eapply mkmcTheory with (rep (extend Γ A U') U').
    - apply rep_power. 
    - enough (~ nd (extend Γ A U') ⊥).
      intro. apply H0. apply (ndW H1).   apply rep_incl.
      intro. apply extend_does_not_derive with Γ A U' in H'. apply H'.  apply ndE. auto.
      
    - intros. rewrite rep_equi in *. 
      apply extend_locally_prime.  auto.  apply ndA.  auto. apply extend_locally_subset in H0.  apply U'_sfc in H0; tauto. auto. apply extend_locally_subset in H0.   apply U'_sfc in H0; tauto. auto.
      all: try apply extend_locally_subset; auto. 
    - intros.
       rewrite rep_equi in *. 
       apply extend_locally_dclosed; auto.  
       apply ndW with ((rep (extend Γ A U') U')). eauto. apply rep_equi.
       all: try apply extend_locally_subset; auto. 
  Defined.

  (* Canonical models are IEL models *)
  Lemma are_iel_models: d = normal -> forall w, exists u, verif w u. 
  Proof.
    intros. 
    assert (exists Δ: mcTheory, (unK (T w)) <<= (T Δ)).
    {
      assert (unK (T w) <<= U'). 
      {
        intros a Ha. apply unK_in_iff in Ha.   destruct Ha; eauto.  destruct w.
        simpl in H0. apply power_incl in Tsubs0. eauto.
        destruct w.
        assert ((K a) el U'). simpl in H0. apply power_incl in Tsubs0. auto. apply U'_sfc in H1; auto. 
      } 
      enough (~ nd (unK (T w)) ⊥).
      eexists (Lindenbaum  H0 H1).
      simpl T. enough (unK (T w) <<= (extend (unK (T w)) ⊥ U')).
      enough ((extend (unK (T w)) ⊥ U') <<= (rep (extend (unK (T w)) ⊥ U') U')).
      intros a Ha. apply H3. apply H2. assumption.
      apply rep_equi. apply extend_locally_subset; auto.  
      apply extend_subset.
      intro. cut (gen (T w) (K ⊥)). intro. apply (@Tcons w). rewrite H.  apply ndgen_iff.   apply genKB.  rewrite H in H2.  apply H2.
      apply genKI.  apply ndgen_iff. apply H1.
    }
    destruct H0.  exists x.  firstorder eauto. 
  Qed.  
  
  Lemma truth_lemma : forall (x: form), In x U' -> forall (t: (@world  canonical)), (evalK x t) <-> x el (T t).
  Proof.
    intro x. intro Hx. induction x.
    - intros w. split.
      + intro. decide (K x el (T w)); eauto.  exfalso.
        assert (exists Δ: mcTheory, (unK (T w)) <<= (T Δ)
                                   /\ ~(x el (T Δ))).
        {
          destruct w. simpl. assert ((x::T0) <<= U'). intros a Ha. destruct Ha; eauto. subst a. apply  U'_sfc in Hx; auto. cbn in H.  specialize (power_incl Tsubs0). eauto. 
          assert (~(nd (unK T0) x)). {
            intro. apply n. simpl. apply Tdedclos0; auto.   apply ndgen_iff. apply ndgen_iff in H1.  apply genKI. auto.  (* TODO: Remove ndgen_iff *)
          }
          assert (unK T0 <<= U'). {
            intros a Ha. apply unK_in_iff in Ha. destruct Ha; auto.
            assert ((K a el U')).             specialize (power_incl Tsubs0). eauto. apply U'_sfc in H3. eauto. 

          }
          eexists (@Lindenbaum  (unK T0) x H2   H1 ). split.
          - simpl. rewrite rep_equi.  apply extend_subset.     apply extend_locally_subset.
            auto. 
          - simpl.  enough (~(nd (extend (unK T0) x U') x)). {
              intro.  apply H3. apply ndA. apply rep_incl in H4.  auto. 
            }   apply  extend_does_not_derive. rewrite-> ndgen_iff.  auto. intro.  apply H1.  apply ndgen_iff. auto.  (* TODO: Remove ndgen_iff *) 
        }
        destruct H0 as (w' & Hw' & Hw'd).
        specialize (H w'). apply Hw'd. apply IHx.   apply U'_sfc in Hx; tauto.  apply H. firstorder eauto.
      + intros H Ω vo.  apply IHx.  apply U'_sfc in Hx; tauto. apply vo.  apply unK_in_iff.  tauto.
    - intro w.     split.
      + intro. decide ((x1 ⊃ x2) el (T w)); eauto.  exfalso.
         assert (exists Δ: mcTheory, (x1::(T w)) <<= (T Δ)
                                   /\ ~(x2 el (T Δ))).
         {
           destruct w. simpl.
           assert ((x1::T0 <<= U')).
           { intros a Ha; destruct Ha. subst a. apply U'_sfc in Hx; tauto. eauto using power_incl.
             specialize (power_incl Tsubs0).  firstorder eauto. 
           }
           assert (~ nd (x1 :: T0) x2).  {
             intro. apply ImpAgree in H1. apply n.  apply Tdedclos0 in H1.  assumption.  assumption. 
           }                          
           eexists (Lindenbaum  H0 H1). split.
           - simpl T. rewrite rep_equi.  apply extend_subset.
             apply extend_locally_subset. auto. 
           - simpl. enough (~(nd (extend (x1 :: T0) x2 U') x2)). {
               intro.  apply H2. apply ndA.  auto. apply rep_equi in H3. auto.
                apply extend_locally_subset. auto. 
            } apply extend_does_not_derive.  auto.
         }
         destruct H0 as (Ω & Ho1 & Ho2).
         specialize (H Ω).  apply Ho2.  apply IHx2.   apply U'_sfc in Hx; tauto. apply H.  firstorder eauto. apply IHx1. apply U'_sfc in Hx; tauto.    eauto.
      + intro. intros Ω Hc He. apply IHx2.  apply U'_sfc in Hx; tauto. apply Tdedclos. apply U'_sfc in Hx; tauto.  apply ndIE with x1.
        apply ndA. auto. apply ndA. apply IHx1; auto. apply U'_sfc in Hx; tauto.
    - intro w.  split.
      + intro. destruct H.  apply Tdedclos.  auto.  apply ndCI;  apply ndA. apply IHx1.  apply U'_sfc in Hx; tauto. auto.
        apply IHx2.  apply U'_sfc in Hx; tauto. auto.
      +   intro.  split.
          * apply IHx1. apply U'_sfc in Hx; tauto. apply Tdedclos. apply U'_sfc in Hx; tauto.
            apply ndCEL with x2. auto. 
          *  apply IHx2. apply U'_sfc in Hx; tauto. apply Tdedclos.  apply U'_sfc in Hx; tauto.
             apply ndCER with x1. auto.
    -   intro w. split. 
        + intro H.  destruct H. 
          * apply Tdedclos. auto.  apply ndDIL.  apply ndA. apply IHx1.   apply U'_sfc in Hx; tauto. auto.
          *  apply Tdedclos. auto.  apply ndDIR.  apply ndA.  apply IHx2.   apply U'_sfc in Hx; tauto. auto.
        + intro. apply TUPrime in H.  destruct H.
          * left. apply IHx1; eauto.   apply U'_sfc in Hx; tauto.
          * right. apply IHx2; eauto.   apply U'_sfc in Hx; tauto.
    -         firstorder eauto. exfalso. destruct t.  apply Tcons0.  apply ndA.  apply H.
    -           firstorder eauto.
                 
  Qed.

  Lemma gen_stable Γ A: ~~(gen Γ A) -> gen Γ A.
  Proof.
    intros. destruct (@gen_dec Γ A d).  auto. exfalso.  tauto.
  Qed.

  Lemma nd_stable Γ A: ~~(nd Γ A) -> nd Γ A.
  Proof.
    intros. destruct (@ielg_dec Γ A d).  auto. exfalso.  tauto.
  Qed.   

  (** Show completeness for subformulas *)
  Lemma completeness Ω A: A el U' -> Ω <<= U' -> entails Ω A -> nd Ω A. 
  Proof.
    intros Au U H. apply nd_stable. intro.
    unfold entails in H.
    specialize (H (@canonical)).
     assert (exists Δ: mcTheory, ~(nd (T Δ) A) /\ (Ω <<= (T Δ))).
     {
       eexists (Lindenbaum  U H0). split.
       - simpl. enough (~ (extend Ω A U') ⊢ A). intro. apply H1. eapply ndW.  apply H2.
         apply rep_equi. apply extend_locally_subset. auto. 
         apply extend_does_not_derive. auto. 
       - simpl. intros a Ha.  apply rep_in.  apply extend_locally_subset. auto.   apply extend_subset. auto. 
     }
     assert (model_constraint canonical). {
       destruct d eqn:dn; simpl; auto. unfold isIEL. apply are_iel_models.
       auto.
     }
     specialize (H H2). clear H2. 
     destruct H1 as [Δ H2].
     specialize (H Δ). destruct H2.
     decide (A el (T Δ)).
    + apply H1. apply ndA.  auto.
    + rewrite<- truth_lemma in n; auto. apply n.  apply H.  unfold evalK'. intros.  apply truth_lemma.   eauto.  eauto.  
  Qed.   

  Print Assumptions completeness.

  (** * Constructive Finite Model Property *)
  Definition finiteModel (M: KripkeModel) := exists (L: list (@world M)), forall (w : (@world M)), exists w', w' el L /\ (cogn w w') /\ (cogn w' w).  
  Definition fentails Γ A := forall M, model_constraint M -> finiteModel M -> (forall w, @evalK' M Γ w  -> evalK A w). 

  Definition fmp := forall Γ A, fentails Γ A -> nd Γ A.  
  
  Instance lce_dec: eq_dec (list (list form)).
  eauto.
  Defined.

  (** *** Compute the candidate list *)
  Definition checkPrimeDisj (C: list form) (A B: form) : bool. 
    decide (A el C).
    - exact true.
    - decide (B el C).   exact true. exact false.
  Defined.

  Definition checkPrimeSingle (L: list form) (A: form) :=
    match A with
      (B1 ∨ B2) => checkPrimeDisj L B1 B2
    | _ => true
    end.                      
  
  Definition checkPrime (A: list form)  : bool :=
    forallb (checkPrimeSingle A) A.

  Definition checkDCLSingle (C: list form) (A: form) : bool. 
    destruct (ielg_dec C A d).
    - decide (A el C). exact true. exact false. 
    - exact true.   
  Defined.

  Definition checkDCL (A: list form) (U: list form) : bool :=
    forallb (checkDCLSingle A) U.                    

  Definition checkConsistent (A: list form) : bool.
    destruct (ielg_dec A ⊥ d).
    - exact false.
    - exact true.
  Defined.     
  Definition candidateList := filter (fun x => match (checkDCL x U',  checkPrime x, checkConsistent x ) with
                                              (true, true, true) => true
                                            | _ => false end) (power U').


    Definition realCandidates (H: list context) : list world.
    induction H as [ |Γ IH].
    - apply nil. 
    -  decide (Γ el (power U')). 2: apply IHIH. rename i into i'. 
       decide (checkConsistent Γ). 2: apply IHIH. 
       +   decide (checkDCL Γ U'). 2: apply IHIH. 
           * decide (checkPrime Γ)  . 2: apply IHIH. 
             assert (new: world).
             { eapply mkmcTheory with (T := Γ).
               - eauto.
               - unfold checkConsistent in i. destruct (ielg_dec Γ ⊥); congruence; auto.
               - intros A B H1. unfold checkPrime in i1. 
                 specialize (@forallb_forall form ( checkPrimeSingle Γ) Γ).
                 intros H2. destruct H2.
                 specialize (H i1 (A ∨ B) H1).  simpl checkPrimeSingle in H. unfold checkPrimeDisj in H.  decide (A el Γ); auto.  decide (B el Γ); auto. 
                 
               - unfold checkDCL in i0.  specialize (@forallb_forall form (checkDCLSingle Γ) U').   intro. destruct H.  specialize (H i0).  clear H0.
                 intros A Ha. specialize (H A Ha).  intro Hg.  unfold checkDCLSingle in H. destruct  (ielg_dec Γ A d).  decide (A el Γ). auto.  congruence.  congruence. 
                 
                 
             }
             eapply (new::IHIH).
    Defined.
         Ltac dec := repeat (destruct Dec).

      Lemma candidatesConnection: forall (x: nd.context),  (x el candidateList) -> exists w', w' el (realCandidates candidateList) /\ (T w') = x.
  Proof.
    intros x H.
    
    pose proof (H1 := H).
    apply in_filter_iff in H. destruct H.   destruct (checkDCL x U') eqn:dcl;  destruct (checkPrime x) eqn:cp; destruct (checkConsistent x) eqn:cc;  try congruence.
    
    induction candidateList.
    -  inversion H1.
    -  destruct H1.
       + subst a. simpl realCandidates.  
              destruct ( @Dec (@In (list form) x (@power form U'))
        (@list_in_dec (list form) x (@power form U') (@gentree.list_eq_dec form form_eq_dec'))) eqn:ni.     destruct (Dec (checkConsistent x)) eqn:nx. destruct (Dec (checkDCL x U')) eqn:nii. destruct (Dec (checkPrime x)) eqn:niiii. 

              eexists. split.
              simpl.   left. reflexivity. simpl.  reflexivity.
              exfalso. apply n. apply cp.
              exfalso. apply n. apply dcl.
              exfalso. apply n. apply cc.
              exfalso. apply n. apply H.

       + specialize (IHl H1).
         destruct IHl as (w & Hw1 & Hw2). exists w.
         simpl realCandidates.  
         dec. all: try right; auto. 
 Qed.


  Lemma canonicalFinite: finiteModel canonical.
  Proof.
    exists (realCandidates candidateList).
    intros.
    destruct w.
    enough (T0 el candidateList).
    specialize (candidatesConnection H).  intro.  destruct H0 as [wCan [HwCan1 HwCan2]].
    exists wCan. split; try tauto.
    split.
    - intros a. simpl.  rewrite HwCan2. auto.
    - intros a. simpl.  rewrite HwCan2. auto.
    - unfold candidateList. apply in_filter_iff.  split; auto.
      destruct (checkDCL T0 U') eqn:dclt.
      destruct (checkPrime T0) eqn:cpt.
      destruct (checkConsistent T0) eqn:cct.
      auto.
      + unfold checkConsistent in cct.  destruct (ielg_dec T0 ⊥ d); congruence.
      + unfold checkPrime in cpt.
      assert (forall x, In x T0 -> (checkPrimeSingle T0 x) = true).
      { intros x Hx.
        unfold checkPrimeSingle. destruct x; auto. specialize (TUPrime0 x1 x2 Hx).  unfold checkPrimeDisj.
        decide (x1 el T0); decide (x2 el T0); try congruence. tauto.  
      }
      apply forallb_forall in H. congruence.
      + unfold checkDCL in dclt. assert (forall x, In x U' -> ( checkDCLSingle T0 x)). {
          intros x Hx. unfold checkDCLSingle. destruct (ielg_dec T0 x d); auto.
          decide (x el T0); auto.  
        }
         apply forallb_forall in H.  congruence.                                                                        
  Qed.

  
  Definition finiteModelProperty := forall Γ A, ~(nd Γ A) -> exists M,  (exists w,  evalK' Γ w /\ ~(evalK A w)) /\ finiteModel M /\ model_constraint M. 

  (* Show that finiteModelproperty implies fmp *)
  Lemma fmp_two_versions:
    finiteModelProperty -> fmp.
  Proof.
    intro.
    unfold fmp. intros Γ A H0.
    apply nd_stable. intro H1.  specialize (H Γ A H1).
    destruct H as (M & Hm1 & Hm2 & Hm3). 
    specialize (H0 M Hm3 Hm2). destruct Hm1. destruct H.    apply H2. auto.
  Qed.

End Canonical. 

Lemma completenessGeneral Ω A (D: DerivationType): entails Ω A -> nd Ω A.
Proof.
  intro. apply completeness with Ω A. unfold U'. apply scl_incl'. auto. intros a Ha. apply scl_incl'. auto. auto.
Qed.

Lemma ielHasFmp (D: DerivationType): finiteModelProperty.
Proof.
  intros Γ A H.
  exists (canonical Γ A). 
  repeat split.
  + assert (Γ <<= U' Γ A). { unfold U'. intros a Ha.  apply scl_incl'.  auto.
                           }
                           eexists (Lindenbaum H0 H). split. unfold evalK'. intros. apply truth_lemma.  unfold U'.  apply scl_incl'.  auto.
    simpl. rewrite rep_equi.  apply extend_subset.  auto.  apply extend_locally_subset.   auto. 
    rewrite truth_lemma. simpl T.  rewrite rep_equi. intro. eapply extend_does_not_derive with Γ A (U' Γ A) in H.  apply H.  apply ndA. auto.
    apply extend_locally_subset.  auto.
    unfold U'. apply scl_incl'.   auto. 
  + apply canonicalFinite.
  + destruct D; simpl; auto. unfold isIEL.   apply are_iel_models. reflexivity.
    
Qed. 

  
(** ** Admissibility *)
Section Admissibility.

    Variable d: DerivationType.
  Definition liftRelOne {X: Type} (R: X -> X -> Prop) (r1 r2: (option X)) :=
    match (r1, r2) with
      (Some x, Some y) => (R x y) |
    (None, _)     => True |
    _ => False
    end.

  Definition liftProp {X: Type} (R: X -> nat -> Prop) (r: (option X)) (n: nat) :=  
    (match r with
       Some r' => R r' n
     | None => False end).
  Lemma onSomeEqualsRlift {X: Type} x R  (n: nat): (@liftProp X R (Some x) n) <-> (R x n).
    split; firstorder eauto.
  Qed.  

  Section liftRelProps.
    Context {X: Type} {R: X -> X -> Prop} {R': X -> X -> Prop}.
    
    Definition lr := (liftRelOne R).
    Definition lr' := (liftRelOne R').
    
    Lemma lr_in a b :
      lr a b -> (exists b', a = None /\ b = Some b') \/ (exists a' b', a = Some a' /\ b = Some b') \/ (a = None /\ b = None).
    Proof.
      Unset Printing All.
      intro.
      unfold lr in H.
      destruct a, b; firstorder eauto; try congruence.
    Defined.
    
    Lemma preserves_reflexivity: Reflexive R -> Reflexive lr.
    Proof.
      intros.
      intro x.
      destruct x; firstorder eauto.
    Defined.

    Lemma preserves_transitivity: Transitive R -> Transitive lr.
      intros H x y z H1 H2.
      destruct x; destruct y; destruct z; firstorder eauto.
    Defined.
    Lemma preservesPreOrder: PreOrder R -> PreOrder lr.
      intros H.  destruct H.  split.
      apply preserves_reflexivity; auto.
      apply preserves_transitivity; auto. 
    Defined.

    Lemma preservesSubrealtion: subrelation R R' -> subrelation lr lr'.
    Proof.
      intros H x  y H1.
      destruct (lr_in H1); firstorder eauto; rewrite H0; rewrite H2.
      cbv. auto. cbv. apply H. rewrite H0 in H1. rewrite H2 in H1.  cbv in H1. auto. 
      cbv. auto.
    Defined.

    Lemma onSomeEqualsR x y: lr (Some x) (Some y) <-> (R x y).
      split; firstorder eauto.
    Qed.  
  End liftRelProps. 

  Definition reflectionModel (m: KripkeModel): (KripkeModel).

    apply mkKripkeModel with (world := (option world)) (cogn := (liftRelOne  cogn)) (verif := (liftRelOne verif)) (val := (liftProp  val)).
    + apply preservesPreOrder; auto. apply m. 
    + intros s x y H H0.
      destruct x; destruct y; firstorder eauto; try congruence.
      destruct m. rewrite onSomeEqualsRlift. apply monotone with (x := w);
                                               firstorder eauto using onSomeEqualsR. 
    + destruct m.  apply preservesSubrealtion.  auto. 
    + intros x y z. destruct m; destruct x; destruct y; destruct  z; firstorder eauto using onSomeEqualsR.
      apply onSomeEqualsR.  apply transvalid with (y := w0).
      rewrite<- onSomeEqualsR.  exact H.  rewrite<- onSomeEqualsR.  exact H0. 
  Defined.

  (* Derivability in the reflection model (Even nicer would be if submodels would be arbitrary) *)
  Lemma derivReflSomeIdent (m: KripkeModel) ϕ: forall w, ((@evalK m ϕ w) <-> (@evalK (reflectionModel m) ϕ (Some w))). 
  Proof.
    - induction ϕ;try firstorder eauto.
      + split.
        intros H r1 v. destruct r1. 
        apply IHϕ. apply H. auto using onSomeEqualsR.
        destruct v.

        intros H r' v.
        apply IHϕ. apply H. auto using onSomeEqualsR. 
      + split.
        * intros H. simpl evalK. intros r' H1 H2.
          destruct r'. 
          apply IHϕ2. apply H.  auto using onSomeEqualsR.
          apply IHϕ1. auto.
          destruct H1.
        * intros H r' c H1.
          apply IHϕ2.
          apply H.
          eauto using onSomeEqualsR.
          apply IHϕ1. auto.
  Qed.

  Lemma derivRefl (m: KripkeModel) ϕ: (exists w, ~(@evalK m ϕ w)) -> ~(@evalK (reflectionModel m) (K ϕ) None).
  Proof.                                 
    intro.
    intro.  destruct H. apply H. 
    apply derivReflSomeIdent. 
    apply H0. simpl verif. cbv. auto.
  Qed.   

  Lemma reflectionPreservesIEL (m: KripkeModel):
    isIEL m -> isIEL (reflectionModel m).
  Proof.
    intros H w.
    destruct w.
    - specialize (H w). destruct H as [w' Hw']. exists (Some w'). apply Hw'.
    - exists None. firstorder eauto.
  Qed.    

  Lemma soundness (Γ: context) (A: form) {D: DerivationType}:
  nd Γ A -> entails Γ A.
Proof. 
  intro. induction H; try firstorder eauto. 
  - unfold entails. intros M c w H0. unfold evalK.  intros r' H1 H2.  apply IHnd. auto. intros a Ha. destruct Ha; eauto.
    + subst s. apply H2.
    + apply eval_monotone with w; eauto.
  - unfold entails in IHnd1.  intros M c w H1. eapply IHnd1; auto. apply H1.  apply preorderCogn. apply IHnd2.  auto. auto. 
  -  
    intros M Mc w H1.
    intros w' cw Hs. specialize (IHnd M Mc w').   simpl evalK in IHnd.
    intros w'' wc. apply IHnd with w''; auto.  apply monotone_ctx with w; auto.
    apply preorderCogn.  
  - intros M c w H0. intros r H1.  apply eval_monotone with w.  apply vericont.  auto.  apply IHnd.  auto. auto.
  - intros M c w H2.   specialize (IHnd1 M c w H2).   destruct IHnd1.
    + eapply IHnd2; auto.  apply H2.  apply preorderCogn. 
    + eapply IHnd3; eauto. apply preorderCogn.
  - intros M Mc w H1 u c.
    apply monotone_ctx with (w' := u)  in H1. 2: auto.
    unfold isIEL in Mc. destruct (Mc u).   
    assert (evalK s x).
    {
      eapply IHnd; auto.
      apply H1. auto. 
    }
    intro.
    apply (H3 x).
    + apply vericont. auto.
    + apply H2.        
Qed.    

  Lemma reflectionAdmissible  A : nd [] (K A) -> nd [] A. 
  Proof.
    intro.
    destruct (ielg_dec [] A d); auto.
    assert (exists (M: KripkeModel) w, ~(@evalK M A w) /\ model_constraint M).  {
      exists (canonical [] A).
      assert ([] <<= (U' [] A)) by  auto. 
      eexists (Lindenbaum H0 n). split. 
      rewrite truth_lemma. enough (~(nd (T (Lindenbaum H0 n)) A)). {
        intro. apply H1. apply ndA. auto. 
      }
      simpl T. intro.   apply extend_does_not_derive with [] A (U' [] A) in n.  apply n.
      apply ndW with (rep (extend [] A (U' [] A)) (U' [] A)).  auto.
      apply rep_equi.  apply extend_locally_subset.  auto.  unfold U'.  simpl scl.
      apply in_app_iff. left.  apply scl'_in.
      destruct d eqn:rd; try firstorder. simpl model_constraint.
      intros w.   
      pose proof (are_iel_models). rewrite rd in H1.  apply H1.  reflexivity. 
    }
    destruct H0 as (M & w & Hmw).
    enough (exists m w, model_constraint m /\ ~ evalK (K A) w).
    apply soundness in H. repeat destruct H0.   exfalso. apply H1.
    apply H. auto.
    firstorder eauto.

    exists (reflectionModel M).
    exists None. 
    split.
    - destruct d eqn:deq; try firstorder.   simpl model_constraint. apply reflectionPreservesIEL.
      tauto.
    -  destruct Hmw.  firstorder eauto using  derivRefl.
 Qed.       
End Admissibility.  
