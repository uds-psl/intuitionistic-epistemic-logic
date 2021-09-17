Require Import nd models.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical.

(** * Classical Strong Completeness *)

Definition LEM := forall p, p \/ ~p.
Definition DN  := forall p, ~~ p -> p. 
(** We can derive double-negation elimination from LEM *)
Lemma LEM2DN: LEM -> DN.
Proof.
  intros LEM p H.
  destruct (LEM p); firstorder. 
Qed. 


Section Models.
  Context {d : DerivationType}.

  Definition evalK' {M: KripkeModel} (Γ: theory) :=
    fun w => forall s, (Γ s) -> @evalK M s w.  

  (** 
    Being an IEL or IEL^- model is a property of a given model.
   **)
  Definition isIEL (M: KripkeModel) := forall w, exists w', verif w w'.


  
  Definition model_constraint (d : DerivationType) m :=
      if d then True else isIEL m.

  
  Definition entails {d: DerivationType} (Γ: theory) (φ: form) := 
    forall (M : KripkeModel), model_constraint d M -> 
      ((forall w,evalK' Γ w -> @evalK M φ w)).
  
  Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

  (** Evaluation is monotone, that is if φ is true at world w
      and we can reach world v from w, φ true at v.  *)
  Variable M : KripkeModel. 

  Lemma monotone_ctx (A:theory)  : 
    forall w w', cogn w w' -> evalK' A w -> evalK' A w'.
  Proof.
    intros. intros t H1.
    apply eval_monotone with (w0 := w); auto. 
  Qed.
End Models.
(** ** Canonical models *)
Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
  Context {d : DerivationType}. 

  Record mcTheory := mkmcTheory {
                         T: theory;
                         Ttheory: forall φ, (@ndT d T φ) -> T φ;
                         consistentT:  ~(T ⊥);
                         prime: is_prime T;
                       }.

  Definition lindenBaumTheory (DN: DN) (Γ: theory) (φ: form) (H: ~(ndT Γ φ)) :mcTheory.
    destruct (Lindenbaum H).  destruct H1. destruct H2.


    apply mkmcTheory with (T := (max Γ φ)). 
    + tauto. 
    + intro. apply H1. apply ndtE. apply ndtA. assumption.
    +  intros a b Ha.
       unfold is_primeDN in H2. specialize (H2 a b).
       apply DN in H2.  eauto. 
  Defined.

  Lemma lindenBaumTheorySubset (DN: DN) Γ (φ: form) (H: ~(ndT Γ φ)) : exists Δ: mcTheory ,Γ ⊆ (T Δ).
  Proof.
    exists (lindenBaumTheory DN H).
    simpl T. assert ( (T (lindenBaumTheory DN H)) = (max Γ φ)). cbv. firstorder.  unfold lindenBaumTheory. apply max_subset. 
  Qed.


  Definition subsetMKT (A B: mcTheory) := subset (T A) (T B).
  Definition valuationMKT (A: mcTheory) (a: nat) := (T A) (Var a).
  
  Definition subsetVerif (A B:mcTheory) := 
    forall a, ((T A) (K a)) -> (T B) a.
  Instance canonical: (KripkeModel).
  apply mkKripkeModel with (world := mcTheory) (cogn := subsetMKT) (val := valuationMKT) (verif := subsetVerif).
  try firstorder.
  firstorder.
  2: firstorder.
  + intros A B c d' E. apply Ttheory with (φ := d'). destruct B. simpl. apply ndtA. apply c. apply ndtA in E. apply ndtKpos in E.
    apply Ttheory in E. exact E.

  Defined.

  Lemma deductionGamma (Gamma: mcTheory) (phi: form):  ndT (T Gamma) phi <-> (T Gamma) phi.
  Proof.
    (* *)
    split.
    intro. apply Ttheory in H. exact H.
    apply ndtA.
  Qed.
  Hint Resolve deductionGamma : core.
  
  Lemma world_canonical_disjunction (t: mcTheory) ψ φ : 
    ((T t) (φ ∨ ψ)) <-> (ndT (T t) φ) \/ ndT (T t) ψ.
  Proof.
    intros. split.
    + intro. 
      apply prime. 
      apply deductionGamma.
      exact H.
    + intro. destruct H; eauto. 
    - apply deductionGamma. apply ndtDIL. eauto.
    - apply deductionGamma. apply ndtDIR. eauto. 

  Qed.

End Canonical. 
Lemma canonicalIEL (DN: DN): isIEL (@canonical normal).
Proof.
  intros w.
  assert (~(@ndT normal (unbox (T w)) ⊥)).
  {
    intros H % modalShiftingLemma.
    destruct w. apply consistentT0.
    apply @Ttheory0.
    apply @ndtIE with (s := (K ⊥)).
    
    - apply @ndtW with (T := empty).
      + apply IELKBot. 
      + firstorder.
    - simpl T in H.  exact H.    

  }
  exists (lindenBaumTheory DN  H).
  intros x H1. simpl lindenBaumTheory.
  simpl T.
  apply max_subset.
  apply unbox_rewrite.
  exact H1.
Qed.

(** ** Strong Completeness *)
Section Completeness.
  
  (** *** Truth-Lemma *)
  Lemma truth_lemma {d: DerivationType} (DN: DN): forall  (X: form) (t: (@world  canonical)), 
    (evalK X t) <-> ((T t) X).
  Proof.
    intro x.
    induction x.
    - split.
      + intro H0. apply DN. intro H'.
        assert (H: ~ unbox (T t) ⊢T x).
        * intros H. now apply H', deductionGamma, modalShiftingLemma.
        * assert (exists Δ: mcTheory , (unbox (T t)) ⊆ (T Δ)
                                  /\ ~((T Δ) x)).
          {  
            exists (lindenBaumTheory DN H).
            split.
            - apply max_subset.
            - intro. apply ndtA in H1.
              apply does_not_derive in H1; auto. 
          }
          destruct H1. destruct H1.  apply H2.  apply IHx. auto. 
          
          
      + intros A. simpl evalK. intros r V. apply IHx. auto. 
    - split. 
      +
        intro.
        apply deductionGamma. apply DN.  rewrite deductionGamma. 
        intro. 
        enough (exists Δ: mcTheory, (T t) ⊆ (T Δ) /\ ((T Δ) x1) /\ ~((T Δ) x2)). destruct H1 as [Δ H2].
        specialize (H Δ). destruct H2. destruct H2. apply H3. apply IHx2. (*apply H0.*) firstorder eauto.
        (*    apply IHx1. exact H2.  *)
        rewrite<- deductionGamma in H0. rewrite ImpAgree in H0.
        destruct (Lindenbaum H0).
        exists (lindenBaumTheory DN H0).
        split. intros x H3. firstorder eauto.  
        
        split. 
        * apply deductionGamma. apply ndtW with  (x1#(T t)). apply ndtA. left. reflexivity. unfold lindenBaumTheory. cbn. apply max_subset.
        * rewrite<- deductionGamma. destruct H2. auto.   
      + intros. intros w H1 H2. apply IHx2. apply deductionGamma. apply ndtIE with (s := x1). apply deductionGamma. apply H1. exact H. apply deductionGamma. apply IHx1. exact H2.
    - split.     
      + intro H.
        destruct H.
        apply deductionGamma. 
        apply ndtCI; apply ndtA.
        * apply IHx1. exact H.
        *  apply IHx2. exact H0.  
      + intros H1.  split.
        * apply deductionGamma in H1.  apply ndtCEL in H1. apply IHx1. 
          apply deductionGamma.  auto.
        * apply deductionGamma in H1.  apply ndtCER in H1. apply IHx2. 
          apply deductionGamma.  auto.
    - intro.  simpl evalK. rewrite world_canonical_disjunction. rewrite IHx1. rewrite IHx2.
      repeat rewrite deductionGamma. tauto.
      
    - split.
      + 
        intro. exfalso. apply H.
      + intro.  exfalso. apply (consistentT H). 
    - split; firstorder. 
  Qed.

  Lemma StrongCompleteness {d: DerivationType} (Γ: theory) (φ: form): 
   LEM ->  (entails Γ φ) -> Γ ⊢T φ.
  Proof.
    
    intros DN % LEM2DN  H0.
    apply DN. 
    intro H.
    unfold entails in H0.
    specialize (H0 canonical).
    enough (exists Δ: mcTheory, ~((T Δ) ⊢T φ) /\ (Γ ⊆ (T Δ))).
    destruct H1 as [Δ H2].
    assert (model_constraint d canonical).  {
      destruct d eqn:deq.
      - simpl. auto.
      - apply canonicalIEL.   auto. 
    }
    specialize (H0 H1 Δ).
    apply H2.
    apply deductionGamma.
    apply truth_lemma. auto. 
    apply H0. intros ψ P. apply truth_lemma. auto.  apply deductionGamma. destruct H2. apply ndtA.
    apply H3. exact P. 
    (* Show that such a theory exists *)
    exists (lindenBaumTheory DN H).
    split.
    apply does_not_derive. exact H.
    apply max_subset.
  Qed.

  
    Lemma evalKimp {M: KripkeModel} s t w: evalK s w -> evalK (Imp s t) w -> evalK t w.
    Proof.
      intros H0 H1.
      apply H1. apply preorderCogn. auto.
    Qed.

    Lemma evalKdistr {M: KripkeModel} s w w': evalK (K s) w -> verif w w' -> evalK s w'.
    Proof.
      intros.
      apply H.
      exact H0.
    Qed.


    Definition ctx2thy (Γ: context) := fun x => In x Γ. 

    Lemma ndSoundIELCtx (A: context) (s: form) {p: DerivationType}  (D:@nd p A s):entails  (ctx2thy A) s.
    Proof.
      intros M Mc. induction D.
      + eauto.
      + intros.   exfalso. apply (IHD) with w; auto.   
      + intros w1 c1 H2 c2 H3. apply IHD; auto.  intro s'. intro H4. destruct H4. subst s'.   assumption.  apply eval_monotone with (w := w1); auto.
      + intros w H. apply evalKimp with (s0 := s). apply IHD2; auto. apply IHD1; auto.
      + intros w H w' c H1 w'' v. specialize IHD with w. apply evalKimp with (s0 := s). apply H1. exact v.
        apply evalKdistr with (w0 := w); auto. apply transvalid with (y := w'); auto.
      + intros w H w' v. apply IHD; auto.  apply monotone_ctx with (w := w); try tauto; auto. apply  vericont; auto.
      + intros w H1. apply IHD in H1; auto. destruct H1. auto. 
      + intros w H1. apply IHD in H1; auto. destruct H1. auto. 
      + intros w H1. split; auto.
      + intros w H1. left. auto.
      + intros w H1. right. auto.
      + intros w H1. destruct (IHD1 Mc w H1).
      - apply (IHD2 Mc w); auto. apply preorderCogn.
      - apply (IHD3 Mc w); auto. apply preorderCogn.
        + intros w H1 u c.  
          apply monotone_ctx with (w' := u)  in H1. 2: auto.
          unfold isIEL in Mc. destruct (Mc u).   
          specialize (IHD Mc u). 
          assert (evalK s x).
          {
            apply IHD; auto. 
          }
          intro.
          apply (H2 x). apply vericont. auto.
          apply H0.
    Qed.

    Lemma ndSoundIEL  (A: theory) (s: form) {p: DerivationType}  (D:@ndT p A s):entails A s.
    Proof.
      intros. destruct D. intros M c w H1. destruct H.
      specialize (ndSoundIELCtx H0) . intro H2.   apply H2. auto. intros a Ha.
      apply H1. apply H. apply Ha.
    Qed.   

    Lemma ndSound (Γ: theory) A {p: DerivationType}: Γ ⊢T A -> entails Γ A.
    Proof.
      intros. apply ndSoundIEL. auto.
    Qed.

    Inductive uno := Uno.
    Definition cogUno := fun (x: uno) (y: uno) => True. 
    Definition unoModel: KripkeModel.  
      apply mkKripkeModel with (world := uno) (cogn := cogUno) (verif := cogUno) (val := fun x y => True).
      firstorder eauto.
      firstorder eauto.
      firstorder eauto.
      firstorder eauto.
    Defined.

    Lemma hasConstraint (D: DerivationType): model_constraint D unoModel.
    Proof.
      destruct D; firstorder eauto.
    Qed.
    
    Print Assumptions ndSound. 
    Lemma ndConsistent (D: DerivationType): ~(nil ⊢ ⊥).
    Proof.
      intro.
      specialize (ndSoundIELCtx H).  intro.
       
      enough (exists M, (exists w, ~(@evalK M ⊥ w) /\ model_constraint D M)).
      destruct H1 as (M & w & (H1 & H2)).  specialize (H0 M H2 w).
      apply H1. apply H0. intros a Ha. destruct Ha.

      
      exists unoModel. exists Uno.  split; try apply hasConstraint.
      intro. simpl evalK in H1. auto. 
    Qed.   
End Completeness.

(** Equivalence between completeness and LEM **)
Notation "Γ ⊨ A" := (entails Γ A) (at level 100). 
Section CompletenessLEM.
  Variable (D: DerivationType).
  Definition XM := forall P, P \/ ~P. 
  Definition strongCompleteness := forall Γ φ, (entails Γ φ) -> Γ ⊢T φ.
  
  Definition falsityStable := forall Γ, ~~(ndT Γ ⊥) -> (ndT Γ ⊥).

  Lemma entailmentBotDN Γ: ~~(entails Γ ⊥) -> entails Γ ⊥. 
  Proof.
    intro.
    intros M mc w H1. simpl evalK. 
     apply wm with (Γ ⊨ ⊥). intro. destruct H0; try tauto.
    specialize (H0 M mc w  H1).  apply H0.
  Qed.
  
  Lemma st2fs: strongCompleteness -> falsityStable. 
  Proof.
    intros H T H1.
    assert (~~(entails T ⊥)).  {
     firstorder eauto using ndSoundIEL.               
    }
    firstorder eauto using entailmentBotDN. 
  Qed.

  Lemma fstab2LEM: falsityStable -> XM. 
  Proof.
    intro fstab.
    intros P.
    pose (T := fun (x: form) => P \/ ~P).
    enough (T ⊢T ⊥).
    destruct H as (Γ & Hgam1 & Hgam2).
    destruct Γ.
    - exfalso.  apply (@ndConsistent D). apply Hgam2.
    - unfold T in Hgam1. apply Hgam1 with f. eauto.
    - apply fstab.  intro. apply wm with P. intro.
      apply H. apply ndtA. unfold T. apply H0.
  Qed.

  Theorem st2lem: strongCompleteness -> XM.
  Proof.
     intros H % st2fs. apply fstab2LEM; auto. 
  Qed.
End  CompletenessLEM.  

(** Completeness for enumerable theories and MP *)
Section CompletenessEnumerableMP.
  Definition MP := forall (f: nat -> bool), ~~(exists n, f n = true) -> exists n, f n = true.
  Context {d: DerivationType}. 

  Definition enumerable (T: theory) := exists (f: nat -> option form), forall x, T x -> exists n, f n = (Some x).
  Definition falsityEnumStable := forall Γ, enumerable Γ ->  ~~(ndT Γ ⊥) -> (ndT Γ ⊥).

  Definition strongEnumerableCompleteness :=
    forall Γ φ, enumerable Γ -> (entails Γ φ) -> Γ ⊢T φ.

  Lemma ste2fs: strongEnumerableCompleteness -> falsityEnumStable. 
  Proof.
    intros H T H0 H1.
    assert (~~(entails T ⊥)).  {
      intro.  apply H1. intro.  apply ndSoundIEL in H3. congruence.                                          
    }
    apply H. auto. apply entailmentBotDN. auto.
  Qed.

  Definition ftheroy (f: nat -> bool) : nat -> option form.
    intro x. 
    destruct (f x) eqn:fx.
    + apply (Some (decode x)).
    + apply None.
  Defined.
  Definition ftheroy' (f: nat -> bool) : nat -> option form :=
    fun n =>
         Some ((decode (n)) ∧ (¬ (decode (n)))).

  Lemma fenum2MP: strongEnumerableCompleteness -> MP.
  Proof.
    intros H1 f H2.
    pose (T := fun (x: form) => exists n, f n = true /\ (exists m, x = (m ∧ ¬ m) /\ (decode n = m)   )).
    enough (T ⊢T ⊥).
    destruct H as (Γ & Hgam1 & Hgam2).
    destruct Γ.
    - exfalso.  apply (@ndConsistent d). apply Hgam2.
    - unfold T in Hgam1. specialize (Hgam1 f0). destruct Hgam1.  eauto.  exists x. tauto.
    - apply ste2fs. auto.
      + exists (ftheroy' f).
        intros x1 Hx1.  unfold T in Hx1. destruct Hx1 as (nHx1 & Thx1).
        destruct Thx1. destruct (decode_surj x1).  destruct H0 as (m1 & Hm1 & Hm2). 
        exists (nHx1).  unfold  ftheroy'.    rewrite Hm2, Hm1.  reflexivity.  
      + intro. apply wm with (exists n, f n = true). intro. destruct H0; try tauto. clear H2. 
        apply H. destruct H0 as (n1 & Hn1).  apply ndtIE with ((decode n1)).
        apply  ndtCER with (decode n1).  apply ndtA. exists n1. split; eauto.
         apply  ndtCEL with (¬(decode n1)). apply ndtA. exists n1. split; eauto.
  Qed.
End CompletenessEnumerableMP.
