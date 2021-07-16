Require Export nd.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import decidability.  

Set Default Goal Selector "!".

(** * Constructive Strong Quasi-Completeness *)
(** **  Kripke Models *) 
Section Models.
  Context {d : DerivationType}. 


  Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            cogn  : world -> world -> Prop;
                            verif : world -> world -> Prop;
                            val   : world -> valuation;
                            preorderCogn: PreOrder cogn;
                            monotone: forall s x y, cogn x y -> val x s -> val y s;
                            vericont: subrelation verif cogn;
                            transvalid: forall x y z, cogn x y -> verif y z -> verif x z;
                          }.
  Context {M: (@KripkeModel)}.
  Instance kripke_verif_trans_equiv_Equiv {M': KripkeModel}:
    Transitive (verif).
  Proof. 
    intros u v w H H2. apply vericont in H. apply transvalid with (y := v); auto.
  Qed.

  Instance cogn_trans {M': KripkeModel}  :
    Transitive (cogn).
  Proof.
    apply preorderCogn.
  Qed.
  (** ** Modified Entailment Relation *)  
  Fixpoint evalK {M: KripkeModel} (s: form) : (world) -> Prop := 
    match s with
    | (K x)  => (fun y => forall r, ((verif y r) -> evalK x r))
    | Bot    => (fun x => False)
    | Var y  => (fun x => ~ ~ val  x y)
    | x ⊃ y  => (fun z => forall r', cogn z r' -> (evalK x r') -> (evalK y r'))
    | s ∨ t  => (fun y =>  ~~(evalK s y \/ evalK t y))
    | s ∧ t  => (fun y => (evalK s y /\  evalK t y))  
    end.

  Definition evalK' {M: KripkeModel} (Γ: theory) :=
    fun w => forall s, (Γ s) -> @evalK M s w.  

  Definition entails (Γ: theory) (φ: form) := 
    forall (M : KripkeModel),
      ((forall w,evalK' Γ w -> @evalK M φ w)).



  Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

  (** 
    Being an IEL or IEL^- model is a property of a given model.
   **)
  Definition isIEL (M: KripkeModel) := forall w, exists w', verif w w'.

  (** Evaluation is monotone, that is if φ is true at world w
      and we can reach world v from w, φ true at v.  *)
  Lemma eval_monotone  (s: form)  w v: 
    cogn w v -> evalK s w -> evalK s v.
  Proof. 
    intros C H. induction s.
    - intros z H1. apply H. apply transvalid with (y := v); auto. 
    - intros z H1 H2. apply H.
      + apply transitivity with (y := v); auto.
      + exact H2.
    - destruct H. split.
      + apply IHs1. auto.
      + apply IHs2. auto.
    - cbn in *. intros H'. apply H. intros H''. apply H'. tauto.
    - exfalso. apply H.
    - cbn in *.   intros H'. apply H. intros H''. apply H'. apply monotone with (x := w); auto.
  Qed.     

  Lemma monotone_ctx (A:theory)  : 
    forall w w', cogn w w' -> evalK' A w -> evalK' A w'.
  Proof.
    intros. intros t H1.
    apply eval_monotone with (w := w); auto. 
  Qed.
End Models.


(** ** Canonical models **)
Section Canonical.
  (** We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
  Context {d : DerivationType}. 

  Record mcTheory := mkmcTheory {
                         T: theory;
                         Ttheory: forall φ, (@ndT d T φ) -> T φ;
                         consistentT:  ~(T ⊥);
                         prime: (is_primeDN T);
                       }.

  Definition lindenBaumTheory (Γ: theory) (φ: form) (H: ~(ndT Γ φ)) :mcTheory.
    destruct (Lindenbaum H).  destruct H1. destruct H2.

    apply mkmcTheory with (T := (max Γ φ)). 
    - tauto. 
    - intro. apply H1. apply ndtE. apply ndtA. assumption.
    - auto. 
  Defined.

  Lemma lindenBaumTheorySubset (Γ: theory) (φ: form) (H: ~(ndT Γ φ)) : exists Δ: mcTheory ,Γ ⊆ (T Δ).
  Proof.
    exists (lindenBaumTheory H).
    simpl T. assert ( (T (lindenBaumTheory H)) = (max Γ φ)).
    - cbv. firstorder.
    -  unfold lindenBaumTheory. apply max_subset. 
  Qed.


  Definition subsetMKT (A B: mcTheory) := subset (T A) (T B).
  Definition valuationMKT (A: mcTheory) (a: nat) := (T A) (Var a).
  
  Definition subsetVerif (A B:mcTheory) := 
    forall a, ((T A) (K a)) -> (T B) a.
  
  Instance canonical: (KripkeModel).
  apply mkKripkeModel with (world := mcTheory) (cogn := subsetMKT) (val := valuationMKT) (verif := subsetVerif).
  - try firstorder.
  - firstorder.
  - intros A B c d' E. apply Ttheory with (φ := d'). destruct B. simpl. apply ndtA. apply c. apply ndtA in E. apply ndtKpos in E.
    apply Ttheory in E. exact E.
  - firstorder.   
  Defined.

  Lemma deductionGamma (Gamma: mcTheory) (phi: form):
    ndT (T Gamma) phi <-> (T Gamma) phi.
  Proof.
    split.
    - intro. apply Ttheory in H. exact H.
    - apply ndtA.
  Qed.

  Lemma maximal_element (Gamma: mcTheory): 
    forall p, (ndT (T Gamma)  p) <-> ((T Gamma) p).
  Proof.
    apply deductionGamma.
  Qed.         

End Canonical.

Lemma cononicalIEL: isIEL (@canonical normal).
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
  exists (lindenBaumTheory H).
  intros x H1. simpl lindenBaumTheory.
  simpl T.
  apply max_subset.
  auto. 
Qed.

Definition entailsIEL (Γ: theory) (φ: form) := 
  forall (M : KripkeModel), isIEL M -> (((forall w,evalK' Γ w -> @evalK M φ w))).
Notation "Γ ⊨+ φ" := (entailsIEL Γ φ) (at level 30). 
Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

Lemma entailsImpliesEntails (Γ: theory) φ:
  (Γ ⊨ φ) -> (Γ ⊨+ φ).
Proof.
  intro.
  intro. intro. apply H. 
Qed.

(** *** Strong Quasi-Completeness *)
Section Completeness.
  
  Lemma truth_lemma {d: DerivationType}: forall  (X: form) (t: (@world  canonical)), 
    (evalK X t) <-> ~ ~ ((T t) X).
  Proof.
    intro x. induction x.
    - split.
      +  intros H0 H'. assert (H: ~ unbox (T t) ⊢T x).
         * intros H. now apply H', deductionGamma, modalShiftingLemma.
         * assert (exists Δ: mcTheory , (unbox (T t)) ⊆ (T Δ)
                                   /\ ~((T Δ) x)).
           {  
             exists (lindenBaumTheory H).
             split.
             - apply max_subset.
             - intro. apply ndtA in H1.
               apply does_not_derive in H1; auto. 
           }
           destruct H1. destruct H1.  apply (IHx x0).
           -- apply H0. auto.
           --   trivial.
      + intros A. simpl evalK. intros r V. apply IHx. intros H1. apply A. intros H2. apply H1. apply V. exact H2.
        
    - split.
      + intro. intro. 
        enough (exists Δ: mcTheory, (T t) ⊆ (T Δ) /\ ((T Δ) x1) /\ ~((T Δ) x2)).
        * destruct H1 as [Δ H2].
          specialize (H Δ). destruct H2. destruct H2. apply (IHx2 Δ); trivial. firstorder eauto.
        * rewrite<- deductionGamma in H0.  rewrite ImpAgree in H0.
          destruct (Lindenbaum H0).
          exists (lindenBaumTheory H0).
          split.
          -- intros x H3. clear IHx1 IHx2. firstorder eauto. 
          -- split. 
             ++ apply deductionGamma. apply ndtW with  (x1#(T t));try apply ndtA; eauto.  left. reflexivity.
             ++ rewrite<- deductionGamma. destruct H2. auto.    
      + intros. intros w H1 H2. apply IHx2. intros H'. apply H. intros H''. apply (IHx1 w); trivial. intros H3. apply H'.
        apply deductionGamma. apply ndtIE with (s := x1).
        * apply deductionGamma. intuition.
        * apply deductionGamma. apply H3.
    - split.     
      + intro H.
        destruct H.
        rewrite <- deductionGamma. intros H'.
        apply (IHx1 t); trivial. intros H1.
        apply (IHx2 t); trivial. intros H2.
        apply H', ndtCI; apply ndtA; auto.
      + intros H1.  split.
        * apply IHx1. rewrite <- deductionGamma in *. firstorder eauto.
        * apply IHx2. rewrite <- deductionGamma in *. firstorder eauto.
    - intro.  simpl evalK. pose proof ((@prime d t) x1 x2). split.
      + intro. intro. apply H0. clear H0.   intro.  rewrite IHx1, IHx2 in H0 .   destruct H0.
        * apply H0.  intro. apply H1. apply deductionGamma. apply ndtDIL. apply deductionGamma.  auto.
        * apply H0.  intro. apply H1. apply deductionGamma. apply ndtDIR. apply deductionGamma.  auto.  
      +  intro.  intro. apply H. intro. apply H0. intro. apply deductionGamma in H3.  specialize (H2 H3). apply H1. rewrite IHx1, IHx2.  rewrite deductionGamma in H2. destruct H2; eauto. right.    intro.  rewrite deductionGamma in H2.  congruence.   
    - split; firstorder eauto. 
      +  exfalso. apply H. intros H'. apply (consistentT H').  
    - cbn. intros t. unfold valuationMKT. tauto. 
  Qed.

  Lemma StrongQuasiCompleteness {d: DerivationType} (Γ: theory) (φ: form): 
    (entails Γ φ) -> ~ ~ Γ ⊢T φ.
  Proof.
    intro H0.
    intro H.
    unfold entails in H0.
    specialize (H0 canonical).
    enough (exists Δ: mcTheory, ~((T Δ) ⊢T φ) /\ (Γ ⊆ (T Δ))).
    - destruct H1 as [Δ H2].
      specialize (H0 Δ). apply (truth_lemma φ Δ).
      + apply H0. intros ψ P. apply truth_lemma. intros H'. apply H'. apply deductionGamma. destruct H2. apply ndtA.
        intuition. 
      + rewrite <- deductionGamma. apply H2.
    (* Show that such a theory exists *)
    - exists (lindenBaumTheory H).
      split.
      + apply does_not_derive. exact H.
      +  apply max_subset.
  Qed.

  Lemma IELStrongQuasiCompleteness (Γ: theory) (φ: form):
    (entailsIEL Γ φ) -> ~~(@ndT normal Γ φ).
  Proof.  
    intro H0.
    intro H.
    unfold entailsIEL in H0.
    specialize (H0 (@canonical normal)).
    specialize (H0 cononicalIEL).
    enough (exists Δ: @mcTheory normal, ~(@ndT normal (T Δ) φ) /\ (Γ ⊆ (T Δ))).
    - destruct H1 as [Δ H2].
      specialize (H0 Δ).
      apply (truth_lemma φ Δ).
      + apply H0.   intros ψ P. apply truth_lemma. intros H'. apply H'. apply deductionGamma. destruct H2. apply ndtA.
        apply H2. exact P.
      + rewrite <- deductionGamma. apply H2.
    - exists (lindenBaumTheory H).
      split.
      + apply does_not_derive. exact H.
      + apply max_subset.
  Qed.

  Definition ctx2thy (Γ: context) := fun x => In x Γ. 
  Lemma nd_ndT_equiv (Γ: context) (D: DerivationType) ϕ:  (nd Γ ϕ) <-> (ndT (ctx2thy Γ) ϕ).  
  Proof.
    split; intro H.
    - exists Γ. split; eauto.
    - destruct H as [l1 Hl].    destruct Hl. apply ndW with l1; auto.
  Qed.
  (** ** Completeness *)
  Lemma CompletenessIEL (Γ: context) (ϕ: form):
    (entailsIEL (ctx2thy Γ) ϕ) -> (@nd normal Γ ϕ). 
  Proof.
    intro.
    apply IELStrongQuasiCompleteness in H. rewrite<-  nd_ndT_equiv in H.
    destruct (@ielg_dec Γ ϕ normal); tauto. 
  Qed.

  Lemma CompletenessIELM (Γ: context) (ϕ: form):
    (entails (ctx2thy Γ) ϕ) -> (@nd minus Γ ϕ). 
  Proof.
    intro.
    apply (@StrongQuasiCompleteness minus) in H. rewrite<-  nd_ndT_equiv in H.
    destruct (@ielg_dec Γ ϕ minus); tauto.   
  Qed.
  
  Lemma evalKimp {M: KripkeModel} s t w: evalK s w -> evalK (Imp s t) w -> evalK t w.
  Proof.
    intros H0 H1.
    apply H1.
    - apply preorderCogn.
    -  auto.
  Qed.

  Lemma evalKdistr {M: KripkeModel} s w w': evalK (K s) w -> verif w w' -> evalK s w'.
  Proof.
    intros.
    apply H.
    exact H0.
  Qed.

  Definition model_constraint (d : DerivationType) m :=
    if d then True else isIEL m.

  Lemma entailsToNot' ϕ {d: DerivationType} :
    ~ (ndT empty ϕ) -> exists m w, model_constraint d m /\ ~(evalK ϕ w).
  Proof. 
    intros.
    exists canonical.
    exists (lindenBaumTheory H). split.
    { destruct d; cbn; trivial. apply cononicalIEL. }
    rewrite truth_lemma.
    destruct (Lindenbaum H).
    destruct H1.
    simpl T.
    destruct H2.
    intro. apply H4. intro. apply H1.  apply ndtA. exact H5.
  Qed.

  Lemma entailsToNot ϕ {d: DerivationType}: (~ (ndT empty ϕ)) -> exists (m: KripkeModel) w, ~(evalK ϕ w).
  Proof. 
    intros H. destruct (entailsToNot' H); firstorder.
  Qed.

  Lemma entailsToNotIEL ϕ: (~ (@ndT normal empty ϕ)) -> exists (m: KripkeModel) w, isIEL m /\ ~(evalK ϕ w).
  Proof. 
    intros H. destruct (entailsToNot' H); firstorder.
  Qed.   

  Axiom LEM: forall P, P \/ ~P.
  (** *** Soundness (using LEM) *)
  Lemma ndSoundIELCtx (A: context) (s: form) {p: DerivationType}  (D:@nd p A s):forall (M: KripkeModel), model_constraint p M ->  forall w, evalK' (ctx2thy A) w -> evalK s w.
  Proof.
    intros M Mc. induction D;try firstorder eauto. 
    - intros. intros w2 cw ek. apply IHD; auto.   intro s'. intro H4. destruct H4.
      + subst s.   assumption.
      + apply eval_monotone with  w; auto.
    -   apply evalKimp with (s0 := s).
        + apply H0; auto.
        + apply H1; auto.
    -  intros w H w' c H1 w'' v. specialize IHD with w. apply evalKimp with (s0 := s).
       + apply H1. exact v.           
       + apply evalKdistr with (w0 := w); auto. apply transvalid with (y := w'); auto.
    - intros w H w' v. apply IHD; auto.  apply monotone_ctx with (w0 := w); try tauto; auto. apply  vericont; auto.
    -  specialize (H1 w H). unfold evalK' in H0. simpl evalK in H1. assert (DN: forall P, ~~P -> P). { intros. destruct (LEM P); eauto;try congruence. exfalso. apply H3.  auto. }
                                                                                               apply DN in H1.   destruct H1.                                                                                   
       + specialize (H2 w H). apply H2.
         * apply preorderCogn.
         * apply H1.
       +  specialize (H0 w H). apply H0; eauto using  preorderCogn, H1.  apply preorderCogn.
    -   intros w H1 u c.  
        apply monotone_ctx with (w' := u)  in H1. 2: auto.
        unfold isIEL in Mc. destruct (Mc u).   
        specialize (IHD Mc u). 
        assert (evalK s x).
        {
          apply IHD; auto. 
        }
        intro.
        apply (H2 x).
        + apply vericont. auto.
        + apply H0.        
  Qed.

  Lemma ndSoundIEL  (A: theory) (s: form) {p: DerivationType} (D:@ndT p A s):forall (M: KripkeModel),model_constraint p M ->  forall w, evalK'  A w -> evalK s w.
  Proof.
    intros. destruct D. apply ndSoundIELCtx with x p.
    - destruct H1; eauto.
    - tauto.
    -  intros t Ht .    apply H0.  destruct H1.  auto. 
  Qed.
End Completeness.

