Require Import nd models.
Require Import List Lia.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.

(** * Enumerable Strong Completeness *)

Definition stable (T : theory) :=
  forall phi, ~ ~ T phi -> T phi.

Lemma Lindenbaum_stable {d: DerivationType} T phi :
  ~ T ⊢T phi -> stable (max T phi).
Proof.
  intros HT psi HP. destruct (decode_surj psi) as [n <-].
  exists (S n). right. split; trivial. intros H.
  apply HP. intros [k Hk]. assert (k <= n \/ n <= k) as [Hn|Hn] by lia.
  - apply (does_not_derive_i HT (i:=n)). apply (ndtW H).
    intros psi [->|]; trivial. now apply (maxn_subset_ij Hn).
  - apply (does_not_derive_i HT (i:=k)). apply (ndtW H).
    intros psi [->|]; trivial. now apply (maxn_subset_ij Hn).
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
                         Tconsistent:  ~(T ⊥);
                         Tprime: is_primeDN T;
                         Tstable : stable T;
                       }.

  Definition lindenBaumTheory (Γ: theory) (φ: form) (H: ~(ndT Γ φ)) :mcTheory.
    destruct (Lindenbaum H).  destruct H1. destruct H2.


    apply mkmcTheory with (T := (max Γ φ)). 
    + tauto. 
    + intro. apply H1. apply ndtE. apply ndtA. assumption.
    + apply H2.
    + now apply Lindenbaum_stable.
  Defined.

  Lemma lindenBaumTheorySubset Γ (φ: form) (H: ~(ndT Γ φ)) : exists Δ: mcTheory ,Γ ⊆ (T Δ).
  Proof.
    exists (lindenBaumTheory H).
    simpl T. assert ( (T (lindenBaumTheory H)) = (max Γ φ)). cbv. firstorder.  unfold lindenBaumTheory. apply max_subset. 
  Qed.


  Definition subsetMKT (A B: mcTheory) := subset (T A) (T B).
  Definition valuationMKT (A: mcTheory) (a: nat) := (T A) (Var a).
  
  Definition subsetVerif (A B:mcTheory) := 
    forall a, ((T A) (K a)) -> (T B) a.
  Instance canonical: (KripkeModel).
  Proof.
    apply mkKripkeModel with (world := mcTheory) (cogn := subsetMKT) (val := valuationMKT) (verif := subsetVerif).
    all: try firstorder.
    intros A B c d' E. apply Ttheory with (φ := d'). destruct B. simpl. apply ndtA. apply c. apply ndtA in E. apply ndtKpos in E.
      apply Ttheory in E. exact E.
  Defined.

  Lemma deductionGamma (Gamma: mcTheory) (phi: form):  ndT (T Gamma) phi <-> (T Gamma) phi.
  Proof.
    split.
    - intro. apply Ttheory in H. exact H.
    - apply ndtA.
  Qed.
  Hint Resolve deductionGamma : core.
  
  Lemma world_canonical_disjunction (t: mcTheory) ψ φ : 
    ((T t) (φ ∨ ψ)) <-> ~ ~ ((ndT (T t) φ) \/ ndT (T t) ψ).
  Proof.
    intros. split.
    - intro. intros H'.
      eapply Tprime. intros H''.
      apply H'. apply H''.
      apply deductionGamma.
      exact H.
    - intro. apply Tstable. intros H'. apply H. intros []; apply H'.
      + apply deductionGamma. apply ndtDIL. eauto.
      + apply deductionGamma. apply ndtDIR. eauto. 
  Qed.

End Canonical.

Lemma canonicalIEL : isIEL (@canonical normal).
Proof.
  intros w.
  assert (~(@ndT normal (unbox (T w)) ⊥)).
  {
    intros H % modalShiftingLemma.
    destruct w. apply Tconsistent0.
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
  apply unbox_rewrite.
  exact H1.
Qed.

(** ** Strong Completeness *)
Section Completeness.

  Hypothesis DNS : forall X (P : X -> Prop), (forall x, ~ ~ P x) -> ~ ~ (forall x, P x).

  Lemma DNS' : forall X (P : X -> Prop), ~ ~ (forall x, P x) -> (forall x, ~ ~ P x).
  Proof.
    intros. intuition.
  Qed.

  Lemma DN_imp (P Q : Prop) :
    (P -> ~ ~ Q) -> ~ ~ (P -> Q).
  Proof.
    tauto.
  Qed.
  
  (** *** Truth-Lemma *)
  Lemma truth_lemma {d: DerivationType} : forall  (X: form) (t: (@world  canonical)), 
    ~ ~ (evalK X t) <-> ((T t) X).
  Proof.
    intro x.
    induction x.
    - split.
      + intro H0. apply Tstable. intro H'.
        assert (H: ~ unbox (T t) ⊢T x).
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
          destruct H1. destruct H1.  apply H2.  apply IHx. intuition.
      + intros H. cbn. apply DNS. intros t'. apply DN_imp. intros H' H''.
        apply (IHx t'); trivial. now apply H'.
    - split. 
      +
        intro.
        apply deductionGamma. rewrite deductionGamma. apply Tstable.
        intro. 
        enough (exists Δ: mcTheory, (T t) ⊆ (T Δ) /\ ((T Δ) x1) /\ ~((T Δ) x2)). destruct H1 as [Δ H2].
        apply H. cbn. intros H'. specialize (H' Δ). destruct H2. destruct H2. firstorder eauto.
        rewrite<- deductionGamma in H0. rewrite ImpAgree in H0.
        destruct (Lindenbaum H0).
        exists (lindenBaumTheory H0).
        split. intros x H3. apply H1. now right.
        
        split. 
        * apply deductionGamma. apply ndtW with  (x1#(T t)). apply ndtA. left.
          reflexivity. unfold lindenBaumTheory. cbn. apply max_subset.
        * rewrite<- deductionGamma. destruct H2. auto.   
      + intros. cbn. apply DNS. intros t'. apply DN_imp. intros Ht. apply DN_imp.
        intros H'. apply IHx2. apply deductionGamma. apply ndtIE with (s := x1). apply deductionGamma. apply Ht, H.
        apply deductionGamma. apply IHx1. tauto.
    - split.     
      + intro H.
        apply deductionGamma. 
        apply ndtCI; apply ndtA.
        * apply IHx1. intuition.
        * apply IHx2. intuition.
      + intros H1 % deductionGamma H2.
        assert (HL : T t x1) by now apply deductionGamma, (ndtCEL H1).
        assert (HR : T t x2) by now apply deductionGamma, (ndtCER H1).
        apply (IHx1 t); trivial. intros H. apply (IHx2 t); trivial. intros H'. 
        apply H2. cbn. split; trivial.
    - intro. simpl evalK. rewrite world_canonical_disjunction.
      repeat rewrite deductionGamma. rewrite <- IHx1. rewrite <- IHx2. tauto.
      
    - split.
      + cbn. tauto. 
      + intro.  exfalso. apply (Tconsistent H). 
    - split; intros H.
      + apply Tstable. apply H.
      + intros H'. apply H', H.
  Qed.

  (*Lemma truth_lemma_list {d: DerivationType} : forall  (X: form) (t: (@world  canonical)) Gamma Delta, 
    ~ ~ (evalK' Gamma Delta) <-> ((T t) X).
  Proof.*)

  Lemma StrongQuasiCompleteness {d: DerivationType} (Γ: theory) (φ: form): 
    (entails Γ φ) -> ~ ~ Γ ⊢T φ.
  Proof.
    intros H0.
    intro H.
    unfold entails in H0.
    specialize (H0 canonical).
    enough (exists Δ: mcTheory, ~((T Δ) ⊢T φ) /\ (Γ ⊆ (T Δ))).
    destruct H1 as [Δ H2].
    assert (model_constraint d canonical).  {
      destruct d eqn:deq.
      - simpl. auto.
      - apply canonicalIEL.
    }
    specialize (H0 H1 Δ).
    apply H2.
    apply deductionGamma.
    apply truth_lemma. intros H'.
    assert (HD : ~ ~ @evalK' canonical Γ Δ).
    { apply DNS. intros psi. apply DN_imp. intros H''. apply truth_lemma. now apply H2. }
    apply HD. intros HD'. apply H'. now apply H0.
    (* Show that such a theory exists *)
    exists (lindenBaumTheory H).
    split.
    apply does_not_derive. exact H.
    apply max_subset.
  Qed.

End Completeness.