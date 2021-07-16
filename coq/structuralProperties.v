(** * Structural Properties for Permutation-based sequent calculi 
    We prove useful versions of contraction and weakening starting from not useful ones.

    This can be used for any G3C style sequent calculus. We also provide helpers for dealing with inversion lemmas. 
 **)
Require Import PslBase.Base PslBase.Lists.Dupfree.
Require Import forms toolbox.
Require  Permutation.
Require Import Permutations. 
Require Import Coq.Program.Equality Coq.Sorting.Permutation.

Section UndupFacts. 
  Ltac dec := repeat (destruct Dec).

  Lemma undup_equi_is_perm (A: list form) B: dupfree A -> dupfree B -> (A === B <-> A ≡P B). 
  Proof.
    intros HA HB.
    split.
    - intro. apply NoDup_Permutation. apply (dupfree_Nodup A). auto.
      apply (dupfree_Nodup B). apply HB.    firstorder eauto.
    -   intro. split; intro x; rewrite H; auto. 
  Qed.     


  Lemma undup_perm (A B: list form): A ≡P B -> (undup A) ≡P (undup B).
  Proof.
    intros. induction H.
    - reflexivity.
    - simpl undup.  dec; firstorder eauto.
      + exfalso. apply n. rewrite<- H. auto.
      +  exfalso. apply n. rewrite H. auto.
    -
      
      simpl undup. dec; firstorder eauto; try congruence; try reflexivity.
      rewrite H0.  reflexivity. constructor. 
    - transitivity (undup l'); auto. 
  Qed.

  Lemma dupfree_perm (A B: list form): A ≡P B -> (dupfree A) <-> (dupfree B).
  Proof.
    intros.
    repeat rewrite dupfree_Nodup.
    split; apply Permutation_NoDup. auto. symmetry. auto. 
  Qed.

  Lemma undup_double (a: form) A: undup (a::a::A) = undup (a::A).
  Proof.
    simpl undup. 
    dec.
    reflexivity.
    reflexivity.
    exfalso. auto. exfalso. apply n. auto.
  Qed.

  Lemma dupfree_rem A (x: form): dupfree A -> In x A -> ((x::(rem A x)) ≡P A).  
  Proof.
    intros.
    induction H.
    - inversion H0.
    -  destruct H0.
       + rewrite H0. simpl rem. dec. congruence. simpl.
         rewrite rem_id. reflexivity. rewrite<- H0. auto.
       + assert (x <> x0). { intro. apply H.  rewrite<- H2. auto.  } specialize (IHdupfree H0).
         simpl rem. dec. simpl.
         transitivity (x0::x::(rem A x)). psolve.
         rewrite IHdupfree.  reflexivity.
         exfalso. apply n. firstorder eauto.
  Qed.

  Lemma dupfree_app_reml A (B: list form): dupfree (A++B) -> dupfree A .
  Proof.
    intros H.
    dependent induction A.
    - constructor. 
    - norm_list_in H.   constructor.
      apply dupfree_cons in H. destruct H. auto.
      apply dupfree_cons in H. apply IHA with B. tauto.
  Qed.

  Lemma dupfree_app_remr A (B: list form): dupfree (A++B) -> dupfree B .
  Proof.
    intros H.
    dependent induction B.
    - constructor. 
    - norm_list_in H.   constructor. intro. 
      apply dupfree_perm with (A := (a :: (A++B))) in H. 
      apply dupfree_cons in H. destruct H. apply H. firstorder eauto. psolve.
      apply IHB.  apply dupfree_perm with (A := (a :: (A++B))) in H. apply dupfree_cons in H.
      tauto. psolve.
  Qed.     

  Lemma undupIncl (A B : list form) : incl A B -> dupfree A -> dupfree B  -> exists B', B ≡P (A++B').
  Proof.
    intros. 
    induction A.
    - exists B. rewrite app_nil_l. reflexivity. 
    - destruct IHA as (B' & HB').
      firstorder eauto.
      apply dupfree_cons in H0.
      tauto.
      assert (a el B').
      enough (a el (A ++ B') /\ ~(a el A)).  destruct H2. apply in_app_iff in H2. destruct H2; tauto.
      split. rewrite<- HB'. apply H. left. auto.
      apply dupfree_cons in H0; tauto.
      
      exists (rem B' a). rewrite HB'. 
      transitivity (A ++ (a:: rem B' a)).
      rewrite dupfree_rem. reflexivity.
      
      apply dupfree_app_remr with A.  apply dupfree_perm with (A := ((B))).    auto. auto. auto.    psolve. 
  Qed.     
End UndupFacts.


Section ClassicalProperties.  
  
  Variable ent : nat -> list form -> list form -> Prop.

  (** We define properties of entailment relations. **)
  Definition structLeftWeakening : Prop := forall h Γ Ω F, ent h Γ Ω -> ent h (F::Γ) Ω.

  Definition structRightWeakening : Prop := forall h Γ Ω F, ent h Γ Ω -> ent h Γ (F::Ω).

  Definition structLeftContraction : Prop := forall h Γ Ω F, ent h (F::F::Γ) Ω -> ent h (F::Γ) Ω.

  Definition structRightContraction : Prop := forall h Γ Ω F, ent h Γ (F::F::Ω) -> ent h Γ (F::Ω).

  Definition PermutationExchange : Prop := forall h Γ Γ' Ω Ω', ent h Γ Ω -> Γ ≡P Γ' -> Ω ≡P Ω' -> ent h Γ' Ω'.

  (* These are the properties we will shwo admissible *)
  Definition Weak : Prop := forall h Γ Ω Γ' Ω', Γ <<= Γ' -> Ω <<= Ω' -> ent h Γ Ω -> ent h Γ' Ω'.

  Definition Contraction : Prop := forall Γ Γ' Δ Δ' h, ent h Γ Δ ->  Γ === Γ' -> Δ === Δ' -> ent h Γ' Δ'. 
  
End ClassicalProperties.

Section UsableContraction.
  Variable ent : nat -> list form -> list form -> Prop.
  Variables (srW : structRightWeakening ent) (slW: structLeftWeakening ent) (slC:structLeftContraction ent) (srC: structRightContraction ent) (pe: PermutationExchange ent) .

  
  Lemma provToUndupRight h Γ Ω: ent h Γ Ω -> ent h Γ (undup Ω).
  Proof.  
    intros. induction Ω using list_length_ind. destruct (dupfree_dec Ω).
    - rewrite (undup_id d). auto. 
    - apply not_dupfree in n. destruct n as (a & A1 & A2 & A3 & Hl').
      rewrite Hl' in H.
      assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))) by psolve.
      unfold PermutationExchange in pe. unfold structRightWeakening in srC.  
      apply pe with (Γ' := Γ) (Ω' := (a::a::A1++A2++A3)) in H; try psolve.  apply srC in H.
      rewrite Hl'.
      specialize (undup_perm H1). intro H2.
      apply pe with (Γ := Γ) (Ω := undup (a :: a :: A1 ++ A2 ++ A3)); try psolve.
      rewrite undup_double.
      apply H0.  rewrite Hl'; firstorder eauto. repeat (rewrite app_length; simpl).  lia. auto.
  Qed.

  Lemma ProvToUndupL  h Γ Ω: ent h Γ Ω -> ent h (undup Γ) Ω.
  Proof.  
    intros. induction Γ using list_length_ind. destruct (dupfree_dec Γ).
    - rewrite (undup_id d). auto. 
    - apply not_dupfree in n. destruct n as (a & A1 & A2 & A3 & Hl').
      rewrite Hl' in H.
      assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))) by psolve.
      unfold PermutationExchange in pe. unfold structLeftWeakening in slC.  
      apply pe with (Ω' := Ω) (Γ' := (a::a::A1++A2++A3)) in H; try psolve.  apply slC in H.
      rewrite Hl'.
      specialize (undup_perm H1). intro H2.
      apply pe with (Ω := Ω) (Γ := undup (a :: a :: A1 ++ A2 ++ A3)); try psolve.
      rewrite undup_double.
      apply H0.  rewrite Hl'; firstorder eauto. repeat (rewrite app_length; simpl).  lia. auto.
  Qed.

  Lemma UndupToProvL h Γ Ω: ent h (undup Γ) Ω -> ent h Γ Ω. 
  Proof.
    intros. induction Γ using list_length_ind.   destruct (dupfree_dec Γ).
    - rewrite<- (undup_id d); auto.
    - apply not_dupfree in n. destruct n as (a & A1 & A2 & A3 & Hl').
      rewrite Hl' in H.
      assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))) by psolve.
      unfold PermutationExchange in pe. unfold structLeftContraction in slC.  
      apply pe with (Ω' := Ω) (Γ' := undup (a::a::A1++A2++A3)) in H; try psolve.
      rewrite undup_double in H. apply H0 in H. 
      apply pe with (Ω := Ω) (Γ :=  (a :: a :: A1 ++ A2 ++ A3)); try psolve.
      apply slC.  auto. rewrite Hl'.  repeat (rewrite app_length; simpl).  lia.
      eauto using undup_perm.
  Qed.

  Lemma UndupToProvR h Γ Ω: ent h  Γ (undup Ω) -> ent h Γ Ω. 
  Proof.
    intros. induction Ω using list_length_ind.   destruct (dupfree_dec Ω).
    - rewrite<- (undup_id d); auto.
    - apply not_dupfree in n. destruct n as (a & A1 & A2 & A3 & Hl').
      rewrite Hl' in H.
      assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))) by psolve.
      unfold PermutationExchange in pe. unfold structRightContraction in srC.  
      apply pe with (Γ' := Γ) (Ω' := undup (a::a::A1++A2++A3)) in H; try psolve.
      rewrite undup_double in H. apply H0 in H. 
      apply pe with (Γ := Γ) (Ω :=  (a :: a :: A1 ++ A2 ++ A3)); try psolve.
      apply srC.  auto. rewrite Hl'.  repeat (rewrite app_length; simpl).  lia.
      eauto using undup_perm.
  Qed.  

  (* Combine above lemmas to get undup equivalence for the calculus *)
  Lemma undup_prove Γ Δ h :  ent h Γ Δ  <-> ent h (undup Γ) (undup Δ).
  Proof.
    split; intro;  eauto using ProvToUndupL, provToUndupRight, UndupToProvR, UndupToProvL.
  Qed.

  Lemma appendWeakeningLeft n Γ1 Γ2 Δ: ent n Γ1 Δ -> ent n (Γ1++Γ2) (Δ). 
  Proof.
    induction Γ2.
    - intro. repeat rewrite app_nil_r. auto.
    - intros.  repeat rewrite app_nil_r.
      unfold PermutationExchange in pe. unfold structLeftWeakening in slW. 
      apply pe with (a::(Γ1++Γ2)) Δ; try psolve. apply slW.   eauto. 
  Qed.

  Lemma appendWeakeningRight n Γ Δ1 Δ2: ent n Γ Δ1 -> ent n (Γ) (Δ1++Δ2).
    induction Δ2.
    - intro. repeat rewrite app_nil_r. auto.
    - intros.  repeat rewrite app_nil_r.
      unfold PermutationExchange in pe. unfold structRightWeakening in srW. 
      apply pe with Γ (a::(Δ1++Δ2)); try psolve. eauto.  
  Qed. 
  Lemma Weakening:  Weak ent.
  Proof.
    unfold Weak. intros.   rewrite undup_incl in H0, H. apply undup_prove.
    apply undup_prove in H1.   apply undupIncl in H0. apply undupIncl in H.
    destruct H as [Γ'' H], H0 as [Ω'' H0].   
    unfold PermutationExchange in pe.  apply pe with (undup Γ ++ Γ'') (undup Ω ++ Ω''); try psolve. 
    apply appendWeakeningLeft, appendWeakeningRight. auto.
    all: apply dupfree_undup.
  Qed.

  Lemma contraction: Contraction ent.
  Proof.
    unfold Contraction.  intros Γ Γ' Δ Δ' h H H0 H1.
    assert (Weak ent) by apply Weakening.
    unfold Weak in H2. apply H2 with Γ Δ.  destruct H1, H0. all: firstorder eauto.  
  Qed.   
End UsableContraction.

