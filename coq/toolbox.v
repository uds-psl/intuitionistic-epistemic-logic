(** * Miscellaneous *)
(** This file contains miscelliounes like induction principles for lists 
    or pairs of natural numbers.
 **)

Require Import List Omega forms  PslBase.Base Permutation.
Require Export Permutations.

Ltac psolve  :=   
  permutation_solver.


Section ContextModifcation.
  (** ** Functions for dealing with contexts and lemmas about them  *)

  Fixpoint unK (f: list form) :=
    match f with
      nil => nil
    | (K x::xr) => (K x)::x::(unK xr)
    | (x::xr) => x::unK xr
    end.

  Fixpoint justK (f: list form) :=
    match f with
      nil => nil
    | (K x::xr) => (K x)::(justK xr)
    | (_::xr) => justK xr
    end.

  Fixpoint remNotK (f: list form) :=
    match f with
      nil => nil
    | (K x::xr) => x::(remNotK xr)
    | (_::xr) => remNotK xr
    end.

  Fixpoint notK (f: list form) :=
    match f with
      nil => nil
    | (K x::xr) => notK xr
    | (x::xr) => x::(notK xr)
    end.

  Lemma unK_in_iff A x: x el (unK A) <-> x el A \/ (K x) el A. 
  Proof.
    induction A.
    - tauto. 
    -  split.
       + intro. destruct a; simpl unK in H; destruct H; try subst a; firstorder eauto. subst a. right. auto.
       + intro. destruct H.  destruct H. subst x.  destruct a; simpl; eauto 10.  
         destruct a.  simpl unK. right. right. apply IHA. tauto. 1-5: simpl unK; right; apply IHA; left; auto.
         destruct H. subst a. simpl unK; auto.  destruct a; firstorder auto. 
  Qed.

  Lemma unK_incl A B: A <<= B -> (unK A) <<= (unK B). 
  Proof.
    intro H.
    intros a Ha.
    apply unK_in_iff in Ha.
    apply unK_in_iff. destruct Ha; eauto.  
  Qed.  

  Lemma unK_perm A B: A ≡P B -> (unK A) ≡P (unK B). 
  Proof.
    intro.
    induction H; firstorder eauto.
    - simpl unK. destruct x; rewrite IHPermutation; auto.
    -
      simpl unK. destruct x;  destruct y; psolve. 
  Qed.

  Lemma unK_justKNoK Γ: (Γ ≡P ((notK Γ)++(List.map K (remNotK Γ)))).
  Proof.
    induction Γ; auto.
    destruct a; simpl; rewrite IHΓ at 1; psolve.
  Qed.

  Lemma unK_decomp Γ: (Γ ++ remNotK Γ) ≡P (unK Γ).
  Proof.
    induction Γ. simpl; psolve.
    destruct a; simpl unK; rewrite<- IHΓ; psolve.
  Qed.

  Lemma remNotK_in_iff A x: x el (remNotK A) <->  (K x) el A. 
  Proof. 
    induction A; eauto.
    - split.
      + intro. cbn in H.  auto.
      + cbn.    auto.
    -    split.
         +  intros H. destruct a; cbn in H; eauto; try destruct H; try subst a; eauto; try (right; apply IHA; auto).
         + intros H.     destruct H; eauto. subst a.  simpl remNotK.  auto.
           simpl remNotK. destruct a;firstorder eauto.
  Qed.          

  Lemma remNotK_subset A B:
    A <<= B -> (remNotK A) <<= remNotK B. 
  Proof.
    intros. intros a Ha.  apply  remNotK_in_iff. apply H. apply-> remNotK_in_iff. auto.
  Qed.   

  Lemma remNotK_perm A B: A ≡P B -> remNotK A ≡P remNotK B. 
  Proof.
    intro.
    induction H; eauto.
    - destruct x; auto. psolve.
    - destruct x; destruct y; auto; psolve.
  Qed.


End ContextModifcation. 

Require Import Lia.

(** ** Induction principles *) 
Lemma le_wf_ind (P: nat -> nat -> Prop) (Hrec: forall n m, (forall p q, p < n -> P p q) -> (forall q, q < m -> P n q) -> P n m) : forall n m, P n m.
Proof.
  induction n using lt_wf_ind.
  - induction m using lt_wf_ind.
    + apply Hrec.
      intros p q H1. apply H. auto.
      
      intros q H1.  apply H0. 
      exact H1.
Qed.

(* Following code is taken from https://stackoverflow.com/questions/45872719/how-to-do-induction-on-the-length-of-a-list-in-coq *)
Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, length l < length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, length l <= length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. lia.
      - apply IHxs. simpl in Hlen. lia.
    }
    intros xs.
    apply H_ind with (xs := xs).
    lia.
  Qed.
End list_length_ind.
