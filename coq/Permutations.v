Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import Coq.Sorting.PermutEq.
Require Export Coq.Sets.Multiset.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Multiset.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Import PslBase.Base.
Require Import List Lia.
Import ListNotations.

(** * Additional Lemmas about Permutations *)

Notation "A ≡P B" := (Permutation A B) (at level 60). 
(* Add Hints about Permutations to the Hint DB *)
Global Hint Resolve Permutation_sym Permutation_trans Permutation_refl : core.
Add Parametric Relation (T: Type): (list T) (@Permutation T )
    reflexivity proved by (@Permutation_refl T)
    symmetry proved by (@Permutation_sym T)                   
                         
    transitivity proved by (@Permutation_trans T)
      as Pl . 

(* Proof some elementary theorems *)
(* Permutation solver similar to https://github.com/foreverbell/permutation-solver *)
Section Permutations.
  Variable T : eqType.
  Lemma list_contents_app_multiplicity_plus :
    forall (a : T) (l m : list T),
      multiplicity (list_contents (@eq T) (@eqType_dec T) (l ++ m)) a =
      multiplicity (list_contents (@eq T) (@eqType_dec T) l) a +
      multiplicity (list_contents (@eq T) (@eqType_dec T) m) a.
  Proof.
    intros.
    specialize (list_contents_app _ (@eqType_dec T) l m).
    intros. unfold meq, munion in H.
    specialize (H a); auto.
  Qed.

  Instance add_proper_r (a: T) : Proper ( (@Permutation T) ==> iff) (@In T a).
  Proof. 
    intros x y H1.
    split; apply Permutation_in.
    firstorder eauto. symmetry.  auto.
  Qed.

End Permutations.

Ltac permutation_simplify a  (* variable for functional extensionality *) :=
  repeat
    match goal with
    | [ H : Permutation _ _ |- _ ] =>
      rewrite (permutation_Permutation (@eqType_dec _)) in H;
      unfold permutation, meq in H;
      specialize (H a);
      repeat (
          simpl list_contents in H;
          unfold munion in H;
          simpl multiplicity in H;
          try rewrite list_contents_app_multiplicity_plus in H
        )
    | [ |- Permutation _ _ ] =>
      rewrite (permutation_Permutation (@eqType_dec _));
      unfold permutation, meq;
      intros a;
      repeat (
          simpl list_contents;
          unfold munion;
          simpl multiplicity;
          try rewrite list_contents_app_multiplicity_plus
        )
    end.

Tactic Notation "equality"  (* variable for functional extensionality *) :=
  let x := fresh in 
  match goal with
  | [ H :  ?a = ?b |- _ ] =>  (
      assert (Permutation a b) as x by (rewrite H; auto); clear H )
                              
  end.
Tactic Notation "assert_perm" ident(x) constr(v) constr(E) :=
  let H := fresh in
  assert (Permutation x v) as H by rewrite<- E; apply Permutation_refl .


Ltac permutation_solver :=
  let a := fresh "a" in permutation_simplify a ;
                        repeat
                          match goal with
                          | [ |- context [if ?A then _ else _] ] => destruct A
                          end; lia.

Ltac psolve :=   
  (try equality);   permutation_solver .


Lemma cons_nil_app {A:Type} :
  forall (a:A) (l:list A),
    a::[] ++ l = a::l.
Proof.
  
  simpl; auto.
Qed.

(** Some tactics which are useful for dealing with lists  **)

Ltac norm_list :=
  repeat first [rewrite <- app_assoc|rewrite <- app_comm_cons];
  repeat rewrite cons_nil_app;
  repeat rewrite app_nil_l.

Ltac norm_list_in H :=
  repeat first [rewrite <- app_assoc in H|rewrite <- app_comm_cons in H];
  repeat rewrite cons_nil_app in H;
  repeat rewrite app_nil_l in H.

Ltac norm_list_all :=
  repeat first [rewrite <- app_assoc in *|rewrite <- app_comm_cons in *];
  repeat rewrite cons_nil_app in *;
  repeat rewrite app_nil_l in *.

(** We can now show some multiset lemmas **)

Section Permutation_Facts.
  Variable T : eqType.

  Lemma Perm_In_Iff (x: T) l: In x l <-> exists l', (x::l') ≡P l. 
  Proof.
    split.
    - intros H1. apply in_split in H1. destruct H1 as (l1 & l2 & Hl). exists (l1++l2).
      psolve.
    -   intros. destruct H as (l' & Hl'). rewrite<- Hl'. auto. 
  Qed.

  Lemma lequiv_cons_destruct'  (A: T) B C D:
    (A::C) ≡P (B::D) ->
    (exists Γ1, (B::Γ1) ≡P (C) /\ (A::Γ1) ≡P (D) /\ A <> B)
    \/ (A = B /\ D ≡P C). 
  Proof.
    intros.
    decide (A = B). 
    - rewrite e in H. apply Permutation_cons_inv in H.
      right. split; auto. 
    - left.
      specialize (Permutation_sym H).
      intro.
      pose proof (Permutation_vs_cons_inv H).
      pose proof (Permutation_vs_cons_inv H0).
      destruct H1 as (l1 & l2 & Hl1).
      destruct H2 as (l1' & l2' & Hl2).
      destruct l1.
      rewrite app_nil_l in Hl1. inversion Hl1. congruence.
      inversion Hl1.
      pose proof H as H'.
      rewrite H3 in H'.
      apply Permutation_sym in H'.

      assert (A :: l1 ++ B :: l2 = (A:: l1) ++ B :: l2). 
      norm_list. reflexivity. 
      rewrite H1 in H'. 
      apply Permutation_cons_app_inv in H'.
      exists (l1++l2). 
      split.
      psolve.
      
      split.

      destruct l1'. 
      inversion Hl2.
      congruence.
      inversion Hl2. 
      pose proof H0 as H0'.
      rewrite H6 in H0'.
      apply Permutation_sym in H0'.

      assert (B :: l1' ++ A :: l2' = (B:: l1') ++ A :: l2'). 
      norm_list; reflexivity. 
      rewrite H4 in H0'. 
      apply Permutation_cons_app_inv in H0'.
      rewrite H3 in H0'.
      apply Permutation_sym in H0'.
      assert ((B :: l1') ++ l2' = B::(l1'++l2')). norm_list. reflexivity. 
      rewrite H7 in H0'.
      apply Permutation_cons_app_inv in H0'.
      assert ((l1' ++ (A :: l2')) ≡P (A :: (l1' ++ l2'))) by psolve.
      rewrite H8.
      rewrite H2.
      constructor.
      apply Permutation_sym. auto.
      intro. congruence. 
  Qed.  

  Lemma lequiv_cons_destruct (A: T) B C D:
    (A::C) ≡P (B::D) ->
    (exists Γ1, (B::Γ1) ≡P (C) /\ (A::Γ1) ≡P (D))
    \/ (A = B /\ D ≡P C). 
  Proof.
    intro. 
    specialize (lequiv_cons_destruct' H).
    intro.
    destruct H0.
    - left. firstorder eauto.
    - firstorder eauto.   
  Qed.

  Lemma lequiv_doublecons_destruct (A: T) B C D:
    (A::A::C) ≡P (B::D) ->
    ((A = B /\ ((A::C) ≡P D))
     \/ (A <> B /\ exists C', C ≡P (B::C') /\ ((A::A::C') ≡P D)  )).
  Proof.
    intro H.
    specialize (lequiv_cons_destruct' H).
    intros.
    destruct H0.
    - destruct H0 as (Γ1 & Hg1 & Hg2 & Hg3).
      right.  split. auto.
      specialize (lequiv_cons_destruct' Hg1). intro H1. destruct H1. 
      + destruct H0 as (Γ2 & Hf1 & Hf2 & Hf3).
        exists Γ2. split. symmetry. auto. rewrite Hf1. rewrite Hg2. reflexivity.
      + destruct H0.  congruence. 
    -       left.  destruct H0.  split. auto. symmetry. auto. 
  Qed.
  


  Lemma lequiv_cons_app (a: T) A' B C : (a:: A') ≡P (B ++ C) ->
                                        (In a B /\ exists B', B ≡P (a::B') /\ A' ≡P (B' ++ C)  ) \/
                                        (In a C /\ exists C', C ≡P (a::C') /\ A' ≡P (B ++ C')  ). 
  Proof.
    intros.
    assert (In a (B++C)).
    rewrite<- H.  auto. 
    apply in_app_iff in H0. destruct H0.
    - left; firstorder eauto.
      
      apply Perm_In_Iff  in H0.
      destruct H0 as (lo & Hlo).
      exists lo; split; firstorder eauto. symmetry. auto.
      apply Permutation_cons_inv with a.
      rewrite H. apply transitivity with ((a::lo)++C). psolve.  psolve.
    - right; firstorder eauto.
      
      apply Perm_In_Iff in H0.
      destruct H0 as (lo & Hlo).
      exists lo; split; firstorder eauto. symmetry. auto.
      apply Permutation_cons_inv with a.
      rewrite H. apply transitivity with ((a::lo)++B).  rewrite Hlo. psolve. psolve. 
  Qed.   
End Permutation_Facts.
(** ** Map and Permutation *)
Section MapPerm.
  Variables (A: Type) (B: Type) .
  Definition injective (f: A -> B) := forall a1 a2, f(a1) = f(a2) -> a1 = a2.
  Lemma map_perm (f: A -> B) l1 l2 : l1 ≡P l2 -> (List.map f l1) ≡P (List.map f l2).
  Proof.
    intro H.
    induction H; firstorder eauto. 
    - rewrite H. reflexivity.
    -   cbn. constructor.  
  Qed.
  
  Lemma map_inj_perm (f: A -> B) l1 l2: injective f -> (map f l1) ≡P (map f l2) -> l1 ≡P l2.
  Proof.
    intros.
    apply Permutation_map_inv in H0.
    destruct H0 as (l3 & L1 & L2).
    transitivity l3.
    apply map_injective in L1. rewrite L1. reflexivity.
    apply H. symmetry; auto. 
  Qed.

  Lemma map_perm_cons (f: A -> B) l1 b l2 : (List.map f l1) ≡P (b::l2) -> exists A', (List.map f A') ≡P l2.
  Proof.  
    intros. symmetry in H.
    apply Permutation_map_inv in H.
    destruct H. destruct H. destruct x. inversion H.
    exists x. simpl map in H. 
    inversion H. reflexivity. 
  Qed.

  Lemma map_perm_cons' (f: A -> B) l1 b l2 : (List.map f l1) ≡P (b::l2) -> exists A', (List.map f A') ≡P l2 /\ exists b', (f b') = b.
  Proof.   
    intros. symmetry in H.
    apply Permutation_map_inv in H.
    destruct H. destruct H. destruct x. inversion H.
    exists x. simpl map in H. 
    inversion H. split.  reflexivity.
    exists a.  reflexivity. 
  Qed.


End MapPerm.  


