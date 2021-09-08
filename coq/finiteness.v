(** ** Finiteness *)
Require Import List.
Require Import PslBase.Lists.Position.
Require Import PslBase.Base.  

Definition lfin (A: Type) := exists (L: list A), forall a, In a L. 

Definition injective {A B: Type} (f: A -> B) := forall a1 a2, (f a1) = (f a2) -> a1 = a2.
Definition surjective {A B: Type} (f: A -> B) := forall b, exists a, f a = b. 

Definition nfin (A: Type) := exists (f: A -> nat), injective f /\ exists B, forall a, (f a) <= B.

Definition injection A B := exists f, @injective A B f. 

Lemma travel_nfin (A B: Type): nfin B -> injection A B -> nfin A. 
Proof.
  intros.
  inversion H. destruct H0 as (g & Hg).
  exists (fun a => (x (g a))). split.
  - intros a b Hab. destruct H1.
    apply Hg.   apply H0. assumption.
  - destruct H1 as (h1' & (B' & Hb')).    exists B'. intro a'. apply Hb'.
Qed.

Print pos. 
Definition deOpti {A B: Type} (f: A -> (option B)) (H: forall a, (f a) <> None) : A -> B.
  intros a. destruct (f a) eqn:fa. exact b. congruence.
Defined.

Print pos. 
Require Import Lia. 
Lemma lfin_nfin (A: eqType): lfin A -> nfin A.
Proof.
  intros Hl.  destruct Hl as (L & HL). unfold nfin.
  exists (fun a => match (pos a L) with None => 0 | (Some s) => s end). 
  assert ((forall a : A, pos a L <> None)).  {
    intros. specialize (HL a). apply el_pos in HL. destruct HL as (m & Hm).  congruence. 
  }
  split.
  - intros a a' H1. destruct (pos a L) eqn:pa. destruct (pos a' L) eqn:pa'. 
   apply pos_elAt in pa. apply pos_elAt in pa'.
   enough ((Some a) = (Some a')).  inversion H0. auto. rewrite<- pa, <- pa'.  rewrite H1. reflexivity.
   specialize (H a').    congruence. specialize (H a). congruence.
  -  exists (length L). intros a'. destruct (pos a' L) eqn:pl. enough (n < | L |). lia.    apply (pos_length pl). lia.
Qed.

