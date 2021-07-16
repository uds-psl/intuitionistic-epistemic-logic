From Coq Require Import
     Morphisms
     Setoid
     RelationClasses
.

Require Import forms.
Require Import nd forms.
Require Import Permutation.
Require Import Coq.Program.Equality.
Require Import Coq.Sets.Multiset.
Require Export Coq.Sets.Multiset.
Require Import Coq.Arith.EqNat.
Require Import PslBase.Base.
Require Import List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Import Coq.Sets.Multiset.
Require Export Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.
Require Import Coq.Sorting.PermutEq.
Require Import Lia.
 Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.CRelationClasses.
Require Import structuralProperties.
Import ListNotations. 

(** * Permutation Based Cut-elimination for K 
   We define a calculus for K 
   Calculus G3K from Negri & van Plato 
 *)

Require Import Permutations. 
Inductive lkh: nat -> list form -> list form -> Prop :=
  lkhA (A: nat) Γ Δ : List.In (Var A) Γ -> List.In (Var A) Δ -> lkh 0 Γ Δ
| lkhB  Γ Δ: List.In Bot Γ -> lkh 0 Γ Δ

                                 
| lkhIL n (A B: form) Γ Δ Γ1 Γ2 Δ':
    Δ' ≡P (A::Δ) -> lkh n Γ Δ' ->
    Γ1 ≡P (B::Γ) -> lkh n Γ1 Δ ->
    Γ2 ≡P ((A ⊃ B)::Γ) -> lkh (S n) Γ2 Δ
| lkhIR n A B Δ Δ1 Δ2 Γ Γ1:
    Γ1 ≡P (A::Γ) -> Δ1 ≡P (B::Δ) -> lkh n Γ1 Δ1 ->
    Δ2 ≡P ((A ⊃ B)::Δ) -> lkh (S n) Γ Δ2

                            
| lkhK n Γ Δ A Γ' Γ'' Δ': lkh n Γ [A] ->

                          Γ' ≡P ((List.map K Γ)++Γ'') ->
                          Δ' ≡P ((K A)::Δ) ->
                          lkh (S n) Γ' Δ'

| lkOL n Γ Δ  A B Γ1 Γ2 Γ3:
    Γ1 ≡P (A::Γ) -> lkh n Γ1 Δ ->
    Γ2 ≡P (B::Γ) -> lkh n Γ2 Δ ->
    Γ3 ≡P ((A ∨ B)::Γ) -> lkh (S n) Γ3 Δ
| lkOR n Γ Δ A B Δ1 Δ2:
    Δ1 ≡P (A::B::Δ) -> lkh n Γ Δ1 ->
    Δ2 ≡P ((A ∨ B)::Δ) -> lkh (S n) Γ Δ2

| lkAL n Γ Δ A B Γ1 Γ2:
    Γ1 ≡P (A::B::Γ) -> lkh n Γ1 Δ ->
    Γ2 ≡P ((A ∧ B)::Γ) -> lkh (S n) Γ2 Δ
| lkAR n Γ Δ A B Δ1 Δ2 Δ3:
    Δ1 ≡P (A::Δ) -> lkh n Γ Δ1 ->
    Δ2 ≡P (B::Δ) -> lkh n Γ Δ2 ->
    Δ3 ≡P ((A ∧ B)::Δ) -> lkh (S n) Γ Δ3 
                            

| lkhStep n Γ Δ: lkh n Γ Δ -> lkh (S n) Γ Δ.  

Lemma multiStep n m Γ Δ: lkh n Γ Δ -> n <= m -> lkh m Γ Δ.
Proof. intros D H. induction H; firstorder eauto using lkhStep. Qed. 
Definition lk Γ Δ := exists d, lkh d Γ Δ. 
Instance form_eq_dec' : eq_dec form. 
	apply form_eq_dec.
	Defined. 
	
(** Proof Permutation Equivalence for both systems **)
Require Export Permutations.


Ltac psolve  :=   
  permutation_solver.

Lemma lkPerm n Δ  Γ:
  lkh n Γ Δ -> forall Δ' Γ', Γ ≡P Γ' -> Δ ≡P Δ'
   -> lkh n Γ' Δ'. 
Proof.
  intro H.  induction H; firstorder eauto.
  - apply lkhA with A. rewrite<- H1. auto. rewrite<- H2. auto.
  - apply lkhB. rewrite<- H0. auto.
  - apply lkhIL with (A := A) (B := B) (Γ := Γ) (Γ1 := (Γ1)) (Δ' := (A::Δ'0)) .  auto. apply IHlkh1.  auto. rewrite H.  rewrite H5. auto.  rewrite H1.  auto.  apply IHlkh2.  auto. auto. rewrite<- H4.  rewrite H3.  auto.
  - apply lkhIR with (A := A) (B := B) (Δ := Δ) (Δ1 := (B::Δ)) (Γ1 := (A::Γ)); eauto. 
  - apply lkhK with (Γ := Γ) (Γ'' := Γ'') (Δ := Δ) (A := A);  auto; try psolve. 
  - apply lkOL with (Γ := Γ) (A := A) (B := B) (Γ1 := Γ1) (Γ2 := Γ2); auto. rewrite<- H4. auto.
  - apply lkOR with (Δ := Δ) (A := A) (B := B) (Δ1 := Δ1); auto.  psolve.
  - apply lkAL with (Γ := Γ) (A := A) (B := B) (Γ1 := Γ1); auto; try psolve.     
  - apply lkAR  with  (Δ := Δ) (A := A) (B := B) (Δ1 := Δ1) (Δ2 := Δ2) ; auto; try psolve.
  - apply lkhStep. apply IHlkh; auto. 
Qed.

Local Hint Constructors lkh : core. 

(** Register with rewriting for ≡P **)
Instance add_proper_l  : Proper (eq ==> (@Permutation form) ==> eq ==> impl) (lkh).
Proof. 
  intros n0 n1 neq a b c d e f   H1.  rewrite<- f. rewrite<- neq. apply lkPerm with d a. assumption. assumption. reflexivity.
Qed.

Instance add_proper_r  : Proper (eq ==> eq ==> (@Permutation form)  ==> impl) (lkh).
Proof. 
  intros n0 n1 neq a b c d e f   H1.  rewrite<- c. rewrite<- neq. apply lkPerm with d a. assumption. reflexivity. assumption.
Qed.

Instance add_proper_r1  : Proper (eq ==> eq ==> (@Permutation form)  ==> (Basics.flip impl)) (lkh).
Proof. 
  intros n0 n1 neq a b c d e f   H1.  rewrite c. rewrite neq. apply lkPerm with e b. assumption. reflexivity. auto. 
Qed.

Instance add_proper_r2  : Proper (eq  ==> (@Permutation form) ==> eq  ==> (Basics.flip impl)) (lkh).
Proof. 
  intros n0 n1 neq a b c d e f   H1.  rewrite f. rewrite neq. apply lkPerm with e b; auto.  
Qed.


Instance add_proper_lt  : Proper (eq ==> (@Permutation _) ==> (@Permutation _)) (@cons form ).
Proof. 
  intros l1 l2 hl1 x y H1. rewrite hl1. rewrite H1. reflexivity.
Qed.


(** Structural Properties *) 

Lemma leftWeakening Γ Δ W n: lkh n Γ Δ -> lkh n (W::Γ) Δ.
Proof.
  intro. revert W.  induction H; firstorder eauto 3.
  - apply lkhIL with (A := A) (B := B) (Γ := (W::Γ)) (Γ1 := (W::Γ1)) (Δ' := Δ'); auto; try psolve. 
  - apply lkhIR with (A := A) (B := B) (Δ := Δ) (Δ1 := Δ1) (Γ1 := (W::Γ1)).
    rewrite H. psolve. auto. auto.  auto.
  - apply lkhK with (Γ := Γ) (Γ'' := (W::Γ'')) (Δ := Δ) (A := A).  auto.   psolve. psolve.
  - apply lkOL with  (A := A) (B := B) (Γ := (W::Γ)) (Γ1 := (W::Γ1)) (Γ2 := (W::Γ2)). psolve. apply IHlkh1. psolve. apply IHlkh2. psolve.
  - apply lkAL with (A := A) (B := B) (Γ := (W::Γ)) (Γ1 := (W::Γ1)).  psolve. apply IHlkh.  psolve.   
Qed.

Lemma rightWeakening Γ Δ W n: lkh n Γ Δ -> lkh n Γ (W::Δ).
Proof.
  intro. revert W. induction H; firstorder eauto 3. 
  - apply lkhIL with (A := A) (B := B) (Γ := Γ) (Γ1 := Γ1) (Δ' := (W::Δ')); auto; try psolve.  
  - apply lkhIR with (A := A) (B := B) (Δ := (W::Δ)) (Δ1 := (W::Δ1)) (Γ1 := Γ1); auto; try psolve. 
  - apply lkhK with (Γ := Γ) (Γ'' := Γ'') (Δ := (W::Δ)) (A := A); auto. rewrite H1. psolve.
  - apply lkOR with (Γ := Γ) (A := A) (B := B) (Δ := (W::Δ)) (Δ1 := (W::Δ1)); auto; try psolve.
  - apply lkAR with (A := A) (B := B) (Δ := (W::Δ)) (Δ1 := (W::Δ1)) (Δ2 := (W::Δ2)); auto; try psolve.
Qed.

(** 
    Show "standard" rules admissible
 **)
Lemma lkOIL n Γ Δ A B: lkh n Γ (A::Δ) -> lkh n (B::Γ) Δ -> lkh (S n) ((A ⊃ B)::Γ) Δ.
  firstorder eauto. 
Qed.

Lemma lkOIR n Γ Δ A B: lkh n (A::Γ) (B::Δ) -> lkh (S n)  Γ ((A ⊃ B)::Δ).
  firstorder eauto. 
Qed.

Lemma lkOAL n Γ Δ A B: lkh n (A::B::Γ) Δ -> lkh (S n) ((A ∧ B)::Γ) Δ.
  firstorder eauto. 
Qed.


Lemma lkOAR n Γ Δ A B: lkh n Γ (A::Δ) -> lkh n Γ (B::Δ) -> lkh (S n) Γ ((A ∧ B)::Δ).
  firstorder eauto.
Qed.

Lemma lkOOR n Γ Δ A B: lkh n Γ (A::B::Δ) -> lkh (S n) Γ ((A ∨ B)::Δ).
  firstorder eauto.
Qed.

Lemma lkOOL n Γ Δ A B: lkh n (A::Γ) Δ -> lkh n (B::Γ) Δ -> lkh (S n) ((A ∨ B)::Γ) Δ.
  firstorder eauto.
Qed.

Lemma lkOKI n Γ Γ'' Δ A:  lkh n Γ [A] -> lkh (S n) ((List.map K Γ)++Γ'') (K A::Δ).
  firstorder eauto.
Qed.   

(**  Invertibility 
     We prove the inversion lemmas from Troelstra & Schwichtenberg 
 **)
Lemma swapLeft n Γ Δ  A B: lkh n (A::B::Γ) Δ -> lkh n (B::A::Γ) Δ.
  intro. eapply lkPerm. apply H. psolve. psolve.
Qed.

Lemma swapRight n Γ Δ A B: lkh n Γ (A::B::Δ) -> lkh n Γ (B::A::Δ).
  intro. eapply lkPerm. apply H. all : psolve.
Qed.

Ltac swapL := apply swapLeft.
Ltac swapR := apply swapRight.
(* mauto ltac can be used with a hypothesis of the form H: *)

Ltac mauto' id  :=
  match goal with
  | [ H: (lkh ?n ?Γ ?F)   |- _  ] => (match H with
        | id => apply lkPerm with F Γ end) |
                                       
                                          [ H: (lkh  ?Γ ?F)   |- _  ] => match H with
        | id => apply lkPerm with F Γ
      end 
  end.

Ltac mauto H  :=
  mauto' H; try psolve; try auto . 


Lemma inversionIL h A B Γ Δ:
  lkh h ((A ⊃ B)::Γ) Δ -> lkh h Γ (A::Δ).  
Proof.
  revert Δ Γ.
  induction h.
  - intros Δ Γ H. inversion H; firstorder eauto.
    + inversion H0.
    + inversion H0.
  - intros Δ Γ H. inversion H.
    + apply lequiv_cons_destruct in H5. destruct H5.
      * destruct H5 as (Γ' & Hg' & Hg'').
        rewrite<- Hg'. apply lkOIL. swapR. apply IHh. mauto H2.
        apply IHh. mauto H4. 
      * destruct H5.  inversion H5. rewrite<- H8.   rewrite<- H1.  apply lkhStep. auto. 
    + rewrite H4. swapR. apply lkOIR. swapR.        apply IHh. rewrite<- H2. mauto H3.
    + rewrite H3. swapR. apply lequiv_cons_app in H2.  destruct H2. destruct H2. apply in_map_iff in H2. destruct H2. destruct H2. congruence.
      destruct H2. destruct H6 as (Γ3 & Hg1 & Hg2).  rewrite Hg2. apply lkOKI. auto. 
    + apply lequiv_cons_destruct in H5. destruct H5.
      *  destruct H5 as (Γ' & Hg' & Hg''). rewrite<- Hg'. apply lkOOL.  apply IHh. mauto H2.
         apply IHh. mauto H4. 
      *   inversion H5. congruence.
    + rewrite H3. swapR. apply lkOOR. apply IHh in H2. mauto H2. 
    + apply lequiv_cons_destruct in H3.   destruct H3.
      *  destruct H3 as (Γ' & Hg' & Hg''). rewrite<- Hg'. apply lkOAL; apply IHh.
         mauto H2. 
      *  destruct H3. congruence.
    +  rewrite H5. swapR. apply lkOAR; swapR; apply IHh.  mauto H2. mauto H4.
    + apply lkhStep.  apply IHh.  auto. 
Qed.     

Ltac exchange L R :=  apply lkPerm with R L; try psolve.

Lemma inversionIL2 h A B Γ Δ:
  lkh h ((A ⊃ B)::Γ) Δ -> lkh h (B::Γ) (Δ).  
Proof.
  revert Δ Γ.
  induction h.
  - intros Δ Γ H. inversion H; firstorder eauto; eauto; congruence. 
  -  intros Δ Γ H. inversion H; auto.
     + apply lequiv_cons_destruct in H5.   destruct H5.
       *  destruct H5 as (Γ' & Hd' & Hd'').  rewrite<- Hd'. apply swapLeft. apply lkOIL.  apply IHh. mauto H2. apply swapLeft.  apply IHh.  mauto H4.
       *  destruct H5.  inversion H5. subst A0 B0. apply lkhStep.  mauto H4.
     + rewrite H4.  apply lkOIR. apply swapLeft, IHh. mauto H3.
     +  rewrite H3.  apply lequiv_cons_app in H2.  destruct H2. destruct H2. apply in_map_iff in H2. destruct H2. destruct H2. congruence.
        destruct H2. destruct H6 as (Γ3 & Hg1 & Hg2).  rewrite Hg2.  apply leftWeakening. apply lkOKI. auto.
     +  apply lequiv_cons_destruct in H5.   destruct H5.
        * destruct H5 as (Γ' & Hd' & Hd'').  rewrite<- Hd'. apply swapLeft. apply lkOOL. apply swapLeft.  apply IHh. mauto H2. apply swapLeft.  apply IHh.  mauto H4.
        * destruct H5. congruence.
     +  rewrite H3.  apply lkOOR. apply IHh. mauto H2.
     +  apply lequiv_cons_destruct in H3.   destruct H3.  
        *  destruct H3 as (Γ' & Hd' & Hd'').  rewrite<- Hd'. apply swapLeft. apply lkOAL. apply lkPerm with (Δ) (B::A0::B0::Γ'); try psolve.   apply IHh. mauto H2.
        *  destruct H3.   congruence.
     +  rewrite H5.   apply lkOAR; apply IHh.  mauto H2. mauto H4. 
Qed.


Lemma inversionIR h A B Γ Δ:
  lkh h (Γ) ((A ⊃ B)::Δ) -> lkh h (A::Γ) (B::Δ).  
Proof.
  revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H;   firstorder eauto.
    + inversion H1.
  - intros Δ Γ H. inversion H; auto.
    + rewrite H5. swapL. apply lkOIL. swapR.  apply IHh.  mauto H2.  swapL. apply IHh.  mauto H4.
    +  apply lequiv_cons_destruct in H4.   destruct H4.
       *  destruct H4 as (Δ' & Hd' & Hd'').  rewrite<- Hd'. swapR. apply lkOIR. swapR. swapL.  apply IHh. mauto H3.
       *  destruct H4.  inversion H4. subst A0 B0. apply lkhStep.  mauto H3.
    +  apply lequiv_cons_destruct in H3.   destruct H3. 
       * destruct H3 as (Δ'' & Hd' & Hd''). rewrite<- Hd'. swapR. rewrite H2.   (* TODO: swap 0 2 / mtf 2 *)
         apply lkPerm with ((K A0 :: B :: Δ'')) ((map K Γ0) ++ (A::Γ'')); try psolve.
         apply lkOKI. auto. 
       *  destruct H3.  congruence.
    + rewrite H5. swapL. apply lkOOL; swapL; apply IHh. mauto H2. mauto H4.
    +  apply lequiv_cons_destruct in H3.   destruct H3.
       *  destruct H3 as (Δ' & Hd' & Hd'').  rewrite<- Hd'. swapR. apply lkOOR. exchange (A::Γ) (B::A0::B0::Δ').   apply IHh. mauto H2.
       *  destruct H3; congruence.
    + rewrite H3.  swapL. apply lkOAL. exchange (A::A0::B0::Γ0) (B::Δ).  apply IHh.  mauto H2.
    +  apply lequiv_cons_destruct in H5.   destruct H5.
       * destruct H5 as (Δ' & Hd' & Hd'').  rewrite<- Hd'. swapR. apply lkOAR; swapR;  apply IHh. mauto H2. mauto H4.
       * destruct H5; congruence.      
Qed.

Lemma inversionOR h A B Γ Δ:
  lkh h Γ ((A ∨ B)::Δ) -> lkh h Γ (A::B::Δ).
Proof.
  revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H;   firstorder eauto.
    + inversion H1.
  - intros Δ Γ H. inversion H; auto.
    + rewrite H5. apply lkOIL.  rewrite H1 in H2. apply swapRight in H2.  apply IHh in H2.
      mauto H2.  
      apply IHh in H4. mauto H4.
    + apply lequiv_cons_destruct in H4.   destruct H4.
      * destruct H4 as (Δ' & Hd' & Hd'').
        rewrite<- Hd'. apply lkPerm with ((A0 ⊃ B0)::A::B::Δ') Γ; try psolve.
        apply lkOIR.  apply lkPerm with (A::B::B0::Δ') (A0::Γ); try psolve.
        apply IHh. mauto H3.
      * destruct H4. congruence.
    + apply lequiv_cons_destruct in H3. destruct H3.
      * destruct H3.   destruct H3.    rewrite<- H3. apply lkPerm with (K A0::A::B::x) Γ; try psolve.
        rewrite H2. apply lkOKI. auto.
      *  destruct H3.  congruence.
    +  rewrite H5.    apply lkOOL.  apply IHh. mauto H2. apply IHh. mauto H4. 
    +  apply lequiv_cons_destruct in H3.   destruct H3. 
       * destruct H3 as (Δ' & Hd' & Hd''). rewrite<- Hd'. (* TODO: swap 0 2 / mtf 2 *)
         apply lkPerm with ((A0 ∨ B0)::A::B::Δ') Γ; try psolve. 
         apply lkOOR. rewrite H1 in H2. apply lkPerm with (A::B::A0::B0::Δ') Γ; try psolve.    apply IHh. mauto H2.
       *  destruct H3.  inversion H3. rewrite<- H6. rewrite<- H1. apply lkhStep. auto.
    + rewrite H3.  apply lkOAL.       apply IHh. mauto H2.
    + apply lequiv_cons_destruct in H5. destruct H5.
      *  destruct H5 as (Δ' & Hd' & Hd''). rewrite<- Hd'. apply lkPerm with ((A0 ∧ B0)::A::B::Δ') Γ; try psolve.
         apply lkOAR. apply lkPerm with (A::B::A0::Δ') Γ; try psolve. apply IHh. mauto H2.
         apply lkPerm with (A::B::B0::Δ') Γ; try psolve. apply IHh. mauto H4.
      * destruct H5; congruence.
Qed.

Lemma inversionOL1 h A B Γ Δ: lkh h ((A ∨ B)::Γ) Δ -> lkh h (A::Γ) Δ.  
Proof.
  revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H; firstorder eauto; inversion H0.
  -  intros Δ Γ H. inversion H; auto.
     + apply lequiv_cons_destruct in H5.   destruct H5.
       * destruct H5 as (Γ' & Hg' & Hg'').
        rewrite<- Hg'. swapL. apply lkOIL. apply IHh. mauto H2.
        swapL. apply IHh. mauto H4. 
       *  inversion H5. congruence.
     +  rewrite H4. apply lkOIR. swapL. apply IHh. mauto H3.
     +  rewrite H3.  apply lequiv_cons_app in H2.  destruct H2. destruct H2. apply in_map_iff in H2. destruct H2. destruct H2. congruence. 
        destruct H2. destruct H6 as (Γ3 & Hg1 & Hg2).  rewrite Hg2.
        apply lkPerm with (K A0 :: Δ0) (map K Γ0 ++ (A::Γ3)). 
        apply lkOKI. auto. psolve. reflexivity.
     +  apply lequiv_cons_destruct in H5.   destruct H5.
        * destruct H5 as (Γ' & Hg' & Hg''). rewrite<- Hg'. swapL. apply lkOOL.
          -- swapL. apply IHh. mauto H2.
          -- swapL. apply IHh. mauto H4.
        * destruct H5.  inversion H5. rewrite<- H8.   rewrite<- H1.  apply lkhStep. auto.
     +      rewrite H3. apply lkOOR. apply IHh. mauto H2.
     +  apply lequiv_cons_destruct in H3.   destruct H3.
        * destruct H3 as (Γ' & Hg' & Hg''). rewrite<- Hg'. swapL. apply lkOAL.
          (* moveToFront 3 *) apply lkPerm with Δ (A::A0::B0::Γ'); try psolve.
          apply IHh. mauto H2.
        * destruct H3; congruence.
     + rewrite H5.      apply lkOAR; apply IHh. mauto H2. mauto H4.
Qed.

Lemma inversionOL2 h A B Γ Δ:
  lkh h ((A ∨ B)::Γ) Δ -> lkh h (B::Γ) Δ.  
Proof.
  revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H; firstorder eauto; inversion H0.
  -  intros Δ Γ H. inversion H; auto.
     + apply lequiv_cons_destruct in H5.   destruct H5.
       * destruct H5 as (Γ' & Hg' & Hg'').
        rewrite<- Hg'. swapL. apply lkOIL. apply IHh. mauto H2.
        swapL. apply IHh. mauto H4. 
       *  inversion H5. congruence.
     +  rewrite H4. apply lkOIR. swapL. apply IHh. mauto H3.
     +  rewrite H3.  apply lequiv_cons_app in H2.  destruct H2. destruct H2. apply in_map_iff in H2. destruct H2. destruct H2. congruence. 
        destruct H2. destruct H6 as (Γ3 & Hg1 & Hg2).  rewrite Hg2.
        apply lkPerm with (K A0 :: Δ0) (map K Γ0 ++ (B::Γ3)). 
        apply lkOKI. auto. psolve. reflexivity.
     +  apply lequiv_cons_destruct in H5.   destruct H5.
        * destruct H5 as (Γ' & Hg' & Hg''). rewrite<- Hg'. swapL. apply lkOOL.
          -- swapL. apply IHh. mauto H2.
          -- swapL. apply IHh. mauto H4.
        * destruct H5.  inversion H5. rewrite<- H8.   rewrite<- H3.  apply lkhStep. auto.
     +      rewrite H3. apply lkOOR. apply IHh. mauto H2.
     +  apply lequiv_cons_destruct in H3.   destruct H3.
        * destruct H3 as (Γ' & Hg' & Hg''). rewrite<- Hg'. swapL. apply lkOAL.
          (* moveToFront 3 *) apply lkPerm with Δ (B::A0::B0::Γ'); try psolve.
          apply IHh. mauto H2.
        * destruct H3; congruence.
     + rewrite H5.      apply lkOAR; apply IHh. mauto H2. mauto H4.
Qed.


Lemma inversionAL h A B Γ Δ:
  lkh h ((A ∧ B)::Γ) Δ -> lkh h (A::B::Γ) Δ. 
Proof.
  revert Δ Γ. induction h.
    - intros Δ Γ H. inversion H; firstorder eauto; inversion H0.
  -  intros Δ Γ H. inversion H; auto.
     + apply lequiv_cons_destruct in H5.   destruct H5.
       * destruct H5 as (Γ' & Hg' & Hg'').
         rewrite<- Hg'. exchange ((A0 ⊃ B0)::A::B::Γ') Δ. apply lkOIL. apply IHh. mauto H2.
         exchange (A::B::B0::Γ') (Δ). apply IHh. mauto H4. 
       *  inversion H5. congruence.
     +  rewrite H4. apply lkOIR. exchange (A::B::A0::Γ) (B0::Δ0).  apply IHh. mauto H3.
     +  rewrite H3.  apply lequiv_cons_app in H2.  destruct H2. destruct H2. apply in_map_iff in H2. destruct H2. destruct H2. congruence. 
        destruct H2. destruct H6 as (Γ3 & Hg1 & Hg2).  rewrite Hg2.
        apply lkPerm with (K A0 :: Δ0) (map K Γ0 ++ (A::B::Γ3)). 
        apply lkOKI. auto. psolve. reflexivity.
     +  apply lequiv_cons_destruct in H5.   destruct H5.
        * destruct H5 as (Γ' & Hg' & Hg''). rewrite<- Hg'. exchange ((A0 ∨ B0)::A::B::Γ') Δ.  apply lkOOL.
          -- exchange (A::B::A0::Γ') Δ. apply IHh. mauto H2.
          -- exchange (A::B::B0::Γ') Δ. apply IHh. mauto H4.
        * destruct H5.  inversion H5. 
     +      rewrite H3. apply lkOOR. apply IHh. mauto H2.
     +  apply lequiv_cons_destruct in H3.   destruct H3.
        * destruct H3 as (Γ' & Hg' & Hg''). rewrite<- Hg'. exchange ((A0 ∧ B0)::A::B::Γ') Δ.  apply lkOAL.
          (* moveToFront 3 *) apply lkPerm with Δ (A::B::A0::B0::Γ'); try psolve.
          apply IHh. mauto H2.
        * destruct H3. inversion H3. subst A0 B0. apply lkhStep. mauto H2.   
     + rewrite H5.      apply lkOAR; apply IHh. mauto H2. mauto H4.
Qed. 

Lemma inversionAR1 h A B Γ Δ:
  lkh h Γ ((A ∧ B)::Δ) -> lkh h Γ (A::Δ).
Proof.
    revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H;   firstorder eauto.
    + inversion H1.
  - intros Δ Γ H. inversion H; auto.
    + rewrite H5. apply lkOIL.  rewrite H1 in H2. apply swapRight in H2.  apply IHh in H2.
      mauto H2.  
      apply IHh in H4. mauto H4.
    + apply lequiv_cons_destruct in H4.   destruct H4.
      * destruct H4 as (Δ' & Hd' & Hd'').
        rewrite<- Hd'. apply lkPerm with ((A0 ⊃ B0)::A::Δ') Γ; try psolve.
        apply lkOIR.  apply lkPerm with (A::B0::Δ') (A0::Γ); try psolve.
        apply IHh. mauto H3.
      * destruct H4. congruence.
    + apply lequiv_cons_destruct in H3. destruct H3.
      * destruct H3.   destruct H3.    rewrite<- H3. apply lkPerm with (K A0::A::x) Γ; try psolve.
        rewrite H2. apply lkOKI. auto.
      *  destruct H3.  congruence.
    +  rewrite H5.    apply lkOOL.  apply IHh. mauto H2. apply IHh. mauto H4. 
    +  apply lequiv_cons_destruct in H3.   destruct H3. 
       * destruct H3 as (Δ' & Hd' & Hd''). rewrite<- Hd'. (* TODO: swap 0 2 / mtf 2 *)
         apply lkPerm with ((A0 ∨ B0)::A::Δ') Γ; try psolve. 
         apply lkOOR. rewrite H1 in H2. apply lkPerm with (A::A0::B0::Δ') Γ; try psolve.    apply IHh. mauto H2.
       *  destruct H3.  inversion H3. 
    + rewrite H3.  apply lkOAL.       apply IHh. mauto H2.
    + apply lequiv_cons_destruct in H5. destruct H5.
      *  destruct H5 as (Δ' & Hd' & Hd''). rewrite<- Hd'. apply lkPerm with ((A0 ∧ B0)::A::Δ') Γ; try psolve.
         apply lkOAR. apply lkPerm with (A::A0::Δ') Γ; try psolve. apply IHh. mauto H2.
         apply lkPerm with (A::B0::Δ') Γ; try psolve. apply IHh. mauto H4.
      * destruct H5. inversion H5. subst A0 B0. apply lkhStep. mauto H2.  
Qed.

Lemma inversionAR2 h A B Γ Δ:
  lkh h Γ ((A ∧ B)::Δ) -> lkh h Γ (B::Δ).
Proof.
    revert Δ Γ. induction h.
  - intros Δ Γ H. inversion H;   firstorder eauto.
    + inversion H1.
  - intros Δ Γ H. inversion H; auto.
    + rewrite H5. apply lkOIL.  rewrite H1 in H2. apply swapRight in H2.  apply IHh in H2.
      mauto H2.  
      apply IHh in H4. mauto H4.
    + apply lequiv_cons_destruct in H4.   destruct H4.
      * destruct H4 as (Δ' & Hd' & Hd'').
        rewrite<- Hd'. apply lkPerm with ((A0 ⊃ B0)::B::Δ') Γ; try psolve.
        apply lkOIR.  apply lkPerm with (B::B0::Δ') (A0::Γ); try psolve.
        apply IHh. mauto H3.
      * destruct H4. congruence.
    + apply lequiv_cons_destruct in H3. destruct H3.
      * destruct H3.   destruct H3.    rewrite<- H3. apply lkPerm with (K A0::B::x) Γ; try psolve.
        rewrite H2. apply lkOKI. auto.
      *  destruct H3.  congruence.
    +  rewrite H5.    apply lkOOL.  apply IHh. mauto H2. apply IHh. mauto H4. 
    +  apply lequiv_cons_destruct in H3.   destruct H3. 
       * destruct H3 as (Δ' & Hd' & Hd''). rewrite<- Hd'. (* TODO: swap 0 2 / mtf 2 *)
         apply lkPerm with ((A0 ∨ B0)::B::Δ') Γ; try psolve. 
         apply lkOOR. rewrite H1 in H2. apply lkPerm with (B::A0::B0::Δ') Γ; try psolve.    apply IHh. mauto H2.
       *  destruct H3.  inversion H3. 
    + rewrite H3.  apply lkOAL.       apply IHh. mauto H2.
    + apply lequiv_cons_destruct in H5. destruct H5.
      *  destruct H5 as (Δ' & Hd' & Hd''). rewrite<- Hd'. apply lkPerm with ((A0 ∧ B0)::B::Δ') Γ; try psolve.
         apply lkOAR. apply lkPerm with (B::A0::Δ') Γ; try psolve. apply IHh. mauto H2.
         apply lkPerm with (B::B0::Δ') Γ; try psolve. apply IHh. mauto H4.
      * destruct H5. inversion H5. subst A0 B0. apply lkhStep. mauto H4.    
Qed.   

(** Contraction *)

Lemma contraction h Γ Δ F: (lkh h (F::F::Γ) Δ -> lkh h (F::Γ) Δ) /\ (lkh h Γ (F::F::Δ) -> lkh h Γ (F::Δ)). 
Proof.
  revert Δ Γ F.
  induction h.
  - intros. split. intro H. inversion H.
    + assert ((Var A) = F \/ (Var A) el Γ) by firstorder. destruct H2.
      *  rewrite<- H2. eauto. 
      *  eauto.  
    + assert (Bot = F \/ Bot el Γ) by firstorder. destruct H1.
      * subst F; eauto.  
      * eauto.
    + intro H.     inversion H.
      * assert ((Var A) = F \/ (Var A) el Δ) by firstorder eauto.   destruct H2; eauto.
        -- subst F; eauto. 
      * eauto.
  - intros.
    assert (IHL: forall Δ Γ F,  (lkh h (F :: F :: Γ) Δ -> lkh h (F :: Γ) Δ)) by firstorder.
    assert (IHR: forall Δ Γ F,  (lkh h Γ (F :: F :: Δ) -> lkh h Γ (F :: Δ))) by firstorder.
    clear IHh. 
    split.
    
    intro H. inversion H.
    + apply lequiv_doublecons_destruct in H5; destruct H5.
      * destruct H5. subst F. rewrite<- H8 in H2.  apply inversionIL in H2.  apply lkOIL.
        -- apply IHR. mauto H2; psolve.
        -- apply IHL. apply inversionIL2 with A. mauto H4.
      * destruct H5. destruct H8 as (Γ' & Hg1 & Hg2). rewrite Hg1. swapL. apply lkOIL.
        -- apply IHL.  mauto H2.
        -- swapL.  apply IHL. mauto H4.   
    +  rewrite H4.  apply lkOIR. swapL. apply IHL. mauto H3.
    +  apply lequiv_cons_app in H2.   destruct H2.
       * destruct H2. rewrite H3. destruct H6 as (B' & Hb' & Hb'').
         apply in_map_iff in H2. destruct H2 as (F' & Hf1 & Hf2).
         rewrite Hb''.
         apply lequiv_cons_app in Hb''.  destruct Hb''.
         -- destruct H2.  destruct H6. destruct H6. rewrite H6. 
            specialize (map_perm_cons' Hb'). intro.  destruct H8 as (A' & Ha' & F'' & Hf). rewrite H6 in Ha'. specialize (map_perm_cons' Ha'). intro. destruct H8 as (C' & Hc' & Hc''').
            rewrite<- Hc'. rewrite<- Hf1. rewrite<- map_cons. 
            apply lkOKI. 
            apply IHL.
            mauto H1.
            apply map_inj_perm with (f := fun x => K x).
            intros a b. firstorder eauto. inversion H8. reflexivity.
            simpl. rewrite Hc'. rewrite Hf1. rewrite<- H6. rewrite<- Hb'. auto. 
         -- destruct H2. destruct H6 as (C' & Hc1 & HC2). rewrite Hc1.
            apply lkPerm with (K A :: Δ0) ((F::B')++C'); try psolve.  rewrite<- Hb'.
            apply lkOKI. auto. 
       * destruct H2.   destruct H6 as (Γ3 & Hg' & Hg'').
         rewrite H3. rewrite Hg''. apply lkOKI. auto. 
    +  apply lequiv_doublecons_destruct in H5.  destruct H5.
       * destruct H5. rewrite H5. apply lkOOL.
         -- apply IHL.  apply inversionOL1 with B. mauto H2. subst F. psolve.
         -- apply IHL. apply inversionOL2 with A. subst F. mauto H4; psolve. 
       * destruct H5. destruct H8 as (Γ' & Hg1 & Hg2). rewrite Hg1. swapL. apply lkOOL; swapL; apply IHL.
         -- mauto H2.
         -- mauto H4.             
    + rewrite H3. apply lkOOR. apply IHL. mauto H2.
    + apply lequiv_doublecons_destruct in H3.  destruct H3.
      * destruct H3. rewrite H3. apply lkOAL. apply IHL. apply lkPerm with Δ (B::A::A::Γ); try psolve. apply IHL.
         apply lkPerm with Δ (A::B::A::B::Γ); try psolve. apply inversionAL.  mauto H2. subst F. psolve. 
      
      *  destruct H3. destruct H6 as (Γ' & Hg1 & Hg2). rewrite Hg1. swapL. apply lkOAL.
         apply lkPerm with Δ (F::A::B::Γ'); try psolve. apply IHL. mauto H2. 
    + rewrite H5.  apply lkOAR.  apply IHL. mauto H2. apply IHL. mauto H4.
    +  apply lkhStep.  apply IHL; auto.


   +  intros. inversion H.
      * rewrite H5. apply lkOIL. swapR. apply IHR. mauto H2. apply IHR. mauto H4.
      *  apply lequiv_doublecons_destruct in H4.  destruct H4.
         -- destruct H4. subst F.  apply lkOIR. apply IHL. apply IHR.   apply inversionIR. mauto H3.
         --  destruct H4.   destruct H7 as (Γ3 & Hg' & Hg''). rewrite Hg'. swapR. apply lkOIR.  swapR. apply IHR. mauto H3. 
      * rewrite H2.  apply lequiv_doublecons_destruct in H3.  destruct H3.
        -- destruct H3. subst F. apply lkOKI. auto.
        -- destruct H3. destruct H6 as (Δ2 & Hd1 & Hd2).   rewrite Hd1. swapR.
           apply lkOKI. auto.
      * rewrite H5.   apply lkOOL; apply IHR. mauto H2. mauto H4.
      *  apply lequiv_doublecons_destruct in H3.  destruct H3.
         -- destruct H3. rewrite H3. apply lkOOR. apply IHR. rewrite H1 in H2. rewrite<- H6 in H2. subst F.
             exchange Γ (B::A::A::Δ).  apply IHR. exchange Γ (A::B::A::B::Δ). apply inversionOR. mauto H2. 
         --  destruct H3. destruct H6 as (Δ3 & Hd1 & Hd2).   rewrite Hd1. swapR.
             apply lkOOR.  rewrite H1 in H2. rewrite<- Hd2 in H2. exchange Γ (F::A::B::Δ3). 
             apply IHR. mauto H2. 
      * rewrite H3.   apply lkOAL, IHR. mauto H2.
      * apply lequiv_doublecons_destruct in H5. destruct H5.
        -- destruct H5. subst F. apply lkOAR; apply IHR.
           ++  apply inversionAR1 with (B := B). mauto H2.
           ++  apply inversionAR2 with (A := A). mauto H4.     
        --  destruct H5.  destruct H8 as (Δ' & Hd1 & Hd2). rewrite Hd1. swapR. apply lkOAR; swapR; apply IHR.  
           mauto H2. mauto H4. 
      * apply lkhStep, IHR.  auto.
Qed.       
(** Get good weakening and contraction results **)

Lemma structuralProperties: structRightWeakening lkh /\ structLeftContraction lkh  /\ structRightContraction lkh /\ structLeftWeakening lkh /\ PermutationExchange lkh.
Proof.  
  repeat split.   
  - unfold structRightWeakening. intros.  apply rightWeakening. auto.
  -   unfold structLeftContraction. intros; firstorder eauto using contraction. apply contraction in H.   auto.
  -   unfold structRightContraction. intros; firstorder eauto. apply contraction in H. auto.    
  -  unfold structLeftWeakening.  intros. apply leftWeakening. auto.
  -  unfold PermutationExchange.   intros. apply lkPerm with Ω Γ; auto. 
Qed.    
Lemma weakLeft n A A' B: lkh n A B -> incl A A' -> lkh n A' B.
  intros.
  assert (Weak lkh).  
  apply Weakening; pose structuralProperties; try tauto.
  unfold Weak in H1.  apply H1 with A B; auto.
Qed.   

Lemma weakRight n A B B': lkh n A B -> incl B B' -> lkh n A B'.
Proof. 
  intros.
  assert (Weak lkh).  
  apply Weakening; pose structuralProperties; try tauto.
  unfold Weak in H1.  apply H1 with A B; auto.
Qed.

Lemma contractionLeft n A A' B: (List.incl A  A') -> (List.incl A' A) -> lkh n A B <-> lkh n A' B.
  intros.
  assert (Contraction lkh).  
  apply structuralProperties.contraction; pose structuralProperties; try tauto.
  unfold Contraction in H1. split; intro; eauto using H1. apply H1 with A B; firstorder eauto.
  apply H1 with A' B; firstorder eauto. 
Qed.

Lemma contractionRight n A B B': (List.incl B  B') -> (List.incl B' B) -> lkh n A B <-> lkh n A B'.
  intros.
  assert (Contraction lkh).  
  apply structuralProperties.contraction; pose structuralProperties; try tauto.
  unfold Contraction in H1. split; intro; eauto using H1. apply H1 with A B; firstorder eauto.
  apply H1 with A B'; firstorder eauto. 
Qed. 

(** ** Cut Elimination **)
Lemma le_wf_ind (P: nat -> nat -> Prop) (Hrec: forall n m, (forall p q, p < n -> P p q) -> (forall q, q < m -> P n q) -> P n m) : forall n m, P n m.
Proof.
  induction n using lt_wf_ind.
  - induction m using lt_wf_ind.
    + apply Hrec.
      intros p q H1. apply H. auto.
      
      intros q H1.  apply H0. 
      exact H1.
Qed.

Lemma cutElimination':
  forall  m n n1 n2 Γ F Δ (P1:lkh n1 Γ (F::Δ) ) (P2: lkh n2 (F::Γ) Δ) ,  n1 + n2 = n -> (size F) = m -> lk  (Γ) Δ.
Proof.
  intros n m. 
  induction n, m   using le_wf_ind.   
  intros n1 n2 Γ F Δ P1 P2 Hn1 Hf .
  inversion P1.
  - destruct H2.
    + exists n2. apply contractionLeft with (F::Γ). auto. subst F.   auto. subst F. auto.  (* Contraction -> done *)  
    + exists 0. apply lkhA with A; auto. 
  - eexists. apply lkhB. auto. 
  -
    assert (lkh n2 (F::B::Γ0) Δ).
    swapL. apply inversionIL2 with (A := A).  swapL. rewrite<- H5. auto.
    assert (lk (B::Γ0) Δ).
    apply H0 with (q := n+n2) (n1 := n) (n2 := n2) (F := F); try lia; auto.  rewrite<- H3. auto.
    assert (lk Γ0 (A::Δ)).  apply H0 with (q := n+n2) (n1 := n) (n2 := n2) (F := F); try lia; auto. mauto H2. apply inversionIL with (B := B). swapL.  rewrite<- H5. auto.  
    
    destruct H10 as [n3 H10], H11 as [n4 H11]. exists (S(Nat.max n3 n4)). rewrite H5. apply lkOIL.
  
    apply multiStep with n4; try lia; auto.   
    apply multiStep with n3; try lia; auto.     
  - apply lequiv_cons_destruct' in H4. destruct H4.
    + destruct H4 as (Δ'' & Hd1 & Hd2 & Hd3).
      assert (lk (A::Γ) (B::Δ'')). {
        apply H0 with (F := F) (q := n + n2) (n1 := n) (n2 := n2); auto; try lia.
        mauto H3.
        swapL. apply inversionIR. mauto P2. 
      }
      destruct H4 as [nH4 H4].  eexists. rewrite<- Hd1. apply lkOIR.   apply H4.  
    + destruct H4.  rewrite H4 in P1, P2.  specialize (inversionIL2 P2).  specialize  (inversionIL P2). intros.
    assert (lk (A::Γ) Δ).
    apply H with (F := B) (p := (size B)) (q := n + n2) (n1 := n) (n2 := n2); auto; try lia. rewrite<- Hf. rewrite H4; cbn; lia. rewrite<- H8. mauto H3. swapL. apply leftWeakening.  mauto H10.
    destruct H11 as [n11 H11].
    apply H with (F := A) (p := (size A)) (q := n11+n2) (n1 := n2) (n2 := n11).
    rewrite<- Hf. rewrite H4; cbn; lia. auto. auto. lia. auto. 
  - apply lequiv_cons_destruct' in H3. destruct H3.
    + destruct H3 as (Δ'' & Hd1 & Hd2 & Hd3).
      eexists (S _).  rewrite<- Hd1. rewrite H2. apply lkOKI. eauto.
    +  destruct H3.  subst F.  inversion P2.
       * destruct H3; try congruence. eexists. apply lkhA with A0; auto.
       *  destruct H3; try congruence.  eexists. apply lkhB. auto.
       *  apply lequiv_cons_destruct in H11. destruct H11. 
          2:destruct H11; congruence.
          destruct H11 as (Γ5 & Hg & Hg').
          assert (lk (B::Γ5) Δ).  
          {
           apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
           apply inversionIL2 with A0. mauto P1.
           mauto H10. 
          }

          assert (lk (Γ5) (A0::Δ)).
          {
            apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
            
           swapR. apply inversionIL with B. mauto P1.
           mauto H8. 
          }

          destruct H11 as [n11 H11], H15 as [n15 H15]. exists (S(Nat.max n11 n15)).
          rewrite<- Hg. apply lkOIL.
          apply multiStep with n15; try lia; auto.
          apply multiStep with n11; try lia; auto. 
       *  assert (lk (A0::Γ) (B::Δ1)).
          {
             apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
             swapR. apply inversionIR. swapR. mauto P1.
             mauto H9. 
          }
          destruct H14 as [n14 H14].
          exists (S n14).
          rewrite H10. apply lkOIR. auto.
       *  apply lequiv_cons_app in H8. destruct H8.
          -- (* Principal => need cut *)
            destruct H8 as (HK & C & HC1 & HC2).
            enough (lk (Γ++Γ) Δ).
            destruct H8 as [n8 H8]. exists n8.
            apply contractionLeft with (Γ ++ Γ). auto. auto. auto.
            
            specialize (map_perm_cons' HC1). intro. 
            destruct H8 as (Γ2 & HG'' & HG''').
            
            assert (lk (Γ0 ++ Γ2) [A0]).
            apply H with (F := (A)) (p := (size A)) (q := n+n0) (n1 := n) (n2 := n0); auto; try lia. subst m1. simpl; lia.
            apply weakLeft with (Γ0); auto. apply weakRight with [A]; auto. 
            apply weakLeft with (A::Γ2); auto.  assert ((A::Γ2) ≡P Γ1).
            apply map_inj_perm with (f := K). intros a b T. inversion T; firstorder eauto. 
            simpl map. rewrite HG''. psolve. rewrite H8. auto.
            destruct H8 as [n8 H8]. 
            exists (S n8). rewrite H9.
            rewrite H2 at 1. rewrite  HC2 at 1. 
            apply lkPerm with ((K A0)::Δ1) (((map K Γ0)++C)++(Γ''++Γ''0)); try psolve.
            rewrite<- HG''. rewrite<- map_app. apply lkOKI. auto. 
          --  destruct H8 as (HK & C' & HC1 & HC2). eexists (S n0).  rewrite H9.
              rewrite HC2. apply lkOKI. auto. 
       *  apply lequiv_cons_destruct in H11. destruct H11. 
          2:destruct H11; congruence.
          destruct H11 as (Γ5 & Hg & Hg').
          assert (lk (A0::Γ5) Δ).
          { rewrite H3 in H8. rewrite<- Hg' in H8. 
            apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
            apply inversionOL1 with B. rewrite Hg.  auto.  mauto H8. }

          assert (lk (B::Γ5) Δ). {
            rewrite H9 in H10.
            apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
            apply inversionOL2 with A0. rewrite Hg. auto. mauto H10. 
          }
          destruct H11 as [n11 H11], H15 as [n15 H15]. exists (S(Nat.max n11 n15)).
          rewrite<- Hg. apply lkOOL.
          apply multiStep with n11; try lia; auto.
          apply multiStep with n15; try lia; auto. 
       * assert (lk Γ (A0::B::Δ1)). {
           apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
           apply lkPerm with (A0::B::K A::Δ1) Γ; try psolve. apply inversionOR.
           mauto P1; try psolve. 
           mauto H8. 
         }
         destruct H13 as [n13 H13].
         exists (S n13). rewrite H9. apply lkOOR. mauto H13.
       *   apply lequiv_cons_destruct in H9. destruct H9. 
           2:destruct H9; congruence.
           destruct H9 as (Γ5 & Hg & Hg').
           assert (lk (A0::B::Γ5) Δ).
           {
             rewrite H3 in H8. rewrite<- Hg' in H8. 
             apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
             apply inversionAL. rewrite Hg. auto.
             mauto H8.
           }
           destruct H9 as [n9 H9].
           exists (S n9). rewrite <- Hg. apply lkOAL. auto. 
       *  assert (lk Γ (A0::Δ1)).  {
            apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
            swapR. apply inversionAR1 with B. mauto P1. 
            mauto H8. 
          }
          assert (lk Γ (B::Δ1)).  {
            apply H0 with (F := (K A)) (q := n0+n1) (n1 := n1) (n2 := n0); auto; try lia.
            swapR. apply inversionAR2 with A0. mauto P1. 
            mauto H10. 
          }

          destruct H15 as [n15 H15], H16 as [n16 H16].
          exists (S(Nat.max n15 n16)). rewrite H11.
          apply lkOAR.
          apply multiStep with n15; auto; try lia.
          apply multiStep with n16; auto; try lia. 
       *  apply H0 with (F := (K A)) (n1 := n1) (n2 := n0) (q := n1+n0); try lia; auto.   
  - (* Do the 2 cuts first *) 
    assert (lk (A::Γ0) Δ).
    {
      apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F) ; try lia.  
      rewrite<- H1. auto.
      swapL.  apply inversionOL1 with (B := B). mauto P2;try psolve.
    }  
    assert (lk (B::Γ0) Δ). {
      apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F) ; try lia.  
      rewrite<- H3. auto.
      swapL.  apply inversionOL2 with (A := A). mauto P2;try psolve.
    }  
    destruct H9 as (lh & Hl) , H10 as (rh & Hr).
    exists (S(Nat.max lh rh)). rewrite H5. apply lkOOL.
    apply multiStep with lh; try lia; auto.
    apply multiStep with rh; try lia; auto. 
  - apply lequiv_cons_destruct in H3. destruct H3.
    + destruct H3 as (Δ'' & Hd1 & Hd2 ).
      assert (lk Γ (A::B::Δ'')). 
      apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F); try lia; auto. 
      mauto H2. apply inversionOR. mauto P2.  destruct H3 as [n3 H3].
      exists (S n3). rewrite<- Hd1. apply lkOOR. auto. 
    + assert (lk (B::Γ) Δ).
      apply H with (F := A) (q := n2+n2) (p := size A) (n1 := n2) (n2 := n2); try lia. subst m1.  destruct H3. subst F. simpl size; lia. apply rightWeakening. apply inversionOL2 with A. destruct H3.  rewrite<- H3. auto. destruct H3. rewrite H3 in P2.
      apply inversionOL1 in P2.  swapL. apply leftWeakening. auto.

      assert (lk (A::Γ) Δ).
      apply H with (F := B) (q := n2+n2) (p := size B) (n1 := n2) (n2 := n2); try lia. subst m1.  destruct H3. subst F. simpl size; lia. apply rightWeakening. apply inversionOL1 with B. destruct H3.  rewrite<- H3. auto. destruct H3. rewrite H3 in P2.
      apply inversionOL2 in P2.  swapL. apply leftWeakening. auto.

      destruct H7 as [nH7 H7].
      destruct H8 as [nH8 H8].
      
      assert (lk Γ (B::Δ)). 
      apply H with (F := A) (q := n1+nH8) (p := size A) (n1 := n1) (n2 := nH8); try lia. subst m1.  destruct H3. subst F. simpl size; lia.  apply inversionOR. destruct H3. subst F.  auto.  apply rightWeakening. auto.
      destruct H9 as [nH9 H9].
      
      
      apply H with (F := B) (q := nH9+nH7) (p := size B) (n1 := nH9) (n2 := nH7); try lia; destruct H3. subst m1. subst F. cbn;lia. auto. auto. 
  - rewrite H3 in P2. apply lkPerm with (Δ' := Δ) (Γ' := ((A ∧ B)::F::Γ0))  in P2; try psolve. apply inversionAL in P2.
    assert (lk (A::B::Γ0) Δ).
    apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F); auto; try lia.
    mauto H2.
    mauto P2.
    destruct H7 as (ht & H7). eexists. rewrite H3. apply lkOAL. eauto. 
  -
    apply lequiv_cons_destruct' in H5. destruct H5.
    + destruct H5 as (Δ' & Hd1 & Hd2 & Hd3).
      rewrite<- Hd1 in P1.
      assert (lk Γ (A::Δ')).
      apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F); auto; try lia.
      swapR. rewrite Hd2. rewrite<- H1. auto. apply inversionAR1 with B. rewrite Hd1.
      auto.
      assert (lk Γ (B::Δ')).
      apply H0 with (n1 := n) (n2 := n2) (q := n+n2) (F := F); auto; try lia.
      swapR. rewrite Hd2. rewrite<- H3. auto. apply inversionAR2 with A. rewrite Hd1.
      auto. 
      
      destruct H5 as [n5 nH5].
      destruct H9 as [n9 nH9].
      exists (S(Nat.max n5 n9)). rewrite<- Hd1. apply lkOAR. 

      apply multiStep with n5; try lia; auto.
      apply multiStep with n9; try lia; auto. 
    (* Replace with 2 smaller cuts *)
    + destruct H5.
      assert (lk (A::Γ) (Δ)).
      apply H with (n1 := n) (n2 := n2) (q := n+n2) (p := (size B)) (F := B); auto;try lia.
      * subst m1; subst F; cbn; lia.
      * rewrite<- H9. apply leftWeakening. rewrite<- H3. auto.
      * swapL. apply inversionAL.  rewrite<- H5. auto.
      * destruct H10 as [n10 H10]. apply H with (n1 := n) (n2 := n10) (q := n+n10) (F := A) (p := size A); auto; try lia. 
        -- subst m1; subst F; cbn; lia.
        -- rewrite<- H9. rewrite<- H1. auto.         
  - 
    apply H0 with (F := F) (n1 := n) (n2 := n2) (q := n+n2); try lia; auto.
Qed.     
