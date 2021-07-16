(** * Permutation-based Cut-Elimination for IEL *)
(** Formalize IEL using list equivalence **)
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
Import ListNotations. 
Set Implicit Arguments.

Definition env : Type := list form.

(* Things about multisets of formulae, which is how the environment is represented *)


Require Import Permutations. 

Inductive IELGM:  env -> form -> Prop :=
  ielgmA (A: nat) Γ: List.In  (Var A) Γ -> IELGM Γ (Var A)
                                          
| ielgmBotVar Γ (s: form): List.In Bot Γ -> IELGM Γ s
                                 
| ielgmAL  Γ Γ1 Γ2 F G H:
    Γ1 ≡P (F::G::Γ) -> Γ2 ≡P ((F ∧ G)::Γ) ->
    IELGM (Γ1) H -> IELGM (Γ2) H
                                                        
| ielgmAR Γ  F G:
    IELGM Γ F -> IELGM Γ G -> IELGM Γ (F ∧ G)
| ielgmOL Γ Γ1 Γ2 Γ3  F G H:
    Γ1 ≡P (F::Γ) -> Γ2 ≡P (G::Γ) -> Γ3 ≡P ((F ∨ G)::Γ) ->
                    
    IELGM (Γ1) H -> IELGM (Γ2) H
    -> IELGM (Γ3) H
| ielgmOR1 Γ F G: IELGM Γ F -> IELGM Γ (F ∨ G)
| ielgmOR2 Γ F G: IELGM Γ F -> IELGM Γ (G ∨ F)
                                           
| ielgmIL Γ Γ1 Γ2 Γ3 F G H:
    Γ1 ≡P ((F ⊃ G)::Γ) -> Γ2 ≡P (G:: Γ) -> Γ3 ≡P ((F ⊃ G) :: Γ) ->
    IELGM (Γ1) F -> IELGM (Γ2) H -> IELGM (Γ3) H
| ielgmIR Γ F G: IELGM (F::Γ) G -> IELGM (Γ) (F ⊃ G)
| ielgmKI Γ Δ F D Γ': IELGM (Γ) F -> Γ ≡P (D ++ Δ ++ (List.map K Δ)) -> Γ' ≡P (D ++ (List.map K Δ)) -> IELGM Γ' (K F)                                                         
| ielgmKB Γ F: IELGM Γ (K ⊥) -> IELGM Γ F.

Search "eqDec". 
Instance form_eq_dec' :
  eq_dec form.
Proof. unfold dec. repeat decide equality. Defined.


Inductive IELGMd: nat -> env -> form -> Prop :=
  ielgmdA (A: nat) Γ: List.In  (Var A) Γ -> IELGMd 0 Γ (Var A)
                                          
| ielgmdBotVar Γ (s: form): List.In Bot Γ -> IELGMd 0 Γ s
                                 
| ielgmdAL  Γ Γ1 Γ2 F G H n:
    Γ1 ≡P (F::G::Γ) -> Γ2 ≡P ((F ∧ G)::Γ) ->
    IELGMd n (Γ1) H -> IELGMd (S n) (Γ2) H
                                                        
| ielgmdAR Γ  F G n:
    IELGMd n Γ F -> IELGMd n Γ G -> IELGMd (S n) Γ (F ∧ G)
| ielgmdOL Γ Γ1 Γ2 Γ3  F G H n:
    Γ1 ≡P (F::Γ) -> Γ2 ≡P (G::Γ) -> Γ3 ≡P ((F ∨ G)::Γ) ->
                    
    IELGMd n (Γ1) H -> IELGMd n (Γ2) H
    -> IELGMd (S n) (Γ3) H
| ielgmdOR1 Γ F G n: IELGMd n Γ F -> IELGMd (S n) Γ (F ∨ G)
| ielgmdOR2 Γ F G n: IELGMd n Γ F -> IELGMd (S n) Γ (G ∨ F)
                                           
| ielgmdIL Γ Γ1 Γ2 Γ3 F G H n:
    Γ1 ≡P ((F ⊃ G)::Γ) -> Γ2 ≡P (G:: Γ) -> Γ3 ≡P ((F ⊃ G) :: Γ) ->
    IELGMd n (Γ1) F -> IELGMd n (Γ2) H -> IELGMd  (S n) (Γ3) H
| ielgmdIR Γ F G n: IELGMd n (F::Γ) G -> IELGMd (S n) (Γ) (F ⊃ G)
| ielgmdKI Γ Δ F D n Γ': IELGMd n (Γ) F -> Γ ≡P (D ++ Δ ++ (List.map K Δ)) -> Γ' ≡P (D ++ (List.map K Δ)) -> IELGMd  (S n) Γ' (K F)                                                         
| ielgmdKB Γ F n: IELGMd n Γ (K ⊥) -> IELGMd (S n) Γ F
| ielgmdStep Γ F n: IELGMd n Γ F -> IELGMd (S n) Γ F.


Notation "A |- ( n ) B" := (IELGMd n A B) (at level 3) .
Notation "A ⇒ B" := (IELGM A B) (at level 3) .
Require Export Permutations.


Ltac psolve  :=   
  permutation_solver.


(* Some lemmatae about ===  *)

Section MapPerm.
  Variables (A: Type) (B: Type) .
  Definition injective (f: form -> form) := forall a1 a2, f(a1) = f(a2) -> a1 = a2.
  Lemma map_perm (f: A -> B) l1 l2 : l1 ≡P l2 -> (List.map f l1) ≡P (List.map f l2).
  Proof.
    intro H.
    induction H; firstorder eauto. 
    - rewrite H. reflexivity.
    -   cbn. constructor.  
  Qed.
  
  Lemma map_inj_perm (f: form -> form) l1 l2: injective f -> (map f l1) ≡P (map f l2) -> l1 ≡P l2.
  Proof.
    
    intros.
    apply Permutation_map_inv in H0.
    destruct H0 as (l3 & L1 & L2).
    transitivity l3.
    apply map_injective in L1. rewrite L1. reflexivity.
    apply H. symmetry; auto. 
  Qed.
        
End MapPerm.  

Global Hint Constructors IELGMd : core. 
Global Hint Constructors IELGM : core. 

Lemma ielgmdMultiset: forall n Γ1 F Γ2 , IELGMd n Γ1 F -> Γ1 ≡P Γ2 -> IELGMd n Γ2 F.
Proof.
  intros. revert H0. revert Γ2. 
  induction H; firstorder. 
  - intros. apply ielgmdA. rewrite<- H0. auto. 
  - apply ielgmdBotVar.  rewrite<- H0. auto. 
  - apply ielgmdAL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ).
    auto. transitivity Γ2. symmetry. auto. auto. auto.
  - apply ielgmdOL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ) (Γ2 := Γ2); auto. 
    auto. transitivity Γ3. symmetry. auto. auto.
  - apply ielgmdIL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ) (Γ2 := Γ2); auto.
    auto. transitivity Γ3. symmetry. auto. auto.
  -  apply ielgmdKI with (Δ := Δ) (Γ := Γ) (D := D); try auto.
     transitivity Γ'. symmetry. auto. auto.
Qed.


Lemma ielgmMultiset: forall Γ1 F Γ2 , IELGM Γ1 F -> Γ1 ≡P Γ2 -> IELGM Γ2 F.
Proof.
  intros. revert H0. revert Γ2. 
  induction H; firstorder. 
  - intros. apply ielgmA. rewrite<- H0. auto. 
  - apply ielgmBotVar.  rewrite<- H0. auto. 
  - apply ielgmAL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ).
    auto. transitivity Γ2. symmetry. auto. auto. auto.
  - apply ielgmOL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ) (Γ2 := Γ2); auto. 
    auto. transitivity Γ3. symmetry. auto. auto.
  - apply ielgmIL with (F := F) (G := G) (Γ1 := Γ1) (Γ := Γ) (Γ2 := Γ2); auto.
    auto. transitivity Γ3. symmetry. auto. auto.
  -  apply ielgmKI with (Δ := Δ) (Γ := Γ) (D := D); try auto.
     transitivity Γ'. symmetry. auto. auto.
Qed.

 Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.CRelationClasses.

Instance add_proper_l  : Proper (eq ==> (@Permutation form) ==> eq ==> impl) (IELGMd  ).
Proof. 
  intros n0 n1 neq a b c d e f   H1.  rewrite<- f. rewrite<- neq. apply ielgmdMultiset with a; assumption.
Qed.
Instance add_proper_l' : Proper ((@Permutation _) ==> eq ==> impl) (IELGM  ).
Proof. 
  intros  a b c d e f   H1. 
  rewrite<- f. 
  apply ielgmMultiset with a; assumption.
Qed.

Instance add_proper_lr : Proper (eq ==> (@Permutation _) ==> eq ==> Basics.flip impl) (IELGMd ).
Proof. 
  intros n1 n2 neq a b c d e f   H1.
  rewrite f.
  rewrite neq.
  
  apply ielgmdMultiset with b.
  exact H1.
  symmetry. exact c.
Qed.

Instance add_proper_lr' : Proper ((@Permutation _) ==> eq ==> Basics.flip impl) (IELGM ).
Proof. 
  intros a b c d e f   H1.
  rewrite f.
  
  apply ielgmMultiset with b.
  exact H1.
  symmetry. exact c.
Qed.


Instance add_proper_lt  : Proper (eq ==> (@Permutation _) ==> (@Permutation _)) (@cons form ).
Proof. 
  intros l1 l2 hl1 x y H1. rewrite hl1. rewrite H1. reflexivity.
Qed.

Lemma ielgmdSwap n A B Γ H:
  IELGMd n (A::B::Γ) H <-> IELGMd n (B::A::Γ) H.
Proof.
  assert ((A::B::Γ) ≡P (B::A::Γ)) by psolve. split;
                                                 rewrite H0; tauto.
  
Qed.

(* We can show simpler rules admissible *)
Lemma ielgmdOAL Γ  F G H n: 
  IELGMd n (F::G::Γ) H -> IELGMd (S n) ((F ∧ G)::Γ) H.  
Proof.
  intro.
  apply ielgmdAL with (Γ := Γ) (Γ1 := (F::G::Γ)) (F := F) (G := G).
  reflexivity. reflexivity. exact H0.
Qed.

Lemma ielgmOAL Γ  F G H: 
  IELGM  (F::G::Γ) H -> IELGM ((F ∧ G)::Γ) H.  
Proof.
  intro.
  apply ielgmAL with (Γ := Γ) (Γ1 := (F::G::Γ)) (F := F) (G := G).
  reflexivity. reflexivity. exact H0.
Qed.


Lemma ielgmdOOL Γ  F G H n: 
  IELGMd n (F::Γ) H ->  IELGMd n (G::Γ) H -> IELGMd (S n) ((F ∨ G)::Γ) H.  
Proof.
  intro.
  apply ielgmdOL with (Γ := Γ) (Γ1 := (F::Γ)) (F := F) (G := G).
  
  reflexivity. reflexivity.  reflexivity. exact H0.
Qed.

Lemma ielgmOOL Γ  F G H: 
  IELGM (F::Γ) H ->  IELGM (G::Γ) H -> IELGM ((F ∨ G)::Γ) H.  
Proof.
  intro.
  apply ielgmOL with (Γ := Γ) (Γ1 := (F::Γ)) (F := F) (G := G).
  
  reflexivity. reflexivity.  reflexivity. exact H0.
Qed.

Lemma ielgmdOIL Γ  F G H n: 
   IELGMd n ((F ⊃ G)::Γ) F -> IELGMd n (G::Γ) H -> IELGMd (S n) ((F ⊃ G)::Γ) H.  
Proof.
  intro.
  apply ielgmdIL with (Γ := Γ) (Γ1 := ((F ⊃ G)::Γ))  (F := F) (G := G).
  
  reflexivity. reflexivity.  reflexivity. exact H0.
Qed.
Lemma ielgmOIL Γ  F G H : 
   IELGM ((F ⊃ G)::Γ) F -> IELGM (G::Γ) H -> IELGM ((F ⊃ G)::Γ) H.  
Proof.
  intro.
  apply ielgmIL with (Γ := Γ) (Γ1 := ((F ⊃ G)::Γ))  (F := F) (G := G).
  
  reflexivity. reflexivity.  reflexivity. exact H0.
Qed.

Lemma ielgmdOKI Γ n Δ F:
  IELGMd n (Γ ++ Δ ++ (List.map K Δ)) F ->  IELGMd (S n) (Γ ++ (List.map K Δ)) (K F) . 
Proof. 
  intro.
  apply ielgmdKI with (D := Γ) (Δ := Δ) (Γ := Γ ++ Δ ++ (map K Δ)); firstorder eauto; try reflexivity. 
Qed.
Lemma ielgmOKI Γ Δ F:
  IELGM (Γ ++ Δ ++ (List.map K Δ)) F ->  IELGM (Γ ++ (List.map K Δ)) (K F) . 
Proof. 
  intro.
  apply ielgmKI with (D := Γ) (Δ := Δ) (Γ := Γ ++ Δ ++ (map K Δ)); firstorder eauto; try reflexivity. 
Qed.
Ltac mauto' id  :=
  match goal with
  | [ H: (IELGMd ?n  ?Γ ?F)   |- _  ] => (match H with
        | id => apply ielgmdMultiset with Γ end) |
                                       
                                          [ H: (IELGM  ?Γ ?F)   |- _  ] => match H with
        | id => apply ielgmMultiset with Γ
      end 
  end.

Ltac mauto H  :=
  mauto' H; try psolve; try auto . 

  (* Equivalence between IELGMD |- (n) F and |- F *)
Lemma ielgmdToIelg F Γ n: IELGMd n Γ F -> IELGM Γ F.  
Proof. 
  intro. induction H; firstorder auto.
  - rewrite H1.  apply ielgmOAL. mauto IHIELGMd.
  - rewrite H2. apply ielgmOOL.  mauto IHIELGMd1. mauto IHIELGMd2.
  - rewrite H2.   apply ielgmOIL. mauto IHIELGMd1. mauto IHIELGMd2.
  - rewrite H1. apply ielgmOKI.   mauto IHIELGMd. 
Qed.

Lemma ielgmdLower (n m: nat) Γ F: (Γ |- (n) F) -> n <= m ->  Γ |- (m) F.  
Proof.
  intros H1 K.
  induction K; firstorder eauto. 
Qed. 

Lemma ielgmToIelgmd F Γ: IELGM Γ F -> exists h,  IELGMd h  Γ F.  
Proof. 
  intro. induction H; try firstorder eauto 3.
  + exists (S(Nat.max x0 x)). apply ielgmdAR. apply ielgmdLower with x0; try lia; auto.  apply ielgmdLower with x; try lia; auto.
  + exists (S(Nat.max x0 x)). rewrite H2. apply ielgmdOOL. rewrite<- H0. apply ielgmdLower with x0; try lia; auto.  rewrite<- H1. apply ielgmdLower with x; try lia; auto.
  +  exists (S(Nat.max x0 x)). rewrite H2. apply ielgmdOIL. rewrite<- H0. apply ielgmdLower with x0; try lia; auto.  rewrite<- H1. apply ielgmdLower with x; try lia; auto.
Qed.

Lemma dwWeakening n Γ W F:
   IELGMd n Γ F -> IELGMd n (W::Γ) F.

   intro. 
   revert W.
   induction H; firstorder eauto 3.
   - rewrite H1. apply ielgmdSwap. apply ielgmdOAL.  apply ielgmdMultiset with (W::F::G::Γ). 2: psolve. rewrite<- H0.  apply IHIELGMd.
   -  rewrite H2. apply ielgmdSwap. apply ielgmdOOL. apply ielgmdSwap. rewrite<- H0. apply IHIELGMd1. apply ielgmdSwap. rewrite<- H1. apply IHIELGMd2. 
   -  rewrite H2. apply ielgmdSwap. apply ielgmdOIL.  apply ielgmdSwap. rewrite<- H0.  apply IHIELGMd1. apply ielgmdSwap. rewrite<- H1. apply IHIELGMd2. 
   -   apply ielgmdIR.  apply ielgmdSwap. apply IHIELGMd.
   -  apply ielgmdKI with (Γ := W::Γ) (Δ := Δ) (D := W::D).
      apply IHIELGMd. rewrite H0. psolve.
      rewrite H1. psolve. 
Qed.        

 Ltac inversionBaseCase := intro H; inversion H; firstorder eauto; try congruence; try apply ielgmdA; try apply ielgmdBotVar; try right; firstorder eauto. 

Lemma inversionAnd Γ  A B C n: IELGMd n ((A ∧ B)::Γ) C -> IELGMd n (A::B::Γ) C.
Proof.
  revert C Γ.
  induction n.
  -
    intros C Γ. 
    inversionBaseCase. 
  - intros.
    inversion H.
    +  apply lequiv_cons_destruct in H3.
       destruct H3.
      (* Case #1 F /\ G = A /\ B *)
      destruct H3 as [Γ1' [hl1 hl2]].
      rewrite<- hl1.
      apply ielgmdMultiset with ((F ∧ G)::A::B::Γ1'); try psolve.
      apply ielgmdOAL.
      apply ielgmdMultiset with (A::B::F::G::Γ1'); try psolve.
      apply IHn.
      apply ielgmdMultiset with (F::G::(A ∧ B)::Γ1'); try psolve.
      rewrite hl2.
      rewrite<- H2.
      exact H4.
       
     destruct H3.
      apply ielgmdStep.
            rewrite<- H7.
      inversion H3.
      rewrite<- H2.
      exact H4. 
    + apply ielgmdAR.   apply IHn. exact H1.
      apply IHn. exact H2.
    + apply lequiv_cons_destruct in H4.
      destruct H4.

      * destruct H4 as [Γ1' [hl1 hl2]].
        rewrite<- hl1.
        apply ielgmdMultiset with ((F ∨ G)::A::B::Γ1'); try psolve.
        apply ielgmdOOL.
        apply ielgmdMultiset with (A::B::F::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H2.
        auto.
        apply ielgmdMultiset with (A::B::G::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H3.
        auto.
     * destruct H4.    inversion H4. 
    + apply ielgmdOR1. apply IHn; auto.
    + apply ielgmdOR2. apply IHn. auto.   
    +  apply lequiv_cons_destruct in H4.
      destruct H4.

      * destruct H4 as [Γ1' [hl1 hl2]].
        rewrite<- hl1.
        apply ielgmdMultiset with ((F ⊃  G)::A::B::Γ1'); try psolve.
        apply ielgmdOIL.
         apply ielgmdMultiset with (A::B::(F ⊃  G)::Γ1'); try psolve.
         apply IHn.
         apply ielgmdSwap.
         rewrite hl2.
         rewrite<- H2. auto.
         apply ielgmdMultiset with (A::B::G::Γ1'); try psolve.
                 apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H3.
        auto.
     * destruct H4.    inversion H4. 
    + apply ielgmdIR. apply ielgmdMultiset with (A::B::F::Γ); try psolve.
      apply IHn. apply ielgmdSwap. auto.  
    + apply lequiv_cons_app in H3. 
      destruct H3.
      destruct H3 as (Hin & (B' & HB1 & HB2)). 
        rewrite HB2. apply ielgmdMultiset with ((A::B::B') ++ (map K Δ)) ; try psolve.
        apply ielgmdOKI.
        norm_list.
        apply IHn.
        apply ielgmdMultiset with ((((A ∧ B) :: B') ++ Δ ++ map K Δ)) ; try psolve.
        rewrite<- HB1.
        rewrite<- H2. firstorder eauto.

        destruct H3 as (Hin & (B' & HB1 & HB2)).
        apply in_map_iff in Hin.
        destruct Hin. destruct H3. congruence.
    + apply ielgmdKB.  apply IHn. exact H1. 
    + apply ielgmdStep.  apply IHn. exact H1. 
Qed.
Lemma inversionOR1 Γ  A B C n: IELGMd n ((A ∨ B)::Γ) C -> IELGMd n (A::Γ) C.
Proof.
 revert C Γ.
 induction n. 
 -  intros C Γ. inversionBaseCase.
 -    intros C Γ H.
      inversion H.
      +
       apply lequiv_cons_destruct in H3.
       destruct H3.
      (* Case #1 F /\ G = A /\ B *)
      destruct H3 as [Γ1' [hl1 hl2]].
      rewrite<- hl1. apply ielgmdSwap. apply ielgmdOAL. 
      apply ielgmdMultiset with (A::F::G::Γ1'); try psolve.
      apply IHn.
      apply ielgmdMultiset with (F::G::(A ∨ B)::Γ1'); try psolve.
      rewrite hl2.
      rewrite<- H2.
      exact H4.
       
     destruct H3.
      apply ielgmdStep.
      rewrite<- H7.
      inversion H3.            
    + apply ielgmdAR.   apply IHn. exact H1. apply IHn. exact H2.
    + apply lequiv_cons_destruct in H4.
      destruct H4.
      * destruct H4 as [Γ1' [hl1 hl2]].
        rewrite<- hl1.
        apply ielgmdMultiset with ((F ∨ G)::A::Γ1'); try psolve.
        apply ielgmdOOL.
        apply ielgmdMultiset with (A::F::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H2.
        auto.
        apply ielgmdMultiset with (A::G::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H3.
        auto.
      * destruct H4.
        inversion H4.
        apply ielgmdStep. 
        
            rewrite<- H9.
      rewrite<- H2.
      assumption.
    + apply ielgmdOR1. apply IHn. auto.
    + apply ielgmdOR2. apply IHn. auto.   
    + 
       apply lequiv_cons_destruct in H4.
       destruct H4.
      (* Case #1 F /\ G = A /\ B *)
      destruct H4 as [Γ1' [hl1 hl2]]. rewrite<- hl1.
      apply ielgmdSwap. 
      apply ielgmdOIL.   apply ielgmdSwap. apply IHn. apply ielgmdSwap. rewrite hl2. rewrite<- H2. auto.
      apply ielgmdSwap. apply IHn. apply ielgmdSwap. rewrite hl2. rewrite<- H3. auto.
      * destruct H4. inversion H4. 
    + apply ielgmdIR. apply ielgmdSwap. apply IHn. apply ielgmdSwap.  auto.
    + apply lequiv_cons_app in H3. 
      destruct H3. destruct H3 as (Hin & (B' & HB1 & HB2)). 
        rewrite HB2. apply ielgmdMultiset with ((A::B') ++ (map K Δ)) ; try psolve.
        apply ielgmdOKI.
        norm_list.
        apply IHn.
        apply ielgmdMultiset with ((((A ∨ B) :: B') ++ Δ ++ map K Δ)) ; try psolve.
        rewrite<- HB1.
        rewrite<- H2. firstorder eauto.
        
        destruct H3 as (Hin & (B' & HB1 & HB2)).
        apply in_map_iff in Hin.
        destruct Hin. destruct H3. congruence.
    +   apply ielgmdKB.   apply IHn.  auto.
    +   apply ielgmdStep.  apply IHn. auto.  
Qed. 

Lemma inversionOR2 Γ  A B C n: IELGMd n ((A ∨ B)::Γ) C -> IELGMd n (B::Γ) C.
Proof.
 revert C Γ.
 induction n. 
 -  intros C Γ. inversionBaseCase.
 -    intros C Γ H.
      inversion H.
      +
       apply lequiv_cons_destruct in H3.
       destruct H3.
      (* Case #1 F /\ G = A /\ B *)
      destruct H3 as [Γ1' [hl1 hl2]].
      rewrite<- hl1. apply ielgmdSwap. apply ielgmdOAL. 
      apply ielgmdMultiset with (B::F::G::Γ1'); try psolve.
      apply IHn.
      apply ielgmdMultiset with (F::G::(A ∨ B)::Γ1'); try psolve.
      rewrite hl2.
      rewrite<- H2.
      exact H4.
       
     destruct H3.
      apply ielgmdStep.
      rewrite<- H7.
      inversion H3.            
    + apply ielgmdAR.   apply IHn. exact H1. apply IHn. exact H2.
    + apply lequiv_cons_destruct in H4.
      destruct H4.
      * destruct H4 as [Γ1' [hl1 hl2]].
        rewrite<- hl1.
        apply ielgmdMultiset with ((F ∨ G)::B::Γ1'); try psolve.
        apply ielgmdOOL.
        apply ielgmdMultiset with (B::F::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H2.
        auto.
        apply ielgmdMultiset with (B::G::Γ1'); try psolve.
        apply IHn.
        apply ielgmdSwap.
        rewrite hl2.
        rewrite<- H3.
        auto.
      * destruct H4.
        inversion H4.
        apply ielgmdStep. 
        
            rewrite<- H9.
      rewrite<- H3.
      assumption.
    + apply ielgmdOR1. apply IHn. auto.
    + apply ielgmdOR2. apply IHn. auto.   
    + 
       apply lequiv_cons_destruct in H4.
       destruct H4.
      (* Case #1 F /\ G = A /\ B *)
      destruct H4 as [Γ1' [hl1 hl2]]. rewrite<- hl1.
      apply ielgmdSwap. 
      apply ielgmdOIL.   apply ielgmdSwap. apply IHn. apply ielgmdSwap. rewrite hl2. rewrite<- H2. auto.
      apply ielgmdSwap. apply IHn. apply ielgmdSwap. rewrite hl2. rewrite<- H3. auto.
      * destruct H4. inversion H4. 
    + apply ielgmdIR. apply ielgmdSwap. apply IHn. apply ielgmdSwap.  auto.
    + apply lequiv_cons_app in H3. 
      destruct H3. destruct H3 as (Hin & (B' & HB1 & HB2)). 
        rewrite HB2. apply ielgmdMultiset with ((B::B') ++ (map K Δ)) ; try psolve.
        apply ielgmdOKI.
        norm_list.
        apply IHn.
        apply ielgmdMultiset with ((((A ∨ B) :: B') ++ Δ ++ map K Δ)) ; try psolve.
        rewrite<- HB1.
        rewrite<- H2. firstorder eauto.
        
        destruct H3 as (Hin & (B' & HB1 & HB2)).
        apply in_map_iff in Hin.
        destruct Hin. destruct H3. congruence.
    +   apply ielgmdKB.   apply IHn.  auto.
    +   apply ielgmdStep.  apply IHn. auto.  
Qed. 


Lemma inversionI Γ  A B C n: IELGMd n ((A ⊃ B)::Γ) C -> IELGMd n (B::Γ) C.
Proof.
 revert C Γ.
 induction n. 
 -  intros C Γ. inversionBaseCase.
 -    intros C Γ H.
      inversion H; try firstorder auto. 
      +
       apply lequiv_cons_destruct in H3.
       destruct H3.
      (* Case #1 F /\ G = A /\ B *)
      destruct H3 as [Γ1' [hl1 hl2]].
      rewrite<- hl1. apply ielgmdSwap. apply ielgmdOAL. 
      apply ielgmdMultiset with (B::F::G::Γ1'). 
      apply IHn; mauto H4. clear IHn H. 
     psolve. 
                                                                  
      destruct H3. inversion H3.
    + 
       apply lequiv_cons_destruct in H4.
       destruct H4.
      (* Case #1 F /\ G = A /\ B *)
      destruct H4 as [Γ1' [hl1 hl2]]. rewrite<- hl1.
      apply ielgmdSwap. 
      apply ielgmdOOL.   apply ielgmdSwap. apply IHn. apply ielgmdSwap. mauto H5.   
      apply ielgmdSwap. apply IHn. mauto H6.  
       * destruct H4. inversion H4.
    + apply lequiv_cons_destruct in H4.
      destruct H4.
      * destruct H4 as [Γ1' [hl1 hl2]].
        rewrite<- hl1. apply ielgmdSwap. apply ielgmdOIL. apply ielgmdSwap.
        apply IHn. mauto H5.  
         apply ielgmdSwap. 
         apply IHn. mauto H6.
      *    destruct H4. inversion H4.  apply ielgmdStep. mauto H6. 
    + apply ielgmdIR.   apply ielgmdSwap.      apply IHn.
      mauto H1.            
    + apply lequiv_cons_app in H3. 
      destruct H3. destruct H3 as (Hin & (B' & HB1 & HB2)). 
        rewrite HB2. apply ielgmdMultiset with ((B::B') ++ (map K Δ)) ; try psolve.
        apply ielgmdOKI.
        norm_list.
        apply IHn.
        mauto H1. 
        destruct H3 as (Hin & (B' & HB1 & HB2)).
        apply in_map_iff in Hin.
        destruct Hin. destruct H3. congruence.
Qed.

Lemma contraction Γ F H n: IELGMd n (F::F::Γ) H -> IELGMd n (F::Γ) H.
Proof.
  revert F H Γ.
  induction n.
  - intros. inversion H0.
    + enough (Var A = F \/ (Var A) el Γ).
      destruct H2; apply ielgmdA.
      *    left. symmetry. assumption.
      *   right.    assumption.
      *     repeat (destruct H1;  firstorder eauto).  
    + enough (⊥ = F \/ ⊥ el Γ).
      destruct H2; apply ielgmdBotVar. 
      *    left. symmetry. assumption.
      *   right.    assumption.
      *     repeat (destruct H1;  firstorder eauto).          
  -  intros.
     inversion H0.
     + apply lequiv_doublecons_destruct in H4.
       destruct H4.
       * destruct H4. 
         rewrite H4.
         apply ielgmdOAL. subst F. rewrite<- H8 in  H3. rewrite H3 in H5. 
         apply IHn. apply ielgmdMultiset with (G::F0::F0::Γ); try psolve. apply IHn. apply ielgmdMultiset with (F0::G::F0::G::Γ); try psolve.
         apply inversionAnd. mauto H5.  
       * destruct H4. destruct H8 as (C' & HC'1 & HC'2).
         rewrite HC'1. apply ielgmdSwap.  apply ielgmdOAL. apply ielgmdMultiset with (F::F0::G:: C'). apply IHn. mauto H5.  psolve.
     +  apply ielgmdAR;       apply IHn; auto. 
     +  apply lequiv_doublecons_destruct in H5. destruct H5.
        * destruct H5. rewrite H5. apply ielgmdOOL. rewrite<- H10 in  H3. rewrite H3 in H6. rewrite H5 in H6.   apply ielgmdSwap in H6. apply inversionOR1 in H6. apply IHn in H6.   auto.
           rewrite<- H10 in  H4. rewrite H4 in H7. rewrite H5 in H7.   apply ielgmdSwap in H7. apply inversionOR2 in H7. apply IHn in H7. auto.
        *   destruct H5. destruct H10 as (C' & HC'1 & HC'2).   rewrite HC'1. apply ielgmdSwap.  apply ielgmdOOL. apply ielgmdMultiset with (F::F0:: C'). apply IHn. apply ielgmdMultiset with (F0::F::F::C').  rewrite HC'2.
            rewrite<- H3. auto. psolve. psolve.
            rewrite H4 in H7. rewrite<- HC'2 in H7. apply ielgmdSwap. apply IHn.

           mauto H7. 
     + apply ielgmdOR1. apply IHn in H2. auto.  
     +  apply ielgmdOR2.  apply IHn in H2. auto.
     +   apply lequiv_doublecons_destruct in H5. destruct H5.
         *  destruct H5. rewrite H5. apply ielgmdOIL.
            rewrite<- H5. apply IHn. rewrite H10. rewrite H5. rewrite<- H3. auto.
            rewrite H4 in H7. rewrite<- H10 in H7.  rewrite H5 in H7.
            apply ielgmdSwap in H7. 
            apply inversionI in H7.
            apply IHn. auto. 
         *     destruct H5. destruct H10. destruct H10.
               rewrite H10. apply ielgmdSwap. apply ielgmdOIL.
               apply ielgmdSwap. apply IHn. apply ielgmdMultiset with ((F0 ⊃ G)::F::F::x). rewrite H11. rewrite<- H3. auto.  psolve.
               apply ielgmdSwap. apply IHn.  apply ielgmdMultiset with (G::F::F::x) ; try psolve.
               rewrite H11. rewrite<- H4. auto. 
     +  apply ielgmdIR. apply ielgmdSwap.  apply IHn. mauto H2.  
     + apply lequiv_cons_app in H4.  destruct H4.  destruct H4.
       destruct H7. destruct H7.  rewrite H8. apply ielgmdOKI. apply ielgmdMultiset with ((x ++ (map K Δ)) ++ Δ).  rewrite<- H8. norm_list. apply IHn. apply ielgmdMultiset with ((F::F::Γ) ++ Δ).  mauto H2.  
        all: try psolve. 
       *  destruct H4.  destruct H7.  destruct H7. rewrite H8.
          (specialize (map_perm_cons H7)). intro. destruct H9.
          rewrite<- H9.
          apply lequiv_cons_app in H8.
          -- destruct H8.  destruct H8. destruct H10 as (B' & Hb1 & Hb2).
             rewrite Hb1.  apply ielgmdMultiset with (B' ++ (F:: (map K x0))); try psolve.
             rewrite H9. rewrite<- H7. apply ielgmdOKI. rewrite H7. apply ielgmdMultiset with (F :: (B' ++ Δ ++ x)); try psolve.
             apply IHn. apply ielgmdMultiset with ((F::B') ++ Δ ++ (F::x)); try psolve.  rewrite<- Hb1. rewrite<- H7. rewrite<- H3. auto.

             destruct H8.   destruct H10 as (B' & Hb1 & Hb2).
             
             apply ielgmdOKI. rewrite H9. rewrite Hb1. rewrite<- H9 in Hb1.
             symmetry in Hb1. rewrite<- H9 in H7.
             specialize (map_perm_cons'  H7). intro H10.
             destruct H10 as (Δ' & Htmp & f & Hkf).
             apply map_inj_perm in Htmp.  rewrite<- Hkf in H7. fold map in H7.
             assert (K f :: map K x0 = (map K (f::x0))) as Ht by reflexivity .
             assert (map K Δ ≡P map K (f::x0)).
             simpl map at 2. auto.   
             apply map_inj_perm in H10. 
             assert (exists B'' F', K F' = F /\ (F' :: B'') ≡P x0) . {
               symmetry in Hb1. destruct (map_perm_cons' Hb1).  destruct H11. exists x1. destruct H12. exists x2.
               split. auto. rewrite<- H11 in Hb1. rewrite<- H12 in Hb1.
               apply map_inj_perm with K.  intros a b c; inversion c; auto.  simpl map.  rewrite Hb1.  reflexivity. 
             } rename H10 into H121. 
             destruct H11 as (x0' & f' & Hx0f & Hx0'). 
             rewrite<- Hx0'.
             apply ielgmdMultiset with (f'::(x0'++D++ (F::B'))); try psolve. apply IHn.
             apply ielgmdMultiset with (((f' :: (f' :: x0'))) ++ D ++ F::B'); try psolve. 
             rewrite Hx0'.
             assert (f' = f). { rewrite<- Hx0f in Hkf. inversion Hkf. reflexivity. }

                              apply ielgmdMultiset with (F:: ((f'::x0)++D++B')). apply IHn.   apply ielgmdMultiset with (D ++  Δ ++ (F::F::B')).
                              mauto H2. rewrite H3.  

                              rewrite Hb1. rewrite<- Hx0f. rewrite H10.
                              psolve.     
                              rewrite<- Htmp.
                              rewrite Hb1.
                              transitivity ((f'::Δ') ++ (D) ++ F::(F::B')).
                              rewrite Hb1. rewrite<- Hx0f. rewrite H10.
                              
                              psolve.
                              psolve.
                              psolve. 
            all: intros a b c; inversion c; auto; intros a b c;  inversion c;    reflexivity.
     +  apply ielgmdKB.   apply IHn in H2. exact H2.
     +  apply ielgmdStep.   apply IHn in H2. exact H2.
Qed.

Require Import Coq.Arith.Wf_nat.

(**
   We make contraction usable by providing a version using list inclusion. 
   We first proof that if A => ϕ then undup A => ϕ where undup A (from the 
   Base library) is the list with all duplicates removed.
 **)
  Instance feqd: eq_dec form.
  Proof. intros x y.  apply form_eq_dec. Qed.
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
  
Lemma undup_proves_llength:
  forall n (l : env) ϕ m, length l = n -> l |- (m)  ϕ -> (undup l) |- (m)  ϕ .
Proof.
  induction n using lt_wf_ind.
  intros l ϕ m Hl D1.
  destruct (dupfree_dec l).
  - rewrite (undup_id d). auto.
  - apply not_dupfree in n0.
    destruct n0 as (a & A1 & A2 & A3 & Hl').
    rewrite Hl' in D1.
    
    assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))).
    psolve.
    rewrite H0 in D1.
    apply contraction in D1.
    
    enough ((undup (a::A1++A2++A3))  |- (m) ϕ). rewrite Hl'.
    assert ((undup (a :: a :: A1 ++ A2 ++ A3)) = (undup (a :: A1 ++ A2 ++ A3))) by apply  undup_double.
    assert ((undup (A1 ++ a :: A2 ++ a :: A3)) ≡P (undup (a::a::A1++A2++A3))).
    apply undup_perm. psolve.
    rewrite H3.
    rewrite H2.
    auto.
    apply H with (|a::A1++A2++A3|). rewrite<- Hl. rewrite Hl'. repeat (rewrite app_length; simpl). 
lia. reflexivity.  auto. 
Qed.

Lemma undup_proves_llength2:
  forall n (l : env) ϕ m, length l = n ->  (undup l) |- (m)  ϕ -> l |- (m)  ϕ  .
Proof.
  induction n using lt_wf_ind.
  intros l ϕ m Hl D1.
  destruct (dupfree_dec l).
  - rewrite<- (undup_id d). auto.
  - apply not_dupfree in n0.
    destruct n0 as (a & A1 & A2 & A3 & Hl').
    rewrite Hl' in D1.
    
    assert ((A1++(a :: A2) ++ (a::A3)) ≡P (a::(a::(A1++A2++A3)))).
    psolve.
    rewrite Hl',  H0. apply dwWeakening.
    apply H with (|a::A1++A2++A3|). 
   rewrite<- Hl. rewrite Hl'. repeat (rewrite app_length; simpl). 
   lia. reflexivity.   apply ielgmdMultiset  with (undup (A1 ++ a :: A2 ++ a :: A3)). auto.  transitivity (undup (a::a::A1++A2++A3)).  
   apply undup_perm.  psolve.
   rewrite undup_double.  reflexivity.
Qed.

Lemma undup_prove l n ϕ:  l |- (n)  ϕ <-> (undup l)  |- (n)  ϕ.
Proof.
  split.
  apply undup_proves_llength with (|l|). reflexivity.
  apply undup_proves_llength2 with (|l|). reflexivity.
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

Lemma ielgmdAppWeakening n Γ1 Γ2 F: IELGMd n Γ1 F -> IELGMd n (Γ1++Γ2) F.
Proof.
  intro.
  induction Γ2.
  -  rewrite app_nil_r. auto.
  -  apply ielgmdMultiset with (a::(Γ1++Γ2)); try psolve.
     apply dwWeakening. auto.
Qed.      
Lemma ielgmdWeakening n Γ F:
  IELGMd n Γ F -> forall Γ', incl Γ  Γ' -> IELGMd n Γ' F. 

Proof.
  intros.
  rewrite undup_incl in H0.
  apply undup_prove.  apply undup_prove in H. 
  apply undupIncl in H0.
  destruct H0. rewrite H0.
  apply ielgmdAppWeakening. auto.
  apply dupfree_undup.  apply dupfree_undup.
Qed.

Lemma ielgmWeakening  Γ F: IELGM Γ F -> forall Γ', incl Γ Γ' -> IELGM Γ' F. 
Proof.
  intros.
  apply ielgmToIelgmd in H.
  destruct H.
  apply ielgmdToIelg with x .
  apply ielgmdWeakening with Γ;
  auto. 
Qed. 


Lemma contractionDepth A B ϕ n: A === B -> (A |- (n)  ϕ <-> B |- (n)  ϕ).
Proof.
  intro H.
    assert ((undup A) ≡P (undup B)). { apply undup_equi_is_perm. 1-2: apply dupfree_undup. repeat rewrite undup_id_equi.  exact H. }
  split.
  intro.
  apply undup_prove in H1. rewrite H0 in H1.
  apply undup_prove. auto.
intro.
  apply undup_prove in H1. rewrite<- H0 in H1.
  apply undup_prove. auto.
Qed.

Lemma contractionMS A B ϕ: A === B -> A ⇒  ϕ <-> B ⇒ ϕ.
Proof.
  intro.
  split; intro H0;
   apply ielgmToIelgmd in H0; destruct H0 as [h Hh];
    apply (contractionDepth ϕ h H) in Hh;
    apply ielgmdToIelg with h;  auto.
Qed.   
(** 
    Let's prove cut elimination
 **)

Fixpoint size (f: form) : nat :=
  match f  with
  | K x => S (size x)
  | Imp s t => S(size s + size t)
  | And s t => S(size s + size t)
  | Or s t => S(size s + size t)
  | Bot => 0
  | Var x => 0
  end.


Require Import Lia.


Lemma le_wf_ind (P: nat -> nat -> Prop) (Hrec: forall n m, (forall p q, p < n -> P p q) -> (forall q, q < m -> P n q) -> P n m) : forall n m, P n m.
Proof.
  induction n using lt_wf_ind.
  - induction m using lt_wf_ind.
    + apply Hrec.
      intros p q H1. apply H. auto.
      
      intros q H1.  apply H0. 
      exact H1.
Qed.


Lemma splitConsR  Γ1 Γ2 A F:
  IELGM (Γ1 ++ (A::Γ2)) F <-> IELGM (A :: (Γ1 ++ Γ2)) F. 
Proof.
  assert ((Γ1++A::Γ2) ≡P (A::Γ1 ++ Γ2)) by psolve. 
  split; rewrite H; auto. 
Qed.


Notation "'K[' Δ ']'" := (List.map K Δ).

Lemma cutElimination':
  forall  m n n1 n2 Γ1 Γ2 F Δ (P1: IELGMd n1 Γ1 F ) (P2: IELGMd n2 (F::Γ2) Δ) ,  n1 + n2 = n -> (size F) = m ->  IELGM (Γ1++Γ2) Δ.
Proof.
  intros n m. 
induction n, m   using le_wf_ind.   
  intros n1 n2 Γ1 Γ2 F Δ P1 P2 Hn1 Hf .
  inversion P1.
  -  apply ielgmWeakening with (Γ := F::Γ2).
     apply ielgmdToIelg in P2. 
     apply P2.
     apply incl_cons. apply in_app_iff. rewrite<- H4.   tauto. apply incl_appr. apply incl_refl. 
  -   apply ielgmWeakening with (Γ1).

      apply ielgmBotVar. auto.
      auto. 
  -
rename F0 into A.
            rename G into B.
            rewrite H3. assert ((((A ∧ B) :: Γ) ++ Γ2) ≡P ((A ∧ B) :: (Γ ++ Γ2))) as Htemp by psolve.
            rewrite Htemp. clear Htemp. apply ielgmOAL.
            assert ((A::B::(Γ ++ Γ2)) ≡P ((A::B::Γ) ++ Γ2)) as Htemp by psolve.
              
            rewrite Htemp. clear Htemp.  
            apply H0 with (F := F) (n1 := n) (n2 := n2)   (q := n+n2); try lia .
            rewrite<- H2.  assumption. 
            assumption. 
  -   rewrite<- H5 in P2.
      apply inversionAnd in P2.
      assert (IELGM (Γ1 ++ (G::Γ2)) Δ).
      apply H with (p := size F0) (q := n+n2) (n1 := n) (n2 := n2) (F := F0); try lia; try auto.
      rewrite<- Hf. rewrite<- H5. simpl. lia.
      apply ielgmToIelgmd in H6.
      destruct H6 as [h D1].
      assert (IELGM (Γ1 ++ (Γ1 ++ Γ2)) Δ). 
      apply H with (p := size G) (q := n+ h) (n1 := n) (n2 := h) (F := G); try lia; try auto.
      rewrite<- Hf. rewrite<- H5. simpl. lia.
      assert ( (G :: Γ1 ++ Γ2) ≡P (Γ1 ++ G :: Γ2)) by psolve.
      rewrite H6. assumption.
      apply contractionMS with (A := Γ1 ++ Γ1 ++ Γ2).
      auto.  auto. 
  - rewrite H4.
          assert ((((F0 ∨ G) :: Γ) ++ Γ2) ≡P ((F0 ∨ G) :: (Γ ++ Γ2))) by psolve.
          rewrite H10.
          apply ielgmOOL.
          assert ((F0 :: Γ ++ Γ2) ≡P ((F0 :: Γ) ++ Γ2)) by psolve.
          rewrite H11. 
          apply H0 with  (q := n+n2) (n1 := n) (n2 := n2) (F := F); try lia.
          rewrite<- H2. auto.
          auto.

           assert ((G :: Γ ++ Γ2) ≡P ((G :: Γ) ++ Γ2)) by psolve.
          rewrite H11. 
          apply H0 with  (q := n+n2) (n1 := n) (n2 := n2) (F := F); try lia.
          rewrite<- H3. auto.
          auto.
  -   rewrite<- H4 in P2. apply inversionOR1 in P2.
      apply H with (p := size F0) (q := n+n2) (n1 := n) (n2 := n2) (F := F0); try lia.
      rewrite<- Hf. rewrite<- H4. simpl. lia.
      assumption. assumption.
  -   rewrite<- H4 in P2. apply inversionOR2 in P2.
      apply H with (p := size F0) (q := n+n2) (n1 := n) (n2 := n2) (F := F0); try lia.
      rewrite<- Hf. rewrite<- H4. simpl. lia.
      assumption. assumption.
  -   rewrite H4.
      assert ((((F0 ⊃ G) :: Γ) ++ Γ2) ≡P ((F0 ⊃ G) :: (Γ ++ Γ2))) by psolve.
      rewrite H10.
      apply ielgmOIL.
      rewrite<- H10.
            rewrite<- H2.

      apply ielgmWeakening with Γ0.
      apply ielgmdToIelg with n.
      auto. 
      apply incl_appl. apply  incl_refl.
      assert ((G:: (Γ ++ Γ2)) ≡P ((G:: Γ)++(Γ2))) by psolve.
      rewrite H11. 
      apply H0 with (F := F) (n1 := n) (n2 := n2)   (q := n+n2); try lia .
      rewrite<- H3. auto.
      exact P2. 
  - 

    inversion P2.
    + destruct H5.
      * rewrite<- H5.
        apply ielgmWeakening with (Γ := Γ1).
        apply ielgmdToIelg with n1 .  auto.
        apply incl_appl. apply incl_refl. 
      * apply ielgmWeakening with (Γ := Γ2).
     apply ielgmA.  auto. 
     apply incl_appr. apply incl_refl.
     
      + destruct H5.
        * congruence.
        * apply ielgmWeakening with Γ2; auto.  
      +  apply lequiv_cons_destruct' in H7.
         destruct H7.
         destruct H7 as (Γ2' & HG2 & HG3 & HG4).
         rewrite<- HG2.
         apply splitConsR. 
         apply ielgmOAL.
         assert ((F1 :: G0 :: Γ1 ++ Γ2') ≡P (Γ1 ++ (F1 :: G0 :: Γ2'))) by psolve. 
         rewrite H7.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
         assert (((F :: F1 :: G0 :: Γ2') ≡P ((F1 :: G0 :: F :: Γ2')))) by psolve. 
         rewrite H12.
         rewrite HG3.
         rewrite<- H6.
         auto.
         destruct H7.
         congruence.
      +  apply ielgmAR.
         * apply H0 with (F := F) (q := n1+ n0) (n1 := n1) (n2 := n0); try lia;
             firstorder.
         * apply H0 with (F := F) (q := n1+ n0) (n1 := n1) (n2 := n0); try lia;
           firstorder.  
      + apply lequiv_cons_destruct' in H8.
        destruct H8.
        destruct H8 as (Γ2' & HG2 & Hg2' & Hg3').
        rewrite<- HG2.
        assert ((Γ1 ++ (F1 ∨ G0) :: Γ2') ≡P ((F1 ∨ G0)::(Γ1 ++ Γ2'))) as Htemp by psolve.
        rewrite Htemp. clear Htemp.
        
        apply ielgmOOL.
        assert ((F1 :: Γ1 ++ Γ2') ≡P ((Γ1)++(F1::Γ2'))) as Htemp by psolve.
        rewrite Htemp. clear Htemp. 
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdSwap.  rewrite Hg2'. rewrite<- H6. assumption.

       assert ((G0 :: Γ1 ++ Γ2') ≡P ((Γ1)++(G0::Γ2'))) as Htemp by psolve.
       rewrite Htemp. clear Htemp. 
       apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
       apply ielgmdSwap.  rewrite Hg2'. rewrite<- H7. assumption.

       destruct H8. congruence. 
      + apply ielgmOR1.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder. 
      + apply ielgmOR2.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
      + apply lequiv_cons_destruct' in H8.
        destruct H8.
        * destruct H8 as (Γ2' & GH1 & GH2 & GH3).
          rewrite<- GH1.
          assert (  (Γ1 ++ (F1 ⊃ G0) :: Γ2') ≡P  ((F1 ⊃ G0)::(Γ1 ++ Γ2'))) as Htemp by psolve. 
          rewrite Htemp. clear Htemp. 
          apply ielgmOIL.
          assert (((F1 ⊃ G0) :: Γ1 ++ Γ2') ≡P (Γ1 ++ ((F1 ⊃ G0) :: Γ2'))) as Htemp by psolve.
          rewrite Htemp. clear Htemp.
          apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
          apply ielgmdSwap. rewrite GH2. rewrite<- H6. assumption.
          assert (((G0) :: Γ1 ++ Γ2') ≡P (Γ1 ++ ((G0) :: Γ2'))) as Htemp by psolve.
          rewrite Htemp. clear Htemp.
          apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
          apply ielgmdSwap.
          rewrite GH2.
          rewrite<- H7.
          auto.
        *   destruct H8 as (Hf1 & Hf2). assert ((F0 ⊃ G) = (F1 ⊃ G0)). transitivity F; auto.
            inversion H8.
            subst F1. subst G0.
            rename F0 into A.
            rename G into B.
            clear H8.
            assert (IELGM (Γ1 ++ Γ2) A).
            apply H0 with (F := F) (n1 := n1) (n2 := n0) (q := n1 + n0); try lia.
            exact P1.
            rewrite Hf1. rewrite<- Hf2. rewrite<- H6. auto.
            assert (IELGM (A :: (Γ1 ++ Γ2)) Δ).
            apply ielgmMultiset with ((A::Γ1) ++ Γ2). 2: psolve.
            apply H with (F := B) (p := size B) (n1 := n) (n2 := n0) (q := n + n0); try lia.
            rewrite<- Hf. rewrite<- H4. simpl size; lia. assumption. rewrite<- Hf2.  rewrite<- H7. auto.
            
            assert (IELGM ((Γ1 ++ Γ2) ++ (Γ1 ++ Γ2)) Δ).
            apply ielgmToIelgmd in H8.
            apply ielgmToIelgmd in H14.
            destruct H8. destruct H14.
            apply H with (F := A) (p := size A) (n1 := x) (n2 := x0) (q := x + x0) .
            rewrite<- Hf; rewrite Hf1; simpl; lia. 
            auto. 
            auto. 
            reflexivity.
            reflexivity.
            apply contractionMS with ((Γ1 ++ Γ2) ++ Γ1 ++ Γ2);
            auto.
            
      + apply ielgmIR.
        assert ((F1 :: Γ1 ++ Γ2) ≡P ((Γ1)++(F1::Γ2))) by psolve.
        rewrite H9. 
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdSwap.  auto.
        
      +
        apply lequiv_cons_app in H7. 
        destruct H7 as [(H' & D' & H'' & H''') |  (D' & H' & H'')]. 
        *  rewrite H'''. 
        apply ielgmKI with (Δ :=  Δ0) (D := Γ1 ++ D') (Γ :=Γ1 ++ D' ++ map K Δ0 ++ Δ0 ).
        apply ielgmMultiset with ((Γ1) ++ (D' ++ map K Δ0 ++ Δ0)). 2: psolve.
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdMultiset with ((F:: D')++Δ0 ++ (map K Δ0) ). 2: psolve.
        rewrite<- H''. rewrite<- H6. 
        assumption.
        psolve.
        psolve.
        *
          apply in_map_iff in D'.
          destruct D'. destruct H7. 
          congruence. 
      + apply ielgmKB.
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder. 
      + apply H0 with (F := F) (n1 := n1) (n2 := n0)   (q := n1+n0); try lia .
       auto.
       auto.
         
 -   inversion P2.
     + destruct H7.
       rewrite<- H7.
        apply ielgmWeakening with (Γ := Γ1).
        apply ielgmdToIelg with n1 .  auto.
        apply incl_appl. apply incl_refl. 
      * apply ielgmWeakening with (Γ := Γ2).
     apply ielgmA.  auto. 
     apply incl_appr. apply incl_refl.
       
      + destruct H7.
        * congruence.
        * apply ielgmWeakening with Γ2; auto.  
      +  apply lequiv_cons_destruct' in H9.
         destruct H9.
         destruct H9 as (Γ2' & HG2 & HG3 & HG4).
         rewrite<- HG2.
         apply splitConsR. 
         apply ielgmOAL.
         assert ((F1 :: G :: Γ1 ++ Γ2') ≡P (Γ1 ++ (F1 :: G :: Γ2'))) by psolve. 
         rewrite H9.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
         assert (((F :: F1 :: G :: Γ2') ≡P ((F1 :: G :: F :: Γ2')))) by psolve. 
         rewrite H14.
         rewrite HG3.
         rewrite<- H8.
         auto.
         destruct H9.
         congruence.
      +  apply ielgmAR.
         * apply H0 with (F := F) (q := n1+ n0) (n1 := n1) (n2 := n0); try lia;
             firstorder.
         *   apply H0 with (F := F) (q := n1+ n0) (n1 := n1) (n2 := n0); try lia;
             firstorder.
      + apply lequiv_cons_destruct' in H10.
        destruct H10.
        destruct H10 as (Γ2' & HG2 & Hg2' & Hg3').
        rewrite<- HG2.
        assert ((Γ1 ++ (F1 ∨ G) :: Γ2') ≡P ((F1 ∨ G)::(Γ1 ++ Γ2'))) as Htemp by psolve.
        rewrite Htemp. clear Htemp.
        
        apply ielgmOOL.
        assert ((F1 :: Γ1 ++ Γ2') ≡P ((Γ1)++(F1::Γ2'))) as Htemp by psolve.
        rewrite Htemp. clear Htemp. 
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdSwap.  rewrite Hg2'. rewrite<- H8. assumption.

       assert ((G :: Γ1 ++ Γ2') ≡P ((Γ1)++(G::Γ2'))) as Htemp by psolve.
       rewrite Htemp. clear Htemp. 
       apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
       apply ielgmdSwap.  rewrite Hg2'. rewrite<- H9. assumption.

       destruct H10. congruence. 
      + apply ielgmOR1.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder. 
      + apply ielgmOR2.
         apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
      + apply lequiv_cons_destruct' in H10.
        destruct H10.
        * destruct H10 as (Γ2' & GH1 & GH2 & GH3).
          rewrite<- GH1.
          assert (  (Γ1 ++ (F1 ⊃ G) :: Γ2') ≡P  ((F1 ⊃ G)::(Γ1 ++ Γ2'))) as Htemp by psolve. 
          rewrite Htemp. clear Htemp. 
          apply ielgmOIL.
          assert (((F1 ⊃ G) :: Γ1 ++ Γ2') ≡P (Γ1 ++ ((F1 ⊃ G) :: Γ2'))) as Htemp by psolve.
          rewrite Htemp. clear Htemp.
          apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
          apply ielgmdSwap. rewrite GH2. rewrite<- H8. assumption.
          assert (((G) :: Γ1 ++ Γ2') ≡P (Γ1 ++ ((G) :: Γ2'))) as Htemp by psolve.
          rewrite Htemp. clear Htemp.
          apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
          apply ielgmdSwap.
          rewrite GH2.
          rewrite<- H9.
          auto.
        * destruct H10. 
          congruence.
      + apply ielgmIR.
        assert ((F1 :: Γ1 ++ Γ2) ≡P ((Γ1)++(F1::Γ2))) as Htemp by psolve.
        rewrite Htemp. 
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdSwap.  auto. 
      +
        apply lequiv_cons_app in H9. 
        destruct H9 as [(H' & D0' & HG2 & Hg3) |  (H' & Δ2 & HD1 & Hd2)]. 

        rewrite H3. rewrite Hg3. 
        apply ielgmKI with (Γ := (D ++ map K Δ0) ++ D0' ++ map K Δ1++Δ0 ++ Δ1) (Δ := Δ0++Δ1 ) (D := D0' ++ D).
        
        apply ielgmMultiset with ((D ++ Δ0 ++ map K Δ0) ++ (D0' ++ map K Δ1 ++ Δ1)). 2: psolve.
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder.
        apply ielgmdWeakening with (Γ1).
        auto.
        intros x Hx. 
        rewrite H3 in Hx.  apply in_app_iff in Hx; destruct Hx; auto 20.
        apply ielgmdMultiset with (((F :: D0') ++ map K Δ1) ++ Δ1). 2: psolve.
        rewrite<- HG2.
        apply ielgmdMultiset with (D0 ++ Δ1 ++ map K Δ1). 2: psolve.
        rewrite<- H8.
        auto. 
        
        rewrite map_app.
        psolve.
        rewrite map_app.
        psolve.

        *
          assert (exists Δ1', (List.map K Δ1') ≡P Δ2).
          {
            apply map_perm_cons with Δ1  F.  auto. 
           
          }      
          rewrite H3. rewrite Hd2.
          apply ielgmMultiset with ((D ++ D0) ++ K[ Δ0] ++ Δ2). 2: psolve.
          destruct H9 as [Δ1' HΔ1'].  rewrite<- HΔ1'. 
          assert (K[ Δ0] ++ K[ Δ1'] = K[Δ0 ++ Δ1']).
          rewrite<- map_app.  reflexivity. 
          rewrite H9.
          apply ielgmOKI.
          
          rewrite<- H9.
          apply ielgmMultiset with ((D  ++ Δ0 ++ K[ Δ0] ) ++ (D0 ++ Δ1'  ++ (List.map K Δ1'))). 2: psolve.
          assert (IELGM ((D  ++ K[ Δ0]) ++ (F0 :: D0 ++ Δ1' ++ K[ Δ1'])) F1).
          apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0). 
          lia.
          rewrite<- H3. auto.
          assert ((F0::Δ1') ≡P Δ1).
          {
            rewrite<- H6 in HD1.
            rewrite<- HΔ1' in HD1.
            rewrite<- map_cons in HD1.
            apply map_inj_perm in HD1. symmetry. auto.
            

            intros a b V. inversion V. auto.
          }  
          apply ielgmdMultiset with (D0 ++ (F0 :: Δ1') ++ (F:: K[ Δ1'])) ; try psolve.
          rewrite H13. rewrite HΔ1'.  rewrite<- HD1.   rewrite<- H8. auto. reflexivity. auto.
          apply ielgmToIelgmd in H13.
          destruct H13. 
          assert (IELGM ((D ++ Δ0 ++ K[ Δ0]) ++ ((D ++ D0) ++ (Δ0 ++ Δ1') ++ K[ Δ0] ++ K[ Δ1'])) F1). 
          apply H with (F := F0) (p := size F0) (q := (n) + x) (n1 := n) (n2 := x).
          subst m1. subst F. simpl. lia.
          rewrite<- H2.  auto.
          apply ielgmdWeakening with ((D ++ K[ Δ0]) ++ F0 :: D0 ++ Δ1' ++ K[ Δ1']). 
          
          exact H13.
          auto 200. 
          lia. lia.
          apply contractionMS with ((D ++ Δ0 ++ K[ Δ0]) ++ (D ++ D0) ++ (Δ0 ++ Δ1') ++ K[ Δ0] ++ K[ Δ1']).
          auto 200. 
          (* Contraction then done *)
          auto. 
      + apply ielgmKB.
        apply H0 with (F := F) (q := n1 + n0) (n1 := n1) (n2 := n0); try lia; firstorder. 
      + apply H0 with (F := F) (n1 := n1) (n2 := n0)   (q := n1+n0); try lia .
       auto.
       auto.
                            
  -   apply ielgmKB.
      apply ielgmWeakening with (Γ := Γ1).
      apply ielgmdToIelg in H1; auto.
      apply incl_appl. apply incl_refl.
  -    apply H0 with (F := F) (n1 := n) (n2 := n2)   (q := n+n2); try lia .
       auto.
       auto.
Qed.        

Theorem cutElim Γ1 Γ2 F Δ: IELGM Γ1 F -> IELGM (F::Γ2) Δ -> IELGM (Γ1 ++ Γ2) Δ.
Proof.
  intros.
  apply ielgmToIelgmd in H0. apply ielgmToIelgmd in H. destruct H as (h1 & D1). destruct H0 as (h2 & D2).
  apply cutElimination' with (F := F) (m := size F) (n1 := h1) (n2 := h2) (n := h1 + h2); try lia; auto.
Qed.   
