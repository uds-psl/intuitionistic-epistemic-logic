Require Import PslBase.FCI.
Require Import PslBase.Base. 
Require Import forms. 
Require Import Coq.Sorting.Permutation.
Require Import permutationSCforK.
Require Import decidability.
Require Import toolbox.

(** * Case study: The classical modal logic K *)
(** ** Sequent Calculus for K *)
Inductive gk3c: list form -> list form -> Prop :=
| gk3cC A B x:     Var x el A -> Var x el B -> gk3c A B
| gk3cF A B:       Bot el A -> gk3c A B
| gk3cIL A B s t:  Imp s t el A -> gk3c A (s::B) -> gk3c (t::A) B -> gk3c A B
| gk3cIR A B s t:  Imp s t el B -> gk3c (s::A) (t::B) -> gk3c A B
| gk3cAL A B s t:  And s t el A -> gk3c (s::t::A) B -> gk3c A B
| gk3cAR A B s t:  And s t el B -> gk3c A (s::B) -> gk3c A (t::B) -> gk3c A B
| gk3cOL A B s t:  Or s t el A -> gk3c (s::A) B -> gk3c (t::A) B -> gk3c A B
| gk3cOR A B s t:  Or s t el B -> gk3c A (s::t::B) -> gk3c A B
| gk3cKI A B s: (K s) el B -> gk3c (remNotK A) [s] -> gk3c A B 
.

Inductive gk3ch: nat -> list form -> list form -> Prop :=
| gk3chC A B x:     Var x el A -> Var x el B -> gk3ch 0 A B
| gk3chF A B:       Bot el A -> gk3ch 0 A B
| gk3chIL A B s t n:  Imp s t el A -> gk3ch n A (s::B) -> gk3ch n (t::A) B -> gk3ch (S n) A B
| gk3chIR A B s t n:  Imp s t el B -> gk3ch n (s::A) (t::B) -> gk3ch (S n) A B
| gk3chAL A B s t n:  And s t el A -> gk3ch n (s::t::A) B -> gk3ch (S n) A B
| gk3chAR A B s t n:  And s t el B -> gk3ch n A (s::B) -> gk3ch n A (t::B) -> gk3ch (S n) A B
| gk3chOL A B s t n:  Or s t el A -> gk3ch n (s::A) B -> gk3ch  n (t::A) B -> gk3ch (S n) A B
| gk3chOR A B s t n:  Or s t el B -> gk3ch n A (s::t::B) -> gk3ch (S n) A B
| gk3chKI A B s   n:  (K s) el B ->  gk3ch n (remNotK A) [s] -> gk3ch (S n) A B
| gk3chS A B n : gk3ch n A B -> gk3ch (S n) A B 
.


Local Hint Constructors gk3c gk3ch : core.

Lemma gk3h_hmon n m A B : n <= m -> gk3ch n A B -> gk3ch m A B.   
Proof.
  intros. induction H; auto.
Qed.
Local Hint Resolve remNotK_subset : core.

Lemma gk3_height A B: gk3c A B <-> exists n, gk3ch n A B.  
Proof.
  split.
  - intro. induction H; firstorder eauto.
    + exists (S(Nat.max x0 x)). apply gk3chIL with s t;firstorder eauto.
      apply gk3h_hmon with x0; auto; lia. apply gk3h_hmon with x; auto; lia.
    + exists (S(Nat.max x0 x)). apply gk3chAR with s t;firstorder eauto.
      apply gk3h_hmon with x0; auto; lia. apply gk3h_hmon with x; auto; lia.
    + exists (S(Nat.max x0 x)). apply gk3chOL with s t;firstorder eauto.
      apply gk3h_hmon with x0; auto; lia. apply gk3h_hmon with x; auto; lia.  
  - intro. destruct H as [nh H]. induction H; firstorder eauto.    
Qed.   


Corollary gk3chW n A B: 
  gk3ch n A B -> forall A' B', A <<= A' -> B <<= B' -> gk3ch n A' B'.
Proof.  
  intro H. induction H; intros; eauto.
  + apply gk3chIL with s t; auto.
  + apply gk3chIR with s t; auto.
  + apply gk3chAL with s t; auto.     apply IHgk3ch;  auto.
  + apply gk3chAR with s t; auto.
  + apply gk3chOL with s t; auto.
  + apply gk3chOR with s t; auto.    apply IHgk3ch;  auto.    
Qed.

Lemma gk3cW A B: 
  gk3c A B -> forall A' B', A <<= A' -> B <<= B' -> gk3c A' B'.
Proof.  
  intros H % gk3_height A' B' HA' HB'. destruct H as [nh H].  apply gk3_height. exists nh.   eauto using gk3chW.   
Qed. 
Local Hint Resolve gk3chW : core.

(** Inversion results **)

(* This tactic can be invoked on goals of the form Γ (n)=> A if the hypothesis H and weakening prove it *) 
Ltac solveWeakC H' :=
  match goal with
  | [ H: (gk3ch ?n ?A ?B)   |- _  ] => (match H with
                                        | H' => apply gk3chW  with A B;  try (auto || firstorder eauto || eauto) end)
  end.

(** ** Inversion Results for K *)
Lemma inversionIL h s t A B: In s B -> gk3ch h ((s ⊃ t)::A) B -> gk3ch h A (B). 
Proof.
  revert A B.
  induction h.
  - intros. inversion H0; destruct H1;try congruence; eauto.
  - intros.  inversion H0;  eauto 4.
    + destruct H2.
      * inversion H2; subst s0 ; subst t0. eauto.
      *  apply gk3chIL  with s0 t0. auto. apply IHh; auto. apply IHh; auto.  solveWeakC H4.
    + apply gk3chIR with s0 t0. auto. apply IHh.  auto. solveWeakC H3. 
    + destruct H2; try congruence.   eapply gk3chAL. eauto. apply IHh; auto.  solveWeakC H3. 
    + apply gk3chAR with s0 t0.   auto. apply IHh. auto. solveWeakC H3. apply IHh. auto. solveWeakC H4.
    + destruct H2; try congruence.   eapply gk3chOL. eauto. apply IHh; auto.  solveWeakC H3.   apply IHh; auto. solveWeakC H4.
    +  firstorder eauto.  
Qed.

Lemma inversionIL2 h s t A B: In t A -> gk3ch h ((s ⊃ t)::A) B -> gk3ch h A B. 
Proof.
  revert A B.
  induction h.
  - intros. inversion H0; destruct H1;try congruence; eauto.
  - intros.   inversion H0; intuition. all: eauto 3.
    + destruct H2.
      *  inversion H2; subst s0 ; subst t0. apply gk3chS. apply IHh; auto. solveWeakC H4. 
      *  apply gk3chIL  with s0 t0. auto. apply IHh; auto. apply IHh; auto.  solveWeakC H4.
    + apply gk3chIR with s0 t0. auto. apply IHh.  auto. solveWeakC H3. 
    + destruct H2; try congruence.   eapply gk3chAL. eauto. apply IHh; auto.  solveWeakC H3.
    + apply gk3chAR with s0 t0; auto.    
    + destruct H2; try congruence.   eapply gk3chOL. eauto. apply IHh; auto.  solveWeakC H3.   apply IHh; auto. solveWeakC H4. 
Qed.

Lemma inversionAL h s t A B : In s A -> In t A -> gk3ch h ((s ∧ t)::A) B -> gk3ch h (A) B. 
  revert A B.
  induction h.
  - intros. inversion H1; destruct H2;try congruence; eauto.
  - intros.   inversion H1; intuition; eauto 3.
    + destruct H3; try congruence.   eapply gk3chIL. eauto. apply IHh; auto. apply IHh; auto. solveWeakC H5.
      
    +  apply gk3chIR with s0 t0. auto.  apply IHh; auto.  solveWeakC H4.
    +  destruct H3.
       * inversion H3; subst s0 ; subst t0. apply gk3chS. apply IHh; auto. solveWeakC H4.
       * apply gk3chAL with s0 t0.   auto. apply IHh; auto. solveWeakC H4.
    + apply gk3chAR with s0 t0;  auto;  apply IHh; auto.       
    + destruct H3; try congruence. apply gk3chOL with s0 t0; auto; apply IHh; auto.  solveWeakC H4. solveWeakC H5.
Qed.       

Lemma inversionOR h s t A B: s el B -> t el B -> gk3ch h (A) ((s ∨ t)::B) -> gk3ch h (A) B. 
Proof.
  revert A B. induction h.
  - intros. inversion H1.  destruct H3; auto; try congruence.    eauto. eauto. 
  -    intros.   inversion H1; (eauto 3).
       + apply gk3chIL with s0 t0;  auto. apply IHh; auto. solveWeakC H4.
       + destruct H3; try congruence.   apply gk3chIR with s0 t0. auto. apply IHh; auto. solveWeakC H4.
       + destruct H3; try congruence.   apply gk3chAR with s0 t0. auto. all: apply IHh; auto. solveWeakC H4.  solveWeakC H5.
       + apply gk3chOL with s0 t0; auto. 
       + destruct H3.
         *   inversion H3. apply gk3chS. apply IHh; auto.  subst s0 t0.   solveWeakC H4.
         *     apply gk3chOR with s0 t0. auto. apply IHh; auto. solveWeakC H4.
       + destruct H3; try congruence.   apply gk3chKI with s0. auto. auto.
Qed.

Lemma inversionOL1 h s t A B: s el A -> gk3ch h ((s ∨ t)::A) (B) -> gk3ch h (A) B. 
Proof.
  revert A B. induction h.
  - intros. inversion H0.  destruct H1; auto; try congruence. eauto.   destruct H1; auto; try congruence. 
  -    intros.   inversion H0; eauto 3.
       + destruct H2; try congruence. apply gk3chIL with s0 t0; auto; apply IHh. auto. solveWeakC H4.
       +  apply gk3chIR with s0 t0.  auto. apply IHh; auto.  solveWeakC H3.
       +  destruct H2; try congruence. apply gk3chAL with s0 t0; auto; apply IHh. auto. solveWeakC H3.
       +   apply gk3chAR with s0 t0;  auto.  
       +   destruct H2.
           *   inversion H2. apply gk3chS. apply IHh; auto.  subst s0 t0.   solveWeakC H3.
           *     apply gk3chOL with s0 t0. auto. apply IHh; auto. solveWeakC H3. apply IHh. auto. solveWeakC H4.
Qed.                

Lemma inversionOL2 h s t A B: t el A -> gk3ch h ((s ∨ t)::A) (B) -> gk3ch h (A) B. 
Proof.
  revert A B. induction h.
  - intros. inversion H0.  destruct H1; auto; try congruence. eauto.  destruct H1; auto; try congruence. 
  -    intros.   inversion H0; eauto 4.
       + destruct H2; try congruence. apply gk3chIL with s0 t0; auto; apply IHh. auto. solveWeakC H4.
       +  apply gk3chIR with s0 t0.  auto. apply IHh; auto.  solveWeakC H3.
       +  destruct H2; try congruence. apply gk3chAL with s0 t0; auto; apply IHh. auto. solveWeakC H3.
       +   destruct H2.
           *   inversion H2. apply gk3chS. apply IHh; auto.  subst s0 t0.   solveWeakC H4.
           *     apply gk3chOL with s0 t0. auto. apply IHh; auto. solveWeakC H3. apply IHh. auto. solveWeakC H4.
Qed.                
(** ** Cut-Elimination for K *)
Lemma cutElimination: 
  forall  m n n1 n2 Γ Δ B (P1: gk3ch n1 Γ (B::Δ) ) (P2: gk3ch n2 (B::Γ) Δ) ,  n1 + n2 = n -> (size B) = m ->  gk3c (Γ) Δ.
Proof. 
  intros n m. 
  induction n, m using le_wf_ind.
  intros n1 n2 Γ Δ B P1 P2 sb hnm.
  assert (scut: forall Γ Δ S, size S < size B ->  (gk3c Γ (S::Δ)) -> (gk3c (S::Γ) Δ) -> (gk3c Γ Δ)).   
  {
    intros. apply gk3_height in H2. apply gk3_height in H3. destruct H2 as [nh2 H2], H3 as [nh3 H3].   eapply H.  subst m1. eapply H1.  eapply H2.  eapply H3. reflexivity.  lia.
  }

  assert (rcut: forall Γ Δ n1 n2,   (gk3ch n1 Γ (B::Δ)) -> (gk3ch n2 (B::Γ) Δ) ->  n1+n2 < m2 -> (gk3c Γ Δ)).  {
    intros. eapply H0. apply H3. apply H1. apply H2.  reflexivity. subst m1. auto.
  }

  inversion P1.
  - destruct H2.
    + eapply gk3cW. eapply gk3_height.  exists n2. apply P2; firstorder eauto. auto.  subst B.  eauto. auto.
    + eauto.
  -  eauto.
  -  apply gk3cIL with s t; auto.
     + eapply rcut.  solveWeakC H2. solveWeakC P2.  lia.
     +  eapply rcut.  apply H3.  solveWeakC P2.   lia.
  - destruct H1.
    + subst B.
      apply scut with s; simpl;try lia.
      * apply gk3_height. exists n2. apply inversionIL with s t.  auto. solveWeakC P2.  (* InversionIL1 *) 
      * apply scut with t. simpl; lia.
        -- apply rcut with n n2. solveWeakC H2.  solveWeakC P2. lia. 
        --  apply gk3_height. exists n2. apply inversionIL2 with s t.   auto. solveWeakC P2.    (* InversionIL2 *)
    + apply gk3cIR with s t.   auto.
      apply rcut with n n2. solveWeakC H2. solveWeakC P2.  lia.    
  - apply gk3cAL with s t. auto. eapply rcut. apply H2.  solveWeakC P2.  lia.
  - destruct H1.
    + eapply scut with (S := t). subst B; simpl; lia.
      eapply rcut. solveWeakC H3. solveWeakC P2. lia. 
      eapply scut with (S := s). subst B; simpl; lia.
      eapply rcut. solveWeakC H2. solveWeakC P2. lia.
      eapply gk3_height. exists n2. apply inversionAL with s t; auto.  rewrite<- H1.  solveWeakC P2. 
    + apply gk3cAR with s t.  auto. apply rcut with n n2. solveWeakC  H2.  solveWeakC P2. lia.
      apply rcut with n n2.  solveWeakC H3. solveWeakC P2. lia.
  - apply gk3cOL with s t. auto.
    eapply rcut. apply H2. solveWeakC P2. lia.  
    eapply rcut. apply H3. solveWeakC P2. lia. 
  - destruct H1.
    + subst B.   eapply scut with t. simpl size; lia. apply scut with s. simpl size; lia.  apply gk3_height. exists n.   apply inversionOR with s t; auto. solveWeakC H2.
      apply gk3_height. exists n2. apply inversionOL1 with s t; auto. solveWeakC P2.  apply gk3_height. exists n2.  apply inversionOL2 with s t. auto. solveWeakC P2. 
    + apply gk3cOR with s t. auto. apply rcut with n n2. solveWeakC H2. solveWeakC P2. lia. 
  - inversion P2.
    + destruct H6.    destruct H1; subst B; try congruence. apply gk3cKI with s.  auto.  apply gk3_height. eauto.
      eauto.
    +  destruct H6.    destruct H1; subst B; try congruence. apply gk3cKI with s.  auto.  apply gk3_height. eauto.
       eauto.
    + destruct H1.
      *  destruct H6; try congruence. apply gk3cIL with s0 t; auto. apply rcut with n1 n0.  solveWeakC P1. solveWeakC H7.  lia. apply rcut with n1 n0.  solveWeakC P1. solveWeakC H8. lia. 
      *  eapply gk3cKI. apply H1. apply gk3_height. eauto.
    +  apply gk3cIR with s0 t. auto.  eapply rcut with n1 n0. solveWeakC P1. solveWeakC H7. lia.
    + destruct H1.
      *  destruct H6; try congruence. apply gk3cAL with s0 t. auto. apply rcut with n1 n0. solveWeakC P1. solveWeakC H7. lia. 
      *  eapply gk3cKI. apply H1. apply gk3_height. eauto.  
    + apply gk3cAR with s0 t. auto. eapply rcut with n1 n0. solveWeakC P1. solveWeakC H7. lia. eapply rcut with n1 n0. solveWeakC P1. solveWeakC H8. lia.
    + destruct H1.    
      *  destruct H6; try congruence. apply gk3cOL with s0 t; auto. apply rcut with n1 n0.  solveWeakC P1. solveWeakC H7.  lia. apply rcut with n1 n0.  solveWeakC P1. solveWeakC H8. lia. 
      *  eapply gk3cKI. apply H1. apply gk3_height. eauto.

    + apply gk3cOR with s0 t. auto. eapply rcut with n1 n0. solveWeakC P1. solveWeakC H7. lia.
    +
      destruct H1.
      *  apply gk3cKI with s0. auto. subst B.  simpl remNotK in H7. apply scut with s.  simpl; lia. apply gk3cW with (remNotK Γ) [s]; eauto. all:  apply gk3_height; eauto.
      * eapply gk3cKI. apply H1. apply gk3_height. eauto.
    +  eapply rcut. apply P1. eauto.        lia.     
  - eapply rcut. apply H1. eauto.        lia. 
Qed.      

Lemma pin A B: A ≡P B -> (forall x: form,In x A <-> In x  B).
Proof.
  intro. firstorder eauto. rewrite<- H. auto.
  rewrite H. auto.
Qed.

Lemma gk3cA A B s: s el A -> s el B -> gk3c A B.
Proof.
  revert A B. induction s as [x|s IHs t IHt|s IHs t IHt|s IHs t IHt| | ];
                intros A B E F.
  - apply gk3cKI with x.  auto. apply IHx. apply remNotK_in_iff. auto.  auto. 
  - apply (gk3cIL E); apply gk3cIR with (s:=s) (t:=t); auto.
  - apply (gk3cAL E); apply gk3cAR with (s:=s) (t:=t); auto.
  - apply (gk3cOL E); apply gk3cOR with (s:=s) (t:=t); auto.
  - eauto.
  - eauto.  
Qed.

Lemma gk3cPerm: forall Γ Δ, gk3c Γ Δ -> forall Γ' Δ', Γ ≡P Γ' -> Δ ≡P Δ' -> gk3c Γ' Δ'.
Proof.   
  intros Γ Δ H. induction H; intros;auto. 
  - eapply gk3cC. rewrite<- H1. apply H.  rewrite<- H2. auto. 
  - apply  gk3cF.  firstorder eauto 10 using pin.  rewrite<- H0. auto. 
  - apply gk3cIL with s t. rewrite<- H2.  auto.
    apply IHgk3c1; auto. eauto.
  - apply gk3cIR with s t; firstorder eauto. rewrite<- H2. auto.
  - apply gk3cAL with s t; firstorder eauto.   rewrite<- H1. auto.
  - apply gk3cAR with s t; firstorder eauto. rewrite<- H3. auto. 
  - apply gk3cOL with s t; firstorder eauto.  rewrite<- H2.  auto.
  - apply gk3cOR with s t; firstorder eauto. rewrite<- H2. auto.
  - apply gk3cKI with s.   rewrite<- H2. auto. apply IHgk3c. apply remNotK_perm.   auto. 
    auto. 
Qed.


Lemma gk3_monol Γ A: gk3c Γ A -> forall Γ', Γ <<= Γ' -> gk3c Γ' A. 
Proof.
  intro. induction H; eauto.
  - intros Γ' S. apply gk3cIL with s t; eauto. 
  - intros Γ' S. apply gk3cAL with s t; firstorder eauto.
  - intros Γ' S. apply gk3cOL with s t; firstorder eauto.   
Qed.

Lemma gk3_monor A B: gk3c A B -> forall B', B <<= B' -> gk3c A B'.
  intro. induction H; eauto.
  all: intros B' S.
  - firstorder eauto.
  - firstorder eauto.
  - apply gk3cAR with s t; auto.
  - apply gk3cOR with s t; auto.   apply IHgk3c. auto.
Qed.

(* Register with Permutation equivalence *) 
Instance gk3_proper_perm  : Proper ( (@Permutation form) ==> (@Permutation form) ==> iff) (gk3c ).
Proof. 
  intros x y H1 a b H2. split; firstorder eauto using gk3cPerm.
Defined.

Instance incl_proper_perm  : Proper ( (@Permutation form) ==> (@Permutation form) ==> iff) (@incl form ).
Proof. 
  intros x y H1 a b H2. split.
  - intros H3 c Hc . rewrite<- H2.  apply H3. rewrite H1. auto.
  - intros H3 c Hc.  rewrite H2.  apply H3. rewrite<- H1. auto. 
Defined.

(* Register with incl *) 

Instance gk3_proper_weak  : Proper ( (@incl form) ==> (@incl form) ==> Basics.impl) (gk3c ).
Proof. 
  intros x y H1 a b H2 H3.  firstorder eauto using gk3_monor, gk3_monol.
Defined.


Lemma gk3c_equi_lk A B: lk A B <-> gk3c A B. 
Proof.
  intros.
  split.
  intro. induction H. induction H.
  - apply gk3cC with A; auto. 
  - apply gk3cF. auto.
  - apply gk3cIL with A B.   rewrite H3. auto. rewrite H3.   apply gk3_monol with Γ; auto.   rewrite<- H. auto. rewrite H3. apply gk3_monol with (B::Γ).   rewrite<- H1. auto. auto. 
  - apply gk3cIR with A B. rewrite H2. auto. apply gk3cPerm with Γ1 ((A ⊃ B)::B::Δ); try psolve.  apply gk3_monor with (Δ1); auto. intros a Ha.  rewrite<- H0. auto. 
  - apply gk3cKI with A. rewrite H1.  auto.   apply gk3_monol with Γ. auto. intros a Ha. apply remNotK_in_iff.  rewrite H0.  apply in_app_iff. left.   apply in_map_iff. exists a.  split; eauto. 
  - apply gk3cOL with A B. rewrite H3. auto. rewrite H3. apply gk3_monol with Γ1; auto. rewrite H.  auto.  apply gk3_monol with Γ2.  auto. rewrite H1. rewrite H3. auto. 
  - apply gk3cOR with  A B. rewrite H1; auto.  apply gk3_monor with Δ1. auto. rewrite H.  rewrite H1. firstorder eauto. 
  - apply gk3cAL with  A B. rewrite H1; auto. apply gk3_monol with Γ1. firstorder eauto. rewrite H, H1. firstorder eauto. 
  - apply gk3cAR with A B. rewrite H3; auto. apply gk3_monor with Δ1; auto.  rewrite H, H3.  firstorder eauto.
    apply gk3_monor with Δ2; auto. rewrite H1, H3; firstorder eauto. 
  - auto.

  - intro. induction H.
    + exists 0.  apply lkhA with x; auto.
    + exists 0.  apply lkhB.  auto.
    + apply Perm_In_Iff in H. destruct IHgk3c1 as [n1 IH1], IHgk3c2 as [n2 IH2], H as [lH H].   eexists (S (Nat.max n1 n2)).
      rewrite<- H. apply contraction.    apply lkOIL. rewrite H.  apply multiStep with n1; try lia; auto.    rewrite H. apply multiStep with n2; try lia. auto. 
    + apply Perm_In_Iff in H. destruct IHgk3c as [n1 IH], H as [lH H]. exists (S n1). rewrite<- H. apply contraction.
      apply lkOIR. rewrite H. auto. 
    + apply Perm_In_Iff in H. destruct H as [lH H], IHgk3c as [n IH]. exists (S n). rewrite<- H.  apply contraction.
      apply lkOAL. rewrite H. auto. 
    + apply Perm_In_Iff in H. destruct IHgk3c1 as [n1 IH1], IHgk3c2 as [n2 IH2], H as [lH H].   eexists (S (Nat.max n1 n2)).
      rewrite<- H. apply contraction. rewrite H.  apply lkOAR. apply multiStep with n1; auto; try lia. apply multiStep with n2; auto; try lia. 
    +  apply Perm_In_Iff in H. destruct IHgk3c1 as [n1 IH1], IHgk3c2 as [n2 IH2], H as [lH H].   eexists (S (Nat.max n1 n2)).
       rewrite<- H. apply contraction. rewrite H. apply lkOOL. apply multiStep with n1; auto; try lia. apply multiStep with n2; auto; try lia.
    + apply Perm_In_Iff in H. destruct H as [lH H], IHgk3c as [n IH].  eexists (S n). rewrite<- H. apply contraction. apply lkOOR. rewrite H.  auto. 
    + apply Perm_In_Iff in H. destruct H as [lH H], IHgk3c as [n IH].  eexists (S n).  rewrite<- H.
      rewrite unK_justKNoK. assert ((notK A ++ map K (remNotK A)) ≡P (( map K (remNotK A) ++ notK A))). psolve.  rewrite H1. 
      apply lkOKI. auto. 
Qed.

Definition context := list form. 
Definition goalc := prod context context.

Instance goalc_eq_dec (gamma delta: goalc) :
  dec (gamma = delta).
Proof.
  unfold dec. repeat decide equality.
Qed.
(** ** Decidability for K *)
Section Decidability_GK3c.
  Variable A0 B0 : context.
  Definition Uc := scl (A0 ++ B0).
  Definition Uc_sfc : sf_closed Uc := @scl_closed _.
  Definition Gammac := list_prod (power Uc) (power Uc).
  Definition stepc (Delta : list goalc) (gamma : goalc) : Prop :=
    let (A,B) := gamma in  
    (exists (u: form), u el A /\ (u el B \/ 
                            (match u with
                             | Bot => True
                             | Imp s t => (A, rep (s::B) Uc) el Delta /\ (rep (t::A) Uc, B) el Delta
                             | And s t => (rep (s::t::A) Uc, B) el Delta
                             | Or s t => (rep (s::A) Uc, B) el Delta /\ (rep (t::A) Uc, B) el Delta
                             | _ => False
                             end) ) )
    \/
    (exists u, u el B /\
          match u with
          | Imp s t => (rep (s::A) Uc, rep (t::B) Uc) el Delta
          | And s t => (A, rep (s::B) Uc) el Delta /\ (A, rep (t::B) Uc) el Delta
          | Or s t => (A, rep (s::t::B) Uc) el Delta
          | K s    => (rep (remNotK A) Uc, (rep [s] Uc)) el Delta
          | _ => False
          end).

  Instance step_dec Delta gamma :
    dec (stepc Delta gamma).
  Proof.
    destruct gamma as [A u]; simpl.
    apply or_dec. apply list_exists_dec. intro . destruct x; auto 10.
    apply list_exists_dec. intro x. destruct x; firstorder eauto. 
  Defined.

  Definition stepcb (Delta : list goalc) (Gamma : goalc) := dec2bool (step_dec Delta Gamma).
  Lemma stepb_reflect D γ: stepcb D γ = true <-> stepc D γ.
  Proof.
    split; intro. 
    apply Dec_reflect in H.   auto.
    apply Dec_reflect. auto. 
  Qed.   

  Definition Lambdac  :=
    (FCI.C stepcb Gammac).

  Lemma lambdac_closure gamma :
    gamma el Gammac -> stepcb Lambdac gamma -> gamma el Lambdac.
  Proof. apply FCI.closure. Qed.

  Lemma gk3c_lambdac A B :
    A <<= Uc -> B <<= Uc -> gk3c A B -> (rep A Uc, rep B Uc) el Lambdac.
  Proof.
    intros D1 D2 D.
    induction D.
    - (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl.
      apply stepb_reflect. left.   exists (Var x). auto using rep_in.
    - (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl.
      apply stepb_reflect.  left. exists Bot. auto using rep_in.
    -  (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl.
       apply stepb_reflect.  left. exists (s ⊃ t).  split; auto using rep_in. right.
       
       + specialize (IHD1 D1). apply D1 in H. apply Uc_sfc in H as [H1 H2].
         split.
         assert (I: (rep A Uc, rep (s :: B) Uc) el Lambdac) by auto.
         assert (J: (rep (t :: A) Uc, rep B Uc) el Lambdac) by auto.
         rewrite rep_eq with (A:=s :: rep B Uc) (B:=s :: B). auto.  rewrite rep_equi; auto. 
         rewrite rep_eq with (A:=t :: rep A Uc) (B:=t :: A); auto.
         rewrite rep_equi.  auto.  auto.
    -      (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl.
           apply stepb_reflect. right. exists (Imp s t). split; auto using rep_in.
           apply D2 in H. apply Uc_sfc in H as [E1 E2].
           assert (I: (rep (s :: A) Uc, rep (t :: B) Uc) el Lambdac) by auto.
           rewrite rep_eq with (B:=s::A).
           rewrite rep_eq with (A:=t :: rep B Uc) (B:=t :: B); auto.
           + setoid_rewrite rep_equi; auto.
           + setoid_rewrite rep_equi; auto.
    - (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl.
      apply stepb_reflect. left. exists (And s t). split; auto using rep_in. right.
      apply D1 in H. apply Uc_sfc in H as [E1 E2].
      assert (I: (rep (s :: t :: A) Uc, rep B Uc) el Lambdac) by auto.
      rewrite rep_eq with (B:=s :: t :: A); auto.
      rewrite rep_equi; auto.
    - (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl. apply stepb_reflect.
      right. exists (And s t). split; auto using rep_in.
      apply D2 in H. apply Uc_sfc in H as [E1 E2].
      assert (I: (rep A Uc, rep (s :: B) Uc) el Lambdac) by auto.
      assert (J: (rep A Uc, rep (t :: B) Uc) el Lambdac) by auto.
      rewrite rep_eq with (A:=s :: rep B Uc) (B:=s :: B).
      rewrite rep_eq with (A:=t :: rep B Uc) (B:=t :: B); auto.
      + rewrite rep_equi; auto.
      + rewrite rep_equi; auto.
    - (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl. apply stepb_reflect.
      left. exists (Or s t). split; auto using rep_in. right.
      apply D1 in H. apply Uc_sfc in H as [E1 E2].
      assert (I: (rep (s :: A) Uc, rep B Uc) el Lambdac) by auto.
      assert (J: (rep (t :: A) Uc, rep B Uc) el Lambdac) by auto.
      rewrite rep_eq with (A:=s :: rep A Uc) (B:=s :: A).
      rewrite rep_eq with (A:=t :: rep A Uc) (B:=t :: A); auto.
      + rewrite rep_equi; auto.
      + rewrite rep_equi; auto.
    -   (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl. apply stepb_reflect.
        right. exists (Or s t). split; auto using rep_in.
        apply D2 in H. apply Uc_sfc in H as [E1 E2].
        assert (I: (rep A Uc, rep (s :: t :: B) Uc) el Lambdac) by auto.
        rewrite rep_eq with (A:=s :: t :: rep B Uc) (B:=s :: t :: B); auto.
        rewrite rep_equi; auto.
    -   (apply lambdac_closure; [now eauto using in_prod, rep_power|]); simpl. apply stepb_reflect.
        right. exists (K s). split; auto using rep_in.
        assert ((rep (remNotK (rep A Uc)) Uc = (rep (remNotK A) Uc))).
        {
          apply rep_eq.
          split.
          + intros a Ha. apply remNotK_in_iff. apply remNotK_in_iff in Ha.     apply rep_incl in Ha.  auto. 
          + intros a Ha.   apply remNotK_in_iff. apply rep_in. auto.  apply remNotK_in_iff in Ha.  auto.
        }
        assert ((rep (remNotK A) Uc, rep [s] Uc) el Lambdac). {
          apply IHD.
          - intros a Ha. apply remNotK_in_iff in Ha.  apply D1 in Ha. apply Uc_sfc in Ha.  auto.
          -  intros a Ha.  apply D2 in H. destruct Ha; auto. subst s.   apply Uc_sfc in H.  auto.  
        }
        rewrite H0. auto.            
  Qed. 

  Lemma lambdac_ind (p : goalc -> Prop) :
    (forall Delta gamma, inclp Delta p ->
                         gamma el Gammac -> stepc Delta gamma -> p gamma)
    -> inclp Lambdac p.
  Proof. intros.  apply FCI.ind. intros.  apply H with A; auto. apply stepb_reflect.  auto.  Qed.

  Lemma lambdac_gk3c A B :
    (A,B) el Lambdac -> gk3c A B.
  Proof.
    revert A B.
    cut (inclp Lambdac (fun gamma => gk3c (fst gamma) (snd gamma))).
    { intros E A B. apply E. }
    apply lambdac_ind. intros Delta [A B] E F G; simpl.
    assert (E': forall A B, (A,B) el Delta -> gk3c A B).
    { intros A' B'. apply E. } clear E.
    destruct G. destruct H. destruct H as [H1 [H2 | H3]]. eapply gk3cA; eauto. 
    destruct x; try firstorder eauto;    try tauto; try (auto using gk3cW, rep_incl). 
    apply E' in H. apply E' in H0.  
    apply gk3cIL with x1 x2;     eauto using gk3cW, rep_incl.
    apply gk3cAL with x1 x2;     eauto using gk3cW, rep_incl. 
    apply gk3cOL with x1 x2;     eauto using gk3cW, rep_incl.
    destruct H as [u H]. destruct H as [H1 H2]; destruct u; firstorder eauto.  
    apply E' in H2. apply gk3cKI with u; auto.  eauto using gk3cW, rep_incl.
    apply gk3cIR with u1 u2; eauto using gk3cW, rep_incl.
    apply gk3cAR with u1 u2; eauto using gk3cW, rep_incl.
    apply gk3cOR with u1 u2; eauto using gk3cW, rep_incl.
  Qed.
  
  
  Theorem gk3c_dec: dec (gk3c A0 B0).
  Proof.
    assert (A1: A0 <<= Uc).
    { apply scl_incl; auto. }
    assert (A2: B0 <<= Uc).
    { apply scl_incl; auto. }
    apply dec_prop_iff with (X:= gk3c (rep A0 Uc) (rep B0 Uc)).
    - split; intros E; apply (gk3cW E), rep_equi; destruct (rep_equi A1); auto.
    - decide ((rep A0 Uc, rep B0 Uc) el Lambdac) as [E|E].
      + left. apply lambdac_gk3c, E.
      + right. intros F. apply E.
        apply gk3c_lambdac; auto.
        apply (gk3cW F); auto; apply rep_equi; auto.
  Qed.
End Decidability_GK3c.





