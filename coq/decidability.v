Require Import PslBase.FCI.
Require Import PslBase.Base.
Require Import PslBase.Lists.BaseLists. 
Require Import forms  nd Permutation.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Classes.CRelationClasses.
Require Import toolbox.
Notation "'K[' Δ ']'" := (List.map K Δ).

(** * Sequent Calculus for IEL *)
Definition context := list form.
Section EntailmentRelationProperties.

  Variable F: Type.
  Variable E: list F -> F -> Prop.

  (** ** Generic Structural Properties ***)
  Definition Monotonicity : Prop :=
    forall A A' s, A <<= A' -> E A s -> E A' s.

  Definition Reflexivity : Prop :=
    forall A s, s el A -> E A s.

  Definition Cut : Prop :=
    forall A s t, E A s -> E (s::A) t -> E A t.

  Definition Consistency : Prop :=
    exists s:F, ~E nil s.

  Definition CharFal (E: context -> form -> Prop) : Prop :=
    forall A, E A Bot <-> forall s, E A s.

  Definition CharImp (E: context -> form -> Prop) : Prop :=
    forall A s t, E A (Imp s t) <-> E (s::A) t.

  Definition CharAnd (E: context -> form -> Prop) : Prop :=
    forall A s t, E A (And s t) <-> forall u, E (s::t::A) u -> E A u.

  Definition CharOr (E: context -> form -> Prop) : Prop :=
    forall A s t, E A (Or s t) <-> forall u, E (s::A) u -> E (t::A) u -> E A u.

End EntailmentRelationProperties.


Inductive gen:forall (D: DerivationType), context -> form -> Prop :=
| genV A x {D}:       Var x el A -> gen D A (Var x)
| genF A u {D}:       Bot el A -> gen D A u
| genIR A s t {D}:    gen D (s::A) t -> gen D A (Imp s t)
| genIL A s t u {D}:  (Imp s t) el A -> gen D A s -> gen D (t::A) u -> gen D A u
| genAL A s t u {D}:  (And s t) el A -> gen D (s::t::A) u -> gen D A u
| genAR A s t {D}:    gen D A s -> gen D A t -> gen D A (And s t)
| genOL A s t u {D}:  (Or s t) el A -> gen D (s::A) u -> gen D (t::A) u -> gen D A u
| genOR1 A s t {D}:   gen D A s -> gen D A (Or s t)
| genOR2 A s t {D}:   gen D A t -> gen D A (Or s t)
| genKI A s {D}:      gen D ((unK A)) s -> gen D A (K s)
| genKB A s:          gen normal A (K ⊥) -> gen normal A s .
Local Hint Constructors gen : core.
Arguments gen {_} _ _.

Lemma genA (D: DerivationType): Reflexivity gen.
Proof.
  intros A s. revert A. induction s; intros A C; auto.
  - apply genKI. apply IHs. apply unK_in_iff.  auto.  
  - apply genIR. eauto.
  - apply genAL with (s:=s1) (t:=s2); auto.
  - apply genOL with (s:=s1) (t:=s2); auto.
Qed.

(** Weakening rule *)
Lemma gen_mono (D': DerivationType): Monotonicity gen.
Proof.
  intros A A' s C D. revert C. revert A'. induction D; intros A' C; eauto 5.
  - apply genIL with s t; eauto.
  - eapply genAL; eauto. apply IHD. firstorder eauto.
  - apply genOL with s t; firstorder eauto.   
  - apply genKI. apply IHD. apply unK_incl. auto. 
Qed.

Lemma genW A B s (Dt: DerivationType): gen A s -> A <<= B -> gen B s.
Proof. intros C D. apply gen_mono with (A:=A); auto. Qed.

Lemma genPerm (Dt: DerivationType): forall Γ1 s,  gen Γ1 s -> forall Γ2, Γ1 ≡P Γ2 ->  gen Γ2 s. 
Proof.
  intros Γ1 s H0.
  induction H0; firstorder eauto. 
  - apply genA. rewrite<- H0. auto. 
  - apply genF. rewrite<- H0. auto. 
  - apply genIL with s t. rewrite<- H0. auto. apply IHgen1.  auto. apply IHgen2. auto.
  -  apply genAL with s t.  rewrite<- H1. auto. apply IHgen.  auto.
  -  apply genOL with s t. rewrite<- H0.  auto.  apply IHgen1. auto. apply IHgen2. auto. 
  -  apply   genKI. apply IHgen. apply unK_perm.   auto.
Qed.


Instance perm_properGen' (D: DerivationType) : Proper ((@Permutation _) ==> eq ==> impl) (gen  ).
Proof. 
  intros  a b c d e f   H1. 
  rewrite<- f. 
  apply genPerm with a; assumption.
Qed.

Local Hint Resolve genA : core.
(** ** Height-bounded sequent calculus *)
Inductive genh: forall (D: DerivationType), nat -> context -> form -> Prop :=
| genhV A x {D}:         Var x el A -> genh D 0 A (Var x)
| genhF A u {D}:         Bot el A -> genh D 0 A u
| genhIR n A s t {D}:    genh D n (s::A) t -> genh D (S n) A (Imp s t)
| genhIL n A s t u {D}:  (Imp s t) el A -> genh D n A s -> genh D n (t::A) u -> genh D (S n) A u
| genhAL n A s t u {D}:  (And s t) el A -> genh D n (s::t::A) u -> genh D (S n) A u
| genhAR n A s t {D}:    genh D n A s -> genh D n A t -> genh D (S n) A (And s t)
| genhOL n A s t u {D}:  (Or s t) el A -> genh D n (s::A) u -> genh D n (t::A) u -> genh D (S n) A u
| genhOR1 n A s t {D}:   genh D n A s -> genh D (S n) A (Or s t)
| genhOR2 n A s t {D}:   genh D n A t -> genh D (S n) A (Or s t)
| genhKI n A s {D}:      genh D n ((unK A)) s -> genh D (S n) A (K s)
| genhS n A s {D}:       genh D n A s -> genh D (S n) A s
| genhKB n A s:          genh normal n A (K ⊥) -> genh normal (S n) A s 
.

Arguments genh {_} _ _ _. 

Local Hint Constructors genh : core.

Lemma genhW n A1 s (Dt: DerivationType):
  genh n A1 s -> forall A2, A1 <<= A2 -> genh n A2 s. 
Proof.
  intro H. 
  induction H;  eauto 5; intros. 
  - apply genhIL with s t; eauto.
  - eapply genhAL; eauto. apply IHgenh. firstorder eauto.
  - apply genhOL with s t; firstorder eauto.   
  - apply genhKI. apply IHgenh. apply unK_incl. auto. 
Qed. 

Local Hint Resolve genhW : core.

Require Import Coq.Program.Equality.
(** ** Inversion Results *)
Ltac find_rwd :=
  match goal with
    H1: genh ?n ?A ?s
    |- genh ?n ?B ?s =>  (apply genhW with A); firstorder eauto
  end.
Ltac solveWeak H' :=
  match goal with
  | [ H: (genh ?n ?A ?B)   |- _  ] => (match H with
                                       | H' => apply genhW  with A; firstorder eauto end)
  end.

Lemma inversionAnd Γ  A B C n (D: DerivationType) :
  genh n ((A ∧ B)::Γ) C -> genh n (A::B::Γ) C.
Proof.
  revert C Γ.
  induction n.
  - intros C Γ. intros.  inversion H. firstorder eauto.  inversion H0. firstorder eauto. inversion H0.
  - intros.
    inversion H; auto. 
    + apply genhIR. apply genhW with (A::B::s::Γ). apply IHn. solveWeak H2. firstorder eauto.
    + destruct H1.  congruence.  apply genhIL with s t. auto. apply IHn. auto. apply genhW with (A::B::t::Γ). 2: firstorder eauto.
      apply IHn. solveWeak H4. 
    + destruct H1.
      * apply genhW with (A::B::A::B::Γ). apply genhS. apply IHn. inversion H1. apply genhW with (s::t::(A ∧ B)::Γ). auto. inversion H1;  firstorder eauto.
        firstorder eauto.
      * apply genhAL with s t. auto.  apply genhW with (A::B::s::t::Γ).  apply IHn.
        apply genhW with (s::t::(A ∧ B)::Γ). all:  firstorder eauto.
    + destruct H1.  congruence. apply genhOL with s t. auto.
      apply genhW with (A::B::s::Γ). apply IHn. apply genhW with (s::(A ∧ B)::Γ). auto. 1-2: firstorder eauto.
      apply genhW with (A::B::t::Γ). apply IHn. apply genhW with (t::(A ∧ B)::Γ). auto. 1-2: firstorder eauto.
    + apply genhKI.  apply genhW with (A::B::unK ( Γ)).  apply IHn. simpl unK in H1.  auto. destruct A; destruct B; simpl; firstorder eauto.
    + subst D.   eauto. 
Qed.

Lemma inversionOR1 Γ  s t C n (D: DerivationType) :
  In s Γ -> genh n ((s ∨ t)::Γ) C -> genh n Γ C.
Proof.
  revert C Γ.
  induction n.
  - intros C Γ. intros.  inversion H0. firstorder eauto.  inversion H1.  firstorder eauto. inversion H1.
  - intros.
    inversion H0;  auto. 
    + apply genhIR.   apply IHn.  auto.  apply genhW with ((s0 :: (s ∨ t) :: Γ)).  auto. all: firstorder eauto.
    + destruct H2.  congruence.  apply genhIL with s0 t0; auto.  apply IHn; auto.  solveWeak H5. 
    + destruct H2; try  congruence.  apply genhAL with s0 t0. auto.   apply IHn.  auto. solveWeak H4.
    + destruct H2.
      * apply genhS. apply IHn. auto. inversion H2.  subst s0.   apply genhW with (s::(s ∨ t)::Γ).  auto. subst t0.  intros a Ha.  destruct Ha. right.  subst a. eauto.
        firstorder eauto.
      *  apply genhOL with s0 t0.  auto.  apply IHn.  auto.  apply genhW with (s0 :: (s ∨ t) :: Γ); firstorder eauto.
         apply IHn.  auto.  apply genhW with (t0 :: (s ∨ t) :: Γ); firstorder eauto.
    + apply genhKI.   apply IHn.  apply unK_in_iff.  firstorder eauto.     simpl unK in H2.  auto.
    + subst D. eauto.   
Qed.

Lemma inversionOR2 Γ  s t C n (D: DerivationType) :
  In t Γ -> genh n ((s ∨ t)::Γ) C -> genh n Γ C.
Proof.
  revert C Γ.
  induction n.
  - intros C Γ. intros.  inversion H0. firstorder eauto.  inversion H1.  firstorder eauto. inversion H1.
  - intros.
    inversion H0;  auto. 
    + apply genhIR.   apply IHn.  auto.  apply genhW with ((s0 :: (s ∨ t) :: Γ)).  auto. all: firstorder eauto.
    + destruct H2.  congruence.  apply genhIL with s0 t0. auto. auto.   apply IHn.  auto. auto.   apply genhW with (t0::(s ∨ t)::Γ); firstorder eauto.
    + destruct H2.  congruence.  apply genhAL with s0 t0. auto.   apply IHn.  auto. solveWeak H4. 
    + destruct H2.
      * apply genhS. apply IHn. auto. inversion H2.  subst s0 t0.     apply genhW with (t::(s ∨ t)::Γ).  auto.  auto.  
      * apply genhOL with s0 t0;  auto;  apply IHn.  auto. solveWeak H3.  auto. solveWeak H5.   
    + apply genhKI.   apply IHn.  apply unK_in_iff.  firstorder eauto.      simpl unK in H2.  auto.
    + subst D. eauto.   
Qed.


Lemma inversionIL Γ s t r n (D: DerivationType) :
  In t Γ -> genh n ((s ⊃ t)::Γ) r -> genh n Γ r.  
  revert r Γ.
  induction n.
  - intros r Γ. intros.  inversion H0. firstorder eauto.  inversion H1.  firstorder eauto. inversion H1.
  -  intros.
     inversion H0;  auto. 
     + apply genhIR.   apply IHn.  auto.  solveWeak H3.  
     + destruct H2.
       * apply genhS. apply IHn. auto. inversion H2.  subst s0. subst t0.  solveWeak H3.   
       * apply genhIL with s0 t0.  auto.  auto.  apply IHn.  auto.  solveWeak H5.   
     + destruct H2. congruence. apply genhAL with s0 t0.  auto.  apply IHn;  auto.  
       find_rwd; firstorder eauto.  
     + destruct H2. congruence. apply genhOL with s0 t0.  auto.  apply IHn;  auto.   apply genhW with (s0 :: (s ⊃ t) :: Γ); firstorder eauto.
       apply IHn;  auto.  apply genhW with (t0 :: (s ⊃ t) :: Γ); firstorder eauto.
     +    apply genhKI.   apply IHn.  apply unK_in_iff.  firstorder eauto.      simpl unK in H2.  auto.
     +  subst D; eauto.     
Qed.
(** We can increase the height of a derivation arbitrarily. **)
Lemma genhInc (n1 n2: nat) A s (D: DerivationType):
  genh n1 A s -> n1 <= n2 -> genh n2 A s.
Proof.
  intros H Hnum. induction Hnum; auto. 
Qed.

(** We show an equivalence between gen and genh. **)
Lemma genh_iff_gen A s (D: DerivationType): gen A s <-> exists n, genh n A s. 
Proof.
  split.
  - intros H.  induction H; firstorder eauto.
    + exists (S(Nat.max x x0)). apply genhIL with s t. auto.  apply  genhInc with x0;  auto; try lia.    apply  genhInc with x;  auto; try lia.
    +  exists (S(Nat.max x x0)). apply genhAR.  apply  genhInc with x0;  auto; try lia.    apply  genhInc with x;  auto; try lia.
    +  exists (S(Nat.max x x0)). apply genhOL with s t. auto.  apply  genhInc with x0;  auto; try lia.    apply  genhInc with x;  auto; try lia.
  -    intros [n Hn].  induction Hn; firstorder eauto. 
Qed.

Local Hint Resolve genh_iff_gen : core. 
(** ** Cut-Elimination *)
Lemma genDPCut (D: DerivationType):
  forall  m n n1 n2 Γ B A (P1: genh n1 Γ B ) (P2: genh n2 (B::Γ) A) ,  n1 + n2 = n -> (size B) = m ->  gen (Γ) A.
Proof. 
  intros n m. 
  induction n, m using le_wf_ind.
  intros n1 n2 Γ B A P1 P2 sb hnm.
  assert (scut: forall Γ A S, size S < size B ->  (gen Γ S) -> (gen (S::Γ) A) -> (gen Γ A)).   
  {
    intros. apply genh_iff_gen in H2. apply genh_iff_gen in H3. destruct H2 as [nh2 H2], H3 as [nh3 H3].   eapply H.   subst m1. eapply H1.  eapply H2.  eapply H3. reflexivity.  lia.
  }

  assert (rcut: forall Γ A n1 n2,   (genh n1 Γ B) -> (genh n2 (B::Γ) A) ->  n1+n2 < m2 -> (gen Γ A)).  {
    intros. eapply H0. apply H3. apply H1. apply H2.  reflexivity. subst m1. auto.
  }

  inversion P1.
  - apply genW with (B::Γ). eapply genh_iff_gen. eexists.    apply P2. subst B; eauto.
  - eauto.
  -
    inversion P2.
    +  destruct H6; auto. subst A. subst B. inversion H6.
    +  destruct H6; auto. subst A. subst B. inversion H6.
    + apply genIR.   eapply rcut. apply genhW with Γ.   eapply P1.  auto.  apply genhW with (s0 :: B :: Γ).  eapply H6. firstorder eauto. lia.
    + subst B.   destruct H6.
      *  inversion H5. subst s0 t0. eapply scut with t. inversion H5. simpl; lia. eapply scut with s. inversion H5. simpl; lia.    eapply rcut.   apply P1.
         apply H7.  lia. eapply genh_iff_gen.   eexists.   apply H1. eapply genh_iff_gen.  eexists.   apply inversionIL with s t.  auto.  apply genhW with (t :: (s ⊃ t) :: Γ). eauto.
         firstorder eauto.
      *  apply genIL with s0 t0.    auto. eapply rcut. eauto using genh_iff_gen.  eapply H7.  lia. eapply rcut. apply genhW with Γ.  eauto using genh_iff_gen. auto.
         apply genhW with (t0 :: (s ⊃ t) :: Γ).  eauto. firstorder eauto.  lia. 
    +  subst B.  destruct H6; try congruence. apply genAL with s0 t0.  auto. eapply rcut. apply genhW with Γ.  apply P1. eauto.   apply genhW with (s0 :: t0 :: (s ⊃ t) :: Γ); firstorder eauto. lia. 
    +  apply genAR.
       * eapply rcut. eapply P1. eapply H6. lia.
       * eapply rcut. eapply P1. eapply H7. lia.  
    +  subst B. destruct H6;try congruence. apply genOL with s0 t0.
       * auto.
       *  eapply rcut. apply genhW with Γ. apply P1. eauto. apply genhW with (s0 :: (s ⊃ t) :: Γ); firstorder eauto. lia.
       *  eapply rcut with (n2 := n0). apply genhW with Γ. apply P1. eauto.  solveWeak  H8. lia. 
    +  apply genOR1. eapply rcut with n1 n0. auto.  auto. lia. 
    +  apply genOR2. eapply rcut with n1 n0. auto.  auto. lia. 
    + 
      apply genKI. eapply rcut. apply genhW with (Γ). apply P1. intros a Ha.  apply unK_in_iff.  auto.   apply genhW with ((unK ((s ⊃ t)::Γ))).  subst B.
      apply H6.  simpl unK. rewrite<- H5.  reflexivity.  lia. 
    +  eapply rcut;    eauto; try lia.
    +  apply genKB. auto. subst D0 D.   eapply rcut.  eapply P1. eapply H6. lia. 
  - apply genIL with s t.   auto.  eapply genh_iff_gen. eauto.
    eapply rcut.  apply H3. apply inversionIL with s t.  auto.  apply genhW with (B :: Γ). apply P2. firstorder eauto. lia. 
  - subst u. apply genAL with s t.  auto. eapply rcut. apply H2. apply genhW with (B::Γ).  eauto. firstorder eauto.  lia.
  - apply scut with t.   subst B. simpl size; lia. apply genh_iff_gen. eauto.
    apply scut with s. subst B; simpl size; lia. apply genW with Γ.   apply genh_iff_gen. eauto. auto. eapply genh_iff_gen. eexists.    apply inversionAnd.  rewrite H6. apply P2.
  -  apply genOL with s t.  auto. 
     * eapply rcut. eapply H2. apply genhW with (B::Γ). eauto. firstorder eauto. lia.
     * eapply rcut.  eapply H3.  apply genhW with (B::Γ). eauto. firstorder eauto. lia. 
  - subst B. eapply scut with s.  simpl; lia.  apply genh_iff_gen. eauto.   apply genh_iff_gen. eexists.  apply inversionOR1 with s t.  auto. apply genhW with ((s ∨ t)::Γ). eauto.
    firstorder eauto. 
  - subst B. eapply scut with t.  simpl; lia.  apply genh_iff_gen. eauto.   apply genh_iff_gen. eexists.  apply inversionOR2 with s t.  auto. apply genhW with ((s ∨ t)::Γ). eauto.
    firstorder eauto. 
  - inversion P2.
    + destruct H6; auto. subst A. subst B. inversion H6.
    +  destruct H6. try congruence.  eauto.
    +  apply genIR.   eapply rcut. apply genhW with Γ.   eapply P1.  auto.  apply genhW with (s0 :: B :: Γ).  eapply H6. firstorder eauto. lia.  
    +  subst B.  destruct H6; try congruence.  apply genIL with s0 t.    auto. eapply rcut. eauto using genh_iff_gen.  eapply H7.  lia. eapply rcut. apply genhW with Γ.  eauto using genh_iff_gen. auto.
       apply genhW with (t :: (K s) :: Γ).  eauto. firstorder eauto.  lia.
    +  destruct H6;try congruence.  apply genAL with s0 t. auto. eapply rcut. apply inversionAnd.  apply genhW with Γ. eapply P1.  firstorder eauto. 
       apply genhW with (s0::t::B::Γ). auto. eauto.   firstorder eauto 100.  lia. 
    +  apply genAR.
       * eapply rcut. eapply P1. eapply H6. lia.
       * eapply rcut. eapply P1. eapply H7. lia.  
    +  subst B. destruct H6;try congruence. apply genOL with s0 t.  auto.
       * eapply rcut. apply genhW with Γ . eapply P1. auto. apply genhW with (s0 :: K s :: Γ).  eapply H7. firstorder eauto.  lia.
       * eapply rcut. apply genhW with Γ . eapply P1. auto. apply genhW with (t :: K s :: Γ).  eapply H8. firstorder eauto.  lia.  
    +  apply genOR1. eapply rcut with n1 n0. auto.  auto. lia. 
    +  apply genOR2. eapply rcut with n1 n0. auto.  auto. lia. 
    +  apply genKI.
       eapply scut with s. subst B; simpl; lia.  apply genh_iff_gen. eauto.  
       eapply rcut. apply genhW with Γ. eauto. intros a Ha.   right. apply unK_in_iff.  auto. 
       subst B. eapply genhW with (unK (K s :: Γ)).  simpl unK; firstorder eauto.  simpl unK.  reflexivity. lia.
    +  eapply rcut;    eauto; try lia.
    +  apply genKB.   subst D D0.   eapply rcut. eapply P1. eapply H6. lia. 
  - eapply rcut.   apply H1. eauto. lia.
  - subst D.   apply genKB.  eapply genh_iff_gen. exists n. auto. 
Qed.
Local Hint Resolve<- genh_iff_gen : core.
Local Hint Resolve-> genh_iff_gen : core.


(** ** Equivalence between ND and SC *)
Local Hint Constructors nd : core.

Lemma gen2nd A s (D: DerivationType) :  (gen A s) -> (nd A s).
Proof.
  intros C. induction C.
  - eauto.
  - eauto.   
  - eauto.
  - apply ndIE with t. apply ndII. auto.  apply ndIE with s.    apply ndA. auto. auto.
  - apply ndIE with t. apply ndII.  apply ndIE with s. apply ndII. auto.  apply ndCEL with t.  apply ndA; auto. apply ndCER with s.  apply ndA; auto.
  - apply ndCI; auto.
  - apply ndDE with s t.   apply ndA; auto. apply ndII. auto.  apply ndII. eauto.
  - eauto.
  - eauto.
  - apply ndW with ((notK A) ++ (K[ (remNotK A)])). apply ndKKrupski. apply ndW with (unK A).  auto. intros a Ha.  apply unK_in_iff in Ha.    destruct Ha; auto.   rewrite<- unK_justKNoK.   auto. apply in_app_iff.  left.  apply remNotK_in_iff.  auto.  intros a Ha.   rewrite<- unK_justKNoK in Ha. auto. 
  - apply ndE.  apply ndIE with (s0 := ¬ ¬ ⊥). auto.
    apply ndIntRefl.  auto. 
Qed.

Lemma gen_cut (Dt: DerivationType): Cut gen.
Proof.
  intros A s t C D.  apply genh_iff_gen in C.  apply genh_iff_gen in D. destruct C as [n1 C], D as [n2 D]. eapply genDPCut.  eapply C.  eapply D. reflexivity. reflexivity. 
Qed.


Lemma genCW A s t (Dt: DerivationType): gen A s -> gen [s] t -> gen A t.
Proof.
  intros D E. apply gen_cut with (s:=s); auto. apply (genW E). auto.
Qed.


Lemma gen_fal (D: DerivationType): CharFal gen.
Proof.
  split.
  - intros C s. apply gen_cut with (s:=Bot); auto.
  - auto.
Qed.



Lemma gen_imp (D: DerivationType): CharImp gen.
Proof.
  split.
  - intros C. apply gen_cut with (s:=Imp s t).  eauto using genW. apply genIL with s t;  auto; try apply genA;  auto.  
  - auto.
Qed.


Lemma gen_and (Dt: DerivationType): CharAnd gen.
Proof.
  split.
  - intros C u D. apply gen_cut with (s:=And s t). auto.
    apply genAL with (s:=s) (t:=t); auto. apply (genW D). firstorder eauto 6.
  - intros H.  apply genAR; (apply H; apply genA; firstorder eauto).   
Qed.

Lemma gen_and_both (Dt: DerivationType) A s t: gen A (And s t) -> gen A s /\ gen A t.
Proof.
  intros C. destruct (gen_and Dt A s t) as [H _]. pose (K:=H C).
  split; apply K; auto. apply genA; firstorder eauto.  apply genA; firstorder eauto. 
Qed.

Lemma gen_or (Dt: DerivationType): CharOr gen.
Proof.
  split.
  - intros C u D E. apply gen_cut with (s:=Or s t). auto.
    apply genOL with (s:=s) (t:=t). auto.
    + apply (genW D); auto.
    + apply (genW E); auto.
  - firstorder eauto. apply H. apply genOR1. apply genA; auto.   apply genOR2. apply genA; auto.   
Qed.

Lemma nd2gen A s (D: DerivationType) :  nd A s -> gen A s.
Proof.
  intro.
  induction H; firstorder eauto.
  - apply genA. auto.
  - apply gen_fal.  auto.
  - apply gen_cut with s; auto. apply gen_imp.  auto. 
  - apply gen_cut with (K (s ⊃ t)). auto.  apply genIR. apply genKI. simpl unK.
    apply genIL with s t. eauto. all: apply genA; auto. 
  - apply genKI.  apply genW with Γ; eauto. intros a Ha. apply unK_in_iff; eauto.  
  - apply gen_and with s t.  auto. apply genA; eauto. 
  -  apply gen_and with s t.  auto. apply genA; eauto.
  - apply gen_cut with (s ∨ t).  auto. apply genOL with s t. auto.
    apply gen_cut with (s ⊃ q). eauto using genW.  apply genIL with s q; auto; (try apply genA; eauto).
    apply gen_cut with (t ⊃ q). eauto using genW.  apply genIL with t q; auto; (try apply genA; eauto).
  - apply genIR. apply gen_cut with (s := K s). eauto using genW. apply genKB.  apply genKI.  simpl unK.
    apply genIL with s ⊥. all:  firstorder eauto  using genA. apply genA; auto. 
Qed.     

Lemma ndgen_iff A s (D: DerivationType): nd A s <-> gen A s.
Proof.
  split; auto using gen2nd, nd2gen.
Qed.

(** ** Disjunction Property *)
Section DisjunctionProperty.
  Lemma disjunction_SC A B {D: DerivationType}: gen [] (A ∨ B) -> gen [] A \/ gen [] B.  
  Proof.
    intro. dependent induction H; firstorder eauto.
  Qed.

  Lemma disjunction_ND A B {D: DerivationType}: nd [] (A ∨ B) -> nd [] A \/ nd [] B.
  Proof.
    repeat rewrite ndgen_iff. apply disjunction_SC.
  Qed.   
End DisjunctionProperty.


(** * Decidability of IEL *)

(** ** Subformulas  *)

Definition sf_closed (A : context) : Prop :=
  forall u, u el A -> match u with
                      | Imp s t | And s t | Or s t => s el A /\ t el A
                      | K s => s el A
                      | _ => True
                      end.
Lemma sf_closed_app A B:
  sf_closed A -> sf_closed B -> sf_closed (A ++ B).
Proof.
  intros.
  intros u Hu.
  apply in_app_iff in Hu. destruct Hu.
  specialize (H u). destruct u; firstorder eauto.
  specialize (H0 u). destruct u; firstorder eauto.
Qed.

Lemma sf_closed_cons u s t A :
  (u = Imp s t \/ u = And s t \/ u = Or s t \/ u = K s  ) ->
  s el A -> t el A -> sf_closed A -> sf_closed (u :: A).
Proof.
  intros [C|[C|C]]; subst; intros D E F [s' | s' t' |s' t' |s' t' | |n  ] G;  auto;
    (destruct G as [G|G]; try inv G; try( eauto;
                                          apply F in G; destruct G; auto)).
  all: try(right; specialize (F (K s') G);  auto). all:  destruct C as [C|C]; inversion C. auto.  split; right; auto.
  
Qed.


Fixpoint scl' (s : form) : context :=
  s :: match s with
       | Imp u v | And u v | Or u v => scl' u ++ scl' v
       | K s => scl' s 
       | _ => nil
       end.

Lemma scl'_in s: s el scl' s.
Proof. destruct s; simpl; auto. Qed.

Lemma scl'_closed s: sf_closed (scl' s).
Proof. 
  induction s; simpl; auto.
  - intros u [A | A].
    + inversion A. auto using scl'_in, sf_closed_app.
    +   destruct u; firstorder eauto.  
  - apply sf_closed_cons with (s:=s1) (t:=s2);
      auto using scl'_in, sf_closed_app.
  - apply sf_closed_cons with (s:=s1) (t:=s2);
      auto using scl'_in, sf_closed_app.
  - apply sf_closed_cons with (s:=s1) (t:=s2);
      auto using scl'_in, sf_closed_app.
  -  intros u [A|A]. inv A.    auto using scl'_in, sf_closed_app. destruct u; firstorder eauto.   
  - intros u [A|A]. inv A.    auto using scl'_in, sf_closed_app. destruct u; firstorder eauto.   
    
Qed.

Fixpoint scl (A : context) : context :=
  match A with
  | nil => nil
  | s :: A' => scl' s ++ scl A'
  end.

Lemma scl_incl' A: A <<= scl A.
Proof. induction A as [|s A]; simpl; auto using scl'_in. Qed.

Lemma scl_incl A B: A <<= B -> A <<= scl B.
Proof. intros E. setoid_rewrite E. apply scl_incl'. Qed.

Lemma scl_closed A: sf_closed (scl A).
Proof.
  induction A as [|s A]; simpl. now auto.
  auto using scl'_closed, sf_closed_app.
Qed.


Definition goal := prod (context) form.

(** ** Step Function *)

Instance goal_eq_dec (gamma delta: goal):
  dec (gamma = delta).
Proof. unfold dec. repeat decide equality. Qed.
Section Decidability.
  Variable A0 : context.
  Variable s0 : form.
  Variable D: DerivationType. 
  Instance feqd: eq_dec form.
  Proof. intros x y.  apply form_eq_dec. Qed.

  Definition U := scl (s0::(K ⊥)::A0).
  Definition U_sfc : sf_closed U := @scl_closed _.
  Definition Gamma := list_prod (power U) U.
  
  Definition step (Delta : list goal) (gamma : goal) : Prop :=
    let (A,u) := gamma in
    (match u with
     | Var _ => u el A
     | Imp s t => (rep (s::A) U, t) el Delta
     | And s t => (A, s) el Delta /\ (A, t) el Delta
     | Or s t => (A, s) el Delta \/ (A, t) el Delta
     | K s => (rep (unK A) U, s) el Delta
     | _ => False
     end)
    \/
    ( exists v, v el A /\
                match v with
                | Bot => True
                | Imp s t => (A, s) el Delta /\ (rep (t::A) U, u) el Delta
                | And s t => (rep (s::t::A) U, u) el Delta
                | Or s t => (rep (s::A) U, u) el Delta /\ (rep (t::A) U, u) el Delta
                | _ => False
                end)
    \/ (match D with normal => ((rep A U, K ⊥) el Delta)    | _ => False end)  
  . 

  Instance step_dec Delta gamma :
    dec (step Delta gamma).
  Proof.
    destruct gamma as [A u]; simpl.
    apply or_dec.
    - destruct u as [x| x | |s t| | s]; auto 10. 
    - apply or_dec. apply list_exists_dec.  intro x. destruct x; auto.
      destruct D; auto. 
  Defined.

  Definition stepb (Delta : list goal) (gamma : goal) := dec2bool (step_dec Delta gamma).
  
  Lemma stepb_reflect D1 γ: stepb D1 γ = true <-> step D1 γ.
  Proof.
    split;  eauto. intro. 
    apply Dec_reflect in H.   auto.
    apply Dec_reflect.
  Qed.
  
  Definition Lambda  :=
    (FCI.C stepb Gamma).
  Lemma lambda_closure gamma:
    gamma el Gamma -> stepb Lambda gamma -> gamma el Lambda.
  Proof.  apply FCI.closure.  Qed.

  Lemma lambda_ind (p : goal -> Prop) :
    (forall Delta gamma, inclp Delta p -> gamma el Gamma
                         -> stepb Delta gamma -> p gamma)
    -> inclp Lambda p.
  Proof. apply FCI.ind. Qed.

  Lemma gen_lambda A u :
    A <<= U -> u el U ->  @gen D A u -> (rep A U,u) el Lambda.
  Proof.
    cut (A <<= U -> u el U ->  forall D', D' = D -> @gen D' A u -> (rep A U,u) el Lambda). 
    eauto. 
    intros D1 D2 D' Hd' E.
    
    induction E as [A x  D' F|A u  D' F|A s t D' F IHF|A s t u D' F G IHG H IHH|
                    A s t u D' F G IHG|A s t D' F IHF G IHG|
                    A s t u D' F G IHG H IHH|A s t D' F IHF|A s t D' F IHF|A D' s|D'   ];
      (apply lambda_closure; [now eauto using in_prod, rep_power|]); simpl; apply stepb_reflect. 
    -  left. auto using rep_in.
    -  right. left.    exists Bot.  firstorder auto using rep_in.
    - apply U_sfc in D2 as [D2 D3].
      left. rewrite rep_eq with (B := s::A); auto.
      setoid_rewrite rep_equi; auto.
    - assert (K := F). apply D1 in K.
      apply U_sfc in K as [K1 K2].
      right. left.  exists (Imp s t); repeat split; auto using rep_in.
      rewrite rep_eq with (B := t::A); auto.
      setoid_rewrite rep_equi; auto.
    - assert (K := F). apply D1 in K.
      apply U_sfc in K as [K1 K2].
      right. left.   exists (And s t); repeat split; auto using rep_in.
      rewrite rep_eq with (B := s::t::A); auto.
      setoid_rewrite rep_equi; auto.
    - apply U_sfc in D2 as [D2 D3]. left. auto.
    - assert (K := F). apply D1 in K.
      apply U_sfc in K as [K1 K2].
      right. left.  exists (Or s t); repeat split; auto using rep_in.
      + rewrite rep_eq with (B := s::A); auto.
        setoid_rewrite rep_equi; auto.
      + rewrite rep_eq with (B := t::A); auto.
        setoid_rewrite rep_equi; auto.
    - apply U_sfc in D2 as [D2 D3]. left. auto.
    - apply U_sfc in D2 as [D2 D3]. left. auto.
    - left. assert (rep (unK (rep A U)) U = rep (unK A) U).  apply rep_eq. {
        split.
        intros x Hx. apply unK_in_iff in Hx. apply unK_in_iff.  destruct Hx. left. apply rep_incl with U.  auto. right. eauto using rep_incl. apply rep_incl with U. auto.
        intros x Hx.  apply unK_in_iff. apply unK_in_iff in Hx.   destruct Hx. left. apply rep_in.  auto.  auto.  right; eauto using rep_in.
        
      } (* Use A <<= u + U scl_closed *)   setoid_rewrite H.
      apply IHE.
      intros x Hx. apply unK_in_iff in Hx. destruct Hx. auto. assert (K x el U).  apply D1. auto. 
      apply (U_sfc) in H1.  auto. apply (U_sfc) in D2.  auto. auto. 
      
    -  right. right. rewrite<- Hd'.  rewrite rep_idempotent.  apply IHE.  auto. unfold U. simpl scl. apply in_app_iff.  right.  left. reflexivity.   
       auto. 
  Qed.

  Lemma lambda_gen A u :
    (A,u) el Lambda -> gen A u.
  Proof.
    revert A u.
    cut (inclp Lambda (fun gamma => gen (fst gamma) (snd gamma))).
    { intros E A u. apply E. }
    apply lambda_ind. intros Delta [A u] E F G; simpl.
    assert (E': forall B v, (B,v) el Delta -> @gen D B v).
    { intros B v. apply E. } clear E. apply stepb_reflect in G. 
    destruct G.
    - destruct u;intuition;  eauto using genW, rep_incl.        
    - destruct H. destruct H.  destruct x. 
      + tauto. 
      + destruct H. destruct H0.  apply genIL with x1 x2; auto.   auto.   intuition; eauto using genW, rep_incl, E'.
      +   intuition; eauto using genW, rep_incl.
      +    destruct H. destruct H0.    assert (K1: gen (rep (x1::A) U) u) by intuition.
           assert (K2: gen (rep (x2::A) U) u) by intuition.  apply genOL with x1 x2;  intuition; eauto using genW, rep_incl.
      +  apply genF.    destruct H. auto.
      +  intuition; eauto using genW, rep_incl, E'.  
      +  destruct D eqn:Deq. auto. apply genKB.  apply genW with (rep  A U).   apply E'.   auto.  apply rep_incl. 
         
  Qed.


  Lemma dec_prop_iff (X Y : Prop) : 	  (X <-> Y) -> dec X -> dec Y.
  Proof.  intros x y. hnf. destruct y. left. tauto. right. tauto.  Qed. 

  Lemma dec_prop_iff2 (X Y : Prop) : 	  (X <-> Y) -> dec Y -> dec X.
  Proof.  intros x y. hnf. destruct y. left. tauto. right. tauto.  Qed. 


  Theorem ielg_dec: dec (nd A0 s0).
  Proof.
    apply (dec_prop_iff) with (X := gen A0 s0).
    split; apply ndgen_iff. 
    assert (A1: A0 <<= U).
    { apply scl_incl; auto. }
    assert (A2: s0 el U).
    { apply scl_incl'; auto. }
    decide (((rep A0 U), s0) el Lambda) as [E|E].
    + left. apply genW with (rep A0 U).   apply lambda_gen.  auto.
      apply rep_incl.
    +  right.  intro.  apply E. apply gen_lambda.  auto. auto. auto.
  Defined.
End  Decidability.
