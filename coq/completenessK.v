Require Import  List PslBase.Lists.BaseLists.
Require Import PslBase.Base.
Require Import Coq.Program.Equality forms decidabilityK.


Import ListNotations.

(* We define an nd system for K *)

Inductive ndc : list form -> form -> Prop :=
| ndcA A s:      s el A -> ndc A s
| ndcC A s:      ndc ((¬ s) :: A) Bot -> ndc A s
| ndcII A s t:   ndc (s::A) t -> ndc A (Imp s t)
| ndcIE A s t:   ndc A (Imp s t) -> ndc A s -> ndc A t
| ndcAI A s t:   ndc A s -> ndc A t -> ndc A (And s t)
| ndcAE A s t u: ndc A (And s t) -> ndc (s::t::A) u -> ndc A u
| ndcOIL A s t:  ndc A s -> ndc A (Or s t)
| ndcOIR A s t:  ndc A t -> ndc A (Or s t)
| ndcOE A s t u: ndc A (Or s t) -> ndc (s::A) u -> ndc (t::A) u -> ndc A u
| ndcNec A s : ndc [] s -> ndc A (K s)
| ndcKD A s t: ndc A (K(s ⊃ t)) -> ndc A ((K s) ⊃ (K t)) .

Hint Constructors ndc.
Section EntailmentRelationProperties.

  Variable F: Type.
  Variable E: list F -> F -> Prop.

  (*** Generic Structural Properties ***)
  Definition Monotonicity : Prop :=
    forall A A' s, A <<= A' -> E A s -> E A' s.

  Definition Reflexivity : Prop :=
    forall A s, s el A -> E A s.

  Definition Cut : Prop :=
    forall A s t, E A s -> E (s::A) t -> E A t.

  Definition Consistency : Prop :=
    exists s:F, ~E nil s.

End EntailmentRelationProperties.

(*** Logical Properties ***)

Definition CharFal (E: context -> form -> Prop) : Prop :=
  forall A, E A Bot <-> forall s, E A s.

Definition CharImp (E: context -> form -> Prop) : Prop :=
  forall A s t, E A (Imp s t) <-> E (s::A) t.

Definition CharAnd (E: context -> form -> Prop) : Prop :=
  forall A s t, E A (And s t) <-> forall u, E (s::t::A) u -> E A u.

Definition CharOr (E: context -> form -> Prop) : Prop :=
  forall A s t, E A (Or s t) <-> forall u, E (s::A) u -> E (t::A) u -> E A u.


Lemma ndc_refl: forall A s, s el A -> ndc A s.
Proof. intros A s. auto. Qed.

Lemma ndc_mono: Monotonicity ndc.
Proof.
  intros A A' s C D. revert C. revert A'. induction D; intros A' C; auto.
  - apply ndcIE with (s:=s); auto.
  - apply ndcAE with (s:=s) (t:=t); try apply IHD2; auto.
  - apply ndcOE with (s:=s) (t:=t); auto.
Qed.

Lemma ndcW1 A s t: ndc A s -> ndc (t::A) s.
Proof. apply ndc_mono; auto. Qed.

Lemma ndcW A B s: ndc A s -> A <<= B -> ndc B s.
Proof. intros C D. apply ndc_mono with (A:=A); auto. Qed.

Lemma ndcE A s: ndc A Bot -> ndc A s.
Proof. intros E. apply ndcC, ndcW1, E. Qed.

Lemma ndc_cut: Cut ndc.
Proof. intros A s t C D. apply ndcIE with (s:=s); auto. Qed.

Lemma ndc_imp: CharImp ndc.
Proof. split; auto.
  intros C. apply ndcIE with (s:=s); auto.
  apply (ndcW C); auto.
Qed.

Lemma ndc_fal: CharFal ndc.
Proof. split; auto.
  intros C s. apply ndcC. apply (ndcW C); auto.
Qed.

Lemma ndc_and: CharAnd ndc.
Proof. split; auto. intros C u. apply ndcAE. auto. Qed.

Lemma ndc_or: CharOr ndc.
Proof. split; auto. intros C u. apply ndcOE. auto. Qed.



Definition neg Γ := List.map (fun x => ¬ x) Γ. 

Lemma neg_in B s: s el B -> (¬ s) el neg B.
Proof.
  intro H. unfold neg. apply in_map_iff. eauto.
Qed.   

Lemma neg_incl B B': B <<= B' -> neg B <<= neg B'.
Proof.
  intro H. unfold neg. apply incl_map.  auto.
Qed.
Print toolbox.remNotK. 
Lemma admissibility_K A s: ndc (toolbox.remNotK A) s -> ndc A (K s). 
Proof.
  revert s. induction A.  simpl; auto.
  intros s H1.
  destruct a; auto.
  - apply ndc_imp. apply ndcKD. apply IHA. apply ndc_imp. simpl toolbox.remNotK in H1.
    apply H1. 
  -  apply ndcW with A.  apply IHA;   auto.  eauto. 
  -   apply ndcW with A.  apply IHA;   auto.  eauto.
  -    apply ndcW with A.  apply IHA;   auto.  eauto.
  -    apply ndcW with A.  apply IHA;   auto.  eauto.    
Qed. 
Lemma gk3c_ndcG A B:
  gk3c A B -> ndc (A ++ neg B) Bot.
Proof.
  intro E. induction E; auto.
  - apply ndcIE with (s:=Var x) (t:=Bot); apply ndcA; auto.
    apply in_app_iff. right. apply neg_in, H0.
  - apply ndc_cut with (s:=t); auto.
    apply ndcIE with (s:=s) (t:=t); auto.
    apply ndcC. apply (ndcW IHE1);  simpl; auto.
  - apply ndcIE with (s:=Imp s t) (t:=Bot).
    + apply ndcA. apply in_app_iff. right. apply neg_in. auto.
    + apply ndcII. apply ndcC. apply (ndcW IHE); simpl; auto. auto 7. 
  - apply ndcAE with (s:=s) (t:=t); auto.
  - apply ndcIE with (s:=And s t) (t:=Bot).
    + apply ndcA. apply in_app_iff. right. apply neg_in. auto.
    + apply ndcAI; apply ndcC.
      * apply (ndcW IHE1); simpl; auto.
      * apply (ndcW IHE2); simpl; auto.
  - apply ndcOE with (s:=s) (t:=t); auto.
  - apply ndc_cut with (s:=¬ t).
    + apply ndcII. apply ndcIE with (s:=Or s t) (t:=Bot); auto.
      apply ndcA. right. apply in_app_iff. right. apply neg_in. auto.
    + apply ndc_cut with (s:=¬ s).
      * apply ndcII. apply ndcIE with (s:=Or s t) (t:=Bot); auto.
        apply ndcA. right. right. apply in_app_iff. right. apply neg_in. auto.
      * apply (ndcW IHE); simpl; auto. intros w G.
        apply in_app_iff in G as [G|[G|[G|G]]]; subst; auto.
  - simpl neg in IHE.
    enough (ndc (A ++ neg B) (K s)). apply ndcIE with (K s).  apply ndcA; eauto. apply in_app_iff; right; apply neg_in; eauto.  auto.
    apply admissibility_K. apply ndcC.  apply (ndcW IHE); auto. intros a Ha.  apply in_app_iff in Ha.  destruct Ha; eauto. right.   apply toolbox.remNotK_in_iff.  apply toolbox.remNotK_in_iff in H0.   apply in_app_iff; eauto.  firstorder. 
Qed.

Lemma gk3c_ndc A s:
  gk3c A [s] -> ndc A s.
Proof.
  intros E. apply gk3c_ndcG in E.
  apply ndcC. apply (ndcW E); simpl; auto.
Qed.

(** From ND to SC **)

Lemma gk3cCut A B A' B' s: gk3c A (s::B) -> gk3c (s::A') B' -> gk3c (A++A') (B++B'). 
Proof.
  intros H H0. apply  gk3_height in H. apply gk3_height in H0. 
  destruct H as (h1 &  H1), H0  as (h2 & H2).
  eapply cutElimination.
  apply gk3chW with A (s::B).  eapply H1.  auto. auto.
  apply gk3chW with (s::A') (B'). eapply H2. firstorder.  firstorder.
  reflexivity.
  reflexivity. 
Qed.

Lemma gk3cCutSimple A B  s: gk3c A (s::B) -> gk3c (s::A) B -> gk3c (A) (B). 

  intros H H0. apply  gk3_height in H. apply gk3_height in H0. 
  destruct H as (h1 &  H1), H0  as (h2 & H2).
  eapply cutElimination.
  eapply H1. eapply H2. 
  reflexivity. reflexivity.
Qed.

Lemma gk3cFL A B s: gk3c A (s::B) -> gk3c ((¬ s)::A) B.
Proof. intros E. apply gk3cIL with (s:=s) (t:=Bot); eauto.  eauto using gk3cW. apply gk3cF.  auto.  Qed.

Lemma gk3cFR A B s: gk3c (s::A) B -> gk3c A ((¬ s)::B).
Proof. intros E. apply gk3cIR with (s:=s) (t:=Bot); eauto using gk3cW. Qed.

Lemma gk3cDNR A B s: gk3c A (s::B) -> gk3c A ((¬ (¬ s))::B).
Proof.
  intros E. apply gk3cFR. apply gk3cIL with (s:=s) (t:=Bot). eauto.  eauto using gk3cW. apply gk3cF; eauto. 
Qed.

Lemma gk3cDNL A B s: gk3c (s::A) B -> gk3c ((¬ (¬ s))::A) B.
Proof. intros E. apply gk3cFL, gk3cFR, E. Qed.
Hint Constructors gk3c. 
Lemma gk3cRW A B: gk3c A B -> forall B', B <<= B' -> gk3c A B'.
Proof. intros. apply gk3cW with A B; eauto.   Qed.

Lemma gk3c_emptyR A: ~ gk3c A [Bot] -> ~ gk3c A [].
Proof.
  intros E F. remember [] as B. induction F; subst; eauto using gk3cRW.
Qed.

  Lemma gk3cCutE A B: gk3c A [Bot] -> gk3c A B.
  Proof.
    intros E. apply gk3cW with (A:=A ++ []) (B:= [] ++ B); auto.
    eapply gk3cCut.  apply E.  apply gk3cF.  eauto. 
  Qed.

    Lemma gk3cFL_invCut A B s:
    gk3c ((¬ s)::A) B -> gk3c A (s::B).
    Proof.
          intros E. apply gk3cW with (A:=A ++ A) (B:=(s::B) ++ B); auto.
          
          eapply gk3cCut with (A := A) (s := ¬ s) (B := (s::B)) (B' := B) (A' := A).
          2: auto.
    apply gk3cFR. apply gk3cA with s; auto. 
  Qed.

    Lemma gk3cFR_invCut A B s:
      gk3c A ((¬ s)::B) -> gk3c (s::A) B.
    Proof.
          intros E. apply gk3cW with (A:=A ++ (s::A)) (B:=B ++ B); auto.
          apply (@gk3cCut A B (s::A) B (¬ s)) ; auto.
          apply gk3cFL. apply gk3cA with s; auto. 
    Qed.


      Lemma gk3cDNR_invCut A B s:
    gk3c A ((¬ (¬ s))::B) -> gk3c A (s::B).
  Proof.
    intros E. apply gk3cW with (A:=A ++ A) (B:=B ++ s :: B); auto.
    apply (@gk3cCut A B A (s::B) (¬ (¬ s)) E).
    apply gk3cDNL.  apply gk3cA with s; auto.
  Qed.

  Lemma gk3cDNL_invCut A B s:
    gk3c ((¬ (¬ s))::A) B -> gk3c (s::A) B.
  Proof.
    intros E.
    apply gk3cW with (A:= (s :: A) ++ A) (B:=B ++ B); auto.
    apply (@gk3cCut (s::A) B A B (¬ (¬ s))). 2: eauto using gk3cW.
    apply gk3cDNR. apply gk3cA with s; auto.
  Qed.

  Example gk3c_Peirce_Cut s t: gk3c [] [(Imp (Imp (Imp s t) s) s)].
  Proof.
    apply gk3cIR with (s:=Imp (Imp s t) s) (t:=s); auto.
    apply gk3cRW with (B:=[s]); auto.
    apply (gk3cDNR_invCut).
    apply gk3cIL with (s:=Imp s t) (t:=s); auto.
    - apply gk3cIR with (s:=s) (t:=t); auto.
      apply gk3cW with (A:=[s; Imp (Imp s t) s]) (B:=[¬ (¬ s); t; Imp s t]);
      auto. apply gk3cDNR. apply gk3cA with s; auto.
    - apply gk3cDNR. apply gk3cA with s; auto.
  Qed.

  (* Equivalence with natural deduction, assuming Cut *)
  Lemma ndc_gk3cCut A s:
    ndc A s -> gk3c A [s].
  Proof.
    intros E. induction E; eauto 4 using gk3cW.
    - apply gk3cA with s; auto.
    - apply gk3cFR in IHE. apply (gk3cDNR_invCut) in IHE.
      apply gk3cW with (A:=A ++ []) (B:=[s] ++ [s]); auto.
      apply (@gk3cCut A [s] [] [s] Bot); auto.
      apply gk3cW with (A:=A) (B:=[s;Bot]); auto.
    - apply gk3cW with (A:=A ++ A) (B:=[] ++ [t]); auto.
      apply (@gk3cCut A [] A [t] s); auto.
      apply gk3cW with (A:=(s::A) ++ [s]) (B:=[t]); auto.
      apply (@gk3cCut (s::A) [] [s] [t] (Imp s t)).  apply gk3cW with A [s ⊃ t]; eauto.
      apply gk3cIL with s t.  auto. apply gk3cA with s; eauto. apply gk3cA with t; eauto.  
    - apply gk3cAR with (s:=s) (t:=t); eauto.  apply gk3cW with A [s]; auto. apply gk3cW with A [t]; auto. 
    - apply gk3cW with (A:=A ++ A) (B:=[u]); auto.
      apply (@gk3cCut A [] A [u] (And s t)); auto.
      apply gk3cAL with (s:=s) (t:=t); eauto using gk3cW, incl_shift.
    - apply gk3cOR with s t.    auto. apply gk3cW with A [t]; auto.
    - apply gk3cW with (A:=A ++ A) (B:=[u]); auto.
      apply (@gk3cCut A [] A [u] (Or s t)); auto.
      apply gk3cOL with (s:=s) (t:=t); eauto. apply gk3cW with (s :: A) [u]; auto.
      apply gk3cW with (t :: A) [u]; auto.
    - apply gk3cIR with (K s) (K t).  auto. apply gk3cCutSimple with (K (s ⊃ t)).
      apply gk3cW with A  [K (s ⊃ t)]; auto. 
      apply gk3cKI with t.  auto. simpl toolbox.remNotK. apply gk3cIL with s t; auto.
      apply gk3cA with s; auto.
      apply gk3cA with t; auto. 
  Qed.

  Theorem gk3cCut_iff_ndc A s:
    gk3c A [s] <-> ndc A s.
  Proof. split.
    - apply gk3c_ndc.
    - apply ndc_gk3cCut.
  Qed.

  Lemma ndc_dec Γ A: {ndc Γ A} + {~(ndc Γ A)}.
  Proof.
    destruct (gk3c_dec Γ [A]).
    - left. apply gk3cCut_iff_ndc; auto.
    - right. intro. apply n.  apply<- gk3cCut_iff_ndc; auto.
  Qed.

  Print Assumptions ndc_dec. 


(** Kripke Models for K **)
Section Models.
    Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            acc: world -> world -> Prop;
                            val: world -> valuation;
                            }.
       Fixpoint evalK {M: KripkeModel} (s: form) : (world) -> Prop := 
    match s with 
    | (K x)  => (fun y => forall r, ((acc y r) -> evalK x r))
    | Bot    => (fun x => False)
    | Var y  => (fun x => val x y)
    | x ⊃ y  => (fun z => (evalK x z) -> (evalK y z))
    | x ∨ y => (fun z => (evalK x z) \/ (evalK y z))
    | x ∧ y => (fun z => (evalK x z) /\ (evalK y z))            
    end.

    Definition evalK' {M: KripkeModel} (Γ: context) :=
    fun w => forall s, (In s Γ) -> @evalK M s w.  

    Definition entails Γ φ := 
      forall (M : KripkeModel), ((forall w,evalK' Γ w -> @evalK M φ w)).

End Models.

Require Import decidability toolbox. 
Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)

  Variable A0 : context.
  Variable s0 : form.
  Fixpoint negateAll (l: list form) :=
    match l with nil => [] | A::xr => A::(¬ A)::negateAll xr end.

  Lemma negateAll_in_iff Γ A: A el (negateAll Γ) <-> (A el Γ \/ (exists F, (A = ¬F) /\ (F el Γ))).  
  Proof.
    induction Γ; firstorder eauto.  simpl negateAll. subst x.  subst A.  firstorder. 
  Qed.   
  Definition U' :=  (scl (s0::⊥::A0)).
  Definition U'_sfc : sf_closed U' := @scl_closed _.

    Record mcTheory := mkmcTheory {
                         T: list form;
                         Tsubs: (T el (power (negateAll U'))) ;
                         Tcons: ~(ndc T ⊥);
                         Tmax: forall A, A el (U') -> A el T \/ (¬ A) el T;
                         TUPrime: forall A B,  (A ∨ B) el T -> A el T \/ B el T;
                         }.

    Lemma    Tdedclos {m: mcTheory}: forall A, A el (negateAll  U') ->  ndc (T m) A -> A el (T m). 
    Proof.
      intros.
      apply negateAll_in_iff in H.  destruct H. 
      + destruct (Tmax m H); auto.
      exfalso. eapply Tcons. eauto.
      +  destruct H as (A' & HA'). destruct HA'.
         destruct (Tmax m H1); auto.
         * subst A. decide ((A' ⊃ ⊥) el (T m)); eauto.
           exfalso. eapply Tcons. eauto. 
         *   subst A. decide ((A') el (T m)); eauto.
   Qed.    
    Definition valuationMKT (A: mcTheory) (a: nat) := (Var a) el (T A).
    
  Definition subsetVerif (A B:mcTheory) := forall x, In (K x) (T A) -> In x (T B). 

    Instance canonical: (KripkeModel).
  Proof.
    eapply mkKripkeModel.
    apply subsetVerif. 
    apply valuationMKT. 

   Defined. 

  
  
  (** Try to establish a truth lemma **)

    Definition single_extend (Ω: context) (A: form) (a: form) :=
    if (@ndc_dec (a::Ω) A) then ((¬ a)::Ω) else (a::Ω). 

    Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
    Proof. 
      intros a Ha.  unfold single_extend. destruct (ndc_dec (B :: Ω) A); eauto.
    Qed.

    Lemma extend_two_possibilites Γ A B:
    ((single_extend Γ A B) === ((¬ B)::Γ) /\ ndc (B::Γ) A) \/   (single_extend Γ A B) === (B::Γ) /\ ~(ndc (B::Γ) A). 
  Proof.
    destruct (ndc_dec (B::Γ) A) eqn:id.
    - left. split; try tauto.
      split.
      + intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      + unfold single_extend. rewrite id; auto.
    - right.      split; auto. split.
      +  intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      +  unfold single_extend. rewrite id; auto.
  Qed.        
  Lemma hil_exfalso Γ: ndc Γ Bot -> (forall A, ndc Γ A).    
  Proof.
    intros H A. 
    apply ndcIE with ⊥; eauto. 
  Qed.   

    Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
    match Γ with
      nil => Ω
    | (a::Γ') =>
      single_extend (extend Ω A Γ') A a  end.

 Lemma a_does_not_matter Γ a b: ndc (a::Γ) b -> ndc ((¬ a)::Γ) b -> ndc Γ b.    
 Proof.
   intros. apply ndcOE with a (¬ a); auto.  apply ndcC. apply ndcIE with (a ∨ (a ⊃ ⊥)). apply ndcA; auto. apply ndcOIR.
   apply ndcII. apply ndcIE with (a ∨ (a ⊃ ⊥)). apply ndcA; auto. apply ndcOIL. apply ndcA. auto. 
 Qed.   

 Lemma extend_does_not_derive Ω A Γ: ~(ndc Ω A) -> ~(ndc (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (ndc_dec (a :: extend Ω A Γ) A) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di.   intro. apply (IHΓ Ω).  apply H.  apply a_does_not_matter with a; auto. (* Use that a \/ ~a is derived *) 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

    Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (ndc_dec (a :: extend Ω A Γ) A); eauto.                          
  Qed.

  Lemma extend_adds_all Ω Γ A B: B el Γ -> B el (extend Ω A Γ) \/ (¬ B) el (extend Ω A Γ).
  Proof.
    intros H.
    dependent induction Γ; auto.
    destruct H.
    +  destruct (ndc_dec (a :: extend Ω A Γ) A) eqn:di;  simpl extend; unfold single_extend; rewrite di;  subst a ; auto.
    +  specialize (IHΓ A B H).   destruct IHΓ.
       * left. unfold extend. apply single_extend_subcontext.  apply H0.
       *  right.   unfold extend. apply single_extend_subcontext.  apply H0.
  Qed.
  
    Lemma extend_locally_dclosed Γ Ω A B: ~(ndc Ω A) -> (ndc (extend Ω A Γ) (B)) -> B el Γ ->  B el (extend Ω A Γ).
  Proof.
    revert Ω B. intros.
    destruct (@extend_adds_all Ω Γ A B H1).
    - auto.
    -   apply extend_does_not_derive with (Γ := Γ) in H.  exfalso. apply H. apply hil_exfalso. apply ndcIE with B.  apply ndcA. auto. auto.
  Qed.
  
    Lemma extend_does_not_derive_imp Ω Γ A B:
    ~(ndc Ω A) -> B el Γ -> ~(ndc (extend Ω A Γ) B) -> (ndc (extend Ω A Γ) (B ⊃ A)).
  Proof.
    intros H H1. revert H. revert Ω.
    induction Γ.
    - intros.  eauto.
    - intros.  destruct H1.
      + subst a. simpl.
        destruct (extend_two_possibilites (extend Ω A Γ) A B) as [(E1 & E2) | (E1 & E2)].
        * apply ndcW with (extend Ω A Γ). eauto.  destruct E1; auto. apply single_extend_subcontext. 
        * exfalso.   apply H0. simpl extend; fold extend. apply ndcW with ( B :: extend Ω A Γ).  apply ndcA. auto. destruct E1; auto. 
      + assert (~(ndc (extend Ω A Γ) B)).  intro. apply H0. apply ndcW with (extend Ω A Γ). auto. apply single_extend_subcontext. 
        specialize (IHΓ H1 (Ω) H H2). 
        simpl extend.  apply ndcW with (extend Ω A Γ). auto.  apply single_extend_subcontext. 
  Qed.   


    Lemma extend_locally_prime Γ Ω A B C:  ~(ndc Ω A) -> (ndc (extend Ω A Γ) (B ∨ C)) -> B el Γ -> C el Γ -> B el (extend Ω A Γ) \/ C el (extend Ω A Γ).
  Proof.
    intros. decide (B el (extend Ω A Γ)).  auto. decide (C el (extend Ω A Γ)).  auto. assert (~(ndc (extend Ω A Γ) (B ∨ C))).
    assert (~ndc (extend Ω A Γ) B). intro. apply (extend_locally_dclosed H) in H3. congruence. auto.
    assert (~ (ndc (extend Ω A Γ)  C)). intro. apply (extend_locally_dclosed H) in H4. congruence. auto. intro. specialize (@extend_does_not_derive Ω A Γ  H ). intro.  apply H6. apply ndcOE with B C. auto. apply ndc_imp.   apply extend_does_not_derive_imp.  auto.  auto.  auto.
apply ndc_imp.   apply extend_does_not_derive_imp.  auto.  auto.  auto.
    congruence. 
  Qed.

  Lemma lindenbaum_subset_helper Γ A:  extend Γ A U' <<= (Γ ++ negateAll U').
  Proof.
        revert Γ.  induction U'.
        - eauto. 
        -  intros Γ f Hf.
           unfold extend in Hf. fold extend in Hf.  unfold single_extend at 1 in Hf.
           destruct (ndc_dec (a :: (extend Γ A l)) A) eqn:di.
           + destruct Hf.
             * apply in_app_iff. right.  simpl negateAll. firstorder.
             * specialize (IHl Γ f H).  apply in_app_iff in IHl; destruct IHl; firstorder. apply in_app_iff; right; simpl negateAll.   firstorder.
           +      destruct Hf.
             * apply in_app_iff. right.  simpl negateAll. firstorder.
             * specialize (IHl Γ f H).  apply in_app_iff in IHl; destruct IHl; firstorder. apply in_app_iff; right; simpl negateAll.   firstorder.
  Qed.

  Lemma lindenbaum_subset  Γ A: Γ <<= U' ->  extend Γ A U' <<= (negateAll U').
  Proof.
    intros H. specialize (lindenbaum_subset_helper).  intros H1.
    intros a Ha.  specialize (H1 Γ A).  specialize (H1 a). specialize (H1 Ha).      apply in_app_iff in H1.   destruct H1.
    - apply negateAll_in_iff. left. apply H. auto.
    - auto.
  Qed.

    Lemma lindenbaum_subset2  Γ A: Γ <<= (negateAll U') ->  extend Γ A U' <<= (negateAll U').
  Proof.
    intros H. specialize (lindenbaum_subset_helper).  intros H1.
    intros a Ha.  specialize (H1 Γ A).  specialize (H1 a). specialize (H1 Ha).      apply in_app_iff in H1.   destruct H1.
    - apply H.  auto. 
    - auto.
  Qed.     


    Definition Lindenbaum (Γ : list form) (A: form) (H: Γ <<= (negateAll U')) (H': ~(ndc Γ A)) : mcTheory.  
    Proof.
     
    eapply mkmcTheory with (rep (extend Γ A U') (negateAll U')).
    - apply rep_power. 
    - enough (~ ndc (extend Γ A U') ⊥).
      intro. apply H0. eapply ndcW. eapply H1.   apply rep_incl.
      intro. apply extend_does_not_derive with Γ A U' in H'. apply H'. apply hil_exfalso. auto.   
      
    -  intros. rewrite rep_equi. apply extend_adds_all. auto.  apply  lindenbaum_subset2.    auto.
    -  intros. rewrite rep_equi in *. all: try (apply  lindenbaum_subset2;    auto).
       apply extend_locally_prime; auto. all: apply  lindenbaum_subset2 in H0; auto;  apply negateAll_in_iff in H0; destruct H0; try apply U'_sfc in H0;try tauto; try destruct H0; try firstorder; try congruence.
       
  Defined.

     Lemma U'_scl_closed_imp  x y: (x ⊃ y) el  U' -> x el  U' /\ y el U'.
    Proof.
      intro. apply U'_sfc in H. tauto.
    Qed.

     Lemma U'_scl_closed_K  x: (K x) el  U' -> x el  U' .
     Proof.
       intros H % U'_sfc. tauto.
      (* Follows immidieatly by using subformula-closure of U' *)
    Qed.
    
    Lemma negAllKClosed x:  K x el negateAll U' -> x el negateAll U'.
    Proof.
      intros Ha.
      apply negateAll_in_iff in Ha. destruct Ha.
      - apply U'_scl_closed_K in H. apply  negateAll_in_iff.  tauto.
      - destruct H. destruct H.   congruence.
    Qed.

    Lemma negAllImoClosed x1 x2 : (x1 ⊃ x2) el negateAll U' -> x1 el (negateAll U') /\ x2 el (negateAll U').
    Proof.
      intros H.
      apply negateAll_in_iff in H. destruct H. 
      - apply U'_scl_closed_imp in H. repeat rewrite negateAll_in_iff. tauto.   
      - destruct H as (x1' & Hx1 & Hx1').
        inversion Hx1; subst x1' x2.
        split; eauto.
        + apply negateAll_in_iff. auto.
        + apply negateAll_in_iff.  left. unfold U'. apply scl_incl'. auto. 
     Qed.      
  Lemma truth_lemma : forall (x: form), In x (negateAll U') -> forall (t: (@world  canonical)), (evalK x t) <-> x el (T t).
  Proof. 
    intros x Hx.
    induction x.
    - intros w. split.
      decide (K x el (T w)); auto. 
      intro H. exfalso.
      assert (~ ndc (toolbox.remNotK (T w)) x). {
        intro. apply admissibility_K in H0 . apply n. apply Tdedclos. auto.
        auto. 
      }
      assert (exists Δ: mcTheory,  (toolbox.remNotK (T w) <<= (T Δ)) /\ ~(x el (T Δ))).
      assert ( (toolbox.remNotK (T w) <<= negateAll U')) as HS. intros a Ha. apply remNotK_in_iff in Ha. enough (K a el (negateAll U')).
      apply  negAllKClosed. auto. specialize (Tsubs w). intro. apply power_incl in H1.  apply H1. auto.  
      eexists (@Lindenbaum (toolbox.remNotK (T w)) x HS H0 ).
      split.
      +  simpl. rewrite rep_equi. apply extend_subset. apply lindenbaum_subset2.   auto. (* extend_subset *)
      +  intro. eapply extend_does_not_derive. apply H0.   apply ndcA. simpl T in H1.  apply rep_equi in H1. eapply H1. apply lindenbaum_subset2.  auto. 
      +    
      destruct H1 as (Δ & Hd1 & Hd2).
      apply Hd2. apply IHx. apply negAllKClosed.  auto.  apply H.  intros a Ha. apply Hd1. apply remNotK_in_iff.  auto. 
      + intro. intros w' Hw'.
      apply IHx.  apply negAllKClosed. auto. 
      apply Hw'. auto.
    -   intros w. split.
        + intro.  simpl evalK in H. decide (x2 el (T w)). 
          * apply Tdedclos. auto.  rewrite IHx2 in H. apply ndcII. apply ndcA.  auto. apply negAllImoClosed in Hx.   tauto.  
          * decide (x1 el (T w)).
            -- exfalso. apply n. apply IHx2. apply negAllImoClosed in Hx.  tauto. apply H.  apply IHx1.  apply negAllImoClosed in Hx.   tauto. auto. 
            -- apply Tdedclos. auto.  assert (x1 el (U')). {
              apply negateAll_in_iff in Hx; destruct Hx.
              *  apply  U'_scl_closed_imp in H0.  tauto. 
              *   destruct H0 as (F & Hf).  destruct Hf. inversion H0.  auto. 
            }  destruct (Tmax w H0).
            ++  assert (x1 el (negateAll U')). {
                 apply negateAll_in_iff.  tauto. 
                }  exfalso; firstorder eauto.
                 
            ++ apply ndcII. apply hil_exfalso.  apply ndcIE with x1. auto. auto. 
        + intro H. apply negAllImoClosed in Hx. simpl evalK.
          decide (x1 el (T w)).  
          decide (x2 el (T w)). 
          all: try firstorder eauto using IHx1, IHx2.
          intro. apply IHx2.  tauto. apply Tdedclos.  tauto. apply ndcIE with x1.  apply ndcA. auto.  apply ndcA. auto. 

    -  split.
       + intro H. apply Tdedclos. auto. apply ndcAI; auto.
         * apply ndcA.   apply IHx1. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
         destruct H0. destruct H0.  congruence. simpl evalK in H.  tauto. 
         * apply ndcA.   apply IHx2. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence. simpl evalK in H.  tauto.
       + intro. simpl.  split.
         * assert (x1 el (negateAll U')).    apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence.
           apply IHx1; auto. apply Tdedclos; auto. apply ndcAE with x1 x2.  apply ndcA. auto.  apply ndcA. auto.
         * assert (x2 el (negateAll U')).    apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence.
           apply IHx2; auto. apply Tdedclos; auto. apply ndcAE with x1 x2.  apply ndcA. auto.  apply ndcA. auto.  
    -  split.
       + intro H. destruct H.
         * apply Tdedclos. auto.  apply ndcOIL. apply ndcA.   apply IHx1. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence. auto.
         * apply Tdedclos. auto.  apply ndcOIR. apply ndcA.   apply IHx2. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence. auto.
       + intro.   apply TUPrime in H.  destruct H.
         * left. apply IHx1. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence. auto.
         * right.    apply IHx2. apply negateAll_in_iff in Hx.  destruct Hx. apply U'_sfc in H0.  apply negateAll_in_iff. tauto.
           destruct H0. destruct H0.  congruence. auto.
    -   intros. split.
        + intro H. simpl in H. tauto.
        + intro.  destruct t. simpl.  apply Tcons0. apply ndcA.  apply H.
    -  firstorder eauto.      
  Qed.

  
  (** Show completeness next **)
    Lemma prf_stable Γ A: ~~(ndc Γ A) -> ndc Γ A.
  Proof.
    intros. destruct (@ndc_dec Γ A).  auto. exfalso.  tauto.
  Qed.   

  (** Show completeness for subformulas *)
  Lemma completeness' Ω A: A el U' -> Ω <<= (negateAll U') -> entails Ω A -> ndc Ω A. 
  Proof.
        intros Au U H. apply prf_stable. intro.
            unfold entails in H.
    specialize (H (@canonical)).
         assert (exists Δ: mcTheory, ~(ndc (T Δ) A) /\ (Ω <<= (T Δ))).
     {
       eexists (Lindenbaum  U H0). split.
       - simpl. enough (~ ndc (extend Ω A U')  A). intro. apply H1. eapply ndcW.  apply H2.
         apply rep_equi. apply lindenbaum_subset2. auto.  
         apply extend_does_not_derive. auto. 
       - simpl. intros a Ha.   apply rep_in.  apply lindenbaum_subset2. auto.   apply extend_subset. auto.  
     }
     destruct H1 as [Δ H2].
     specialize (H Δ). destruct H2.
     assert ( {In A (T Δ)} + {~In A (T Δ)}). eauto.
     destruct H3; eauto.
     rewrite<- truth_lemma in n; auto. apply n. apply H.  unfold evalK'. intros.  apply truth_lemma.   eauto.  eauto.
     apply negateAll_in_iff.  tauto. 
  Qed.
  
End Canonical.


Lemma completeness Ω A: entails Ω A -> ndc Ω A.
Proof.
  intro. apply completeness' with Ω A. unfold U'. apply scl_incl'. auto. intros a Ha. apply  negateAll_in_iff.  left. apply scl_incl'. auto. auto.
Qed.

Print Assumptions completeness.  
