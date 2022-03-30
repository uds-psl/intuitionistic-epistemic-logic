Require Import List. 
Import ListNotations. 
Require Import  List PslBase.Lists.BaseLists.
Require Import PslBase.Base.
Require Import Coq.Program.Equality.

(** * Completeness for classical modal logics assuming dec **)
(**
    We sketch how, assuming decidability of Hilbert-systems for KT
    our method can be used to obtain completeness constructively
 **)

(** Define implicational fragment **)
Inductive form :=
  | Imp : form -> form -> form 
  | Bot : form
  | Var : nat -> form
  | Box : form -> form.
(* Define Notation for negation *)
Notation "⊥" := Bot.
Notation "¬ ϕ" := (Imp ϕ Bot) (at level 100, right associativity).

Infix "⊃" := Imp (right associativity, at level 103).
Definition Or (A B: form) := (¬ A ⊃ B).
Definition And (A B: form) := ¬ ((¬ B) ⊃ A). 
Definition Not s := Imp s Bot.
Definition Diamond A := Not(Box(Not(A))). 
Inductive prf : list form -> form -> Prop :=
   ax Γ p      :  List.In p Γ -> prf Γ p
 | pl1 Γ {p q} : prf Γ (p ⊃ (q ⊃ p))
 | pl2 Γ {p q r}: prf Γ ((p ⊃ (q ⊃ r)) ⊃ ((p ⊃ q) ⊃ (p ⊃ r)))
 | pl3 {Γ} {p q} : prf Γ (((¬p) ⊃ ¬q) ⊃ (((¬p) ⊃ q) ⊃ p))
 | k Γ {p q}     : prf Γ ( Box(p ⊃ q) ⊃ (Box(p) ⊃ Box(q)))
 | d Γ {p}:      prf Γ  (Box(p) ⊃ Diamond(p))
 | mp Γ p q      : prf Γ (p ⊃ q) -> prf Γ p -> prf Γ q
 | nec Γ p       : prf [] p -> prf Γ (Box(p))
                                  
.

Hypothesis prf_dec : forall Γ A, {prf Γ A}+{ ~ prf Γ A}. 
Hint Constructors prf. 



Lemma p_imp_p Γ p: prf Γ (p ⊃ p). 
Proof.
  pose proof (@pl2 Γ p (p ⊃ p) p).
  pose proof (@pl1 Γ p (p ⊃ p)).
  assert (prf Γ ((p ⊃ (p ⊃ p)) ⊃ (p ⊃ p))). eapply mp. apply H. apply H0.
  pose proof (@pl1 Γ p p). 
  eapply mp.  apply H1.  auto.
Qed.   

Lemma weakening Γ p: prf Γ p -> forall Δ, Γ <<= Δ -> prf Δ p. 
Proof.
  intro H. induction H; eauto.
Qed.   
Theorem deduction_thm Γ p q: prf Γ (p ⊃ q) <-> prf (p::Γ) q.
Proof.
  split.
  - intro.  remember (p::Γ) as Γ'. dependent induction H.  
    + apply mp with p. apply ax. rewrite HeqΓ'. auto.  apply ax.  rewrite HeqΓ'. auto.
    + pose proof (@pl1 Γ' p q0).  apply mp with p.  apply H. apply ax. rewrite HeqΓ'. auto.
    + pose proof (@pl2 Γ' p0 q0 r). eapply mp.  apply H.   apply ax.  rewrite HeqΓ'.  auto.
    + pose proof (@pl3 Γ' p0 q0).  eapply mp. apply H.  apply ax. rewrite HeqΓ'. auto. 
    + apply mp with (Box (p0 ⊃ q0)).  apply k.  rewrite HeqΓ'. apply ax. auto.
    + apply mp with (Box (p0)).   apply d.  rewrite HeqΓ'.  apply ax; auto. 
    + assert (prf Γ (p ⊃ q)).  apply mp with p0. auto.    auto.
      apply mp with (p).   apply weakening with Γ. apply H1.  rewrite HeqΓ'. eauto.  apply ax.  rewrite  HeqΓ'.  auto. 
  -      intro H1. dependent induction H1; eauto. destruct H.
         + subst p0. apply p_imp_p.
         +  eauto.
Qed.



Lemma exfalso_qoudlibet Γ A B: prf Γ ((¬ A) ⊃ (A ⊃ B)). 
Proof.
  apply deduction_thm.
  apply deduction_thm.
  pose proof (@pl1 Γ (¬ A) (¬ B)).
  pose proof (@pl1 Γ A (¬ B)).  
  pose proof (@pl3 Γ B A).
  assert (prf  (A :: (A ⊃ ⊥) :: Γ) ((B ⊃ ⊥) ⊃ A ⊃ ⊥)). {
    eapply mp. apply weakening with Γ; eauto.   apply ax; eauto. 
  }
   assert (prf  (A :: (A ⊃ ⊥) :: Γ) ((B ⊃ ⊥) ⊃ A)). {
    eapply mp. apply weakening with Γ; eauto.   apply ax; eauto. 
  }
  apply mp with ((B ⊃ ⊥) ⊃ A); auto.  apply mp with (((B ⊃ ⊥) ⊃ A ⊃ ⊥)); eauto. 
Qed.

Lemma prf_bot_to_arb Γ A: prf Γ (⊥ ⊃ A).  
Proof.
  firstorder eauto.
  pose proof (exfalso_qoudlibet Γ  ⊥ A).
  apply mp with (⊥ ⊃ ⊥); auto. 
  apply p_imp_p.
Qed.   

Lemma prf_imp_char Γ s t: (prf Γ (¬ s) \/ prf Γ t) -> prf Γ (s ⊃ t).
Proof.
  intro H. destruct H.
  - apply deduction_thm. apply mp with ⊥. apply  prf_bot_to_arb.     apply deduction_thm.  auto. 
  - apply mp with t.   apply pl1.  auto.
Qed.

Lemma hilbert_dne Γ s: prf Γ (¬ ¬ s) -> prf Γ s. 
Proof.
  intro.
  
  admit. 
Admitted.   

Lemma hilbert_dni Γ s: prf Γ ( s) -> prf Γ (¬ ¬ s). 
Proof.
  intro. apply deduction_thm.
  apply mp with s.  apply ax. auto.
  apply weakening with Γ; auto. 
Qed.



Section Models.
    Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            acc: world -> world -> Prop;
                            val: world -> valuation;

                            acc_serial: forall w, exists w', acc w w';
                            }.
       Fixpoint evalK {M: KripkeModel} (s: form) : (world) -> Prop := 
    match s with 
    | (Box x)  => (fun y => forall r, ((acc y r) -> evalK x r))
    | Bot    => (fun x => False)
    | Var y  => (fun x => val x y)
    | x ⊃ y  => (fun z => (evalK y z) \/ ~(evalK x z))
    end.

    Definition evalK' {M: KripkeModel} (Γ: list form) :=
    fun w => forall s, (In s Γ) -> @evalK M s w.  

    Definition entails Γ φ := 
      forall (M : KripkeModel), ((forall w,evalK' Γ w -> @evalK M φ w)).



End Models.
Notation context := (list form). 


Definition sf_closed (A : context) : Prop :=
  forall u, u el A -> match u with
                      | (Imp s1  s2) => s1 el A /\ s2 el A
                      | Box s => s el A
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
  (u = Imp s t \/ u = Box s  ) ->
  s el A -> t el A -> sf_closed A -> sf_closed (u :: A).
Proof.
  intros H H0 H1 H2.
  destruct H.
  - subst u.  intros a Ha. destruct Ha.  subst a.  firstorder.  destruct a; firstorder.
  -  subst u.  intros a Ha. destruct Ha; try subst a;  firstorder eauto. destruct a ; firstorder.   
Qed.


Fixpoint scl' (s : form) : context :=
  s :: match s with
       | Imp u v  => scl' u ++ scl' v
       | Box s => scl' s 
       | _ => nil
       end.

Lemma scl'_in s: s el scl' s.
Proof. destruct s; simpl; auto. Qed.

Lemma scl'_closed s: sf_closed (scl' s).
Proof. 
  induction s; simpl; auto.
  - apply sf_closed_cons with (s:=s1) (t:=s2);
      auto using scl'_in, sf_closed_app.
  -  intros u [A | A].
    + inversion A. auto using scl'_in, sf_closed_app.
    +   destruct u; firstorder eauto.  
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

  Lemma feqd: eq_dec form.
    intros a b. unfold dec. repeat decide equality.
  Defined.   
Instance form_eq_dec' :
  eq_dec form.
Proof.
  apply feqd.
Defined. 


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
                         Tcons: ~(prf T ⊥);
                         Tmax: forall A, A el (U') -> A el T \/ (¬ A) el T;
                         }.

    Lemma    Tdedclos {m: mcTheory}: forall A, A el (negateAll  U') ->  prf (T m) A -> A el (T m). 
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
        Fixpoint unK (l: list form) : list form := match l with
                                                     nil => nil |
                                                   (Box A::xr) => (A)::(unK xr)
                                                   | x::xr => unK xr
                                                   end .

        (** ** Option 1: Define unK with A \/ Box A **)

  Definition subsetVerif (A B:mcTheory) := forall x, In (Box x) (T A) -> In x (T B). 
  Lemma unK_in_iff Γ A: A el (unK Γ) <->    (Box A) el Γ .
  Proof.
      induction Γ.
      - firstorder eauto.
      - split.
        + intros Ha. destruct a; firstorder eauto. subst a. firstorder eauto.
        + intros Ha. destruct Ha.
          * subst a; firstorder eauto.
          * destruct a; firstorder eauto.

  Qed.

        Require Import Coq.Relations.Relation_Operators.
        Print clos_refl_trans.
     Lemma U'_scl_closed_Box  x: (Box x) el  U' -> x el  U' .
     Proof.
       intros H % U'_sfc. tauto.
      (* Follows immidieatly by using subformula-closure of U' *)
    Qed.

            Lemma negAllKClosed x:  Box x el negateAll U' -> x el negateAll U'.
    Proof.
      intros Ha.
      apply negateAll_in_iff in Ha. destruct Ha.
      - apply U'_scl_closed_Box in H. apply  negateAll_in_iff.  tauto.
      - destruct H. destruct H.   congruence.
    Qed.

    
        Definition single_extend (Ω: context) (A: form) (a: form) :=
    if (@prf_dec (a::Ω) A) then ((¬ a)::Ω) else (a::Ω). 

    Lemma single_extend_subcontext  A Ω B: Ω <<= (single_extend Ω A B).
    Proof. 
      intros a Ha.  unfold single_extend. destruct (prf_dec (B :: Ω) A); eauto.
    Qed.

    Lemma extend_two_possibilites Γ A B:
    ((single_extend Γ A B) === ((¬ B)::Γ) /\ prf (B::Γ) A) \/   (single_extend Γ A B) === (B::Γ) /\ ~(prf (B::Γ) A). 
  Proof.
    destruct (prf_dec (B::Γ) A) eqn:id.
    - left. split; try tauto.
      split.
      + intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      + unfold single_extend. rewrite id; auto.
    - right.      split; auto. split.
      +  intros a Ha. unfold single_extend in Ha. rewrite id in Ha. auto.
      +  unfold single_extend. rewrite id; auto.
  Qed.        
  Lemma hil_exfalso Γ: prf Γ Bot -> (forall A, prf Γ A).    
  Proof.
    intros H A. apply mp with ⊥.  apply  prf_bot_to_arb.  auto. 
  Qed.   


    Fixpoint extend (Ω: context) (A: form) (Γ: context) : context :=
      match Γ with
        nil => Ω
      | (a::Γ') =>
        single_extend (extend Ω A Γ') A a  end.

 Lemma a_does_not_matter Γ a b: prf (a::Γ) b -> prf ((¬ a)::Γ) b -> prf Γ b.    
 Proof.
 Admitted.   

 Lemma extend_does_not_derive Ω A Γ: ~(prf Ω A) -> ~(prf (extend Ω A Γ) A). 
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intros.  destruct (prf_dec (a :: extend Ω A Γ) A) eqn:di.
      +  simpl extend. unfold single_extend. rewrite di.   intro. apply (IHΓ Ω).  apply H.  apply a_does_not_matter with a; auto. (* Use that a \/ ~a is derived *) 
      +  simpl extend. unfold single_extend. rewrite di. apply n.   
  Qed.

    Lemma extend_subset Ω Γ A: Ω <<= (extend Ω A Γ).
  Proof.
    revert Ω. 
    induction Γ; eauto.
    - intro.  simpl extend. unfold single_extend.  destruct (prf_dec (a :: extend Ω A Γ) A); eauto.                          
  Qed.

  Lemma extend_adds_all Ω Γ A B: B el Γ -> B el (extend Ω A Γ) \/ (¬ B) el (extend Ω A Γ).
  Proof.
    intros H.
    dependent induction Γ; auto.
    destruct H.
    +  destruct (prf_dec (a :: extend Ω A Γ) A) eqn:di;  simpl extend; unfold single_extend; rewrite di;  subst a ; auto.
    +  specialize (IHΓ A B H).   destruct IHΓ.
       * left. unfold extend. apply single_extend_subcontext.  apply H0.
       *  right.   unfold extend. apply single_extend_subcontext.  apply H0.
  Qed.

  
    Lemma extend_locally_dclosed Γ Ω A B: ~(prf Ω A) -> (prf (extend Ω A Γ) (B)) -> B el Γ ->  B el (extend Ω A Γ).
  Proof.
    revert Ω B. intros.
    destruct (@extend_adds_all Ω Γ A B H1).
    - auto.
    -   apply extend_does_not_derive with (Γ := Γ) in H.  exfalso. apply H. apply hil_exfalso. apply mp with B.  apply ax. auto. auto.
  Qed.
    Lemma extend_does_not_derive_imp Ω Γ A B:
    ~(prf Ω A) -> B el Γ -> ~(prf (extend Ω A Γ) B) -> (prf (extend Ω A Γ) (B ⊃ A)).
  Proof.
    intros H H1. revert H. revert Ω.
    induction Γ.
    - intros.  eauto.
    - intros.  destruct H1.
      + subst a. simpl.
        destruct (extend_two_possibilites (extend Ω A Γ) A B) as [(E1 & E2) | (E1 & E2)].
        * apply weakening with (extend Ω A Γ). eauto.  destruct E1; auto. apply deduction_thm.  auto.  apply single_extend_subcontext. 
        * exfalso.   apply H0. simpl extend; fold extend. apply weakening with ( B :: extend Ω A Γ).  apply ax. auto.   destruct E1; auto. 
      + assert (~(prf (extend Ω A Γ) B)).  intro. apply H0. apply weakening with (extend Ω A Γ). auto. apply single_extend_subcontext. 
        specialize (IHΓ H1 (Ω) H H2). 
        simpl extend.  apply weakening with (extend Ω A Γ). auto.  apply single_extend_subcontext. 
  Qed.   



     (* Lemma extend_locally_easy_subset Ω A Γ: (extend Ω A Γ) <<= (Ω ++ Γ).
  Proof.
  Admitted.

  Lemma extend_locally_subset Γ A Ω: Ω <<= Γ -> (extend Ω A Γ) <<= Γ.
  Proof.
    intros. enough (extend Ω A Γ <<= Γ ++ Γ).  intros a Ha. specialize (H0 a Ha). apply in_app_iff in H0; destruct H0; assumption.
    enough (extend Ω A Γ <<= Ω ++ Γ). intros a Ha. specialize (H0 a Ha).  apply in_app_iff in H0. destruct H0; eauto.  apply extend_locally_easy_subset. 
  Qed.  *)
  Lemma lindenbaum_subset_helper Γ A:  extend Γ A U' <<= (Γ ++ negateAll U').
  Proof.
        revert Γ.  induction U'.
        - eauto. 
        -  intros Γ f Hf.
           unfold extend in Hf. fold extend in Hf.  unfold single_extend at 1 in Hf.
           destruct (prf_dec (a :: (extend Γ A l)) A) eqn:di.
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


    Definition Lindenbaum (Γ : list form) (A: form) (H: Γ <<= (negateAll U')) (H': ~(prf Γ A)) : mcTheory.  
    Proof.
     
    eapply mkmcTheory with (rep (extend Γ A U') (negateAll U')).
    - apply rep_power. 
    - enough (~ prf (extend Γ A U') ⊥).
      intro. apply H0. eapply weakening. eapply H1.   apply rep_incl.
      intro. apply extend_does_not_derive with Γ A U' in H'. apply H'. apply hil_exfalso. auto.   
      
    -  intros. rewrite rep_equi. apply extend_adds_all. auto.  apply  lindenbaum_subset2.    auto.
       
  Defined.
Lemma admissibility_K A s: prf (unK A) s -> prf A (Box s). 
Proof.
  revert s. induction A.  simpl; auto.
  intros s H1.
  destruct a; auto.
  -  apply weakening with A.  apply IHA;   auto.  eauto.
  -  apply weakening with A.  apply IHA;   auto.  eauto.
  -  apply weakening with A.  apply IHA;   auto.  eauto.

 -  apply deduction_thm. apply mp with (Box (a ⊃ s)).  apply k.  apply IHA. simpl unK in H1.  apply deduction_thm.  auto.     
Qed.

Search "negAll". 

    Instance canonical: (KripkeModel).
    Proof.
      eapply mkKripkeModel with (acc :=  subsetVerif).
      apply valuationMKT.
      - intros ta. assert (~(prf (unK (T ta)) ⊥)). intro.  apply admissibility_K in H.  assert (prf (T ta) (Diamond ( ⊥))). apply mp with (Box ⊥).
        apply d. auto. assert (prf (T ta) (¬ Diamond ⊥)). unfold Diamond. apply hilbert_dni.  apply nec. 
        unfold Not. apply deduction_thm.  apply ax. auto. 
        destruct ta.  apply Tcons0.  apply mp with (Diamond ⊥).  auto.  auto.
        assert (unK (T ta) <<= negateAll U').  {
          intros x Hx. destruct ta.  assert ((Box x) el (negateAll U')).  pose proof (power_incl  Tsubs0).  apply H0.  apply unK_in_iff in Hx.    auto. apply negAllKClosed in H0.  auto. 
        }
        exists (@Lindenbaum (unK (T ta)) ⊥ H0 H). intros a Ha. simpl. apply rep_in. apply lindenbaum_subset2. apply H0.  apply extend_subset.    apply unK_in_iff in Ha.   auto. 
        
    Defined.

     Lemma U'_scl_closed_imp  x y: (x ⊃ y) el  U' -> x el  U' /\ y el U'.
    Proof.
      intro. apply U'_sfc in H. tauto.
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
    -   intros w. split.
        + intro. 
          destruct H.
          * apply Tdedclos. auto.  rewrite IHx2 in H. apply deduction_thm. apply ax.  auto. apply negAllImoClosed in Hx.   tauto.  
          * apply Tdedclos. auto.  assert (x1 el (U')). {
              apply negateAll_in_iff in Hx; destruct Hx.
              *  apply  U'_scl_closed_imp in H0.  tauto. 
              *   destruct H0 as (F & Hf).  destruct Hf. inversion H0.  auto. 
            }  destruct (Tmax w H0).
            --  assert (x1 el (negateAll U')). {
                 apply negateAll_in_iff.  tauto. 
                }  exfalso; firstorder eauto.
                 
            -- apply deduction_thm. apply hil_exfalso.  apply mp with x1. auto. auto. 
        + intro H. simpl evalK.
          decide (x1 el (T w)).  
          decide (x2 el (T w)). 
          all: eauto using IHx1, IHx2.
        * left. apply IHx2; try  apply negAllImoClosed in Hx.   tauto.  auto.
        * exfalso.    apply n. apply Tdedclos.  apply negAllImoClosed in Hx.   tauto.   apply mp with x1;  apply ax; auto.  
                  * right.  rewrite IHx1. auto.  apply negAllImoClosed in Hx.   tauto.  
       -   intros. split.
        + intro H. simpl in H. tauto.
        + intro.  destruct t. simpl.  apply Tcons0. apply ax.  apply H.
    -  firstorder eauto.      
    - intros w. split.
      decide (Box x el (T w)); auto. 
      intro H. exfalso.
      assert (~ prf (unK (T w)) x). {
        intro. apply admissibility_K in H0 . apply n. apply Tdedclos. auto.
        auto. 
      }
      assert (exists Δ: mcTheory,  (unK (T w) <<= (T Δ)) /\ ~(x el (T Δ))).
      assert ( (unK (T w) <<= negateAll U')) as HS. intros a Ha. apply unK_in_iff in Ha. enough (Box a el (negateAll U')).
      apply  negAllKClosed. auto. specialize (Tsubs w). intro. apply power_incl in H1.  apply H1. auto.  
      eexists (@Lindenbaum (unK (T w)) x HS H0 ).
      split.
      +  simpl. rewrite rep_equi. apply extend_subset. apply lindenbaum_subset2.   auto. (* extend_subset *)
      +  intro. eapply extend_does_not_derive. apply H0.   apply ax. simpl T in H1.  apply rep_equi in H1. eapply H1. apply lindenbaum_subset2.  auto. 
      +    
      destruct H1 as (Δ & Hd1 & Hd2).
      apply Hd2. apply IHx. apply negAllKClosed.  auto.  apply H.  intros a Ha. apply Hd1. apply unK_in_iff.  auto. 
      + intro. intros w' Hw'.
      apply IHx.  apply negAllKClosed. auto. 
      apply Hw'. auto.
          
  Qed.

  
  (** Show completeness next **)
    Lemma prf_stable Γ A: ~~(prf Γ A) -> prf Γ A.
  Proof.
    intros. destruct (@prf_dec Γ A).  auto. exfalso.  tauto.
  Qed.   

  (** Show completeness for subformulas *)
  Lemma completeness' Ω A: A el U' -> Ω <<= (negateAll U') -> entails Ω A -> prf  Ω A. 
  Proof.
        intros Au U H. apply prf_stable. intro.
            unfold entails in H.
    specialize (H (@canonical)).
         assert (exists Δ: mcTheory, ~(prf (T Δ) A) /\ (Ω <<= (T Δ))).
     {
       eexists (Lindenbaum  U H0). split.
       - simpl. enough (~ prf (extend Ω A U')  A). intro. apply H1. eapply weakening.  apply H2.
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


Lemma completeness Ω A: entails Ω A -> prf Ω A.
Proof.
  intro. apply completeness' with Ω A. unfold U'. apply scl_incl'. auto. intros a Ha. apply  negateAll_in_iff.  left. apply scl_incl'. auto. auto.
Qed.

Print Assumptions completeness. 
