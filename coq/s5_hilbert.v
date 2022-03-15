Require Import List. 
Import ListNotations. 
Require Import  List PslBase.Lists.BaseLists.
Require Import PslBase.Base.
Require Import Coq.Program.Equality.

(** * Completeness for classical modal logics assuming dec **)
(**
    We sketch how, assuming decidability of Hilbert-systems for S5, KT, S4
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
 | t Γ {p}:      prf Γ  (Box(p) ⊃ p)
 | s4 Γ {p}:     prf Γ (Box(p) ⊃ Box(Box(p)))
 | b Γ {p}:      prf Γ (p ⊃ Box(Diamond(p))) 
 | mp Γ p q      : prf Γ (p ⊃ q) -> prf Γ p -> prf Γ q
 | nec Γ p       : prf [] p -> prf Γ (Box(p))
                                  
.
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
    + apply mp with (Box q).   apply t.  apply ax. subst Γ'. eauto.
    + apply mp with (Box p0). apply s4.  subst Γ'.     apply ax. auto.
    + apply mp with p.   apply b.  subst Γ'. auto. 
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


Section Models.
    Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            acc: world -> world -> Prop;
                            val: world -> valuation;

                            acc_refl: forall w, acc w w;
                            acc_sym: forall u v, acc u v -> acc v u;
                            acc_trans: forall u v w, acc u v -> acc v w -> acc u w;
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

  Lemma negateAll_in_iff Γ A: A el (negateAll Γ) <-> (A el Γ \/ (exists F, (A = ¬F) /\ (F el Γ)) \/ (exists F, (A = Box F) /\ (F el Γ)) ).  
  Proof.
    (*induction Γ; firstorder eauto.  simpl negateAll. subst x.  subst A.  firstorder.*) 
  Admitted.   
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
      +  destruct H. destruct H as (A' & HA'). destruct HA'.
         destruct (Tmax m H1); auto.
         * subst A. decide ((A' ⊃ ⊥) el (T m)); eauto.
           exfalso. eapply Tcons. eauto. 
         *   subst A. decide ((A') el (T m)); eauto.
         * destruct H.  destruct H.    subst A. 
   Admitted.    

        Definition valuationMKT (A: mcTheory) (a: nat) := (Var a) el (T A).
        Fixpoint unK (l: list form) : list form := match l with
                                                     nil => nil |
                                                   (Box A::xr) => (Box A)::A::(unK xr)
                                                   | x::xr => unK xr
                                                   end .
        (*
        Definition subsetVerif (A B:mcTheory) := forall s, (prf (T A) (Box s)) -> prf (T B) s. 
        
        Lemma todo: False. Admitted.  
            Instance canonical: (KripkeModel).
            Proof.
              eapply mkKripkeModel with (acc := subsetVerif).
              apply valuationMKT.
              - intros ta. intros a Ha. apply mp with (Box a).  apply t. auto.
              - intros u v H1 a Ha.   apply mp with (Diamond (Box a)).  exfalso; apply todo.
                unfold Diamond. enough (~prf (T u) (Box (Not (Box a)))).  exfalso; apply todo. intro.  apply H1 in H.
                apply (@Tcons v). apply mp with (Box a); auto.
              -   intros u v w H H0 a Ha. apply mp with (Box a). apply t. apply H0.  apply H.
                  apply mp with (Box (Box a)).  apply s4.  apply mp with (Box a). apply s4.
                  auto.
            Defined.

        Lemma truth_lemma : forall (x: form), In x (negateAll U') -> forall (t: (@world  canonical)), (evalK x t) <-> x el (T t).
        Proof.
          intros x.
              induction x.
          -     intros H t0. *)


        (** ** Option 1: Define unK with A \/ Box A **)

        Definition subsetVerif (A B:mcTheory) := forall F, (F el (unK (T A)) ) -> F el (T B). 
        Lemma unK_in_iff Γ A: A el (unK Γ) <->    (Box A) el Γ .
        Admitted.
        Lemma todoF: False. Admitted.  
        Ltac todo := exfalso; exact todoF. 

        Require Import Coq.Relations.Relation_Operators.
        Print clos_refl_trans.
    Instance canonical: (KripkeModel).
    Proof.
      eapply mkKripkeModel with (acc := clos_trans _ subsetVerif).
      apply valuationMKT.
      - intros ta. apply t_step.   intros a Ha.    apply unK_in_iff in Ha.  apply Tdedclos. todo.    apply mp with (Box a).  apply t. apply ax. auto.  
      - intros u v H1.  induction H1.
        +  apply t_step.  intros a Ha.  unfold subsetVerif in H.  apply unK_in_iff in Ha.
           apply Tdedclos. todo.  apply mp with (Diamond (Box a)). todo. (* Is a theorem of S5 *)
        unfold Diamond. enough (~prf (T x) (Box (Not (Box a)))). todo. 
        intro. assert ((Box (Not (Box a))) el (T x)). apply Tdedclos. todo.  auto.
        assert (Not (Box a) el (T y)).  apply H.  apply unK_in_iff.   auto.  apply (@Tcons y).
        apply mp with (Box a);  apply ax; auto. 
        + eapply t_trans.   apply IHclos_trans2. apply IHclos_trans1.
       
      -  intros u v w H H0. eapply t_trans.  eauto.  eauto.         
    Defined.

        Lemma truth_lemma : forall (x: form), In x (negateAll U') -> forall (t: (@world  canonical)), (@evalK canonical x t) <-> x el (T t).
        Proof.
          intros x.
              induction x.
          - intros H t0. split; eauto.
            + intro.  simpl evalK in H0. admit.
            + intro.  decide (x2 el (T t0)).
              * left.  apply IHx2.  admit. auto.
              * right. intro. apply IHx1 in H1. apply n. apply Tdedclos.  admit.
                apply mp with x1; apply ax; auto. admit.
          -  intros H t0. split.
             + intro. exfalso. apply H0.
             + intro.  exfalso.  eapply Tcons.  apply ax. apply H0.
          -  firstorder eauto.
          -  intro.   split.
             + intro. decide (Box x el T t0); auto. exfalso.
               admit.
             +  intro.  intros w Ha.  apply IHx. admit. assert (clos_trans _ subsetVerif t0 w). admit.
                induction H1.
                *  apply H1. apply unK_in_iff. auto.
                *   apply IHx. admit. 
 Admitted.                




        
        Definition subsetVerif (A B:mcTheory) := (unK (T A)) <<= (T B). 
        Lemma unK_in_iff Γ A: A el (unK Γ) <-> (* A el Γ \/ *)  (Box A) el Γ.
        Admitted.


    Instance canonical: (KripkeModel).
    Proof.
      eapply mkKripkeModel with (acc := subsetVerif).
      apply valuationMKT.
      - intros ta. intros a Ha.  apply unK_in_iff in Ha.  apply Tdedclos. admit.   apply mp with (Box a).  apply t. apply ax. auto.
        
      - intros u v H1 a Ha.  unfold subsetVerif in H1. apply unK_in_iff in Ha.
        
        + apply Tdedclos. admit. apply mp with (Diamond (Box a)). admit. (* Is a theorem of S5 *)
        unfold Diamond. enough (~prf (T u) (Box (Not (Box a)))). admit.
        intro. assert ((Box (Not (Box a))) el (T u)). apply Tdedclos. admit. auto.
        assert (Not (Box a) el (T v)).  apply H1.  apply unK_in_iff.   auto. apply (@Tcons v).
        apply mp with (Box a);  apply ax; auto.
      - intros u v w H H0. intros a Ha.
        apply unK_in_iff in Ha. apply Tdedclos.   admit. apply ax. 
        apply H0. apply unK_in_iff.  apply H.  apply unK_in_iff.  apply Tdedclos. admit.   apply mp with ((Box a)).  auto.
        apply ax. auto. 
        
   Defined. 
