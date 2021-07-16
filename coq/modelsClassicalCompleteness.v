Require Export nd.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical.

(** * Classical Strong Completeness *)

  (** We use double-negation elimination as an axiom *)
  Axiom DN: forall p, ~~p -> p. 

Section Models.
  Context {d : DerivationType}. 
  (** ** Kripke Models *)

  Class KripkeModel  := mkKripkeModel {
                            world : Type;
                            valuation := nat -> Prop;
                            cogn  : world -> world -> Prop;
                            verif : world -> world -> Prop;
                            val   : world -> valuation;
                            preorderCogn: PreOrder cogn;
                            monotone: forall s x y, cogn x y -> val x s -> val y s;
                            vericont: subrelation verif cogn;
                            transvalid: forall x y z, cogn x y -> verif y z -> verif x z;
                          }.
  Context {M: (@KripkeModel)}.
  Instance kripke_verif_trans_equiv_Equiv {M': KripkeModel}  : Transitive (verif).
  Proof. 
    intros u v w H H2. apply vericont in H. apply transvalid with (y := v); auto.
  Qed.

  Instance cogn_trans {M': KripkeModel}  : Transitive (cogn).
  Proof.
    apply preorderCogn.  
  Qed.

  Fixpoint evalK {M: KripkeModel} (s: form) : (world) -> Prop := 
    match s with 
    | (K x)  => (fun y => forall r, ((verif y r) -> evalK x r))
    | Bot    => (fun x => False)
    | Var y  => (fun x => val  x y)
    | x ⊃ y  => (fun z => forall r', cogn z r' -> (evalK x r') -> (evalK y r'))
    | s ∨ t  => (fun y => evalK s y \/ evalK t y)
    | s ∧ t  => (fun y => evalK s y /\  evalK t y)  
    end.

  Definition evalK' {M: KripkeModel} (Γ: theory) :=
    fun w => forall s, (Γ s) -> @evalK M s w.  

  Definition entails (Γ: theory) (φ: form) := 
    forall (M : KripkeModel),
      ((forall w,evalK' Γ w -> @evalK M φ w)).
  
  Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

  (** 
    Being an IEL or IEL^- model is a property of a given model.
   **)
  Definition isIEL (M: KripkeModel) := forall w, exists w', verif w w'.

  (** Evaluation is monotone, that is if φ is true at world w
      and we can reach world v from w, φ true at v.  *)
  Lemma eval_monotone  (s: form)  w v: 
    cogn w v -> evalK s w -> evalK s v.
  
  Proof. 
    intros C H. induction s.
    + intros z H1. apply H. apply transvalid with (y := v); auto. 
    + intros z H1 H2. apply H. apply transitivity with (y := v); auto. exact H2.
    + destruct H. split.
      ++ apply IHs1. auto.
      ++ apply IHs2. auto.
    + destruct H.
      ++ left. auto.
      ++ right. auto.
    + exfalso. apply H.
    + apply monotone with (x := w); auto.
  Qed.     

  Lemma monotone_ctx (A:theory)  : 
    forall w w', cogn w w' -> evalK' A w -> evalK' A w'.
  Proof.
    intros. intros t H1.
    apply eval_monotone with (w := w); auto. 
  Qed.
End Models.
(** ** Canonical models *)
Section Canonical.
  (** 
We define the *canonical models*, whose worlds are the maximally consistent theories.
We first define the relations.
   **)
  Context {d : DerivationType}. 

  Record mcTheory := mkmcTheory {
                         T: theory;
                         Ttheory: forall φ, (@ndT d T φ) -> T φ;
                         consistentT:  ~(T ⊥);
                         prime: is_prime T;
                       }.

  Definition lindenBaumTheory (Γ: theory) (φ: form) (H: ~(ndT Γ φ)) :mcTheory.
    destruct (Lindenbaum H).  destruct H1. destruct H2.


    apply mkmcTheory with (T := (max Γ φ)). 
    + tauto. 
    + intro. apply H1. apply ndtE. apply ndtA. assumption.
    +  intros a b Ha.
       unfold is_primeDN in H2. specialize (H2 a b).
       apply DN in H2.  eauto. 
  Defined.

  Lemma lindenBaumTheorySubset Γ (φ: form) (H: ~(ndT Γ φ)) : exists Δ: mcTheory ,Γ ⊆ (T Δ).
  Proof.
    exists (lindenBaumTheory H).
    simpl T. assert ( (T (lindenBaumTheory H)) = (max Γ φ)). cbv. firstorder.  unfold lindenBaumTheory. apply max_subset. 
  Qed.


  Definition subsetMKT (A B: mcTheory) := subset (T A) (T B).
  Definition valuationMKT (A: mcTheory) (a: nat) := (T A) (Var a).
  
  Definition subsetVerif (A B:mcTheory) := 
    forall a, ((T A) (K a)) -> (T B) a.
  Instance canonical: (KripkeModel).
  apply mkKripkeModel with (world := mcTheory) (cogn := subsetMKT) (val := valuationMKT) (verif := subsetVerif).
  try firstorder.
  firstorder.
  2: firstorder.
  + intros A B c d' E. apply Ttheory with (φ := d'). destruct B. simpl. apply ndtA. apply c. apply ndtA in E. apply ndtKpos in E.
    apply Ttheory in E. exact E.

  Defined.

  Lemma deductionGamma (Gamma: mcTheory) (phi: form):  ndT (T Gamma) phi <-> (T Gamma) phi.
  Proof.
    (* *)
    split.
    intro. apply Ttheory in H. exact H.
    apply ndtA.
  Qed.
  Hint Resolve deductionGamma : core.
  
  Lemma world_canonical_disjunction (t: mcTheory) ψ φ : 
    ((T t) (φ ∨ ψ)) <-> (ndT (T t) φ) \/ ndT (T t) ψ.
  Proof.
    intros. split.
    + intro. 
      apply prime. 
      apply deductionGamma.
      exact H.
    + intro. destruct H; eauto. 
    - apply deductionGamma. apply ndtDIL. eauto.
    - apply deductionGamma. apply ndtDIR. eauto. 

  Qed.

End Canonical. 
Lemma canonicalIEL: isIEL (@canonical normal).
Proof.
  intros w.
  assert (~(@ndT normal (unbox (T w)) ⊥)).
  {
    intros H % modalShiftingLemma.
    destruct w. apply consistentT0.
    apply @Ttheory0.
    apply @ndtIE with (s := (K ⊥)).
    
    - apply @ndtW with (T := empty).
      + apply IELKBot. 
      + firstorder.
    - simpl T in H.  exact H.    

  }
  exists (lindenBaumTheory  H).
  intros x H1. simpl lindenBaumTheory.
  simpl T.
  apply max_subset.
  apply unbox_rewrite.
  exact H1.
Qed.

Definition entailsIEL (Γ: theory) (φ: form) := 
  forall (M : KripkeModel), isIEL M -> (((forall w,evalK' Γ w -> @evalK M φ w))).
Notation "Γ ⊨+ φ" := (entailsIEL Γ φ) (at level 30). 
Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

Lemma entailsImpliesEntails Γ φ:
  (Γ ⊨ φ) -> (Γ ⊨+ φ).
Proof.
  intro.
  intro. intro. apply H. 
Qed.

(** ** Strong Completeness *)
Section Completeness.
  
  (** *** Truth-Lemma *)
  Lemma truth_lemma {d: DerivationType}: forall  (X: form) (t: (@world  canonical)), 
    (evalK X t) <-> ((T t) X).
  Proof.
    intro x.
    induction x.
    - split.
      + intro H0. apply DN. intro H'.
        assert (H: ~ unbox (T t) ⊢T x).
        * intros H. now apply H', deductionGamma, modalShiftingLemma.
        * assert (exists Δ: mcTheory , (unbox (T t)) ⊆ (T Δ)
                                  /\ ~((T Δ) x)).
          {  
            exists (lindenBaumTheory H).
            split.
            - apply max_subset.
            - intro. apply ndtA in H1.
              apply does_not_derive in H1; auto. 
          }
          destruct H1. destruct H1.  apply H2.  apply IHx. auto. 
          
          
      + intros A. simpl evalK. intros r V. apply IHx. auto. 
    - split. 
      +
        intro.
        apply deductionGamma. apply DN.  rewrite deductionGamma. 
        intro. 
        enough (exists Δ: mcTheory, (T t) ⊆ (T Δ) /\ ((T Δ) x1) /\ ~((T Δ) x2)). destruct H1 as [Δ H2].
        specialize (H Δ). destruct H2. destruct H2. apply H3. apply IHx2. (*apply H0.*) firstorder eauto.
        (*    apply IHx1. exact H2.  *)
        rewrite<- deductionGamma in H0. rewrite ImpAgree in H0.
        destruct (Lindenbaum H0).
        exists (lindenBaumTheory H0).
        split. intros x H3. firstorder eauto.  
        
        split. 
        * apply deductionGamma. apply ndtW with  (x1#(T t)). apply ndtA. left. reflexivity. unfold lindenBaumTheory. cbn. apply max_subset.
        * rewrite<- deductionGamma. destruct H2. auto.   
      + intros. intros w H1 H2. apply IHx2. apply deductionGamma. apply ndtIE with (s := x1). apply deductionGamma. apply H1. exact H. apply deductionGamma. apply IHx1. exact H2.
    - split.     
      + intro H.
        destruct H.
        apply deductionGamma. 
        apply ndtCI; apply ndtA.
        * apply IHx1. exact H.
        *  apply IHx2. exact H0.  
      + intros H1.  split.
        * apply deductionGamma in H1.  apply ndtCEL in H1. apply IHx1. 
          apply deductionGamma.  auto.
        * apply deductionGamma in H1.  apply ndtCER in H1. apply IHx2. 
          apply deductionGamma.  auto.
    - intro.  simpl evalK. rewrite world_canonical_disjunction. rewrite IHx1. rewrite IHx2.
      repeat rewrite deductionGamma. tauto.
      
    - split.
      + 
        intro. exfalso. apply H.
      + intro.  exfalso. apply (consistentT H). 
    - split; firstorder. 
  Qed.

  Lemma StrongCompleteness {d: DerivationType} (Γ: theory) (φ: form): 
    (entails Γ φ) -> Γ ⊢T φ.
  Proof.
    
    intro H0.
    apply DN. 
    intro H.
    unfold entails in H0.
    specialize (H0 canonical).
    enough (exists Δ: mcTheory, ~((T Δ) ⊢T φ) /\ (Γ ⊆ (T Δ))).
    destruct H1 as [Δ H2].
    specialize (H0 Δ).
    apply H2.
    apply deductionGamma.
    apply truth_lemma.
    apply H0. intros ψ P. apply truth_lemma. apply deductionGamma. destruct H2. apply ndtA.
    apply H2. exact P. 
    (* Show that such a theory exists *)
    exists (lindenBaumTheory H).
    split.
    apply does_not_derive. exact H.
    apply max_subset.
  Qed.

    Lemma StrongCompletenessIEL (Γ: theory) (φ: form):
      (entailsIEL Γ φ) -> (@ndT normal Γ φ).
    Proof.  
      intro H0.
      apply DN. 
      intro H.
      unfold entailsIEL in H0.
      specialize (H0 (@canonical normal)).
      specialize (H0 canonicalIEL).
      enough (exists Δ: @mcTheory normal, ~(@ndT normal (T Δ) φ) /\ (Γ ⊆ (T Δ))).
    destruct H1 as [Δ H2].
    specialize (H0 Δ).
    apply H2.
    apply deductionGamma.
    apply truth_lemma.
    apply H0. intros ψ P. apply truth_lemma. apply deductionGamma. destruct H2. apply ndtA.
    apply H2. exact P.
    exists (lindenBaumTheory H).
    split.
    apply does_not_derive. exact H.
    apply max_subset.
    Qed.  

    Lemma evalKimp {M: KripkeModel} s t w: evalK s w -> evalK (Imp s t) w -> evalK t w.
    Proof.
      intros H0 H1.
      apply H1. apply preorderCogn. auto.
    Qed.

    Lemma evalKdistr {M: KripkeModel} s w w': evalK (K s) w -> verif w w' -> evalK s w'.
    Proof.
      intros.
      apply H.
      exact H0.
    Qed.

    Definition model_constraint (d : DerivationType) m :=
      if d then True else isIEL m.

    Lemma entailsToNot' ϕ {d: DerivationType} :
      ~ (ndT empty ϕ) -> exists m w, model_constraint d m /\ ~(evalK ϕ w).
    Proof. 
      intros.
      exists canonical.
      exists (lindenBaumTheory  H). split.
      { destruct d; cbn; trivial. apply canonicalIEL. }
      rewrite truth_lemma.
      destruct (Lindenbaum H).
      destruct H1.
      simpl T.
      destruct H2.
      intro. apply H1.  apply ndtA. exact H4.
    Qed.

    Lemma entailsToNot ϕ {d: DerivationType}: (~ (ndT empty ϕ)) -> exists (m: KripkeModel) w, ~(evalK ϕ w).
    Proof. 
      intros H. destruct (entailsToNot'  H); firstorder.
    Qed.

    Lemma entailsToNotIEL ϕ: (~ (@ndT normal empty ϕ)) -> exists (m: KripkeModel) w, isIEL m /\ ~(evalK ϕ w).
    Proof. 
      intros H. destruct (entailsToNot' H); firstorder.
    Qed.   
    Definition ctx2thy (Γ: context) := fun x => In x Γ. 

    Lemma ndSoundIELCtx (A: context) (s: form) {p: DerivationType}  (D:@nd p A s):forall (M: KripkeModel), model_constraint p M ->  forall w, evalK' (ctx2thy A) w -> evalK s w.
    Proof.
      intros M Mc. induction D.
      + eauto.
      + intros.   exfalso. apply (IHD) with w; auto.   
      + intros w1 c1 H2 c2 H3. apply IHD; auto.  intro s'. intro H4. destruct H4. subst s'.   assumption.  apply eval_monotone with (w := w1); auto.
      + intros w H. apply evalKimp with (s0 := s). apply IHD2; auto. apply IHD1; auto.
      + intros w H w' c H1 w'' v. specialize IHD with w. apply evalKimp with (s0 := s). apply H1. exact v.
        apply evalKdistr with (w0 := w); auto. apply transvalid with (y := w'); auto.
      + intros w H w' v. apply IHD; auto.  apply monotone_ctx with (w0 := w); try tauto; auto. apply  vericont; auto.
      + intros w H1. apply IHD in H1; auto. destruct H1. auto. 
      + intros w H1. apply IHD in H1; auto. destruct H1. auto. 
      + intros w H1. split; auto.
      + intros w H1. left. auto.
      + intros w H1. right. auto.
      + intros w H1. destruct (IHD1 Mc w H1).
      - apply (IHD2 Mc w); auto. apply preorderCogn.
      - apply (IHD3 Mc w); auto. apply preorderCogn.
        + intros w H1 u c.  
          apply monotone_ctx with (w' := u)  in H1. 2: auto.
          unfold isIEL in Mc. destruct (Mc u).   
          specialize (IHD Mc u). 
          assert (evalK s x).
          {
            apply IHD; auto. 
          }
          intro.
          apply (H2 x). apply vericont. auto.
          apply H0.
    Qed.

    Lemma ndSoundIEL  (A: theory) (s: form) {p: DerivationType}  (D:@ndT p A s):forall (M: KripkeModel),model_constraint p M ->  forall w, evalK'  A w -> evalK s w.
    Proof.
      intros. destruct D. apply ndSoundIELCtx with x p.  destruct H1; eauto.  auto. intros t Ht .    apply H0.  destruct H1.  auto. 
    Qed.
End Completeness.

Section NotClassicalTruth.
Inductive dual := One | Two. 
Local Definition p := (Var 0).
Definition propVal (x: dual) (y: nat) := match x with
                                       | One => False
                                       | Two => y = 0
                                       end.
Definition epistemicAccessible (x y: dual) := y = Two.
Definition cognitionAccessible (x y: dual) := match x with
                                              | One => True
                                              | Two => y = Two
                                              end.
Definition miniModel: KripkeModel.
  apply mkKripkeModel with (world := dual) (cogn := cognitionAccessible) (verif := epistemicAccessible) (val := propVal).
  + split; intros. intro x; destruct x; firstorder eauto.
    intros x y z; destruct x ; destruct y ; destruct z; firstorder eauto.
  +  intros s x y H1 H2. destruct x; destruct y; destruct H1; firstorder eauto.
  +  intros x y H.  destruct x; destruct y; firstorder eauto.
  +    intros x y z H1 H2. destruct x; destruct y; destruct z; firstorder eauto.   
Defined.

Lemma miniModelNotKphiimpphi: ~(@evalK miniModel (K p ⊃ p) One).
  simpl. intro. specialize (H One). simpl in H. apply H. exact I.
  intros a H'.
  inversion H'. firstorder eauto.
Qed.

Lemma miniModelIEL: isIEL (miniModel).
Proof.
  intros w. exists Two. reflexivity.
Qed.
Lemma IELTruthCondNotAdmissible: ~(forall ϕ, (empty ⊢T+ (K ϕ ⊃ ϕ))).
Proof.
  intro H.
  specialize (H p).
  apply ndSoundIEL with (M := miniModel) (w := One) in H.
  apply miniModelNotKphiimpphi. auto.
  apply miniModelIEL.
  firstorder eauto.
Qed.

Lemma IELMINUSTruthCondNotAdmissible: ~(forall ϕ, (empty ⊢T- (K ϕ ⊃ ϕ))).
Proof.
  intro H.
  specialize (H p).
  apply ndSoundIEL with (M := miniModel) (w := One) in H.
  apply miniModelNotKphiimpphi. auto. simpl model_constraint.  auto. 
  firstorder eauto.
Qed.

End NotClassicalTruth.

Section NoKDisjunction.
  Inductive triple := one | two | three.
  Definition tripleR (x y: triple) :=
    match x with
      one => True
    | two => y = two
    | three => y = three
    end.

  Definition tripleE (x y: triple) :=
    match x with
      one => y = two \/ y = three
    | two => y = two
    | three => y = three
    end.
  Definition peval (w: triple) (n: nat) := w = three /\ n = 0.

  Definition M3: KripkeModel.
    apply mkKripkeModel with (world := triple) (cogn := tripleR) (verif := tripleE) (val := peval).
    + split.  intros x; destruct x; firstorder eauto.
      intros x y z H H0; destruct x; destruct y; destruct z; destruct H; destruct H0; firstorder eauto.
    + intros s x y H Z.   destruct x; destruct y; destruct H; firstorder eauto; try discriminate.
    + intros x y H.   destruct x; destruct y; firstorder eauto.
    + intros x y z H1 H2.  destruct x; destruct y; destruct z; firstorder eauto; try discriminate.
  Defined.

  Lemma M3IEL: isIEL M3.
    intros x. destruct x.
    - exists two. cbn; auto.
    - exists two. cbn; auto.
    - exists three. cbn; eauto.
  Qed.

  Lemma m3DoesNotDeriveKPorNegKp: (@evalK M3 (K(p ∨ (¬p))) one).
  Proof.
    simpl evalK. 
    intros r H.
    destruct H.
    - right. intros r' H1 H2.
      destruct r'; try destruct H1; try firstorder eauto; try discriminate.
      subst r. discriminate.
    -  left. firstorder eauto.
  Qed.
  
  Lemma m3DoesNotDeriveKPorNegK: ~(@evalK M3 (K p ∨ (K  (¬p))) one).
  Proof.  
    intro H.
    simpl evalK in H. 
    destruct H.
    - specialize (H two).
      firstorder eauto; discriminate.
    - specialize (H three).
      firstorder eauto;try discriminate.
      specialize (H0 three).
      firstorder eauto.
  Qed.
  
  Lemma IELKDisjNotAdmissible: ~(forall ϕ ψ, empty ⊢T+ (K(ϕ ∨ ψ) ⊃ K(ϕ) ∨ K(ψ))).
  Proof.
    intro H.
    specialize (H p (¬ p)).
    apply ImpAgree in H.
    apply ndSoundIEL with (M := M3) (w := one) in H.
    -  apply m3DoesNotDeriveKPorNegK; auto.
    -  apply M3IEL.
    -  intro. intro.   firstorder eauto. rewrite H0.   apply m3DoesNotDeriveKPorNegKp.
  Qed.

  Lemma IELMKDisjNotAdmissible:
    ~(forall ϕ ψ, empty ⊢T- (K(ϕ ∨ ψ) ⊃ K(ϕ) ∨ K(ψ))).
  Proof.
    intro H.
    specialize (H p (¬ p)).
    apply ImpAgree in H.
    
    apply ndSoundIEL with (M := M3) (w := one) in H.
    -  apply m3DoesNotDeriveKPorNegK; auto.
    -  simpl model_constraint. auto.
    - intro. intro.   firstorder eauto. rewrite H0.   apply m3DoesNotDeriveKPorNegKp. 
  Qed.      

End NoKDisjunction.


(** ** Classical Admissability Results **)
Section AdmissibilityReflection.
  Variable d: DerivationType.
  Definition liftRelOne {X: Type} (R: X -> X -> Prop) (r1 r2: (option X)) :=
    match (r1, r2) with
      (Some x, Some y) => (R x y) |
    (None, _)     => True |
    _ => False
    end.

  Definition liftProp {X: Type} (R: X -> nat -> Prop) (r: (option X)) (n: nat) :=  
    (match r with
       Some r' => R r' n
     | None => False end).
  Lemma onSomeEqualsRlift {X: Type} x R  (n: nat): (@liftProp X R (Some x) n) <-> (R x n).
    split; firstorder eauto.
  Qed.  

  Section liftRelProps.
    Context {X: Type} {R: X -> X -> Prop} {R': X -> X -> Prop}.
    
    Definition lr := (liftRelOne R).
    Definition lr' := (liftRelOne R').
    
    Lemma lr_in a b :
      lr a b -> (exists b', a = None /\ b = Some b') \/ (exists a' b', a = Some a' /\ b = Some b') \/ (a = None /\ b = None).
    Proof.
      Unset Printing All.
      intro.
      unfold lr in H.
      destruct a, b; firstorder eauto; try congruence.
    Defined.
    
    Lemma preserves_reflexivity: Reflexive R -> Reflexive lr.
    Proof.
      intros.
      intro x.
      destruct x; firstorder eauto.
    Defined.

    Lemma preserves_transitivity: Transitive R -> Transitive lr.
      intros H x y z H1 H2.
      destruct x; destruct y; destruct z; firstorder eauto.
    Defined.
    Lemma preservesPreOrder: PreOrder R -> PreOrder lr.
      intros H.  destruct H.  split.
      apply preserves_reflexivity; auto.
      apply preserves_transitivity; auto. 
    Defined.

    Lemma preservesSubrealtion: subrelation R R' -> subrelation lr lr'.
    Proof.
      intros H x  y H1.
      destruct (lr_in H1); firstorder eauto; rewrite H0; rewrite H2.
      cbv. auto. cbv. apply H. rewrite H0 in H1. rewrite H2 in H1.  cbv in H1. auto. 
      cbv. auto.
    Defined.

    Lemma onSomeEqualsR x y: lr (Some x) (Some y) <-> (R x y).
      split; firstorder eauto.
    Qed.  
  End liftRelProps. 

  Definition reflectionModel (m: KripkeModel): (KripkeModel).

    apply mkKripkeModel with (world := (option world)) (cogn := (liftRelOne  cogn)) (verif := (liftRelOne verif)) (val := (liftProp  val)).
    + apply preservesPreOrder; auto. apply m. 
    + intros s x y H H0.
      destruct x; destruct y; firstorder eauto; try congruence.
      destruct m. rewrite onSomeEqualsRlift. apply monotone0 with (x := w);
                                               firstorder eauto using onSomeEqualsR. 
    + destruct m.  apply preservesSubrealtion.  auto. 
    + intros x y z. destruct m; destruct x; destruct y; destruct  z; firstorder eauto using onSomeEqualsR.
      apply onSomeEqualsR.  apply transvalid0 with (y := w0).
      rewrite<- onSomeEqualsR.  exact H.  rewrite<- onSomeEqualsR.  exact H0. 
  Defined.

  (* Derivability in the reflection model (Even nicer would be if submodels would be arbitrary) *)
  Lemma derivReflSomeIdent (m: KripkeModel) ϕ: forall w, ((@evalK m ϕ w) <-> (@evalK (reflectionModel m) ϕ (Some w))). 
  Proof.
    - induction ϕ;try firstorder eauto.
      + split.
        intros H r1 v. destruct r1. 
        apply IHϕ. apply H. auto using onSomeEqualsR.
        destruct v.

        intros H r' v.
        apply IHϕ. apply H. auto using onSomeEqualsR. 
      + split.
        * intros H. simpl evalK. intros r' H1 H2.
          destruct r'. 
          apply IHϕ2. apply H.  auto using onSomeEqualsR.
          apply IHϕ1. auto.
          destruct H1.
        * intros H r' c H1.
          apply IHϕ2.
          apply H.
          eauto using onSomeEqualsR.
          apply IHϕ1. auto.
  Qed.

  Lemma derivRefl (m: KripkeModel) ϕ: (exists w, ~(@evalK m ϕ w)) -> ~(@evalK (reflectionModel m) (K ϕ) None).
  Proof.                                 
    intro.
    intro.  destruct H. apply H. 
    apply derivReflSomeIdent. 
    apply H0. simpl verif. cbv. auto.
  Qed.   

  Lemma reflectionPreservesIEL (m: KripkeModel):
    isIEL m -> isIEL (reflectionModel m).
  Proof.
    intros H w.
    destruct w.
    - specialize (H w). destruct H as [w' Hw']. exists (Some w'). apply Hw'.
    - exists None. firstorder eauto.
  Qed.    
  Notation "∅" := empty.
  Theorem contra (p q:Prop) : (~q->~p)->(p->q).
  Proof.
    intros.
    apply NNPP.
    intro.
    apply H in H1.
    contradiction.
  Qed.

  (** *** Admissibility of reflection *) 

  Lemma reflectionAdmissibleIEL ϕ: ∅ ⊢T+ (K ϕ) -> ∅ ⊢T+ ϕ.  
  Proof.
    apply contra.
    intros.
    apply entailsToNotIEL in H.
    intro.
    enough (exists m w, isIEL m /\ ~ evalK (K ϕ) w).
    destruct H1 as [M [mw Hmw]].
    apply ndSoundIEL with (M := M) (w := mw)  in H0 .
    destruct Hmw.  apply H2. exact H0. 
    tauto. 
    intro; firstorder eauto.
    destruct H as [m [mw Hmw]].
    exists (reflectionModel m).
    exists None.
    split.
    - apply reflectionPreservesIEL. firstorder auto. 
    - destruct Hmw.  firstorder eauto using  derivRefl. 
  Qed.

  Lemma reflectionAdmissibleIELM ϕ: ∅ ⊢T- (K ϕ) -> ∅ ⊢T- ϕ.  
  Proof.
    apply contra.
    intros.
    apply entailsToNot in H.
    intro.
    enough (exists m w, ~ (@evalK m (K ϕ) w)).
    destruct H1 as [M [mw Hmw]].
    apply ndSoundIEL with (M := M) (w := mw)  in H0 .
    destruct Hmw. auto.
    simpl.  auto. 
    intro; firstorder eauto.
    destruct H as [m [mw Hmw]].
    exists (reflectionModel m).
    exists None.
    firstorder eauto using  derivRefl.  
  Qed.
End AdmissibilityReflection. 

(** *** Disjunction property **)
Lemma t (X Y:Prop): ~(X \/ Y) <-> ~X /\ ~Y.
Proof. tauto. Qed.


Section DisunctionProp.
  Context {d : DerivationType}.
  Notation "∅" := empty.


  (**
     We build the new model. 
   **)
  
  Section LiftDisjuction.
    Definition lT (X Y:Type) := option (X + Y).

    Definition liftRels {X Y:Type} (R: X -> X -> Prop) (S: Y -> Y -> Prop)  (a b: (lT X Y)) :=
      match (a, b) with
        (None, _) => True
      | (Some (inl x),Some (inl y)) => R x y
      | (Some (inr x), Some (inr y)) => S x y                                      
      | _ => False end .

    Lemma liftRelsDestruct {X Y: Type} (R: X -> X -> Prop) (S: Y -> Y -> Prop) (a b: (lT X Y)):
      (liftRels R S a b) -> ((a = None /\ exists x, b = Some (inl x)) \/ (a = None /\ exists y,b = Some (inr y)) \/ (exists x x', a = (Some (inl x)) /\ b = (Some (inl x'))) \/ (exists y y', a = Some (inr y) /\ b = Some (inr y'))) \/ (a = None /\ b = None).
    Proof.
      intro.
      destruct a; destruct b; firstorder eauto; try destruct H; try destruct s0; try destruct s; try destruct x; try destruct x0; firstorder eauto.
    Qed.
    
    Definition liftPropDisj {X Y: Type} (R1: X -> nat -> Prop) (R2: Y -> nat -> Prop) (x: (lT X Y)) (n: nat) :=
      match x with
        None => False
      | Some (inl x) => R1 x n
      | Some (inr y) => R2 y n end.

    Lemma liftRelsReflexive  {X Y:Type} {R: X -> X -> Prop} {S: Y -> Y -> Prop}: Reflexive R -> Reflexive S -> Reflexive (liftRels R S).
    Proof.   
      intros RR RS.
      intro x. destruct x;firstorder eauto.
      destruct s; firstorder eauto. 
    Qed.

    Lemma liftRelsTrans  {X Y:Type} {R: X -> X -> Prop} {S: Y -> Y -> Prop}: Transitive R -> Transitive S -> Transitive (liftRels R S).
    Proof.   
      intros RR RS.
      intros x y z.
      destruct x.
      - intros H1 H2. destruct s; try destruct H1. destruct y; destruct z; try destruct H1; try destruct H2.
        destruct s0; destruct s; try (destruct H1); try (destruct H2). 
        + simpl liftRels. cbv. apply RR with (y := x1) . apply H1.  apply H2.
        + destruct s; auto. 
        + destruct y; auto.  destruct z; auto.  destruct s; try destruct s0; try destruct y0; firstorder eauto using liftRelsDestruct.
          destruct s; destruct H2. destruct H1.
      - intros H H0. destruct z; firstorder eauto. 
    Qed.
    Definition relation X := X -> X -> Prop .
    Lemma preservesSubrelation {X Y: Type} (R R': relation X) (S S': relation Y):
      subrelation R R' -> subrelation S S' -> subrelation (liftRels R S) (liftRels R' S').
    Proof.
      intros H1 H2 x y H3.
      destruct x; destruct y; try destruct s; try destruct s0; firstorder eauto.
    Qed.  
  End LiftDisjuction.


  Definition disjunctionModel (m1: KripkeModel) (m2: KripkeModel) : KripkeModel.
  Proof.
    apply mkKripkeModel with (world := (@lT (@world m1) (@world m2))) (cogn := (liftRels (@cogn m1) (@cogn m2)))
                             (verif := (liftRels (@verif m1) (@verif m2))) (val := (liftPropDisj (@val m1) (@val m2))).
    - split.
      + destruct m1. destruct m2. destruct preorderCogn0. destruct preorderCogn1. apply liftRelsReflexive.  apply PreOrder_Reflexive.
        auto.    
      + destruct m1. destruct m2. destruct preorderCogn0. destruct preorderCogn1. apply liftRelsTrans. apply PreOrder_Transitive. apply PreOrder_Transitive0.
    - intros n x y H1 H2.  destruct (liftRelsDestruct H1).  destruct H; destruct H. 
      + destruct H0 as [y' eqy']. subst y. subst x. contradict H2. 
      + destruct H. subst x. destruct H0 as [y' Heqy]. subst y. destruct H2.
      +  destruct H.  destruct H as [x0 [y0 [Heqx Heqy]]].
         subst x. subst y. apply (@monotone m1) with (x := x0). exact H1.  exact H2.
         destruct H as [x0 [y0 [Heqx Heqy]]].
         subst x. subst y. apply (@monotone m2) with (x := x0). exact H1. exact H2.
      +  destruct H.  subst x y. destruct H2.
    - apply preservesSubrelation; destruct m1; destruct m2; assumption.    
    - intros x y z.  destruct x; destruct y; destruct z; firstorder eauto.
      + destruct s1; destruct s0; destruct s; destruct m1; destruct m2; firstorder eauto. apply transvalid0 with (y := w0); assumption.
        apply transvalid1 with (y := w0); assumption.
      + destruct s0; destruct H0.
      + destruct s; destruct H.   
  Defined.

  Lemma disjunctionLeftEquiv (m1 m2: KripkeModel) ϕ w: (@evalK m1 ϕ w) <-> (@evalK (disjunctionModel m1 m2) ϕ (Some (inl w))).
  Proof.
    revert w.
    induction ϕ;try eauto.
    - split.
      + intros. intros w' H'. destruct w'; try destruct H'. destruct s; try destruct H'.
        apply IHϕ. apply H. apply H'.
      + intros H. intros w' H'.  apply IHϕ. apply H. exact H'.
    - split.
      + intros H w' H' H''.
        destruct w'; try destruct H'. destruct s; try destruct H'.  apply IHϕ2.
        apply H. exact H'. apply IHϕ1; auto.
      + intros H w' H' H''. apply IHϕ2.  apply H. assumption. apply IHϕ1. auto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
  Qed.

  Lemma disjunctionRightEquiv (m1 m2: KripkeModel) ϕ w: (@evalK m2 ϕ w) <-> (@evalK (disjunctionModel m1 m2) ϕ (Some (inr w))).
  Proof.
    revert w.
    induction ϕ;try eauto.
    - split.
      + intros. intros w' H'. destruct w'; try destruct H'. destruct s; try destruct H'.
        apply IHϕ. apply H. apply H'.
      + intros H. intros w' H'.  apply IHϕ. apply H. exact H'.
    - split.
      + intros H w' H' H''.
        destruct w'; try destruct H'. destruct s; try destruct H'.  apply IHϕ2.
        apply H. exact H'. apply IHϕ1; auto.
      + intros H w' H' H''. apply IHϕ2.  apply H. assumption. apply IHϕ1. auto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
    - intro. firstorder eauto.
  Qed.    

  Lemma disjunctionSubmodelm1 (m1 m2: KripkeModel) w ϕ:  ~(@evalK m1 ϕ w) -> ~(@evalK (disjunctionModel m1 m2) (ϕ) (Some (inl w))).
  Proof.                                 
    intros  Hw.
    rewrite <- disjunctionLeftEquiv. auto. 
  Qed.   

  Lemma disjunctionSubmodelm2 (m1 m2: KripkeModel) ϕ w: ~(@evalK m2 ϕ w) -> ~(@evalK (disjunctionModel m1 m2) (ϕ) (Some (inr w))).
  Proof.                                 
    intros Hw.
    rewrite <- disjunctionRightEquiv. auto. 
  Qed.

  Lemma disjunctionIEL (m1 m2: KripkeModel): isIEL m1 -> isIEL m2 -> isIEL (disjunctionModel m1 m2).
  Proof.
    intros H H0.
    intro. 
    destruct w.
    - destruct s.
      +  destruct (H w) as [hw HW]. exists (Some (inl hw)). auto.
      + destruct (H0 w) as [hw HW]. exists (Some (inr hw)). auto. 
    - exists None. cbv; auto.
  Qed.    

  Lemma disjunctionPropertyIEL ϕ ψ:
    (@ndT normal ∅ (ϕ ∨ ψ)) <-> (∅ ⊢T+ ϕ \/ ∅ ⊢T+ ψ).
  Proof.
    split.
    - apply contra.
      intros H H1.
      apply t in H. destruct  H.
      apply entailsToNotIEL in H.
      apply entailsToNotIEL in H0.
      enough (exists m w, isIEL m /\ ~ evalK (ϕ ∨ ψ) w).
      destruct H2 as [djm [w [DJIEL DJM] ]].
      apply ndSoundIEL with (M := djm) (w := w) in H1.
      2: auto.
      2: firstorder eauto.
      apply DJM. apply H1.

      destruct H as [mphi [ielHphi evalHphi]].
      destruct H0 as [mpsi [ielHpsi evalHpsi]].
      exists (disjunctionModel mphi mpsi).
      exists None.
      split.
      apply  disjunctionIEL; destruct evalHpsi; destruct evalHphi; auto.
      intro H.
      destruct H.
      + destruct evalHphi.
        eapply disjunctionSubmodelm1 in H2. 
        apply H2.
        apply (@eval_monotone (disjunctionModel mphi mpsi) ϕ) with (w := None).
        cbv. auto. exact H.
      + destruct evalHpsi.  
        eapply disjunctionSubmodelm2 in H2.
        apply H2. 
        apply (@eval_monotone (disjunctionModel mphi mpsi) ψ) with (w := None);
          cbv; auto.
    - intros. destruct H; firstorder using nd.    
  Qed. 

  Lemma disjunctionPropertyIELM ϕ ψ:
    (∅ ⊢T- (ϕ ∨ ψ)) <-> (∅ ⊢T- ϕ \/ ∅ ⊢T- ψ).
  Proof.
    split.
    - apply contra.
      intros H H1.
      apply t in H. destruct  H.
      apply entailsToNot in H.
      apply entailsToNot in H0.
      enough (exists m w, ~ @evalK m (ϕ ∨ ψ) w).
      destruct H2 as  [djm [w DJM]].
      apply ndSoundIEL with (M := djm) (w := w) in H1. auto. 
      2: firstorder eauto.
      cbn; auto.

      destruct H as [mphi [ielHphi evalHphi]].
      destruct H0 as [mpsi [ielHpsi evalHpsi]].
      exists (disjunctionModel mphi mpsi).
      exists None.
      intro H.
      destruct H.
      + 
        eapply disjunctionSubmodelm1 in evalHphi. 
        apply evalHphi.
        apply (@eval_monotone (disjunctionModel mphi mpsi) ϕ) with (w := None).
        cbv. auto. exact H.
      +
        eapply disjunctionSubmodelm2 in evalHpsi.
        apply evalHpsi. 
        apply (@eval_monotone (disjunctionModel mphi mpsi) ψ) with (w := None);
          cbv; auto.
    - intros. destruct H; firstorder using nd.    
  Qed. 

  (** *** Disjunction Property for verifications *)  
  
  Corollary disjunctionK ϕ ψ: ∅ ⊢T+ K (ϕ ∨ ψ) -> ( ∅ ⊢T+ K ϕ \/ ∅ ⊢T+ K ψ).  
  Proof.
    intros.
    apply reflectionAdmissibleIEL in H.
    apply disjunctionPropertyIEL in H.
    destruct H.
    + left. apply ndtKpos.  auto. 
    + right. apply  ndtKpos. auto. 
  Qed.

  Corollary disjunctionKIELM ϕ ψ: ∅ ⊢T- K (ϕ ∨ ψ) -> ( ∅ ⊢T- K ϕ \/ ∅ ⊢T- K ψ).  
  Proof.
    intros.
    apply reflectionAdmissibleIELM in H.
    apply disjunctionPropertyIELM in H.
    destruct H.
    + left. apply ndtKpos.  auto. 
    + right. apply  ndtKpos. auto. 
  Qed.

End DisunctionProp.
