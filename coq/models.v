(** * Kripke-Models *)
Require Import nd forms.
Require Import Coq.Classes.CRelationClasses.
Require Import PslBase.Base.
Require Import PslBase.Lists.BaseLists. 

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

  Definition evalK' {M: KripkeModel} (Γ: context) :=
    fun w => forall s, (s el Γ) -> @evalK M s w.  

    Definition isIEL (M: KripkeModel) := forall w, exists w', verif w w'.

  Definition model_constraint  m :=
    if d then True else isIEL m.

  
  Definition entails Γ φ := 
    forall (M : KripkeModel), model_constraint M -> 
      ((forall w,evalK' Γ w -> @evalK M φ w)).
  
  Notation "Γ ⊨ φ" := (entails Γ φ) (at level 30). 

  (** Evaluation is monotone, that is if φ is true at world w
      and we can reach world v from w, φ true at v.  *)
  Lemma eval_monotone  (s: form)  w v: 
    cogn w v -> evalK s w -> evalK s v.
  
  Proof. 
    intros C H. induction s.
    + intros z H1. apply H. apply transvalid with (y := v); auto. 
    + intros z H1 H2. apply H. apply transitivity with v; auto. exact H2.
    + destruct H. split.
      ++ apply IHs1. auto.
      ++ apply IHs2. auto.
    + destruct H.
      ++ left. auto.
      ++ right. auto.
    + exfalso. apply H.
    + apply monotone with (x := w); auto.
  Qed.     

  Lemma monotone_ctx (A:context)  : 
    forall w w', cogn w w' -> evalK' A w -> evalK' A w'.
  Proof.
    intros. intros t H1.
    apply eval_monotone with (w := w); auto. 
  Qed.

End Models.
  Lemma soundness (Γ: context) (A: form) {D: DerivationType}:
    nd Γ A -> entails Γ A.
  Proof. 
    intro. induction H; try firstorder eauto. 
    - unfold entails. intros M' c w H0. unfold evalK.  intros r' H1 H2.  apply IHnd. auto. intros a Ha. destruct Ha; eauto.
      + subst s. apply H2.
      + apply eval_monotone with w; eauto.
    - unfold entails in IHnd1.  intros M c w H1. eapply IHnd1; auto. apply H1.  apply preorderCogn. apply IHnd2.  auto. auto. 
    -  
      intros M Mc w H1.
      intros w' cw Hs. specialize (IHnd M Mc w').   simpl evalK in IHnd.
      intros w'' wc. apply IHnd with w''; auto.  apply monotone_ctx with w; auto.
      apply preorderCogn.  
    - intros M c w H0. intros r H1.  apply eval_monotone with w.  apply vericont.  auto.  apply IHnd.  auto. auto.
    - intros M c w H2.   specialize (IHnd1 M c w H2).   destruct IHnd1.
      + eapply IHnd2; auto.  apply H2.  apply preorderCogn. 
      + eapply IHnd3; eauto. apply preorderCogn.
    - intros M Mc w H1 u c.
      apply monotone_ctx with (w' := u)  in H1. 2: auto.
      unfold isIEL in Mc. destruct (Mc u).   
      assert (evalK s x).
      {
        eapply IHnd; auto.
        apply H1. auto. 
      }
      intro.
      apply (H3 x).
      + apply vericont. auto.
      + apply H2.        
  Qed.
