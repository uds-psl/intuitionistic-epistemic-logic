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
