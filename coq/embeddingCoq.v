(** * Shallow Embedding type-based nd into Coq *)
Require Export forms.
Require Import List.
Import ListNotations.
Fixpoint In f (l: list form) : Type :=
  match l with nil => False
          | (x::xr) => (x = f) + (In f xr)
  end. 
Notation "x 'el' A" := (In x A) (at level 70).
Section Shallow.
  Variable env: nat -> Type.
Inductive inhabited (A:Type) : Type := inhabits : A -> inhabited A.
(** Define list based nd for IEL **)
Inductive nd: list form -> form -> Type :=
  ndE A s: nd A ⊥ -> nd A s
| ndA A s: s el A -> nd A s
| ndII A s t: nd (s::A) t -> nd A (Imp s t)
| ndIE A s t: nd A (Imp s t) -> nd A s -> nd A t

| ndCI A s t: nd A s -> nd A t -> nd A (And s t)
| ndCEL A s t: nd A (And s t) -> nd A s
| ndCER A s t: nd A (And s t) -> nd A t

| ndDIL A s t: nd A s -> nd A (Or s t)
| ndDIR A s t: nd A t -> nd A (Or s t)
| ndDE A s t v: nd A (Imp s v) -> nd A (Imp t v) -> nd A (Or s t) -> nd A v

| ndKpos A s: nd A s -> nd A (K s)
| ndKImp A s t: nd A (K(s ⊃ t)) -> nd A ((K s) ⊃ (K t))
| ndPosIntro A s: nd A (K s) -> nd A (¬ ¬ s).

Fixpoint translate (f: form) : Type :=
    match f with
    | K x => inhabited (translate x)
    | Imp s t => (translate s) -> (translate t)
    | And s t => (translate s) * (translate t)
    | Or s t => (translate s) + (translate t)
    | Bot => False
    | Var x => (env x)
    end.

Definition  multiTrans (l: list form) (f: form) : Type := (forall ϕ, In ϕ l -> (translate ϕ)) -> (translate f). 

Lemma ndCorrect: forall l ϕ, nd l ϕ ->  ((multiTrans l ϕ)).
Proof.
  intros l ϕ H.
  induction H; firstorder eauto.
  -  intros H1. simpl translate. intro H2. apply IHnd.  intros ψ H3.
     destruct H3.
     + rewrite<- e. auto.
     +   apply H1. auto.
Defined.          


Lemma ndCorrectNil: forall ϕ, nd nil ϕ -> translate ϕ.
Proof.
  intros ϕ H.
  apply (ndCorrect H).
  intros ψ Hpsi. destruct Hpsi.
Qed.
(** ** Consistency of nd, if lifted to type *)
Lemma nd_type_consistent: (nd [] ⊥) -> False.
Proof.
  intro H. apply ndCorrect in H. cbv  in H.  apply H. firstorder eauto.  
Qed.

End Shallow.

