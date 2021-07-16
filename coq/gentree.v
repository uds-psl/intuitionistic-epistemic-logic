(*
 * Source: https://github.com/christ2go/gherkin/blob/main/gentree.v
 *
 *)

Require Import Nat.
Require Import List.
Import ListNotations.
Require Import Relations.
Require Import PeanoNat. 

(** MTrees are the trees we pickle into
 *)
Inductive Ntree : Type := NLeaf: nat -> Ntree | NBranch:  nat -> list Ntree -> Ntree.

Section correct_ntree_ind.

Variables
  (A : Set)(P : Ntree -> Prop).
Hypotheses
  (H : forall (a:nat)(l:list (Ntree)), (forall x, In x l -> P x) -> P (NBranch a l))
  
 (H1 : forall t:Ntree, P t -> forall l:list (Ntree), (forall x, In x l -> P x) -> (forall x, In x (cons t l) -> P x))
 (H2: forall (n: nat), P(NLeaf n)).
Lemma  H0: forall x, In x [] -> P x.
  intros x H4.  destruct H4.
  Qed. 
Fixpoint ntree_ind2 (t:Ntree) : P t :=
  match t as x return P x with
  | NBranch a l =>
      H a l
        (((fix l_ind (l':list (Ntree)) : (forall x, In x l' -> P x) :=
             match l' as x return forall y, In y x -> P y with
             | nil => H0
             | cons t1 tl => H1 t1 (ntree_ind2 t1) tl (l_ind tl)
             end)) l)
  | NLeaf x => H2 x
  end.

End correct_ntree_ind.
Definition list_eq (A: Type) (f: A -> A -> bool) (l1 l2: list A) :=
  let fll := fix gh (l1 l2:list A) :=
                 match (l1, l2) with
                   (nil ,nil) => true
                 | (a::xr1, b::xr2) => if f a b then gh xr1 xr2 else false 
                 | _ => false end
             in fll l1 l2.
Fixpoint ntree_eq_dec (n1 n2: Ntree) : bool :=
  match (n1, n2) with
    (NLeaf a ,NLeaf b) => if Nat.eq_dec a b then true else false
  | (NBranch a xr1, NBranch b xr2) => if Nat.eq_dec a b then list_eq Ntree ntree_eq_dec xr1 xr2 else false 
  | _ => false end.

(**
   Note: I know that this proof is quite ugly, sorry :-(
 **)

Definition ntree_equal_dec_lemma: forall (x1 x2: Ntree), x1 = x2 <-> (ntree_eq_dec x1 x2) = true . 
Proof.
  intro.
  induction x1 using ntree_ind2.
  - intro x2. destruct x2.
    split.
    + intro. congruence.
    + intro.   simpl ntree_eq_dec in H1.  congruence.
    + split.
      intro.
      inversion H1.
      simpl ntree_eq_dec.
      destruct (Nat.eq_dec n n). subst l0. induction l. simpl.  reflexivity.
      simpl list_eq. enough (ntree_eq_dec a0 a0 = true).
      rewrite H2. apply IHl. intros x H4. apply H. right. assumption.
      rewrite H3.
      reflexivity.
      apply H.
      left. auto.
      reflexivity.
      congruence.
      intro H1.
      simpl ntree_eq_dec in H1.
      destruct (Nat.eq_dec a n).
      enough (l = l0).
      subst a.  subst l. reflexivity.
      assert (forall (l' l'': list Ntree), (forall x, In x l' -> In x l) -> list_eq Ntree ntree_eq_dec l' l'' = true <-> l' = l'').
      intro l'.
      induction l'.
      *  intro l''. intro Hx. destruct l''. firstorder eauto.
         split. intro. simpl list_eq in H2.  congruence.  intro. inversion H2.
      *  intros l'' H2. split.
         destruct l''.
         intro. simpl in  H3.  congruence. 
         intro. assert (l' = l'').
         apply IHl'. intros. apply H2. right. auto.
         simpl in  H3. destruct (ntree_eq_dec a0 n0). auto.  congruence.
         assert (a0 = n0).  apply H.  apply H2.  left. auto.
         simpl in H3. destruct ( ntree_eq_dec a0 n0). reflexivity. congruence.  rewrite H4.  rewrite H5.
         reflexivity.
         destruct l''. 
         intro. congruence.
         intro.
         simpl list_eq.
         inversion H3.
         enough((ntree_eq_dec n0 n0) = true).
         rewrite H4.
         inversion H3.  rewrite<- H6.
         apply IHl'. intros x H10. apply H2. right. auto.
         reflexivity.
         apply H. rewrite<- H5.
         apply H2. left. auto.
         reflexivity.
      *   apply H2.   intro. auto.
          auto.
      *      congruence.
  -    intro.       destruct H1.
       subst x1_2.
       apply IHx1_1.
       apply H.  auto.
  -  intro.
     destruct x2.
     + split.
       intro.
       inversion H.
       simpl ntree_eq_dec.  destruct (Nat.eq_dec n0 n0).  reflexivity.
       congruence.
       simpl ntree_eq_dec. destruct (Nat.eq_dec n n0). subst n. firstorder eauto.
       intro. congruence.
     +  split. intro. congruence.
        intro. simpl ntree_eq_dec in H. congruence.
Defined.

(*
  * We can embed Ltrees / Gentrees (Ltrees are just gentrees with nat as a type)
  * into lists of (nat * nat) + nat.
  * The proofs of this equivalence are based on proofs from the stdpp library.
  *)
Definition flatten {A: Type} (l: list (list A)) : list A :=
  List.fold_right (@app A) [] l. 

Fixpoint ntree_to_list (t : Ntree ) : list ((nat *  nat) + nat) :=
  match t with
  | NLeaf x => [inr x]
  | NBranch n ts =>  (flatten (List.map ntree_to_list ts )) ++ [ @inl (nat*nat) nat (length ts, n) ]
  end.

Fixpoint ntree_of_list 
    (k : list (Ntree)) (l : list (nat * nat + nat)) : option (Ntree) :=
  match l with
  | [] => head k
  | inr x :: l => ntree_of_list (NLeaf x :: k) l
  | inl (len,n) :: l =>
     ntree_of_list (NBranch n (rev' (firstn len k)) :: skipn len k) l
  end.

Tactic Notation "trans" constr(A) := transitivity A.

Lemma take_app_alt {A: Type} (l: list A) k :  firstn (length l) (l ++ k) = l.
Proof.
  induction l. 
  - reflexivity. 
  - simpl firstn.  rewrite IHl. reflexivity.
Qed.

Lemma drop_app_alt {A: Type} (l: list A) k :  skipn (length l) (l ++ k) = k.
Proof.
  induction l. 
  - reflexivity. 
  - simpl skipn.  rewrite IHl. reflexivity.
Qed.

Lemma ntree_of_to_list k l (t : Ntree) :
  ntree_of_list k (ntree_to_list t ++ l) = ntree_of_list (t :: k) l.
Proof.
  revert t k l. fix FIX 1. intros [|n ts] k l; simpl; auto.
    trans (ntree_of_list (rev' ts ++ k) ([inl (length ts, n)] ++ l)).
  -   rewrite<- app_assoc. revert k. generalize ([inl (length ts, n)] ++ l).
      induction ts as [|t ts'' IH]; intros k ts'''; simpl; auto.
      unfold rev. simpl rev_append.   rewrite<- app_assoc.  rewrite FIX. rewrite IH.
      unfold rev' at 2. simpl rev_append. rewrite rev_append_rev. rewrite<- app_assoc. simpl app at 3.  repeat rewrite<- app_assoc.  unfold rev'. 
     rewrite rev_append_rev. rewrite app_nil_r . reflexivity.
  -  simpl.
     enough ((length ts) = length (rev' ts)).
     rewrite H. 
     rewrite take_app_alt.
     rewrite drop_app_alt.
     unfold rev'. 
     rewrite rev_append_rev.
     rewrite<- rev_alt. 
     rewrite rev_involutive. 
     enough (ts++[] = ts).
     rewrite H1.
     reflexivity.
     induction ts. simpl. reflexivity. simpl. rewrite IHts.  reflexivity.
     unfold rev'. 
     rewrite rev_append_rev.
     enough ((rev ts)++[] = rev ts).
     rewrite H1.
     symmetry. apply rev_length.
     induction (rev ts). simpl. reflexivity. simpl. rewrite IHl0.  reflexivity.
     symmetry. unfold rev'. 
     rewrite rev_append_rev. rewrite app_nil_r .  apply rev_length.
Qed.


Require Import List.
Import ListNotations.

Definition cumulative {X} (L: nat -> list X) :=
  forall n, exists A, L (S n) = L n ++ A.
  Global Hint Extern 0 (cumulative _) => intros ?; cbn; eauto : core.

Lemma cum_ge {X} {L: nat -> list X} {n m} :
  cumulative L -> m >= n -> exists A, L m = L n ++ A.
Proof.
  induction 2 as [|m _ IH].
  - exists nil. now rewrite app_nil_r.
  - destruct (H m) as (A&->), IH as [B ->].
    exists (B ++ A). now rewrite app_assoc.
Qed.

Lemma cum_ge' {X} {L: nat -> list X} {x n m} :
  cumulative L -> In x (L n) -> m >= n -> In x (L m).
Proof.
  intros ? H [A ->] % (cum_ge (L := L)). apply in_app_iff. eauto. eauto.
Qed.

Definition list_enumerator {X} (L: nat -> list X) (p : X -> Prop) :=
  forall x, p x <-> exists m, In x (L m).
Definition list_enumerable {X} (p : X -> Prop) :=
  exists L, list_enumerator L p.

Definition list_enumerator__T' X f := forall x : X, exists n : nat, In x (f n).
Notation list_enumerator__T f X := (list_enumerator__T' X f).
Definition list_enumerable__T X := exists f : nat -> list X, list_enumerator__T f X.
Definition inf_list_enumerable__T X := { f : nat -> list X | list_enumerator__T f X }.

Section enumerator_list_enumerator.
  Variable X : Type.
  Variable p : X -> Prop.
  Variables (e : nat -> option X).

  Let T (n : nat) : list X :=  match e n with Some x => [x] | None => [] end.

  Lemma enumerator_to_list_enumerator : forall x, (exists n, e n = Some x) <-> (exists n, In x (T n)).
  Proof.
    split; intros [n H].
    - exists n. unfold T. rewrite H. firstorder.
    - unfold T in *. destruct (e n) eqn:E. inversion H; subst. eauto. destruct H1.  destruct H. 
  Qed.

End enumerator_list_enumerator.

Definition enumerable {X} (p : X -> Prop) := exists f, forall x, p x <-> exists n : nat, f n = Some x.
Definition enumerable__T X := exists f : nat -> option X, forall x, exists n, f n = Some x.


Lemma enumerable_list_enumerable {X} {p : X -> Prop} :
  enumerable p -> list_enumerable p.
Proof.
  intros [f Hf]. eexists.
  unfold list_enumerator.
  intros x. rewrite <- enumerator_to_list_enumerator.
  eapply Hf.
Qed.

Lemma enumerable__T_list_enumerable {X} :
  enumerable__T X -> list_enumerable__T X.
Proof.
  intros [f Hf]. eexists.
  unfold list_enumerator.
  intros x. rewrite <- enumerator_to_list_enumerator.
  eapply Hf.
Qed.
(* bijection from nat * nat to nat *)
Definition embed '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition unembed (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.

Lemma embedP {xy: nat * nat} : unembed (embed xy) = xy.
Proof.
  assert (forall n, embed xy = n -> unembed n = xy).
    intro n. revert xy. induction n as [|n IH].
      intros [[|?] [|?]]; intro H; inversion H; reflexivity.
    intros [x [|y]]; simpl.
      case x as [|x]; simpl; intro H.
        inversion H.
      rewrite (IH (0, x)); [reflexivity|].
      inversion H; simpl. rewrite Nat.add_0_r. reflexivity.
    intro H. rewrite (IH (S x, y)); [reflexivity|]. 
    inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
  apply H. reflexivity.
Qed.

Lemma unembedP {n: nat} : embed (unembed n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. revert IH. case (unembed n). intros x y.
  case x as [|x]; intro Hx; rewrite <- Hx; simpl.
    rewrite Nat.add_0_r. reflexivity.
  rewrite ?Nat.add_succ_r. simpl. rewrite ?Nat.add_succ_r. reflexivity. 
Qed.
Arguments embed : simpl never.


Module EmbedNatNotations.
  Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).
End EmbedNatNotations.
Section enumerator_list_enumerator.

  Variable X : Type.
  Variables (T : nat -> list X).

  Let e (n : nat) : option X :=
    let (n, m) := unembed n in
    nth_error (T n) m.

  Lemma list_enumerator_to_enumerator : forall x, (exists n, e n = Some x) <-> (exists n, In x (T n)).
  Proof.
    split; intros [k H].
    - unfold e in *.
      destruct (unembed k) as (n, m).
      exists n. eapply (nth_error_In _ _ H).
    - unfold e in *.
      eapply In_nth_error in H as [m].
      exists (embed (k, m)). now rewrite embedP, H.
  Qed.

End enumerator_list_enumerator.

Definition enumerator {X} (f : nat -> option X) (P : X -> Prop) : Prop :=
	  forall x, P x <-> exists n, f n = Some x.


Lemma list_enumerator_enumerator {X} {p : X -> Prop} {T} :
  list_enumerator T p -> enumerator (fun n => let (n, m) := unembed n in
    nth_error (T n) m) p.
Proof.
  unfold list_enumerator.
  intros H x. rewrite list_enumerator_to_enumerator. eauto.
Qed.

Lemma list_enumerable_enumerable {X} {p : X -> Prop} :
  list_enumerable p -> enumerable p.
Proof.
  intros [T HT]. eexists.
  unfold list_enumerator.
  intros x. rewrite list_enumerator_to_enumerator.
  eapply HT.
Qed.

Lemma list_enumerable__T_enumerable {X} :
  list_enumerable__T X -> enumerable__T X.
Proof.
  intros [T HT]. eexists.
  unfold list_enumerator.
  intros x. rewrite list_enumerator_to_enumerator.
  eapply HT.
Qed.

Lemma enum_enumT {X} :
  enumerable__T X <-> list_enumerable__T X.
Proof.
  split.
  eapply enumerable__T_list_enumerable.
  eapply list_enumerable__T_enumerable.
Qed.

Definition to_cumul {X} (L : nat -> list X) := fix f n :=
  match n with 0 => [] | S n => f n ++ L n end.

Lemma to_cumul_cumulative {X} (L : nat -> list X) :
  cumulative (to_cumul L).
Proof.
  eauto.
Qed.

Lemma to_cumul_spec {X} (L : nat -> list X) x :
  (exists n, In x (L n)) <-> exists n, In x (to_cumul L n).
Proof.
  split.
  - intros [n H].
    exists (S n). cbn. eapply in_app_iff. eauto.
  - intros [n H].
    induction n; cbn in *.
    + inversion H.
    + eapply in_app_iff in H as [H | H]; eauto.
Qed.

Lemma cumul_In {X} (L : nat -> list X) x n :
  In x (L n) -> In x (to_cumul L (S n)).
Proof.
  intros H. cbn. eapply in_app_iff. eauto.
Qed.

Lemma In_cumul {X} (L : nat -> list X) x n :
  In x (to_cumul L n) -> exists n, In x (L n).
Proof.
  intros H. eapply to_cumul_spec. eauto.
Qed.

Lemma Cumul_Step {X} (L : nat -> list X) x n :
  forall m, n < m -> In x (L n) -> In x (to_cumul L m).
Proof.
  intros m. intros E. induction E. firstorder eauto.  apply cumul_In. assumption.
  intro. simpl to_cumul. apply in_app_iff. left. apply IHE. assumption.
Qed.

Global Hint Resolve cumul_In In_cumul : core.

Lemma list_enumerator_to_cumul {X} {p : X -> Prop} {L} :
  list_enumerator L p -> list_enumerator (to_cumul L) p. 
Proof.
  unfold list_enumerator.
  intros. rewrite H.
  eapply to_cumul_spec.
Qed.

Lemma cumul_spec__T {X} {L} :
  list_enumerator__T L X -> list_enumerator__T (to_cumul L) X.
Proof.
  unfold list_enumerator__T.
  intros. now rewrite <- to_cumul_spec.
Qed.

Lemma cumul_spec {X} {L} {p : X -> Prop} :
  list_enumerator L p -> list_enumerator (to_cumul L) p.
Proof.
  unfold list_enumerator.
  intros. now rewrite <- to_cumul_spec.
Qed.

Module ListAutomationNotations.

  Notation "x 'el' L" := (In x L) (at level 70).
  Notation "A '<<=' B" := (incl A B) (at level 70).

  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).

End ListAutomationNotations.
Import ListAutomationNotations.


Ltac in_app n :=
  (match goal with
  | [ |- In _ (_ ++ _) ] => 
    match n with
    | 0 => idtac
    | 1 => eapply in_app_iff; left
    | S ?n => eapply in_app_iff; right; in_app n
    end
  | [ |- In _ (_ :: _) ] => match n with 0 => idtac | 1 => left | S ?n => right; in_app n end
  end) || (repeat (try right; eapply in_app_iff; right)).


Require Import Lia Arith.
Local Set Implicit Arguments.
Local Unset Strict Implicit.

Global Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end : core.

Global Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
end : core.
Lemma incl_nil X (A : list X) :
  nil <<= A.
Proof. intros x []. Qed.

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
Global Hint Resolve in_eq in_nil in_cons in_or_app : core.
Global Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil : core.

Lemma app_incl_l X (A B C : list X) :
A ++ B <<= C -> A <<= C.
Proof.
firstorder eauto.
Qed.

Lemma app_incl_R X (A B C : list X) :
A ++ B <<= C -> B <<= C.
Proof.
firstorder eauto.
Qed.

Lemma cons_incl X (a : X) (A B : list X) : a :: A <<= B -> A <<= B.
Proof.
intros ? ? ?. eapply H. firstorder.
Qed.

Lemma incl_sing X (a : X) A : a el A -> [a] <<= A.
Proof.
now intros ? ? [-> | [] ].
Qed.

Global Hint Resolve app_incl_l app_incl_R cons_incl incl_sing : core.

Global Hint Extern 4 (_ el map _ _) => eapply in_map_iff : core.
Global Hint Extern 4 (_ el filter _ _) => eapply filter_In : core.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]; congruence. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Require Import Setoid Morphisms.

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Local Notation "A === B" := (equi A B) (at level 70).
Global Hint Unfold equi : core.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed. 
Notation cumul := (to_cumul).

Ltac inv H := inversion H; subst; clear H.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.
Definition is_true (b : bool) := b = true.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Lemma Dec_reflect (X: Prop) (d: dec X) :
  is_true (Dec X) <-> X.
Proof.
  destruct d as [A|A]; cbv in *; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> is_true (Dec X).
Proof.
  destruct d as [A|A]; cbn; intuition congruence.
Qed.

(* Lemma Dec_auto_not (X: Prop) (d: dec X) : *)
(*   ~ X -> ~ Dec X. *)
(* Proof. *)
(*   destruct d as [A|A]; cbn; tauto. *)
(* Qed. *)

(* Hint Resolve Dec_auto Dec_auto_not : core. *)
Global Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.
Tactic Notation "decide" "_" :=
  destruct (Dec _).

Lemma Dec_true P {H : dec P} : dec2bool (Dec P) = true -> P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Lemma Dec_false P {H : dec P} : dec2bool (Dec P) = false -> ~P.
Proof.
  decide P; cbv in *; firstorder.
Qed.

Global Hint Extern 4 =>
match goal with
  [ H : dec2bool (Dec ?P) = true  |- _ ] => apply Dec_true in  H
| [ H : dec2bool (Dec ?P) = true |- _ ] => apply Dec_false in H
end : core.

(* Decided propositions behave classically *)

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

(* Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto. 
Qed.



Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Qed.

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Qed.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Qed.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. firstorder eauto.
Qed.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. firstorder eauto.
Qed.

(* Discrete types *)
Require Import PslBase.EqDec. 


Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.

Instance unit_eq_dec :
  eq_dec unit.
Proof.
  unfold dec. decide equality. 
Qed.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.


Instance sum_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X + Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance option_eq_dec X :
  eq_dec X -> eq_dec (option X).
Proof.
  unfold dec. decide equality.
Defined.

Instance Empty_set_eq_dec:
  eq_dec Empty_set.
Proof.
  unfold dec. decide equality.
Qed.

Instance True_eq_dec:
  eq_dec True.
Proof.
  intros x y. destruct x,y. now left.
Qed.

Instance False_eq_dec:
  eq_dec False.
Proof.
  intros [].
Qed.


  Notation "[ s | p ∈ A ',' P ]" :=
    (map (fun p => s) (filter (fun p => Dec P) A)) (p pattern).

Section L_list_def.
  Context {X : Type}.
  Variable (L : nat -> list X).
  Import ListAutomationNotations.
  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

  Fixpoint L_list (n : nat) : list (list X) :=
	  match n
	  with
	  | 0 => [ [] ]
	  | S n => L_list n ++ [x :: L | (x,L) ∈ (cumul L n × L_list n)]
	  end.
	
  
End L_list_def.

Lemma L_list_cumulative {X} L : cumulative (@L_list X L).
Proof.
  intros ?; cbn; eauto. 
Qed.

Ltac in_collect a :=
  eapply in_map_iff; exists a; split; [ eauto | match goal with
                                              _ => try (rewrite !in_prod_iff; repeat split) end ].


Lemma enumerator__T_list {X} L :
  list_enumerator__T L X -> list_enumerator__T (L_list L) (list X).
Proof.
  intros H l.
  induction l.
  - exists 0. cbn. eauto.
  - destruct IHl as [n IH].
    destruct (cumul_spec__T H a) as [m ?].
    exists (1 + n + m). cbn. intros. in_app 2.
    in_collect (a,l).
    all: eapply cum_ge'; eauto using L_list_cumulative; lia.
Qed.

Section L_sum_def.
  Context {X1 X2 : Type}.
  Variables (L1 : nat -> list X1) (L2: nat -> list X2).
  Import ListAutomationNotations.
  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

  Definition L_sum_list (n : nat) : list (X1+X2) :=
	  (List.map inl (L1 n)) ++ (List.map inr (L2 n))
	 .
	
  
End L_sum_def.


Lemma enumerator_sum_list {X1 X2} L1 L2 :
  list_enumerator__T L1 X1 -> list_enumerator__T L2 X2 -> list_enumerator__T (L_sum_list L1 L2) (X1+X2).
Proof.
  intros H1 H2.
  intro.
  destruct x.
  - destruct (H1 x) as [n1 Hn1]. 
   exists n1.  unfold L_sum_list. rewrite in_app_iff.
    left. apply in_map_iff. exists x. firstorder eauto.
  - destruct (H2 x).    unfold L_sum_list. exists x0. rewrite in_app_iff.
    right. apply in_map_iff.  exists x. split; firstorder eauto.
Qed.

(* Pickles X1 * X2 *)
Section L_prod_def.
  Context {X1 X2 : Type}.
  Variables (L1 : nat -> list X1) (L2: nat -> list X2).
  Import ListAutomationNotations.
  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).

  Definition L_prod_list (n : nat) : list (X1*X2) :=
	   ((L1 n) × (L2 n)).
	
  
End L_prod_def.

  Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
  Proof.
    revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
    rewrite in_app_iff, IHl, in_map_iff; simpl.
    split.
    + intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
    + intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
  Qed.

  
Lemma enumerator_prod_list {X1 X2} L1 L2 :
  list_enumerator__T L1 X1 -> list_enumerator__T L2 X2 -> list_enumerator__T (L_prod_list (to_cumul L1) (to_cumul L2)) (X1*X2).
Proof.
  intros H1 H2.
  intro.
  destruct x as [x1 x2].
  specialize (H1 x1). specialize (H2 x2).
  destruct H1 as [n1 Hn1]. destruct H2 as [n2 Hn2].
  exists (S(Nat.max n1 n2)).
  
  apply list_prod_spec.
  split.
  simpl fst.
  apply Cumul_Step with n1.
  lia.
  auto.

  apply Cumul_Step with n2.
  lia.
  exact Hn2.
Qed.



Lemma  enumerable_list {X} : list_enumerable__T X -> list_enumerable__T (list X).
Proof.
  intros [L H].
  eexists. now eapply enumerator__T_list.
Qed.


Lemma  enumerable_sum {X1 X2} : list_enumerable__T X1 -> list_enumerable__T X2 -> list_enumerable__T (X1+X2).
Proof.
  intros [L1 H1]. intros  [L2 H2].
  
  eexists. now eapply enumerator_sum_list.
Qed.

Lemma  enumerable_prod {X1 X2} : list_enumerable__T X1 -> list_enumerable__T X2 -> list_enumerable__T (X1*X2).
Proof.
  intros [L1 H1]. intros  [L2 H2].
  
  eexists. now eapply enumerator_prod_list.
Qed.
Lemma enumNatNat: enumerable__T ((nat*nat)+nat).
Proof.
  enough (H: enumerable__T nat).
  apply enum_enumT. 
  apply enumerable_sum.
  apply enum_enumT.
  apply enum_enumT.
  
  apply enumerable_prod. apply enum_enumT. apply H.
  apply enum_enumT. apply H. apply enum_enumT. apply H.
  unfold enumerable__T.
  exists (fun x => Some x).  intro. eauto.
Defined.
Lemma enumerableDecodeEncode (A B: Type)
      (code: A -> B)
      (decode: B -> option A)
      (H1: forall a, (decode (code a)) = Some a)
      (enumB: enumerable__T B)
  : enumerable__T A.
Proof.
  unfold enumerable__T.
  destruct enumB as [fb Hb].
  exists (fun n => match (fb n) with None => None | Some x => (decode x) end).
  intro a. specialize (H1 a).
  specialize (Hb (code a)).
  destruct Hb. exists x. rewrite H. apply H1.
Defined.

Lemma enumLtree: enumerable__T Ntree. 
Proof.
  apply (@enumerableDecodeEncode Ntree (list ((nat*nat)+nat)) ntree_to_list (ntree_of_list [])  ).
  intro.
  pose (ntree_of_to_list [] [] a).
  rewrite app_nil_r in e.
  rewrite e.
  simpl ntree_of_list.
  reflexivity.
  apply  enum_enumT. 
  apply enumerable_list.
  apply enum_enumT.
  apply enumNatNat.
Defined.


(** Ntrees are decidable **)
Instance Ntree_eq_dec :
  eq_dec Ntree.
Proof. 
  intros x y.
  destruct ((ntree_eq_dec x y)) eqn:H.
  left.
  apply ntree_equal_dec_lemma.
  auto.
  right. intro.  apply ntree_equal_dec_lemma in H1. congruence.
Defined.
