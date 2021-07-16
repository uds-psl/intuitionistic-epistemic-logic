(** * Syntax of IEL *)
Require Import PslBase.Base.
Require Import Permutation.

Section forms.
Inductive form :=
  K    : form -> form
| Imp  : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Bot  : form
| Var  : nat -> form. 

Inductive formIPC :=
| ImpI  : formIPC -> formIPC -> formIPC
| AndI  : formIPC -> formIPC -> formIPC
| OrI   : formIPC -> formIPC -> formIPC
| BotI  : formIPC
| VarI  : nat       -> formIPC. 

(** Equality on forms is decidable *)
Lemma form_eq_dec: forall (x y:form), {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Qed.  

Instance form_eq_dec' :
  eq_dec form.
Proof.
  apply form_eq_dec.
Defined. 
Canonical Structure eqtf :=  (EqType form).
(** ** Size *)
Fixpoint size (f: form) : nat :=
  match f  with
  | K x => S (size x)
  | Imp s t => S(size s + size t)
  | And s t => S(size s + size t)
  | Or s t => S(size s + size t)
  | Bot => 0
  | Var x => 0
  end.

Lemma formI_eq_dec: forall (x y: formIPC), {x = y} + {x <> y}.
Proof.
  repeat decide equality.
Qed.  
End forms. 
(* Define some notation for formulas *)
Notation "⊥" := Bot.
Notation "¬ ϕ" := (Imp ϕ ⊥) (at level 100, right associativity).
Infix "∧" := And (left associativity, at level 101).
Infix "∨" := Or  (left associativity, at level 102).
Infix "⊃" := Imp (right associativity, at level 103).
Notation "A <--> B" := (And (Imp A B) (Imp B A)) (left associativity, at level 104).

(** ** Countability *)
Require Import gentree.

Fixpoint pickleNat (n: nat) : Ntree :=
  match n with
    0 => NBranch 0 []
  | (S n) => NBranch 1 [(pickleNat n)]
  end.

Fixpoint unpickleNat (T: Ntree) : option nat :=
  match T with
    NBranch 0 [] => Some 0 
  | NBranch 1 [a] => (match unpickleNat a with None => None | Some x => Some (S x) end)
  | _ => None
  end. 
                        
Fixpoint pickle (f: form) : Ntree :=
  match f with
    K A => NBranch 0 [pickle A]
  | Imp A B => NBranch 1 [pickle A; pickle B]                
  | And A B => NBranch 2 [pickle A; pickle B]
  | Or A B => NBranch 3 [pickle A; pickle B]
  | Bot => NBranch 4 []
  | Var a => NBranch 5 [pickleNat a]                
  end.                    

Fixpoint unpickle (T: Ntree) : option form :=
  match T with
  | NBranch 0 [a] => (match unpickle a with None => None | Some x => Some (K x) end)
  | NBranch 1 [a; b] => (match (unpickle a, unpickle b) with  (Some x, Some y) => Some (Imp x y) | _ => None end)
  | NBranch 2 [a; b] => (match (unpickle a, unpickle b) with  (Some x, Some y) => Some (And x y) | _ => None end)
  | NBranch 3 [a; b] => (match (unpickle a, unpickle b) with  (Some x, Some y) => Some (Or x y) | _ => None end)
  | NBranch 4 []     => Some Bot
  | NBranch 5 [a] => (match unpickleNat a with None => None | Some x => Some (Var x) end)              
  | _ => None
  end. 

(* Cancellation Lemmata for pickle unpickle **)
Definition Pickle (A: Type) := A -> Ntree.
Definition Unpickle (A: Type) := Ntree -> (option A). 
Definition pcancel {A: Type} (f: Pickle A) (g: Unpickle A) := forall (a: A), (g (f a)) = Some a.

Lemma cancelNat: pcancel pickleNat unpickleNat. 
Proof.
  intros a.
  induction a; eauto. cbn.   rewrite IHa.  auto.
Qed.

Lemma cancelForm: pcancel pickle unpickle.
Proof.
  intros f.
  induction f; eauto. all: cbn; try rewrite IHf; try rewrite IHf1, IHf2;  auto.
  rewrite cancelNat.  auto. 
Qed.


Section Countability. 
  Definition countable_list__T T := {f: nat -> list T | forall t, exists n, In t (f n)}.
  Definition countable__T T := {f: nat -> option T | forall t, exists n, f n = Some t}.  

(*
  In the file gentree.v, it is proven that Ltrees can be embedded into list (nat * nat + nat)
  we can directly construct a list enumerator for this type. 
 *)
Definition listEnumerator (n: nat) : list ((nat * nat)+nat) :=

  (List.map (@inl (nat*nat) nat) (list_prod (seq 0 n) (seq 0 n))) ++ (List.map (@inr (nat*nat) nat) (seq 0 n)).

Lemma countableNatNatOpt : countable_list__T ((nat * nat)+nat).
  exists listEnumerator.
  intro t.
  - destruct t.
    destruct p.  exists (S (max n n0)). unfold listEnumerator. rewrite in_app_iff. left.
    apply in_map_iff. exists (n, n0).  rewrite list_prod_spec. split; auto. split.
    simpl fst. apply in_seq.  lia.
    simpl snd. apply in_seq. lia. 
    exists (S n). unfold listEnumerator. rewrite in_app_iff. right. apply in_map_iff. exists n. split; eauto. apply in_seq.  lia.
Defined.
(** We still need to proof, that if A is countable, so is list A *)
Section ListEnumerator.
  Variable (X: Type).
  Variable (L: nat -> list X).
  Notation "( A × B × .. × C )" := (list_prod .. (list_prod A B) .. C) (at level 0, left associativity).
  Notation "[ s | p ∈ A ]" :=
    (map (fun p => s) A) (p pattern).
  
  Fixpoint L_list (n : nat) : list (list X) :=
	  match n
	  with
	  | 0 => [ [] ]
	  | S n => L_list n ++ [x :: L | (x,L) ∈ (cumul L n × L_list n)]
	  end.
End ListEnumerator.
Lemma  countable_list {X} : countable_list__T X -> countable_list__T (list X).
Proof.
  intros [L H].
  eexists (L_list L).
  intro l.
  induction l.
  - exists 0. cbn. eauto.
  - destruct IHl as [n IH].  destruct (cumul_spec__T H a) as [m ?].
    exists (1 + n + m). cbn. intros. in_app 2.
    in_collect (a,l).
    all: eapply cum_ge'; eauto using L_list_cumulative; lia.
Defined.    
(** We show that having a pickle / unpickle function works well with list enumerators **)

(* Removes all None Elements from a list and deSomes the other *)
Fixpoint deOptionize {A: Type} (l: list (option A)) : list A :=
  match l with
    (Some x :: xr) => x::(deOptionize xr)
  | (_::xr) => deOptionize xr
  | nil => nil end.


Lemma deOptIn {A: Type} l (x: A): In x (deOptionize l) <-> In (Some x) l.
Proof.
  induction l. simpl deOptionize. tauto.
  split. intro. destruct a.
  simpl deOptionize in H. destruct H. rewrite H. left. auto. right. rewrite<- IHl. auto.
  right. apply IHl. apply H.
  intro. destruct H. rewrite H. simpl deOptionize. left. reflexivity. destruct a. simpl deOptionize. right. apply IHl. exact H. simpl deOptionize. apply IHl. exact H.
Qed.  
Lemma countableDecodeEncode (A B: Type)
      (code: A -> B)
      (decode: B -> option A)
      (H1:forall a, (decode (code a)) = Some a)
      (enumB: countable_list__T B)
  : countable_list__T A.
Proof.
  unfold enumerable__T.
  destruct enumB as [fb Hb].
  exists (fun n => (deOptionize (List.map decode (fb n)))).
  intro a. specialize (H1 a).
  specialize (Hb (code a)).
  destruct Hb. exists x. apply deOptIn. rewrite<- H1. apply in_map_iff. exists (code a).  split; tauto.
Defined.
(* Now we can show, that Ntrees are countable *)
Lemma enumLtree: countable_list__T Ntree. 
Proof.
  apply (@countableDecodeEncode Ntree (list ((nat*nat)+nat)) ntree_to_list (ntree_of_list [])  ).
  intro.
  pose (ntree_of_to_list [] [] a).
  rewrite app_nil_r in e.
  rewrite e.
  simpl ntree_of_list.
  reflexivity.
  apply countable_list.
  apply countableNatNatOpt. 
Defined.

(* With these lemmas in place, we can now obtain list counters for the types *)
Lemma form_countable: countable_list__T form.
  apply (@countableDecodeEncode form Ntree pickle unpickle cancelForm enumLtree).
Defined.


End Countability. 

Section enumerator_list_enumerator.

  Variable X : Type.
  Variables (T : nat -> list X).

  Definition e (n : nat) : option X :=
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
  Lemma countableT_countableLT (X: Type) : countable_list__T X -> countable__T X.
  Proof.
    intros. 
    unfold countable__T. destruct X0.   
    exists (e x).  intro. apply list_enumerator_to_enumerator.  auto. 
  Defined.

  Lemma countableForm: countable__T form.
    apply countableT_countableLT.
    apply form_countable.
  Defined.   

  Definition decodeOpt := proj1_sig countableForm.
  Definition decode (n: nat) : form.
    destruct (decodeOpt n).
    + exact f.
    + exact Bot.
  Defined.     
  Lemma decode_surj :  forall f, exists n, decode n = f.
  Proof.
    
    unfold decode;     destruct countableForm eqn:cnf. intro f.   destruct (e0 f).
    exists x0. 
    unfold decodeOpt. rewrite cnf. simpl. rewrite H.  reflexivity. 
  Qed. 


