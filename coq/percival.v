(** * IEL and the knowability paradox *)
(** ** Church-Fitch *)
Section Church.
  Axiom K: Prop -> Prop.
  Axiom Diamond: Prop -> Prop.
  Axiom Box: Prop -> Prop.

  Axiom Nec: forall (P: Prop), P -> Box P.
  Axiom knowability: forall (P: Prop), P -> Diamond (K P). 
  (* K is factive *)
  (* K is factive *)
  Hypothesis K_fact: forall A, K A -> A.
  (* K is distributes over conjucntion *)
  Hypothesis k_distr: forall A B, K(A /\ B) -> K A /\ K B.
  (* Interdef *)
  Hypothesis interdef: forall A,  Box (~A) -> ~Diamond A. 
  Lemma interdefTransl (X: Type) (x: X) (P: X -> Prop): (~exists x, P x) <-> (forall x, ~(P x)).
  Proof.   firstorder eauto. 
  Qed.

  Lemma CF: ~(exists A, A /\ ~(K A)).
  Proof.
    intro.
    destruct H as (A & HK). specialize (knowability  _ HK). intro.
    assert (~(K (A /\ ~ K A))). 
    {
      intro. apply k_distr in H0.  destruct H0.  apply K_fact in H1.  congruence. 
    }
    apply Nec in H0.
    apply interdef in H0.
    congruence.
  Qed.   
End Church.
  
(** ** Percivals Criticism of intuitionistic reflection *)

Section Percival.
  (* Introduce K operator using axioms *)
  Definition factive (K: Prop -> Prop) := forall P, K P -> P.
  Axiom irefl: forall (P: Prop), P -> ~~(K P).

  Lemma pc1: forall P, ~(K P) -> ~P.
  Proof.
    intros. intro. assert (~~~K P). tauto. apply H1. apply irefl. auto.
  Qed.

  Lemma pc2: factive K ->forall P, (~(K P) <-> ~P).
  Proof.
    intros F P.
    split; auto using pc1, F.
    - intro. intro. apply F in H0. congruence.
  Qed.

  Lemma pc3:forall P, ~(~(K P) /\ ~(K (~P))).
  Proof.
    intros.
    intros [H1 H2]. apply pc1 in H1. apply pc1 in  H2.   tauto.
  Qed.   
End Percival.

(** We can also proof all three in IEL *)
