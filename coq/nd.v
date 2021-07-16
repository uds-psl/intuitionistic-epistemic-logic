(**
   * Natural Deduction for IEL
**)
Require Export forms. 
Require Import List Permutation.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Max.
From Equations Require Import Equations.
Require Import PslBase.Base.

(** First, we add a type for contexts and proof some basic facts about subsets, define notation for element. **)
Definition theory := form -> Prop.
Notation context := (list form).   
Implicit Type Γ Ω : context.
Implicit Type T U: theory. 
Implicit Types ϕ ψ: form. 
Definition subset T U := forall ϕ, T ϕ -> U ϕ.
Definition equalCtx T U := forall ϕ, T ϕ <-> U ϕ.
Definition unionCtx T U := fun z => T z \/ U z.
Definition elem T ϕ := T ϕ.
Definition consT ϕ T := fun z => z = ϕ \/ T z. 
(** Define Notation for Contexts **)
Notation "A ∪ B" := (unionCtx A B) (at level 50).
Notation "A ≡ B" := (equalCtx A B) (at level 50).
Notation "a ∈ B" := (elem B a) (at level 20).
Notation "A ⊆ B" := (subset A B) (at level 10).
Notation "s # Γ" := (consT s Γ) (at level 30).
Inductive DerivationType := minus | normal.
  
Existing Class DerivationType.

(** ** Natural Deduction
We define deduction for contexts first *)

Inductive nd : forall (D: DerivationType), list form -> form -> Prop :=
| ndA {D} (Γ: list form) s :List.In s Γ -> (nd D Γ s)
| ndE {D} (Γ: list form) s : (nd D Γ Bot) -> (nd D Γ s)

| ndII {D} (Γ: list form) s t : (nd D (s::Γ) t) -> (nd D Γ (s ⊃ t))
| ndIE {D} (Γ: list form) s t : (nd D Γ (s ⊃  t)) -> (nd D Γ s) ->  (nd D Γ  t)
| ndKImp {D} (Γ: list form) s t: (nd D Γ (K(s ⊃ t))) -> (nd D Γ (K s ⊃ K t))
| ndKpos {D} (Γ: list form) s: (nd D Γ s) -> (nd D Γ (K s))
| ndCEL {D} (Γ: list form) s t: nd D Γ (s ∧ t) -> nd D Γ s
| ndCER {D} (Γ: list form) s t: nd D Γ (s ∧ t) -> nd D Γ t 
| ndCI  {D} (Γ: list form) s t: nd D Γ s -> nd D Γ t -> nd D Γ (s ∧ t)
| ndDIL {D} (Γ: list form) s t: nd D Γ s -> (nd D Γ (s ∨ t))
| ndDIR {D} (Γ: list form) s t: nd D Γ t -> (nd D Γ (s ∨ t))
| ndDE  {D} (Γ: list form) s t q: (nd D Γ (s ∨ t)) -> (nd D Γ (s ⊃ q)) -> (nd D Γ (t ⊃ q)) -> (nd D Γ q)
| ndIntRefl  (Γ: list form) s: (nd normal Γ (K s)) -> (nd normal Γ (¬ ¬s))
.

Definition ndminus := @nd minus.
Global Hint Constructors nd : core export.

(** We reduce the theory case to existence of a contained sublist *)
Definition ndT (D: DerivationType) T ϕ  :=
  exists L, (forall ψ, ψ el L -> T ψ) /\ @nd D L ϕ.

Arguments nd {_} _ _.
Arguments ndT {_} _ _.
(** Define notations for the derivation *)
Global Notation "Γ ⊢ φ" := (nd Γ φ) (at level 40).
Global Notation "T ⊢T φ" := (ndT T φ) (at level 40).

Global Notation "Γ ⊢+ φ" := (@nd normal Γ φ) (at level 40).
Global Notation "T ⊢T+ φ" := (@ndT normal T φ) (at level 40).

Global Notation "Γ ⊢- φ" := (@nd minus Γ φ) (at level 40).
Global Notation "T ⊢T- φ" := (@ndT minus T φ) (at level 40).

(** ** Weakening
    We show weakening for contexts and theories.
 **)
Section Weakening.
  Context {d : DerivationType}. 

  Fact ndtW φ T U:
     T ⊢T φ -> T ⊆ U ->  U ⊢T φ.
  Proof.
    firstorder eauto.
  Qed.
  
  Fact ndW Γ φ Ω :
    ( Γ ⊢ φ -> Γ <<= Ω ->  Ω ⊢ φ).
  Proof.
    intro H. revert Ω.  induction H;eauto.
  Qed.
  (* For backwards compatability *)
  Definition weak := ndW.
  
  Lemma consWeak Γ ϕ ψ: Γ ⊢ ϕ -> (ψ::Γ) ⊢ ϕ.
  Proof.
    intro. apply ndW with (Γ := Γ); firstorder eauto.
  Qed.

  Fact derivationExtensional Γ Ω : 
    (Γ === Ω) -> (forall φ, Ω ⊢ φ <-> Γ ⊢ φ).
  Proof.
    intros. split; firstorder eauto using ndW. 
  Qed.     
End Weakening.

(** ** Admissibility for theories
We show the nd rules admissible for theories (ndT), we need weakening for nd to do this *)
Section ndTAdmissible.
    Context {d : DerivationType}.
    Variable (T: theory). 
    Fact ndtA s: T s -> T ⊢T s.
    Proof.
      intro. exists [s]; firstorder eauto. rewrite<- H0.  auto.
    Qed.

    Fact ndtE s: ndT T ⊥ ->  T ⊢T s.
    Proof.
      intro.  destruct H as [lB Hb]. exists lB. split; firstorder eauto.
    Qed.

    Fact ndtII s t: (s#T) ⊢T t -> T ⊢T (s ⊃ t).
    Proof.
      intros.
      destruct H as [lT lht].
      exists (rem lT s). split. destruct lht. intros a Ha. specialize (H a). destruct H. apply in_rem_iff in Ha.  firstorder.
      subst a. apply in_rem_iff in Ha; tauto. auto. apply ndII. destruct lht. apply ndW with lT. auto.
      intros a Ha. decide (s = a). subst a; firstorder. right. firstorder eauto. 
    Qed.

    Fact ndtIE s t: (T) ⊢T (s ⊃ t) ->  T ⊢T s -> T ⊢T t.
    Proof.
      intros. destruct H as [lH H], H0 as [lH0 H0]. exists (lH++lH0). split.
      - intros ψ Hp. apply in_app_iff in Hp. firstorder  eauto.
      - apply ndIE with s.
        + apply ndW with lH. tauto. auto. 
        + apply ndW with lH0; firstorder eauto. 
    Qed.

    Fact ndtKImp s t: T ⊢T (K(s ⊃ t)) ->  T ⊢T (K s ⊃ K t).
    Proof.
       firstorder eauto.
    Qed.

    Fact ndtKpos s: T ⊢T s ->  T ⊢T (K s). 
    Proof.
       firstorder auto.
    Qed.   

    Fact ndtCEL s t: ndT T (s ∧ t) -> ndT T s.
    Proof.   
      firstorder eauto.
    Qed.

    Fact ndtCER s t: ndT T (s ∧ t) -> ndT T t.
    Proof.   
      firstorder eauto.
    Qed.
    
    Fact ndtCI s t: ndT T s -> ndT T t -> ndT T (s ∧ t).
    Proof.
      intros Hs Ht. destruct Hs as [ls [Hs1 Hs2]], Ht as [lt [Ht1 Ht2]].
      exists (ls++lt); firstorder eauto.
      - apply in_app_iff in H. destruct H; auto.
      - apply ndCI;   firstorder eauto using ndW.        
    Qed.

    Fact ndtDIL s t: ndT T s -> ndT T (s ∨ t).
    Proof.   
      firstorder eauto.
    Qed.

    Fact ndtDIR s t: ndT T t -> ndT T (s ∨ t).
    Proof.   
      firstorder eauto.
    Qed.
    
    Fact ndtDE s t q: ndT T (s ∨ t) -> ndT T (s ⊃ q) -> ndT T (t ⊃ q) -> ndT T q.
    Proof.
      intros Hs Ht Hq. destruct Hs as [ls [Hs1 Hs2]], Ht as [lt [Ht1 Ht2]], Hq as [lq [Hq1 Hq2]].
      exists (ls++lt++lq); firstorder eauto.
      -  apply in_app_iff in H; destruct H; auto. apply in_app_iff in H.  destruct H; eauto. 
      - apply ndDE with s t;   firstorder eauto using ndW.        
    Qed.

    Fact ndtIntRefl s: @ndT normal T (K s) -> @ndT normal T (¬ ¬ s). 
    Proof.
      intro. firstorder eauto.
    Qed.

End ndTAdmissible.   
(** We can show implication agreement: *)
Lemma ImpAgree (D: DerivationType) (Γ: theory) (a b: form) :
  Γ ⊢T (a ⊃ b) <-> (a#Γ ⊢T b).  
Proof.
  split.
  - intro H.  apply ndtIE with a; auto. apply ndtW with Γ; firstorder eauto.
    apply ndtA. firstorder eauto.
  -  intros.  apply ndtII. firstorder eauto.
Qed.      


(** List and context derivation transaltion *) 
Section Transl.
  Definition ctx2thy (Γ: context) : theory := fun x => In x Γ. 

  Lemma ndTEq {D: DerivationType} Γ s: nd Γ s <-> ndT (ctx2thy Γ) s.
  Proof.
    split.
    - intro. exists Γ.  firstorder eauto.
    - intro. destruct H as [lH H]. apply weak with lH; firstorder eauto.
  Qed.     
End Transl.  


Fixpoint shift (l: list form) (s: form) := 
  match l with
    nil  => s 
  | (x::xr) => (x ⊃ (shift xr s)) end.

Definition kIfy (l: list form) := map K l.

(** ** Modal shifting lemma *)
Section shifting. 
  Context {d : DerivationType}. 

  Lemma ImplDistr (Γ: context) (a b:form) : 
    (Γ ⊢ (K(a ⊃ b))) -> (Γ ⊢ ((K a) ⊃ (K b))).
  Proof.
    intros. apply ndKImp. exact H.
  Qed.
  
  Lemma ImpAss (Γ: context) (a b: form) :
    (Γ ⊢ (a ⊃ b)) <-> (nd (a::Γ) b).
  Proof.
    split.
    - intros.
      apply ndIE with (s := a). apply consWeak.  exact H.
      apply ndA. left. auto.
    - intros. apply ndII. exact H.
  Qed.


  Lemma kIfys2  (l: list form) (s: form): 
    forall Γ,  (Γ ⊢ (K (shift (l) (s)))) -> Γ ⊢ (shift (map K l) (K s)).
  Proof.
    induction l.
    + intros. simpl map. simpl shift. simpl shift in H. exact H.
    + intros. simpl map. simpl shift.  apply ndII. apply IHl. apply ImpAss.
      apply ndKImp. exact H.
  Qed.

  
  Lemma partialShift (l1 l2: context) (s: form):
     (l1++l2) ⊢ s <-> l1 ⊢ (shift l2 s). 
  Proof.
    revert l1. revert s.  induction l2; intros. 
    - simpl shift. rewrite app_nil_r. tauto. 
    - split.
      +  intro. apply ndII.  apply IHl2. apply ndW with (l1++a::l2); auto.
      +  intro.   apply ndW with (a::(l1++l2)).
         simpl shift in H. apply ImpAss in H.  apply IHl2 in H.  auto.
         intros x Hx.  destruct Hx as [Hx | Hx]; try apply in_app_iff in Hx; try subst x;try destruct Hx; eauto. 
  Qed.
  (** The next lemma shows that Krupski's rule from the sequent calculus is admissible in IEL *)
  Fact ndKKrupski (l1 l2: context) (s: form):
    (l1++l2++(List.map K l1)) ⊢ s -> (l2++(List.map K l1)) ⊢ (K s).
  Proof.
    intro.
    apply ndW with ((l2 ++ map K l1) ++ (map K l1)); auto. 
    apply partialShift, kIfys2, ndKpos.  apply-> partialShift.
    apply ndW with (l1++l2++map K l1);  auto. 
  Qed.

  (**
     Now we can prove the modal shifting lemma. 
   **)
  Definition unbox (Γ: theory) : theory := 
    fun x => Γ (K x).


  Lemma unbox_rewrite (Γ: theory): forall φ,
      (Γ (K φ)) <-> ((unbox Γ) φ).
  Proof.
    firstorder.
  Qed.
  Import ListNotations.

  Lemma modalShiftingLemma (Γ: theory)  (s: form): 
    ndT  (unbox Γ )  s -> ndT Γ  (K s).
  Proof.
    intros H0.
    destruct H0 as [y [H0]].
    exists (List.map K y).  split.
    - intros.  eauto. apply in_map_iff in H1.  destruct H1 as [z Hz]. destruct Hz. rewrite<- H1. apply H0.  auto. 
    -
      assert ((map K y) = ([]++(map K y))).
      { rewrite app_nil_l.  auto. }
      rewrite H1. apply partialShift, kIfys2, ndKpos.
      apply-> partialShift. rewrite app_nil_l.  auto.
  Qed.   

End shifting.

(** ** Prime theories and contexts
 *)
Section Contexts.
  Context {d : DerivationType}. 

  (** We begin by defining what a theory is *)
  Definition dedClosed (T: theory) :=  forall φ, (T ⊢T φ) -> T φ.
  Definition consistent (T: theory) : Prop := ~(T ⊢T ⊥).

  Definition is_prime (T: theory) := forall φ ψ, (T ⊢T (φ ∨ ψ) -> T ⊢T φ \/ T ⊢T ψ).
  Definition is_primeDN (T: theory) := forall φ ψ, ~~(T ⊢T (φ ∨ ψ) -> (T ⊢T φ \/ T ⊢T ψ)).

  (** *** Lindenbaum Lemma
    We will proof the Lindenbaum Lemma, which states that any set L of formulae which does not derive φ
     can be extended to a set 
    of formula which
    - is prime
    - is a theory
    - does not derive φ
   Note, that such a set is consistent (otherwise it would derive φ )
   **)

  Definition insert_form (Γ: theory) (φ ψ : form) : theory :=
    fun z => (Γ z \/ (~(ndT (ψ#Γ) φ) /\ ψ = z)).

  Definition insert_num (Γ: theory) (φ: form) (n: nat) := 
    insert_form Γ φ (decode n).  
  Equations maxn (Gamma: theory) (φ: form) (n: nat) : theory :=
    maxn Gamma φ 0     := Gamma;
    maxn Gamma φ (S n) := insert_num (maxn Gamma φ n) φ  n.
  
  Definition max (Gamma: theory) (φ: form) : theory := 
    fun z =>  
      exists n, (maxn Gamma φ n) z.
  
  (** *** Subset properties *)
  Lemma insert_form_subset (Γ: theory) φ ψ: Γ ⊆ (insert_form Γ φ ψ).
  Proof.
    intros x H. left. exact H.
  Qed.

  Lemma insert_phi_subset (Γ: theory) φ i : Γ ⊆ (insert_num Γ φ i).
  Proof.
    unfold insert_num. apply insert_form_subset.
  Qed.
  
  Lemma maxn_subset (Γ: theory) φ i: Γ ⊆ (maxn Γ φ i).
  Proof.
    induction i.
    simpl. intros a B. assumption.
    intros a H. simp maxn. unfold insert_num. unfold insert_form. left. auto. 
  Qed.
  
  Fact max_subset (Γ: theory) φ: Γ ⊆ (max Γ φ).
  Proof.
    intros x H. exists 0. auto.
  Qed.
End Contexts.    
   
Section Chaining.
  (* We proof, that if Δ = ∪ Δ_i derives a formula φ there already is a level i, s.t. Δ_i derives φ. *)
  Variable (D: DerivationType). 
  Lemma max_In_lemma (Γ: theory) φ ψ: (max Γ φ) ψ <-> exists i, (maxn Γ φ i) ψ.
  Proof.
    firstorder.
  Qed.  

  Lemma maxn_subset_ij i j (Γ: theory) φ: i <= j -> (maxn Γ φ i) ⊆ (maxn Γ φ j).
  Proof.
    intro. induction H; firstorder. 
  Qed.   

  Lemma maxnlist (l: list form) (Γ: theory) φ: (forall x, (List.In x l ->  (max Γ φ) x)) -> exists i, forall x, (List.In x l ->  (maxn Γ φ i) x ).
  Proof.
    induction l. (* TODO: Use length induction here *)
    + intros. exists 0. intro. specialize (H x). intro.  exfalso. apply H0.
    + intros.  
      assert (exists i, forall x, List.In x l -> maxn Γ φ i x).
      apply IHl. intros x H1. apply (H x). right. assumption.
      (specialize (H a)).
      assert (exists i, maxn Γ φ i a).
      {
        rewrite<- max_In_lemma.
        apply H.
        left. auto.
      }
      destruct H0 as [li lH]. destruct H1 as [ai aH].
      exists (Nat.max li ai).
      intros ψ L.
      destruct L.
    - apply maxn_subset_ij with (i := ai) (j := Nat.max li ai). apply le_max_r.
      rewrite<- H0. apply aH.
    - apply maxn_subset_ij with (i := li) (j := Nat.max li ai). apply le_max_l. 
      apply lH. assumption.
  Qed.        
  Fact maxn_chain (Γ: theory) φ ψ: 
    (ndT (max Γ φ) ψ) <-> exists i, (ndT (maxn Γ φ i) ψ).
  Proof.
    split.
    intro. destruct H as (l & linc & H).  
    assert (exists i, forall x', List.In x' l -> (maxn Γ φ i) x').
    {
       eauto using maxnlist.
    }
    destruct H0 as [ni nH].
    exists ni.
    exists l. auto. 
    + intro. firstorder eauto. 
  Qed.    
End Chaining.

Section Lindenbaum.
  Variable (Dt: DerivationType). 
  Lemma does_not_derive_i (Γ: theory) φ i:
    ~(ndT Γ φ) -> ~(ndT (maxn Γ φ i) φ).
  Proof.
    induction i.
    - intuition. 
    - intros nP. specialize (IHi nP). 
      intro.
      apply IHi. 
      apply ndtW with (maxn Γ φ (S i)); auto.
      intros a Ha. simp maxn in Ha. destruct Ha.
      + auto.
      + destruct H0. exfalso.  apply H0. apply ndtW with (maxn Γ φ (S i)).
        auto.
        simp maxn. unfold insert_num. intros x Hx.  destruct Hx; eauto.
        firstorder eauto.
        firstorder eauto. 
  Qed.   

  Fact does_not_derive (Γ: theory) φ:
    ~(ndT Γ φ) -> ~(ndT (max Γ φ) φ).
  Proof.
    intros. intro D.
    apply maxn_chain in D. destruct D.
    pose (does_not_derive_i H H0). auto. 
  Qed.
  
  Lemma subset_derives (A B: theory) φ: A ⊆ B -> ~(B ⊢T φ) -> ~(A ⊢T φ).
  Proof.
    intros H H0. intro H1. apply H0.  apply ndtW with (T := A); auto.
  Qed.
  (** Theory property **)
  Fact maxIsTheory (Γ: theory) φ ψ: ~(ndT Γ φ) -> (ndT (max Γ φ) ψ) -> (max Γ φ ψ).
  Proof.
    intros D M.
    apply max_In_lemma.
    destruct (decode_surj ψ).
    exists (S x).
    simp maxn.
    unfold insert_num. rewrite H. unfold insert_form.
    right.  split. 2: reflexivity. intro.
    assert (max Γ φ ⊢T φ).
    apply ndtIE with (s := ψ). apply ndtII.  apply ndtW with  (ψ # maxn Γ φ x) .  auto. intros a Ha; destruct Ha; firstorder auto. auto.
    apply does_not_derive in D.
    congruence.
  Qed.
  
  Lemma equalCtxCons A B a: A ≡ B -> a#A ≡ a#B.
  Proof.
    firstorder.
  Qed.  

  Lemma max_nd_is_in (Γ: theory) φ γ:  ~(ndT Γ φ) ->
                                       ((max Γ φ) ⊢T γ) <-> ((max Γ φ γ)).
  Proof.
    intros.
    split. intro. apply maxIsTheory; auto.
    intro. apply ndtA. auto. 
  Qed.
  
  Lemma wm (P: Prop) : ~~(P \/ ~P).
    tauto.
  Qed.   

  Lemma max_does_not_derive_lemma (Γ: theory) φ ψ:
    ~( Γ ⊢T φ) -> ~((max Γ φ) ψ) -> ~~((max Γ φ) ⊢T (ψ ⊃ φ)).
  Proof.
    intros D M.
    intro.
    (* ψ has a number in the enumeration *)
    destruct (decode_surj ψ) as [npsi Hnpsi].
    specialize wm with  (@maxn Dt Γ φ  (S npsi) ψ). intro. destruct H0. 
    intro. destruct H0.
    -    apply M. exists (S npsi).  auto.
    - apply H0.   simp maxn. unfold insert_num. unfold insert_form. right. split.
      2: auto.
      intro. apply ImpAgree in H1.  rewrite Hnpsi in H1.
      apply H.   apply ndtW with (maxn Γ φ npsi). exact H1.
      intros a Ha.   exists npsi.  auto. 
  Qed.

  (** *** Primeness properties *)
  Fact maxprime (Γ: theory) φ: ~(ndT Γ φ) -> is_primeDN (max Γ φ).
  Proof.
    intros H ϕ ψ.
    intro.
    specialize wm with ((@max Dt Γ φ) ψ). 
    intro. apply H1.  clear H1.  intro. 
    destruct H1.   
    apply H0.  eauto using ndtA. 
    
    specialize  wm with (((@max Dt Γ φ) ϕ)).
    intro. apply H2. clear H2. intro. 
    destruct H2.
    
    eauto using ndtA. 
    apply H0. intro.
    apply max_does_not_derive_lemma in H1.
    apply max_does_not_derive_lemma in H2. 
    assert (~~ (max Γ φ ⊢T φ)).
    {
      intro. apply H1.  intro. apply H2. intro.  apply H4. apply ndtDE with ϕ  ψ; auto.
    }
    apply does_not_derive in H. exfalso.  apply H4. auto. auto.  auto.
  Qed.   

  Lemma Lindenbaum (Γ: theory) (φ: form):  ~(ndT Γ φ) -> 
                                           Γ ⊆ (max Γ φ) /\ ~(ndT (max Γ φ) φ) /\ is_primeDN (max Γ φ) /\ dedClosed (max Γ φ).
  Proof.
    split.
    + apply max_subset.
    + split.
    - apply does_not_derive. exact H.
    - split.
      -- apply maxprime. exact H.
      -- intros x H1. apply maxIsTheory. exact H. exact H1.               
  Defined.

End Lindenbaum.

(** **  Truth Conditions and Derivations **)
Section Derivations.
  (* In this section derive for IEL *)
  Definition empty :theory := fun x => False. 
  Notation "∅" := empty.
  Lemma tripleNegIEL (Γ: theory) {d: DerivationType} ϕ:
    (Γ ⊢T (¬ϕ)) <-> (Γ ⊢T ¬ ¬ ¬ ϕ).
  Proof.
    split.
    - intro H. apply ndtII.  apply ndtIE with (s := ¬ ϕ). apply ndtA. firstorder.
      apply ndtII. apply ndtIE with (s := ϕ). apply ndtW with  Γ.  exact H.
      firstorder eauto. apply ndtA. firstorder eauto.
    - intro H. apply ndtII. apply ndtIE with (s := ¬ ¬ ϕ). 
      apply ndtW with Γ. exact H. firstorder eauto.  apply ndtII. apply ndtIE with (s := ϕ).
      apply ndtA. firstorder eauto.
      apply ndtA. firstorder eauto.
  Qed.     

  Lemma IELKBot: (@ndT normal empty (¬ (K ⊥))).
  Proof.
    apply ndtII.
    apply ndtIE with (s := ¬ ¬ ⊥).
    - apply ndtII. apply ndtIE with (s := (¬ ⊥)). apply ndtA; firstorder eauto. apply ndtII. apply ndtA; firstorder eauto.
    - apply ndtIntRefl. apply ndtA. firstorder eauto.
  Qed.

  Lemma IELTruthB ϕ: (@ndT normal empty (¬(K ϕ ∧ ¬ ϕ))).
  Proof.
    apply ndtII.
    apply ndtIE with (s := (¬ ¬ ϕ)).
    + apply ndtII.  apply ndtIE with (s := ¬ ϕ). try apply ndtA; firstorder eauto.
      apply ndtCER with (s := (K ϕ)); apply ndtA; firstorder eauto.
    + apply ndtIntRefl.  apply ndtCEL with (t := ¬ ϕ). apply ndtA. firstorder eauto 7.
  Qed.

  Lemma IELContra {d': DerivationType} (ϕ ψ: form) (A: theory): ndT A (ϕ ⊃ ψ) -> ndT A ((¬ ψ) ⊃ (¬ ϕ)). 
  Proof.
    intro H.
    repeat apply ndtII. apply ndtIE with (s := ψ). apply ndtA; firstorder eauto.
    apply ndtIE with (s := ϕ). apply ndtW with  A.   exact H. firstorder eauto. apply ndtA. firstorder eauto.
  Qed.  

  Lemma IELTruthC ϕ: (@ndT normal empty ((¬ ϕ) ⊃ (¬ K ϕ))).
  Proof.
    apply ndtII.
    apply ndtIE with (s := ¬ ¬ ¬ ϕ).
    + apply IELContra.
      apply ndtII. apply ndtIntRefl. apply ndtA. firstorder eauto.
    + rewrite <- tripleNegIEL.   apply ndtA. firstorder eauto. 
  Qed.
  Lemma linCoq (X Y: Prop): ((~ ~ X) -> (~~Y)) -> (~~ (X -> Y)).
  Proof.
    tauto. 
  Qed.
  
  Lemma ndTautologyNotNotX (X Y: form) {D: DerivationType} :
    (ndT  empty ((((¬ ¬ X) ⊃ (¬ ¬ Y)) ⊃ (¬ ¬ (X ⊃ Y))))) /\ (ndT  empty ((¬ ¬ (X ⊃ Y)) ⊃ ((¬ ¬ X) ⊃ (¬ ¬ Y)))).
  Proof.   
    split. 
    - repeat apply ndtII. 
      apply ndtIE with (s := (X ⊃ Y)). apply ndtA; firstorder eauto.
      apply ndtII. apply ndtE. apply ndtIE with (s := ¬ Y).
      apply ndtIE with (s := ((X ⊃ ⊥) ⊃ ⊥)). apply ndtA; firstorder eauto.
      apply ndtII. apply ndtIE with (s := X); apply ndtA; firstorder eauto.
      apply ndtII. apply ndtIE with (s := (X ⊃ Y)). apply ndtA; firstorder eauto. apply ndtII. apply ndtA; firstorder eauto. 
    - repeat apply ndtII.   apply ndtIE with (s := ((X ⊃ Y) ⊃ ⊥)).
      apply ndtA; firstorder eauto.
      apply ndtII. apply ndtIE with (s := (X ⊃ ⊥)).
      apply ndtA; firstorder eauto.
      apply ndtII.
      apply ndtIE with (s := Y). apply ndtA; firstorder eauto.
      apply ndtIE with (s := X); apply ndtA; firstorder eauto.
  Qed.
  
  Lemma IELTruthD ϕ: (@ndT normal empty (¬ ¬ (K ϕ ⊃ ϕ))).
  Proof.
    pose (@ndTautologyNotNotX (K ϕ) ϕ normal) as H. 
    destruct H.
    apply ndtIE with (s := (((K ϕ ⊃ ⊥) ⊃ ⊥) ⊃ (ϕ ⊃ ⊥) ⊃ ⊥)).
    auto.
    apply IELContra.
    apply IELTruthC.
  Qed.  
  Lemma t6 ϕ (Γ: theory): @ndT normal Γ ((K (¬ ϕ)) ⊃ ¬ ϕ).
  Proof.
    apply ndtII.
    apply tripleNegIEL. apply ndtIntRefl. 
    apply ndtA.
    firstorder eauto.
  Qed.
  Lemma implToCoq (Γ: theory) {d: DerivationType} ϕ ψ: (Γ ⊢T (ϕ ⊃ ψ) -> ((Γ ⊢T ϕ) -> (Γ ⊢T ψ))).
  Proof.
    - intros H H0.
      apply ndtIE with (s := ϕ); firstorder eauto.
  Qed.     

  Lemma t6C ϕ (Γ: theory): @ndT normal Γ (K (¬ ϕ)) -> @ndT normal Γ  (¬ ϕ).
  Proof.
    apply implToCoq.
    apply t6.
  Qed.

  Lemma t7 ϕ : ∅ ⊢T+ ((¬ (K ϕ)) ⊃ (K (¬ ϕ))) /\ ∅ ⊢T+ ((K (¬ ϕ)) ⊃ ¬ (K ϕ)).
  Proof.
    split.
    - apply ndtII. 
      apply ndtIE with (s := ¬ ϕ).
      apply ndtII. apply ndtKpos. apply ndtA; firstorder eauto.
      rewrite<- ImpAgree. 
      apply IELContra.
      apply ndtII. 
      apply ndtKpos.
      apply ndtA; firstorder eauto. 
    -  apply ndtII.
       apply ndtIE with (s := ¬ ϕ).
       apply ndtW with ∅.
       apply IELTruthC.
       firstorder eauto.
       rewrite<- ImpAgree. 
       apply t6.
  Qed.


  Lemma t8 ϕ: ∅ ⊢T+ ((¬ K ϕ) <--> (¬ ϕ)).
  Proof.
    apply ndtCI.
    apply IELContra.
    apply ndtII. 
    apply ndtKpos.
    apply ndtA; firstorder eauto.
    apply ndtII.
    apply ndtIE with (s := (K (¬ϕ))).
    apply ndtW with empty.
    destruct (t7 ϕ). auto. firstorder eauto. 
    apply ndtKpos.  apply ndtA; firstorder eauto. 
  Qed.
  
  Lemma t9 ϕ: ∅ ⊢T+ ¬ ((¬ K ϕ) ∧ ¬ (K (¬ ϕ))).
  Proof.
    apply ndtII.
    apply ndtIE with (s := ((¬ ϕ) ∧ (¬ ¬ ϕ))).
    apply ndtII. apply ndtIE with (s := (¬ ϕ)).
    apply ndtCER with (s := ¬ ϕ). apply ndtA; firstorder eauto.
    apply ndtCEL with (t := ¬ ¬ ϕ). apply ndtA; firstorder eauto.
    apply ndtCI.
    - apply t6C. apply ndtIE with (s := ¬ (K ϕ)).
      +  apply ndtW with ∅.
         apply t7.
         firstorder eauto.
      +    
      apply ndtCEL with (t := (K (ϕ ⊃ ⊥) ⊃ ⊥)). apply ndtA; firstorder eauto.
    - apply t6C. apply ndtIE with (s := ¬ (K (¬ ϕ))).  apply ndtW with  ∅.
      apply t7.
      firstorder eauto.
      apply ndtCER with (s := (K ϕ ⊃ ⊥)).
      apply ndtA; firstorder eauto. 
  Qed.
End Derivations.

(** ** Equivalence between IEL and IELm *)
Section IELMtoIEL.

  Lemma ielToIELM Γ s: (@nd normal Γ s) -> (@nd minus ((¬ (K ⊥))::Γ) s).
  Proof.
    intros.
    induction H; firstorder eauto.
    apply ndII. apply weak with ((K ⊥ ⊃ ⊥) :: (s :: Γ)). auto. auto.
    apply ndII. apply ndIE with (K ⊥). apply ndA; auto. apply ndIE with (K s). apply ndKImp. apply ndKpos. apply ndA. auto.
    apply ndW with ((K ⊥ ⊃ ⊥) :: Γ); firstorder eauto.
  Qed.   
  
  Lemma ielmToIEL Γ s: (@nd minus Γ s) -> (@nd normal Γ s). 
  Proof.
    intros.
    induction H; firstorder eauto.
  Qed.   
  Lemma ielmToIELKb Γ s: (@nd minus ((¬ (K ⊥))::Γ) s) -> forall Γ', Γ <<= Γ' -> (@nd normal Γ' s). 
  Proof.
    intros.  apply ndIE with (¬ K ⊥). apply ndII. apply ielmToIEL. apply ndW with  ( (K ⊥ ⊃ ⊥)::Γ).   auto. intro; firstorder eauto. apply ndTEq.
    apply ndtW with empty. apply IELKBot.  firstorder eauto. 
  Qed.

  Lemma ielmReducesIEL Γ s: (@nd minus ((¬ (K ⊥))::Γ) s) <-> (@nd normal Γ s).
  Proof.
    split; eauto using ielmToIELKb, ielToIELM.
  Qed.

  Lemma ielmReducesIEL_theories (T: theory) s:  ((¬ (K ⊥))#T) ⊢T- s <-> T ⊢T+ s.
  Proof.
    split. 
    - intro. destruct H. destruct H.  exists (rem x ((K ⊥ ⊃ ⊥))). split.
      + intros. destruct (H ψ);  apply in_rem_iff in H1. tauto. destruct H1. congruence.  auto.
      +  apply  ielmReducesIEL. apply ndW with x. auto. intros a Ha.  specialize (H a Ha).
         decide (a = (¬ K ⊥)).
         *  subst a; auto.
         *  right.   apply in_rem_iff; tauto.
    -  intro. repeat destruct H.   apply  ielmReducesIEL in H0. exists ((K ⊥ ⊃ ⊥) :: x). split.
       + firstorder eauto. 
       + auto.   
  Qed.        
End IELMtoIEL.
