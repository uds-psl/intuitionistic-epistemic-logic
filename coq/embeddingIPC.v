(** * Embedding IEL into IPC **)

Require Import forms nd List.
Section Embedding.
  Definition E := (VarI 0). 
  Fixpoint e (f: form) : formIPC :=
    match f with
    | K x => (ImpI (ImpI (e x) E) (e x))
    | (ϕ ⊃ ψ) => (ImpI (e ϕ) (e ψ))
    | And ϕ ψ => (AndI (e ϕ) (e ψ))
    | Or ϕ ψ => (OrI (e ϕ) (e ψ))
    | Bot => BotI
    | Var x => (VarI x)
    end
  .  
  Definition ℇ := map e.
  Notation "x 'el' A" := (In x A) (at level 70).
  Notation "A <<= B" := (incl A B) (at level 70).


  (** Define ND for IPC  **)
  Inductive ndI: list formIPC -> formIPC -> Prop :=
    ndiE A s: ndI A BotI -> ndI A s
  | ndiA A s: s el A -> ndI A s
  | ndiII A s t: ndI (s::A) t -> ndI A (ImpI s t)
  | ndiIE A s t: ndI A (ImpI s t) -> ndI A s -> ndI A t

  | ndiCI A s t: ndI A s -> ndI A t -> ndI A (AndI s t)
  | ndiCEL A s t: ndI A (AndI s t) -> ndI A s
  | ndiCER A s t: ndI A (AndI s t) -> ndI A t

  | ndiDIL A s t: ndI A s -> ndI A (OrI s t)
  | ndiDIR A s t: ndI A t -> ndI A (OrI s t)
  | ndiDE A s t v: ndI A (ImpI s v) -> ndI A (ImpI t v) -> ndI A (OrI s t) -> ndI A v.

  Hint Constructors ndI : core.
  Hint Constructors nd : core.

  Lemma ndiWeak Γ ϕ: (ndI Γ ϕ) -> forall Ω, Γ <<= Ω -> (ndI Ω ϕ).  
  Proof.
    intro H. 
    induction H;   eauto.
  Qed.
  Ltac iselement := try apply ndiA; firstorder eauto.
  Lemma embedding Γ {D: DerivationType}: forall ϕ, nd Γ ϕ -> (ndI (ℇ Γ) (e ϕ)).
  Proof.
    intros ϕ H.
    
  induction H; simpl e; firstorder eauto.
    - apply ndiA. unfold ℇ.    apply in_map_iff. eauto. 
    - apply ndiII.  apply ndiII.
      remember (ImpI (e t) E :: ImpI (ImpI (e s) E) (e s) :: ℇ Γ) as Γ'.
      assert (ndI ((e s)::Γ') (ImpI (e (s ⊃ t)) E) ).
      {
        simpl e. apply ndiII.
        apply ndiIE with (s := (e t)).   rewrite HeqΓ'. iselement.
        apply ndiIE with (s := (e s)); rewrite HeqΓ'; iselement. 
      }
      assert (ndI Γ' (e s)).
      {
        apply ndiIE with (s :=  (ImpI (e s) E)).
        - rewrite HeqΓ'. iselement. 
        - apply ndiII.  apply ndiIE with (s := ((ImpI (e s) (e t)))).
          + apply ndiII. apply ndiIE with (s := (e t)). rewrite HeqΓ'. iselement.
            apply ndiIE with (s := (e s)); iselement.
          + simpl e in IHnd. apply ndiIE with (s := (ImpI (ImpI (e s) (e t)) E)).
            apply ndiWeak with (Γ := (ℇ Γ)). exact IHnd. rewrite HeqΓ'.  firstorder eauto.
            exact H0.
      }
      apply ndiIE with (s := (e s)).
      apply ndiIE with (s := (ImpI (ImpI (e s) (e t)) E)).
      simpl e in IHnd. apply ndiWeak with (Γ := (ℇ Γ)).  apply IHnd.   rewrite HeqΓ'. firstorder eauto.
      apply ndiII. apply ndiIE with (s := (e t)). rewrite HeqΓ'. iselement. apply ndiIE with (s := (e s)).
      iselement. apply ndiWeak with (Γ := Γ'); firstorder eauto. assumption.
    - 
      simpl e in IHnd. apply ndiII.  apply ndiIE with (s := (e s)). apply ndiII. iselement.
      apply ndiWeak with (Γ := (ℇ Γ)). exact IHnd. intro; firstorder eauto.
    - 
      simpl e in IHnd. apply ndiII.  apply ndiIE with (s := (e s)).  iselement.  apply ndiIE with (s := (ImpI (e s) E)).
      apply ndiWeak with (Γ := (ℇ Γ)). exact IHnd. intro; firstorder eauto.
      apply ndiII. apply ndiE. apply ndiIE with (s := (e s)); iselement.     
  Qed.                               
End Embedding.                                 
