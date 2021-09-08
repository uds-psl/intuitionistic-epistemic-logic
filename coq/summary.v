(** * Summary File *)
Require Import forms models nd constructiveCompleteness modelsClassicalCompleteness decidability. 
(* You can comment out "Print Assumptions" below to check for
   that no axioms where used. *)

(* Definition 3  *)
About form. Print form.

(* Lemma 4  *)
(* Discriteness *) About form_eq_dec.
(* Enumerability *)

(* Tagged ND-System *)
About nd. 
Print nd.

(* Definition 5 *)
About KripkeModel. 
Print KripkeModel.

(* Definition 6 *)
About evalK'.

(* Lemma 7 *)
About monotone_ctx.

(* Lemma 8  *)
About soundness. 
(* Lemma 9   *)
About ndConsistent. 

(* Theorem 10 *)
Check StrongCompleteness.
(* Here LEM was used: *)
(* Print Assumptions StrongCompleteness.*) 

(* Lemma 11 *)
About genhW.

(* Lemma 12 *)
(* TODO: Copy *)

(* Theorem 13 *)
Check genDPCut.

(* Theorem 14 *)
Check ndgen_iff.

(* Theorem 15 *)
Check disjunction_SC.
(* Corollary 16 *)
Check disjunction_ND.

(* *)
