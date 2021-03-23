From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.strings.
(*
Require Import stdpp.stringmap.
*)

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Definition ctx (X : Type) : Type := list (string * X).
Record judgment (X : Type) : Type := {hyps : ctx X; concl : X}.
Arguments hyps {_} !_ /.
Arguments concl {_} !_ /.
Notation "Γ '⊢ A" := {| hyps := Γ; concl := A |}
                       (no associativity, at level 70) : proset_scope.

Instance ctx_le `{Proset X} : Le (ctx X) := flip submseteq.
Instance ctx_proset `{Proset X} : Proset (ctx X).
Proof. rewrite /Proset /ctx_le; typeclasses eauto. Qed.
(*
Definition ctx_all `{Proset X, !MeetSemilattice X} (Γ : ctx X) : X
  := foldr meet ⊤ Γ.*2.
*)
Fixpoint ctx_all `{MeetSemilattice X} (Γ : ctx X) : X :=
  match Γ with
  | nil => ⊤
  | cons (s, A) Γ' => A ⩕ ctx_all Γ'
  end.
Instance: Params (@ctx_all) 4 := {}.
Instance ctx_all_proper `{MeetSemilattice X}
  : Proper (submseteq --> (⊢)) (ctx_all (X:=X)).
Proof.
  move=> Γ Γ'; elim: Γ' Γ / => //
    [[s A] Γ Γ' _ | [s A] [t B] Γ | [s A] Γ Γ' _ | *] //=.
  - apply: bi_r.
  - rewrite massoc [A ⩕ B]sym -massoc //.
  - apply: meet_left2.
  - by etransitivity.
Qed.
Instance ctx_all_proper' `{MeetSemilattice X}
  : Proper (submseteq ++> flip (⊢)) (ctx_all (X:=X)).
Proof. move=> * /=; by apply: ctx_all_proper. Qed.
(*
Instance ctx_all_mono `{Proset X, !MeetSemilattice X} : Monotone (ctx_all (X:=X)).
Proof. typeclasses eauto. Qed.
*)

Local Instance submseteq_rewrite {X}
  : RewriteRelation (@submseteq (string * X)) := {}.
Instance judgment_le `{Proset X} : Le (judgment X)
  := fun J J' => hyps J' ⊢ hyps J /\ concl J ⊢ concl J'.
Arguments judgment_le {_ _ _} !_ !_ /.
Instance judgment_proset `{Proset X} : Proset (judgment X).
Proof.
  constructor.
  - firstorder.
  - move=> [Γ A] [Γ' A'] [Γ'' A''] /= [? ?] [? ?]; split; by etransitivity.
Qed.
Instance judgment_proper `{Proset X}
  : Proper (submseteq ++> (⊢) ++> (⊢)) (Build_judgment X).
Proof. firstorder. Qed.
Instance judgment_proper' `{Proset X}
  : Proper (submseteq --> (⊢) --> flip (⊢)) (Build_judgment X).
Proof. firstorder. Qed.
(*
Instance judgment_di `{Proset X} : Dimonotone (Build_judgment X).
Proof. firstorder. Qed.
*)
Instance hyps_anti `{Proset X} : Antitone (hyps (X:=X)).
Proof. firstorder. Qed.
Instance concl_mono `{Proset X} : Monotone (concl (X:=X)).
Proof. firstorder. Qed.


Definition holds `{MeetSemilattice X} (J : judgment X) : Prop
  := ctx_all (hyps J) ⊢ concl J.
Arguments holds {_ _ _ _ _ _} J /.
Instance: Params (@holds) 6 := {}.
Notation "[| J |]" := (holds J) (format "[|  J  |]").
Instance holds_proper `{MeetSemilattice X}
  : Proper ((⊢) ++> impl) (holds (X:=X)).
Proof. move=> J J' /= -> //. Qed.
Instance holds_proper' `{MeetSemilattice X}
  : Proper ((⊢) --> flip impl) (holds (X:=X)).
Proof. move=> J J' /= -> //. Qed.
(*
Instance holds_mono `{Proset X, !MeetSemilattice X} : Monotone (holds (X:=X)).
Proof. typeclasses eauto. Qed.
*)


(* Natural deduction rules. *)
Lemma in_ctx `{MeetSemilattice X} {Γ : ctx X} (s : string) {A : X}
  : (s, A) ∈ Γ -> [| Γ '⊢ A |].
Proof.
  move=> /(elem_of_list_split _ _) [Γ1] [Γ2] ->.
  rewrite cons_middle -submseteq_middle /=; apply: meet_proj1.
Qed.
Lemma assm `{MeetSemilattice X} {Γ : ctx X} (s : string) {A : X}
      `{In : !TCElemOf (s, A) Γ}
  : [| Γ '⊢ A |].
Proof. apply: (in_ctx s); elim: In => /=; by constructor. Qed.

Lemma top_i `{MeetSemilattice X} {Γ : ctx X}
  : [| Γ '⊢ ⊤ |].
Proof. apply: top_right. Qed.
Lemma bot_e `{MeetSemilattice X, !Bot X} {Γ : ctx X} {A}
  : [| Γ '⊢ ⊥ |] -> [| Γ '⊢ A |].
Proof. move=> /= ->; apply: bot_left. Qed.

Lemma meet_i `{MeetSemilattice X} {Γ : ctx X} {A B}
  : [| Γ '⊢ A |] -> [| Γ '⊢ B |] -> [| Γ '⊢ A ⩕ B |].
Proof. apply: meet_right. Qed.
Lemma meet_e1 `{MeetSemilattice X} {Γ : ctx X} {A B}
  : [| Γ '⊢ A ⩕ B |] -> [| Γ '⊢ A |].
Proof. move=> /= ->; apply: meet_proj1. Qed.
Lemma meet_e2 `{MeetSemilattice X} {Γ : ctx X} {A B}
  : [| Γ '⊢ A ⩕ B |] -> [| Γ '⊢ B |].
Proof. move=> /= ->; apply: meet_proj2. Qed.

Lemma join_i1 `{MeetSemilattice X, !BinJoins X} {Γ : ctx X} {A B}
  : [| Γ '⊢ A |] -> [| Γ '⊢ A ⩖ B |].
Proof. move=> /= ->; apply: join_inj1. Qed.
Lemma join_i2 `{MeetSemilattice X, !BinJoins X} {Γ : ctx X} {A B}
  : [| Γ '⊢ B |] -> [| Γ '⊢ A ⩖ B |].
Proof. move=> /= ->; apply: join_inj2. Qed.
Lemma join_e `{HeytingAlgebra X} {Γ : ctx X} (s t : string) {A B C}
  : [| Γ '⊢ A ⩖ B |] -> [| (s, A) :: Γ '⊢ C |] -> [| (t, B) :: Γ '⊢ C |] ->
    [| Γ '⊢ C |].
Proof.
  move=> /= Disj Br1 Br2.
  rewrite (meet_right Disj (reflexivity _)) meet_exponential.
  apply: join_left; rewrite -meet_exponential //.
Qed.

Lemma impl_i `{HeytingAlgebra X} {Γ : ctx X} (s : string) {A B}
  : [| (s, A) :: Γ '⊢ B |] -> [| Γ '⊢ A ⟿ B |].
Proof. rewrite /= l_meet_exponential //. Qed.
Lemma impl_e `{HeytingAlgebra X} {Γ : ctx X} {A B}
  : [| Γ '⊢ A ⟿ B |] -> [| Γ '⊢ A |] -> [| Γ '⊢ B |].
Proof. move=> /= D1 D2; rewrite (meet_right D1 D2) modus_ponens //. Qed.

Arguments holds {_ _ _ _ _ _} J : simpl never.

(*
Definition box {X} (A : X) : Prop := True.
Ltac internalize_main e :=
  match e with
  | (fun x => ?e') => apply: (impl_i ""); internalize_main e'
  | (?e1, ?e2) => apply: meet_i; [internalize_main e1 | internalize_main e2]
  | ?e'.1 => apply: meet_e1; internalize_main e'
  | ?e'.2 => apply: meet_e2; internalize_main e'
  | inl ?e' => apply: join_i1; internalize_main e'
  | inr ?e' => apply: join_i2; internalize_main e'
  | ?v => is_var v;
         match type of v with
         | box ?P => refine (assm _ (A:=P))
         end
  end.
Tactic Notation "internalize" constr(e) := internalize_main e.
*)

Example nn_lem `{HeytingAlgebra H} {P : H}
  : [| [] '⊢ ¬ₕ ¬ₕ (P ⩖ ¬ₕ P) |].
Proof.
  apply: (impl_i "N"); apply: (impl_e (assm "N")).
  apply: join_i2.
  apply: (impl_i "H_P"); apply: (impl_e (assm "N")).
  apply: join_i1; apply: assm.
Qed.
