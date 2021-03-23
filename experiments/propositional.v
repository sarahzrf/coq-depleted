From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.pmap.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Inductive form : Type :=
  atom (x : positive) |
  _true | _false |
  _and (p q : form) | _or (p q : form) | _impl (p q : form).
Coercion atom : positive >-> form.
Notation "'⊤" := _true.
Notation "'⊥" := _false.
Infix "'/\" := _and (at level 20).
Infix "'\/" := _or (at level 25).
Infix "'->" := _impl (at level 30).
Notation "'~ p" := (p '-> '⊥) (at level 15).

Definition ctx : Type := list form.
Reserved Notation "Γ '⊢ p" (at level 85).
Inductive entails : ctx -> form -> Prop :=
| assm : forall {Γ p}, p ∈ Γ -> Γ '⊢ p

| top_I : forall {Γ}, Γ '⊢ '⊤
| bot_E : forall {Γ p}, Γ '⊢ '⊥ -> Γ '⊢ p

| conj_I : forall {Γ p q},
    Γ '⊢ p -> Γ '⊢ q -> Γ '⊢ p '/\ q
| conj_E1 : forall {Γ p q},
    Γ '⊢ p '/\ q -> Γ '⊢ p
| conj_E2 : forall {Γ p q},
    Γ '⊢ p '/\ q -> Γ '⊢ q

| impl_I : forall {Γ p q},
    p :: Γ '⊢ q -> Γ '⊢ p '-> q
| impl_E : forall {Γ p q},
    Γ '⊢ p '-> q -> Γ '⊢ p -> Γ '⊢ q

| disj_I1 : forall {Γ p q},
    Γ '⊢ p -> Γ '⊢ p '\/ q
| disj_I2 : forall {Γ p q},
    Γ '⊢ q -> Γ '⊢ p '\/ q
| disj_E : forall {Γ p q r},
    Γ '⊢ p '\/ q -> p :: Γ '⊢ r -> q :: Γ '⊢ r ->
    Γ '⊢ r

where "Γ '⊢ p" := (entails Γ p) : type_scope.
Hint Constructors entails.

Lemma weakening {Γ Δ p} (D : Γ ⊆+ Δ) (Prf : Γ '⊢ p) : Δ '⊢ p.
Proof.
  elim: Γ p / Prf Δ D; auto.
  - move=> *; by apply/assm/elem_of_submseteq.
  - move=> *; apply/conj_E1; auto.
  - move=> *; apply/conj_E2; auto.
  - move=> Γ p q Prf IH Δ D; apply/impl_I/IH; by constructor.
  - move=> *; apply/impl_E; auto.
  - move=> Γ p q r Prf1 IH1 Prf2 IH2 Prf3 IH3 Δ D; apply/disj_E.
    + auto.
    + apply/IH2; by constructor.
    + apply/IH3; by constructor.
Qed.

(*
Typeclasses Opaque ctx.
*)
Instance form_le : Le form := fun p q => [p] '⊢ q.
Instance ctx_le : Le ctx := fun Γ Δ => Forall (entails Γ) Δ.

Instance form_proset : Proset form.
Proof.
  constructor.
  - move=> p; apply/assm; constructor.
  - move=> p q r D1 D2; unfold form_le in *.
    apply: (impl_E (weakening _ (impl_I D2)) D1); by constructor.
Qed.

Instance cons_bi' : Bimonotone (cons (A:=form)).
Proof.
  move=> p q D1 Γ Δ D2; constructor.
  - apply: weakening D1; constructor; apply: submseteq_nil_l.
  - apply: Forall_impl D2 _ => r; apply: weakening; by constructor.
Qed.
Instance app_bi' : Bimonotone (app (A:=form)).
Proof.
  move=> Γ Γ' D1 Δ Δ' D2; apply/Forall_app; split.
  - apply: Forall_impl D1 _ => r; by apply/weakening/submseteq_inserts_r.
  - apply: Forall_impl D2 _ => r; by apply/weakening/submseteq_inserts_l.
Qed.

Instance entails_di : Dimonotone entails.
Proof.
  move=> Γ Δ /= D p q D' Prf.
  apply: (impl_E (weakening _ (impl_I D'))); first by apply: submseteq_nil_l.
  elim: Γ p / Prf Δ D {q D'}; auto.
  - move=> ? ? ? ? /Forall_forall D; auto.
  - move=> *; apply/conj_E1; auto.
  - move=> *; apply/conj_E2; auto.
  - move=> ? ? ? ? IH ? D; by apply/impl_I/IH/cons_bi'.
  - move=> *; apply/impl_E; auto.
  - move=> Γ p q r Prf1 IH1 Prf2 IH2 Prf3 IH3 Δ D; apply/disj_E.
    + auto.
    + by apply/IH2/cons_bi'.
    + by apply/IH3/cons_bi'.
Qed.
Instance ctx_proset : Proset ctx.
Proof.
  constructor.
  - move=> Γ; apply/Forall_forall; auto.
  - move=> Γ Δ Λ D1 /Forall_forall D2.
    apply/Forall_forall => p => /D2; by apply/entails_di.
Qed.


Program Instance form_top : Top form := mk_top '⊤ _.
Next Obligation. compute; dintuition. Qed.
Program Instance form_bot : Bot form := mk_bot '⊥ _.
Next Obligation. compute; dintuition. Qed.
Program Instance form_binmeets : BinMeets form
  := mk_binmeets _and _.
Next Obligation.
  split.
  - by split; [apply/conj_E1 | apply/conj_E2].
  - move=> []; by apply/conj_I.
Qed.
Program Instance form_binjoins : BinJoins form
  := mk_binjoins _or _.
Next Obligation.
  move=> *. split=> [<- | [H1 H2]].
  - split; [apply/disj_I1 | apply/disj_I2]; apply/assm; constructor.
  - apply: disj_E.
    + apply: assm. constructor.
    + apply: weakening H1. repeat constructor.
    + apply: weakening H2. repeat constructor.
Qed.

Program Instance form_exponents : Exponents form
  := {| exponential := _impl |}.
Next Obligation.
  move=> p q r; split=> Prf.
  - apply: impl_I; rewrite -Prf.
    apply: (conj_I (assm _) (assm _)); repeat constructor.
  - rewrite Prf; apply: impl_E; change ([?p] '⊢ ?q) with (p ⊢ q).
    + apply: meet_proj1.
    + apply: meet_proj2.
Qed.
Instance form_heyting : HeytingAlgebra form := _.


Definition assignment (H : Type) : Type := positive -> H.

Fixpoint eval `{HeytingAlgebra H} (ν : assignment H) (p : form) : H :=
  match p with
  | atom x => ν x
  | '⊤ => ⊤
  | '⊥ => ⊥
  | p '/\ q => eval ν p ⩕ eval ν q
  | p '\/ q => eval ν p ⩖ eval ν q
  | p '-> q => eval ν p ⟿ eval ν q
  end.
Notation "⟦ p ⟧_ ν" := (eval ν p) (at level 10, format "⟦  p  ⟧_ ν").
Fixpoint eval_ctx `{HeytingAlgebra H} (ν : assignment H) (Γ : ctx) : H :=
  match Γ with
  | [] => ⊤
  | p :: Γ' => ⟦ p ⟧_ν ⩕ eval_ctx ν Γ'
  end.
Notation "⟦ Γ ⟧*_ ν" := (eval_ctx ν Γ) (at level 10, format "⟦  Γ  ⟧*_ ν").

Theorem soundness {Γ p} (Prf : Γ '⊢ p)
  : forall `{HeytingAlgebra H} {ν : assignment H}, ⟦ Γ ⟧*_ν ⊢ ⟦ p ⟧_ν.
Proof.
  move=> *; elim: Γ p / Prf => //= Γ.
  - move=> p; elim: p Γ / => /= [* | ? ? ? ? ->];
      [apply: meet_proj1 | apply: meet_proj2].
  - apply: top_right.
  - move=> p _ ->; apply: bot_left.
  - move=> p q _ + _; apply: meet_right.
  - move=> p q _ ->; apply: meet_proj1.
  - move=> p q _ ->; apply: meet_proj2.
  - move=> p q _ ?; by apply/l_meet_exponential.
  - move=> p q _ D1 _ D2; rewrite -[⟦ q ⟧__]modus_ponens; by apply: meet_right.
  - move=> p q _ ->; apply: join_inj1.
  - move=> p q _ ->; apply: join_inj2.
  - move=> p q r _ D1 _ /meet_exponential D2 _ /meet_exponential D3; move: D1.
    rewrite D2 D3 (join_left (reflexivity _) (reflexivity _))
      -meet_exponential -meet_right //.
Qed.

Instance eval_proper `{HeytingAlgebra H}
  : Proper ((⟛) ==> (⊢) ++> (⊢)) (eval (H:=H)).
Proof.
  move=> ν ν' E_ν p p' D_p.
  rewrite -[L in L ⊢ _](runit (T:=meet)).
  change (⟦ [p] ⟧*_ν ⊢ ⟦ p' ⟧_ν'); etransitivity; first by apply: soundness.
  apply: pro_core_sub1; elim: p' {p D_p} => //=.
  1: firstorder.
  all: move=> p E1 q E2; split.
  - rewrite (proj1 E1) (proj1 E2) //. (* yikes *)
  - rewrite (proj2 E1) (proj2 E2) //.
  - rewrite (proj1 E1) (proj1 E2) //.
  - rewrite (proj2 E1) (proj2 E2) //.
  - rewrite (proj2 E1) (proj1 E2) //.
  - rewrite (proj1 E1) (proj2 E2) //.
Qed.


Theorem completeness {Γ p}
        (Tauto : forall `{HeytingAlgebra H} {ν : assignment H}, ⟦ Γ ⟧*_ν ⊢ ⟦ p ⟧_ν)
  : Γ '⊢ p.
Proof.
  pose proof (Tauto form _ _ _ _ _ _ _ _ _ atom) as Prf.
  elim: Γ p Prf {Tauto}.
  - move=> p.
    apply: entails_di; first by constructor.
    apply: pro_core_sub1; elim: p; cbn [eval]; try done.
    all: move=> p E1 q E2; split.
    + rewrite (proj1 E1) (proj1 E2) //. (* yikes *)
    + rewrite -(proj2 E1) -(proj2 E2) //.
    + rewrite (proj1 E1) (proj1 E2) //.
    + rewrite -(proj2 E1) -(proj2 E2) //.
    + rewrite -(proj2 E1) (proj1 E2) //.
    + rewrite (proj1 E1) -(proj2 E2) //.
  - move=> p Γ IH q /= D.
    apply: (impl_E (weakening _ (IH (p '-> q) _)) (assm _)); try by constructor.
    move: D => /l_meet_exponential //.
Qed.
