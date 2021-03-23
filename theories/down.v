From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.adjunction.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Definition down (X : Type) `{Proset X} : Type := Hom (op X) Prop.
Identity Coercion down_to_hom : down >-> Hom.

Lemma danti `{Proset X} (F : down X) {A B : X}
  : A ⊢ B -> F B -> F A.
Proof. move=> /opify /(mono F) //. Qed.
Hint Resolve danti.

Program Definition yo `{Proset X} (A : X) : down X :=
  fun B : X => B ⊢ A.
Next Obligation. move=> * ? * ?; by etransitivity. Qed.
Instance: Params (@yo) 3 := {}.
Lemma yoneda `{Proset X} (A : X) (F : down X)
  : yo A ⊢ F <-> F A.
Proof.
  split.
  - apply; by simpl.
  - move=> FA A' D; by apply: danti FA.
Qed.

Instance yo_mono `{Proset X} : Monotone (yo (X:=X)).
Proof. move=> /= * ? ?; by etransitivity. Qed.
Instance yo_reflect `{Proset X} : Reflecting (yo (X:=X)).
Proof. move=> A B /(_ A) /=; by apply. Qed.
Instance yo_continuous `{Proset X} : Continuous (yo (X:=X)).
Proof.
  move=> R J A [C U]; split=> [r | A' C'] B /=.
  - move=> ->; apply: C.
  - move=> /yoneda D; apply: U => r; apply: (reflect yo); etransitivity; firstorder.
Qed.
Definition principal `{Proset X} (F : down X) : Prop :=
  exists A, F ⟛ yo A.
