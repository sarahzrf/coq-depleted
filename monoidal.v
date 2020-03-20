From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.

Require Import proset.
Require Import bounds.
(*
Require Import adjunction.
*)
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Class Monoidal `{Proset X} (T : X -> X -> X) `{!Bimonotone T} (U : X) :=
  {lunit A : T U A ⟛ A;
   runit A : T A U ⟛ A;
   massoc A B C : T A (T B C) ⟛ T (T A B) C}.
Hint Mode Monoidal ! - ! - - : typeclass_instances.
Class Sym `{Proset X} (T : X -> X -> X) :=
  twist A B : T A B ⊢ T B A.
Hint Mode Sym ! - ! : typeclass_instances.
Definition sym `{Sym X T} (A B : X) : T A B ⟛ T B A :=
  conj (twist A B) (twist B A).

Class MonSet (X : Type) `{Proset X} :=
  {memp : X; pro_tens : X -> X -> X;
   pro_tens_bi :> Bimonotone pro_tens; pro_monoidal :> Monoidal pro_tens memp}.
Arguments pro_tens {_ _ _} !_ !_ /.
Hint Mode MonSet ! - : typeclass_instances.
Infix "⊗" := pro_tens (at level 30) : proset_scope.
Notation "(⊗)" := pro_tens (only parsing) : proset_scope.
Definition pro_lunit `{MonSet X} (A : X) : memp ⊗ A ⟛ A := lunit A.
Definition pro_runit `{MonSet X} (A : X) : A ⊗ memp ⟛ A := runit A.
Definition pro_massoc `{MonSet X} (A B C : X) : A ⊗ (B ⊗ C) ⟛ (A ⊗ B) ⊗ C
  := massoc A B C.
Class SymMonSet (X : Type) `{MonSet X} :=
  {pro_twist :> Sym (X:=X) (⊗)}.
Hint Mode SymMonSet ! - - : typeclass_instances.
Definition pro_sym `{SymMonSet X} (A B : X) : A ⊗ B ⟛ B ⊗ A := sym A B.

Instance cartesian_monoidal `{Proset X, !MeetSemilattice X}
  : Monoidal (X:=X) meet ⊤.
Proof.
  constructor.
  - move=> A; split.
    + apply/meet_proj2.
    + apply/meet_right; [apply/top_right | done].
  - move=> A; split.
    + apply/meet_proj1.
    + apply/meet_right; [done | apply/top_right].
  - split; repeat apply/meet_right.
    + apply/meet_proj1.
    + apply/meet_left2/meet_proj1.
    + apply/meet_left2/meet_proj2.
    + apply/meet_left1/meet_proj1.
    + apply/meet_left1/meet_proj2.
    + apply/meet_proj2.
Qed.
Instance cocartesian_monoidal `{Proset X, !JoinSemilattice X}
  : Monoidal (X:=X) join ⊥.
Proof.
  constructor.
  - move=> A; split.
    + apply/join_left; [apply/bot_left | done].
    + apply/join_inj2.
  - move=> A; split.
    + apply/join_left; [done | apply/bot_left].
    + apply/join_inj1.
  - split; repeat apply/join_left.
    + apply/join_right1/join_inj1.
    + apply/join_right1/join_inj2.
    + apply/join_inj2.
    + apply/join_inj1.
    + apply/join_right2/join_inj1.
    + apply/join_right2/join_inj2.
Qed.
Instance cartesian_sym `{Proset X, !MeetSemilattice X} : Sym (X:=X) meet.
Proof. move=> A B; apply/(meet_right meet_proj2 meet_proj1). Qed.
Instance cocartesian_sym `{Proset X, !JoinSemilattice X} : Sym (X:=X) join.
Proof. move=> A B; apply/(join_left join_inj2 join_inj1). Qed.

Definition op_tens {X} (T : X -> X -> X) (a1 a2 : op X) : op X :=
  Op (T (get_op a1) (get_op a2)).
Arguments op_tens {X} T a1 a2 /.
Instance op_tens_bi `{Proset X} {T : X -> X -> X} `{!Bimonotone T}
  : Bimonotone (op_tens T).
Proof.
  move=> A A' /op_def D_A B B' /op_def D_B /=.
  apply/op_def/bi; by apply/op_def.
Qed.
Instance op_tens_monoidal `{Monoidal X T U} : Monoidal (op_tens T) (Op U).
Proof.
  constructor=> * /=; change (get_op (Op ?A)) with A.
  - apply op_core, lunit.
  - apply op_core, runit.
  - apply op_core, massoc.
Qed.
Instance op_tens_sym `{Sym X T} : Sym (op_tens T).
Proof. move=> A B /=; apply op_def, sym. Qed.
Instance op_mset `{MonSet X} : MonSet (op X) := {| pro_tens := op_tens (⊗) |}.
Instance op_smset `{SymMonSet X} : SymMonSet (op X) := {}.

Definition pw_tens (X : Type) {Y} (T : Y -> Y -> Y) (f1 f2 : X -> Y) : X -> Y :=
  fun x => T (f1 x) (f2 x).
Arguments pw_tens _ {_} _ _ _ _ /.
Instance pw_tens_bi {X} `{Proset Y} {T : Y -> Y -> Y} `{!Bimonotone T}
  : Bimonotone (pw_tens X T).
Proof. move=> ? ? ? ? ? ? ? /=; firstorder. Qed.
Instance pw_tens_monoidal {X} `{Monoidal Y T U} : Monoidal (pw_tens X T) (const U).
Proof. firstorder. Qed.
Instance pw_tens_sym {X} `{Sym Y T} : Sym (pw_tens X T).
Proof. firstorder. Qed.
Instance pw_mset {X} `{MonSet Y} : MonSet (X -> Y) := {| pro_tens := pw_tens X (⊗) |}.
Instance pw_smset {X} `{SymMonSet Y} : SymMonSet (X -> Y) := {}.

Definition prod_tens {X Y} (T : X -> X -> X) (T' : Y -> Y -> Y) (p1 p2 : X * Y) : X * Y :=
  (T p1.1 p2.1, T' p1.2 p2.2).
Arguments prod_tens {X Y} T T' !p1 !p2 /.
Instance prod_tens_bi `{Proset X, Proset Y} {T : X -> X -> X} {T' : Y -> Y -> Y}
         `{!Bimonotone T, !Bimonotone T'}
  : Bimonotone (prod_tens T T').
Proof. move=> [? ?] [? ?] /= ? [? ?] [? ?] /= ?; firstorder. Qed.
Instance prod_tens_monoidal `{Monoidal X T U, Monoidal Y T' U'}
  : Monoidal (prod_tens T T') (U, U').
Proof. firstorder. Qed.
Instance prod_tens_sym `{Sym X T, Sym Y T'} : Sym (prod_tens T T').
Proof. firstorder. Qed.
Instance prod_mset `{MonSet X, MonSet Y} : MonSet (X * Y)
  := {| pro_tens := prod_tens (⊗) (⊗) |}.
Instance prod_smset `{SymMonSet X, SymMonSet Y} : SymMonSet (X * Y) := {}.
