From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.
Require Import stdpp.list.
(* This brings Z into scope, which I tend to use as a variable name sometimes,
   so this dummy definition will prevent me from accidentally using that Z when I thought
   I was doing an implicit binder. *)
Definition Z : () := ().


Declare Scope proset_scope.
Declare Scope proset_util_scope.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.
(* Local Set Universe Polymorphism. *)

Class Proset (X : Type) := {pro_le : X -> X -> Prop; pro_pro :> PreOrder pro_le}.
Hint Mode Proset ! : typeclass_instances.
Arguments pro_le {_ _} !_ !_ /.
Infix "⊢" := pro_le (no associativity, at level 70) : proset_scope.
Notation "(⊢)" := pro_le (only parsing) : proset_scope.

Definition core_rel {X} (R : X -> X -> Prop) : X -> X -> Prop := fun a1 a2 => R a1 a2 /\ R a2 a1.
Instance core_sub1 {X} {R : X -> X -> Prop} : subrelation (core_rel R) R | 10.
Proof. firstorder. Qed.
(*
Instance core_sub2 {X} {R : X -> X -> Prop} : subrelation (core_rel R) (flip R) | 10.
Proof. firstorder. Qed.
*)
Instance core_symmetric {X} {R : X -> X -> Prop} : Symmetric (core_rel R).
Proof. firstorder. Qed.
Instance core_equivalence `{PreOrder X R} : Equivalence (core_rel R).
Proof.
  constructor.
  1,2: firstorder.
  move=> a1 a2 a3 [H1 H1'] [H2 H2']; split; etransitivity; eauto.
Qed.
Notation pro_core := (core_rel (⊢)).
Infix "⟛" := pro_core (no associativity, at level 70) : proset_scope.
Notation "(⟛)" := pro_core (only parsing) : proset_scope.
Lemma core_eq {X} {R : X -> X -> Prop} `{!Antisymmetric X (=) R} {A B} :
  core_rel R A B -> A = B.
Proof. firstorder. Qed.
(* TODO Hmmmmm. Is this good to have around? *)
Instance proper_wrt_core `{!Antisymmetric X (=) R} {Y} {f : X -> Y}
  : Proper (core_rel R ==> (=)) f.
Proof. firstorder. Qed.

Notation Monotone := (Proper ((⊢) ++> (⊢))).
Notation Antitone := (Proper ((⊢) --> (⊢))).
(* TODO better names lmao *)
Notation Bitone := (Proper ((⊢) ++> (⊢) ++> (⊢))).
Notation Ditone := (Proper ((⊢) --> (⊢) ++> (⊢))).

Notation Reflecting := (Inj (⊢) (⊢)).

Lemma mono `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F} {A B}
  : A ⊢ B -> F A ⊢ F B.
Proof. firstorder. Qed.
Lemma anti `{Proset X, Proset Y} (F : X -> Y) `{!Antitone F} {A B}
  : B ⊢ A -> F A ⊢ F B.
Proof. firstorder. Qed.
Lemma bi `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Bitone F} {A B P Q}
  : A ⊢ B -> P ⊢ Q -> F A P ⊢ F B Q.
Proof. firstorder. Qed.
Lemma di `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Ditone F} {A B P Q}
  : B ⊢ A -> P ⊢ Q -> F A P ⊢ F B Q.
Proof. firstorder. Qed.
Lemma reflect `{Proset X, Proset Y} (F : X -> Y) `{!Reflecting F} {A B}
  : F A ⊢ F B -> A ⊢ B.
Proof. firstorder. Qed.

(*
Class Monotone `{Proset X, Proset Y} (F : X -> Y) :=
  mono : forall {A B}, A ⊢ B -> F A ⊢ F B.
Hint Mode Monotone ! - ! - ! : typeclass_instances.
Class Reflecting `{Proset X, Proset Y} (F : X -> Y) :=
  reflect : forall {A B}, F A ⊢ F B -> A ⊢ B.
Hint Mode Reflecting ! - ! - ! : typeclass_instances.
*)

Lemma embed `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F, !Reflecting F} {A B}
  : F A ⊢ F B <-> A ⊢ B.
Proof. split; [apply: reflect | apply: mono]. Qed.
Lemma mono_core `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F} {A B}
  : A ⟛ B -> F A ⟛ F B.
Proof. firstorder. Qed.
Lemma reflect_core `{Proset X, Proset Y} (F : X -> Y) `{!Reflecting F} {A B}
  : F A ⟛ F B -> A ⟛ B.
Proof. firstorder. Qed.
(*
Instance monotone_proper' `{Monotone X Y F} : Proper ((⊢) --> flip (⊢)) F.
Proof. move=> ? ?; apply: mono. Qed.
*)
Instance monotone_proper_core `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
  : Proper ((⟛) ==> (⟛)) F.
Proof. move=> ? ? [? ?]; split; by apply mono. Qed.
Instance monotone_proper_core' `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
  : Proper ((⟛) --> (⟛)) F.
Proof. move=> ? ? [? ?]; split; by apply mono. Qed.
(* TODO This should probably be falling out of monotone_proper...
Instance compose_proper `{Proset X, Proset Y, Proset Z}
  : Proper ((⊢) ++> (⊢) ++> (⊢)) (@compose X Y Z).
Proof. move=> F F' E1 G G' E2 A /=. setoid_rewrite E1. setoid_rewrite E2.  ? ? ? ? ? ? ? /=. firstorder. Qed.
*)

(* Basic kinds of proset. *)
Definition core (X : Type) : Type := X.
Definition Core {X} (A : X) : core X := A.
Definition get_core {X} (A : core X) : X := A.
Instance core_proset `{H : Proset X} : Proset (core X)
  := {| pro_le := @core_rel X (@pro_le X H) |}.
Typeclasses Opaque core Core get_core.
Opaque core Core get_core.
Instance get_core_mono `{Proset X} : Monotone (@get_core X).
Proof. firstorder. Qed.

Definition discrete (X : Type) : Type := X.
Definition Discrete {X} (A : X) : discrete X := A.
Definition get_discrete {X} (A : discrete X) : X := A.
Typeclasses Opaque discrete Discrete get_discrete.
Opaque discrete Discrete get_discrete.
Instance discrete_proset {X} : Proset (discrete X) := {| pro_le := eq |}.
Instance discrete_mono {X} `{Proset Y} {F : discrete X -> Y} : Monotone F | 3.
Proof. move=> a1 a2 /= -> //. Qed.

Definition indiscrete (X : Type) : Type := X.
Definition Indiscrete {X} (A : X) : indiscrete X := A.
Definition get_indiscrete {X} (A : indiscrete X) : X := A.
Typeclasses Opaque indiscrete Indiscrete get_indiscrete.
Opaque indiscrete Indiscrete get_indiscrete.
Program Instance indiscrete_proset {X} : Proset (indiscrete X) := {| pro_le _ _ := True |}.
Next Obligation. done. Qed.
Instance indiscrete_mono `{Proset X} {Y} {F : X -> indiscrete Y} : Monotone F | 3.
Proof. done. Qed.

Definition op (X : Type) : Type := X.
Definition Op {X} (A : X) : op X := A.
Definition get_op {X} (A : op X) : X := A.
Instance op_proset `{H : Proset X} : Proset (op X)
  := {| pro_le := @flip (op X) (op X) Prop (@pro_le X H) |}.
Typeclasses Opaque op Op get_op.
Opaque op Op get_op.
Lemma op_core `{Proset X} {A B : op X}
  : A ⟛ B <-> get_op A ⟛ get_op B.
Proof. done. Qed.

Instance pw_pro {Y} `{PreOrder X R} : PreOrder (pointwise_relation Y R).
Proof. constructor; typeclasses eauto. Qed.
Instance pw_proset {Y} `{Proset X} : Proset (Y -> X) :=
  {| pro_le := pointwise_relation Y (⊢) |}.
Lemma pw_core0 {X} {R : X -> X -> Prop} {Y} {F G : Y -> X}
  : core_rel (pointwise_relation Y R) F G <-> (forall A, core_rel R (F A) (G A)).
Proof. firstorder. Qed.
Lemma pw_core `{Proset X} {Y} {F G : Y -> X} : F ⟛ G -> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Lemma pw_core' `{Proset X} {Y} {F G : Y -> X} : F ⟛ G <-> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Instance pw_core_subrel `{Proset X} {Y}
  : @subrelation (Y -> X) (⟛) (pointwise_relation Y (⟛)).
Proof. firstorder. Qed.

(* TODO Maybe shouldn't do this. *)
Arguments prod_relation {A B} R1 R2 !x !y /.
Instance prod_relation_pro `{PreOrder X R, PreOrder Y R'}
  : PreOrder (prod_relation R R').
Proof. constructor; typeclasses eauto. Qed.
Instance prod_proset `{Proset X, Proset Y} : Proset (X * Y) :=
  {| pro_le := prod_relation (⊢) (⊢) |}.

Instance void_proset : Proset void := {| pro_le _ _ := True |}.
Instance void_mono1 `{Proset X} {F : void -> X} : Monotone F | 3.
Proof. move=> []. Qed.
Instance void_mono2 `{Proset X} {F : X -> void} : Monotone F | 3.
Proof. firstorder. Qed.

Instance unit_proset : Proset () := {| pro_le _ _ := True |}.
Instance unit_mono1 `{Proset X} {F : unit -> X} : Monotone F | 3.
Proof. move=> [] [] //. Qed.
Instance unit_mono2 `{Proset X} {F : X -> unit} : Monotone F | 3.
Proof. done. Qed.

Program Instance prop_proset : Proset Prop := {| pro_le := impl |}.
Next Obligation. firstorder. Qed.
Instance and_bi : Bitone and.
Proof. firstorder. Qed.
Instance or_bi : Bitone or.
Proof. firstorder. Qed.
Instance not_anti : Antitone not.
Proof. firstorder. Qed.
Instance impl_di : Ditone impl.
Proof. firstorder. Qed.

Instance nat_proset : Proset nat := {| pro_le := le |}.
Definition chain `{Proset X} (F : nat -> X) : Prop := forall n, F n ⊢ F (S n).
Lemma chain_mono `{Proset X} {F : nat -> X} :
  Monotone F <-> chain F.
Proof.
  split.
  - move=> ? n; apply/mono; by constructor.
  - move=> Chain n m; elim: m / => //=; by etransitivity.
Qed.
Instance S_mono : Monotone S.
Proof. compute => *; lia. Qed.
Instance S_reflect : Reflecting S.
Proof. compute => *; lia. Qed.
Instance pred_mono : Monotone Nat.pred.
Proof. move=> -[| n] -[| m]; compute; lia. Qed.
Instance add_bi : Bitone Nat.add.
Proof. move=> ? ? ? ? ? ?; by apply: Nat.add_le_mono. Qed.
Instance mul_bi : Bitone Nat.mul.
Proof. move=> ? ? ? ? ? ?; by apply: Nat.mul_le_mono. Qed.

Program Instance bool_proset : Proset bool := {| pro_le := implb |}.
Next Obligation. constructor=> [[] | [] []] //=. Qed.
Instance andb_bi : Bitone andb.
Proof. move=> [] [] // _ [] [] //. Qed.
Instance orb_bi : Bitone orb.
Proof. move=> [] [] // _ [] [] //. Qed.
Instance notb_anti : Antitone negb.
Proof. move=> [] //. Qed.
Instance implb_di : Ditone implb.
Proof. move=> [] [] // _ [] [] //. Qed.

Definition sig_rel {X} (R : X -> X -> Prop) (P : X -> Prop) : sig P -> sig P -> Prop :=
  fun s1 s2 => R (`s1) (`s2).
Arguments sig_rel {_} _ _ !_ !_ /.
(*
Instance derives_pro `{NatDed X} : PreOrder (derives (A:=X))
  := {| PreOrder_Reflexive := derives_refl; PreOrder_Transitive := derives_trans |}.
*)
Instance sig_reflexive `{Reflexive X R} {P} : Reflexive (sig_rel R P).
Proof. by compute. Qed.
Instance sig_transitive `{Transitive X R} {P} : Transitive (sig_rel R P).
Proof. move=> a b c; unfold sig_rel; by etransitivity. Qed.
Instance sig_symmetric `{Symmetric X R} {P} : Symmetric (sig_rel R P).
Proof. by compute. Qed.
Instance sig_pro `{PreOrder X R} {P} : PreOrder (sig_rel R P)
  := {}.
Instance sig_proset `{Proset X} {P : X -> Prop} : Proset (sig P) :=
  {| pro_le := sig_rel (⊢) P |}.
Instance sval_mono `{Proset X} {P : X -> Prop} : Monotone (proj1_sig (P:=P)).
Proof. firstorder. Qed.
Instance sval_reflect `{Proset X} {P : X -> Prop} : Reflecting (proj1_sig (P:=P)).
Proof. firstorder. Qed.
Definition pack {A} (P : A -> Prop) (x : A) `{H : P x} : sig P
  := x ↾ H.
Definition pack_ph {A P} (ph : phant (sig P)) (x : A) `{H : P x} : sig P
  := x ↾ H.
Definition restrict_cod {A B} (P : B -> Prop) (f : A -> B) `{H : forall a, P (f a)} : A -> sig P
  := fun a => f a ↾ H a.
Definition restrict_cod_ph {A B} {P : B -> Prop} (ph : phant (sig P)) (f : A -> B)
           `{H : forall a, P (f a)} : A -> sig P
  := fun a => f a ↾ H a.
Notation "x 'packed_with' P" := (pack P x) (at level 20) : proset_util_scope.
Notation "x 'as_a' T" := (pack_ph (Phant T) x : T)
                           (at level 20) : proset_util_scope.
Notation "f ▷ P" := (restrict_cod P f) (at level 20) : proset_util_scope.
Notation "f ↑" := (restrict_cod _ f) (at level 20) : proset_util_scope.
Notation "f ↣ T" := (restrict_cod_ph (Phant T) f : _ -> T)
                      (at level 20) : proset_util_scope.
Arguments pack {_} _ _ {_} /.
Arguments pack_ph {_ _} _ _ {_} /.
Arguments restrict_cod {_ _} _ _ {_} _ /.
Arguments restrict_cod_ph {_ _ _} _ _ {_} _ /.
Instance restrict_cod_mono `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
         {P : Y -> Prop} {I : forall A, P (F A)}
  : Monotone (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_reflect `{Proset X, Proset Y} {F : X -> Y} `{!Reflecting F}
         {P : Y -> Prop} {I : forall A, P (F A)}
  : Reflecting (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_mono `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
         {P : Y -> Prop} {I : forall A, P (F A)}
         {ph : phant (sig P)}
  : Monotone (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_reflect `{Proset X, Proset Y} {F : X -> Y} `{!Reflecting F}
         {P : Y -> Prop} {I : forall A, P (F A)}
         {ph : phant (sig P)}
  : Reflecting (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.

Instance list_proset `{Proset X} : Proset (list X) :=
  {| pro_le := Forall2 (⊢) |}.
Instance list_map_mono `{Proset X, Proset Y} : Monotone (fmap (M:=list) (A:=X) (B:=Y)).
Proof. move=> F G D As; apply/Forall2_fmap/Forall2_impl; firstorder. Qed.
Instance list_map_mono' `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
  : Monotone (fmap (M:=list) F).
Proof. move=> As Bs D; apply/Forall2_fmap/Forall2_impl; [apply: D | done]. Qed.
Instance cons_mono `{Proset X} : Monotone (@cons X).
Proof. by constructor. Qed.
Instance cons_mono' `{Proset X} {A : X} : Monotone (cons A).
Proof. by constructor. Qed.
Instance mret_mono `{Proset X} : Monotone (mret (M:=list) (A:=X)).
Proof. by constructor. Qed.
