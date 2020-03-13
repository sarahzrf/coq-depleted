From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.
Require Import stdpp.list.


Declare Scope proset_scope.
Declare Scope proset_util_scope.
Declare Scope optic_scope.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.
Local Open Scope optic_scope.
(* Local Set Universe Polymorphism. *)

Class Proset (X : Type) := {pro_le : X -> X -> Prop; pro_pro :> PreOrder pro_le}.
Hint Mode Proset ! : typeclass_instances.
Infix "⊢" := pro_le (no associativity, at level 70) : proset_scope.
Arguments pro_le {_ _} !_ !_ /.
Definition core {X} (R : X -> X -> Prop) : X -> X -> Prop := fun a1 a2 => R a1 a2 /\ R a2 a1.
Instance core_sub1 {X} {R : X -> X -> Prop} : subrelation (core R) R | 10.
Proof. firstorder. Qed.
(*
Instance core_sub2 {X} {R : X -> X -> Prop} : subrelation (core R) (flip R) | 10.
Proof. firstorder. Qed.
*)
Instance core_symmetric {X} {R : X -> X -> Prop} : Symmetric (core R).
Proof. firstorder. Qed.
Instance core_equivalence `{PreOrder X R} : Equivalence (core R).
Proof.
  constructor.
  1,2: firstorder.
  move=> a1 a2 a3 [H1 H1'] [H2 H2']; split; etransitivity; eauto.
Qed.
Infix "⟛" := (core pro_le) (no associativity, at level 70) : proset_scope.
Lemma core_eq : forall {X} {R : X -> X -> Prop} `{!Antisymmetric X (=) R} {A B},
    core R A B -> A = B.
Proof. firstorder. Qed.
(* TODO Hmmmmm. Is this good to have around? *)
Instance proper_wrt_core `{!Antisymmetric X (=) R} {Y} {f : X -> Y}
  : Proper (core R ==> (=)) f.
Proof. firstorder. Qed.
Record op (A : Type) := Op {get_op : A}.
Add Printing Constructor op.
Arguments Op {_}.
Arguments get_op {_}.
Definition pro_op {X} (R : X -> X -> Prop) : op X -> op X -> Prop :=
  fun a1 a2 => R (get_op a2) (get_op a1).
Arguments pro_op {X} R !a1 !a2 /.
Instance pro_op_pro `{PreOrder X R} : PreOrder (pro_op R).
Proof.
  constructor; first by firstorder.
  move=> [x] [y] [z] /=; etransitivity; eauto.
Qed.
Instance op_proset `{Proset X} : Proset (op X) := {| pro_le := pro_op pro_le |}.
Instance pw_pro {Y} `{PreOrder X R} : PreOrder (pointwise_relation Y R) :=
  {| PreOrder_Reflexive f y := PreOrder_Reflexive (f y);
     PreOrder_Transitive f g h E1 E2 y := PreOrder_Transitive _ _ _ (E1 y) (E2 y) |}.
Instance pw_proset {Y} `{Proset X} : Proset (Y -> X) :=
  {| pro_le := pointwise_relation Y pro_le |}.
Lemma pw_core0 : forall {X} {R : X -> X -> Prop} {Y} {F G : Y -> X},
    core (pointwise_relation Y R) F G <-> (forall A, core R (F A) (G A)).
Proof. firstorder. Qed.
Lemma pw_core : forall `{Proset X} {Y} {F G : Y -> X}, F ⟛ G -> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Lemma pw_core' : forall `{Proset X} {Y} {F G : Y -> X}, F ⟛ G <-> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Instance pw_core_subrel `{Proset X} {Y}
  : subrelation (core (pro_le (X:=Y -> X))) (pointwise_relation Y (core (pro_le (X:=X)))).
Proof. firstorder. Qed.
Local Arguments prod_relation {A B} R1 R2 !x !y /.
Instance prod_relation_pro `{PreOrder X R, PreOrder Y R'}
  : PreOrder (prod_relation R R').
Proof. firstorder. Qed.
Instance prod_proset `{Proset X, Proset Y} : Proset (X * Y) :=
  {| pro_le := prod_relation pro_le pro_le |}.

Class Functor `{Proset X, Proset Y} (F : X -> Y) :=
  fmap' : forall {A B}, A ⊢ B -> F A ⊢ F B.
Hint Mode Functor ! - ! - ! : typeclass_instances.
Class Full `{Proset X, Proset Y} (F : X -> Y) :=
  unfmap : forall {A B}, F A ⊢ F B -> A ⊢ B.
Hint Mode Full ! - ! - ! : typeclass_instances.
(* TODO Double-check this definition. *)

Lemma unfmap_fmap : forall `{Proset X, Proset Y} {F : X -> Y} `{!Functor F, !Full F} {A B},
    F A ⊢ F B <-> A ⊢ B.
Proof. split; [apply: unfmap | apply: fmap']. Qed.
Lemma fmap_core : forall `{Functor X Y F} {A B}, A ⟛ B -> F A ⟛ F B.
Proof. firstorder. Qed.
Lemma unfmap_core : forall `{Full X Y F} {A B}, F A ⟛ F B -> A ⟛ B.
Proof. firstorder. Qed.
Instance functor_proper `{Functor X Y F} : Proper (pro_le ++> pro_le) F.
Proof. move=> ? ?; apply: fmap'. Qed.
Instance functor_proper' `{Functor X Y F} : Proper (pro_le --> flip pro_le) F.
Proof. move=> ? ?; apply: fmap'. Qed.
Instance functor_proper_core `{Functor X Y F} : Proper (core pro_le ==> core pro_le) F.
Proof. move=> ? ? [? ?]; split; by apply fmap'. Qed.
Instance functor_proper_core' `{Functor X Y F} : Proper (core pro_le --> core pro_le) F.
Proof. move=> ? ? [? ?]; split; by apply fmap'. Qed.
(* TODO This should probably be falling out of functor_proper...
Instance compose_proper `{Proset X, Proset Y, Proset Z}
  : Proper (pro_le ++> pro_le ++> pro_le) (@compose X Y Z).
Proof. move=> F F' E1 G G' E2 A /=. setoid_rewrite E1. setoid_rewrite E2.  ? ? ? ? ? ? ? /=. firstorder. Qed.
*)

Class Monoidal {X} (R : X -> X -> Prop) (T : X -> X -> X) (U : X) :=
  {bimap : forall {A A' B B'}, R A A' -> R B B' -> R (T A B) (T A' B');
   lunit : forall A, core R (T U A) A;
   runit : forall A, core R (T A U) A;
   massoc : forall A B C, core R (T A (T B C)) (T (T A B) C)}.
Hint Mode Monoidal ! ! ! - : typeclass_instances.
Class Sym {X} (R : X -> X -> Prop) (T : X -> X -> X) :=
   sym : forall A B, R (T A B) (T B A).
Hint Mode Sym ! ! ! : typeclass_instances.
Class MonSet (X : Type) `{Proset X} :=
  {memp : X; pro_tens : X -> X -> X; pro_monoidal :> Monoidal pro_le pro_tens memp}.
Arguments pro_tens {_ _ _} !_ !_ /.
Hint Mode MonSet ! - : typeclass_instances.
Infix "⊗" := pro_tens (at level 30) : proset_scope.
Definition pro_lunit `{MonSet X} (A : X) : memp ⊗ A ⟛ A := lunit A.
Definition pro_runit `{MonSet X} (A : X) : A ⊗ memp ⟛ A := runit A.
Definition pro_massoc `{MonSet X} (A B C : X) : A ⊗ (B ⊗ C) ⟛ (A ⊗ B) ⊗ C
  := massoc A B C.
Class SymMonSet (X : Type) `{MonSet X} :=
  {pro_sym :> Sym (X:=X) pro_le pro_tens}.
Hint Mode SymMonSet ! - - : typeclass_instances.
Definition pro_sym' `{SymMonSet X} (A B : X) : A ⊗ B ⟛ B ⊗ A :=
  conj (pro_sym A B) (pro_sym B A).
Definition tens_op {X} (T : X -> X -> X) (a1 a2 : op X) : op X :=
  Op (T (get_op a1) (get_op a2)).
Arguments tens_op {X} T !a1 !a2 /.
Instance pro_op_monoidal `{Monoidal X R T U} : Monoidal (pro_op R) (tens_op T) (Op U).
Proof.
  constructor.
  all: rewrite /pro_op /core /= => *; rewrite -/(core R _ _).
  - by eapply bimap.
  - symmetry; apply: lunit.
  - symmetry; apply: runit.
  - symmetry; apply: massoc.
Qed.
Instance pro_op_sym `{Sym X R T} : Sym (pro_op R) (tens_op T).
Proof. move=> [A] [B] /=; apply sym. Qed.
Instance op_mset `{MonSet X} : MonSet (op X) := {| pro_tens := tens_op pro_tens |}.
Instance op_smset `{SymMonSet X} : SymMonSet (op X) := {}.
Instance pw_monoidal {Y} `{Monoidal X R T U} :
  Monoidal (pointwise_relation Y R) (fun f g y => T (f y) (g y)) (const U).
Proof.
  constructor.
  - move=> A A' B B' D1 D2 y; apply bimap; [apply: D1 | apply: D2].
  - move=> A; apply/pw_core0 => y; apply: lunit.
  - move=> A; apply/pw_core0 => y; apply: runit.
  - move=> A B C; apply/pw_core0 => y; apply: massoc.
Qed.
Instance pw_sym {Y} `{Sym X R T}
  : Sym (pointwise_relation Y R) (fun f g y => T (f y) (g y)).
Proof. move=> A B y; apply sym. Qed.
Instance pw_mset {Y} `{MonSet X} : MonSet (Y -> X) :=
  {| pro_tens := fun f g y => f y ⊗ g y |}.
Instance pw_smset {Y} `{SymMonSet X} : SymMonSet (Y -> X) := {}.
Definition tens_prod {X Y} (T : X -> X -> X) (T' : Y -> Y -> Y) (p1 p2 : X * Y) : X * Y :=
  (T p1.1 p2.1, T' p1.2 p2.2).
Arguments tens_prod {X Y} T T' !p1 !p2 /.
Instance prod_monoidal `{Monoidal X R T U, Monoidal Y R' T' U'}
  : Monoidal (prod_relation R R') (tens_prod T T') (U, U').
Proof. compute; firstorder. Qed.
Instance prod_sym `{Sym X R T, Sym Y R' T'} : Sym (prod_relation R R') (tens_prod T T').
Proof. by compute. Qed.
Instance prod_mset `{MonSet X, MonSet Y} : MonSet (X * Y)
  := {| pro_tens := tens_prod pro_tens pro_tens |}.
Instance prod_smset `{SymMonSet X, SymMonSet Y} : SymMonSet (X * Y) := {}.

Class LaxMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {pres_memp : memp ⊢ F memp; pres_tens : forall {A B}, F A ⊗ F B ⊢ F (A ⊗ B)}.
Hint Mode LaxMon ! - - ! - - ! : typeclass_instances.
Class OplaxMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {pres_memp_op : F memp ⊢ memp; pres_tens_op : forall {A B}, F (A ⊗ B) ⊢ F A ⊗ F B}.
Hint Mode OplaxMon ! - - ! - - ! : typeclass_instances.
(* This definition is OK, since we are in prosets---I think??? *)
Class StrongMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {strong_lax :> LaxMon F; strong_oplax :> OplaxMon F}.
Hint Mode StrongMon ! - - ! - - ! : typeclass_instances.

Instance monoidal_proper `{Monoidal X R T} : Proper (R ++> R ++> R) T.
Proof. move=> ? ? ? ? ? ?; by apply bimap. Qed.
Instance monoidal_proper' `{Monoidal X R T} : Proper (R --> R --> flip R) T.
Proof. move=> ? ? ? ? ? ? /=; by apply bimap. Qed.
Instance monoidal_proper_core `{Monoidal X R T} : Proper (core R ==> core R ==> core R) T.
Proof. firstorder. Qed.

Instance void_proset : Proset void := {| pro_le _ _ := True |}.
Instance void_functor `{Proset X} {F : void -> X} : Functor F | 3.
Proof. move=> []. Qed.

Program Instance prop_proset : Proset Prop := {| pro_le := impl |}.
Next Obligation. firstorder. Qed.
Instance and_monoidal : Monoidal pro_le and True.
Proof. firstorder. Qed.
Instance or_monoidal : Monoidal pro_le or False.
Proof. firstorder. Qed.
Instance and_sym : Sym pro_le and.
Proof. firstorder. Qed.
Instance or_sym : Sym pro_le or.
Proof. firstorder. Qed.
Instance prop_mset : MonSet Prop
  := {| pro_tens := and |}.
Instance prop_smset : SymMonSet Prop := {}.

Instance nat_proset : Proset nat := {| pro_le := le |}.
Instance plus_monoidal : Monoidal pro_le plus 0.
Proof. constructor=> *; compute -[plus] in *; lia. Qed.
Instance plus_sym : Sym pro_le plus.
Proof. compute -[plus] => *; lia. Qed.
Instance nat_mset : MonSet nat := {| pro_tens := plus |}.
Instance nat_smset : SymMonSet nat := {}.
Lemma nat_functor : forall `{Proset X} {F : nat -> X},
    (forall n, F n ⊢ F (S n)) -> Functor F.
Proof. move=> X ? F Step n m; elim: m / => //=; by etransitivity. Qed.

Program Instance bool_proset : Proset bool := {| pro_le := implb |}.
Next Obligation. constructor=> [[] | [] []] //=. Qed.
Instance andb_monoidal : Monoidal pro_le andb true.
Proof. constructor=> [[] [] | | [] | []] //=. Qed.
Instance orb_monoidal : Monoidal pro_le orb false.
Proof. constructor=> [[] [] [] | | [] | []] //=. Qed.
Instance andb_sym : Sym pro_le andb.
Proof. move=> [] [] //=. Qed.
Instance orb_sym : Sym pro_le orb.
Proof. move=> [] [] //=. Qed.
Instance bool_mset : MonSet bool
  := {| pro_tens := andb |}.
Instance bool_smset : SymMonSet bool := {}.

(*
Record discrete (A : Type) := Discrete {get_discrete : A}.
Add Printing Constructor discrete.
Arguments Discrete {_}.
Arguments get_discrete {_}.
*)
Definition discrete (X : Type) : Type := X.
Definition Discrete {X} (A : X) : discrete X := A.
Definition get_discrete {X} (A : discrete X) : X := A.
Typeclasses Opaque discrete Discrete get_discrete.
Opaque discrete Discrete get_discrete.
Instance discrete_proset {X} : Proset (discrete X) := {| pro_le := eq |}.
Instance discrete_functor {X} `{Proset Y} {F : discrete X -> Y} : Functor F | 3.
Proof. move=> a1 a2 /= -> //. Qed.

Definition indiscrete (X : Type) : Type := X.
Definition Indiscrete {X} (A : X) : indiscrete X := A.
Definition get_indiscrete {X} (A : indiscrete X) : X := A.
Typeclasses Opaque indiscrete Indiscrete get_indiscrete.
Opaque indiscrete Indiscrete get_indiscrete.
Program Instance indiscrete_proset {X} : Proset (indiscrete X) := {| pro_le _ _ := True |}.
Next Obligation. done. Qed.
Instance indiscrete_functor `{Proset X} {Y} {F : X -> indiscrete Y} : Functor F | 3.
Proof. done. Qed.

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
  {| pro_le := sig_rel pro_le P |}.
Class MonClosed `{MonSet X} (P : X -> Prop) :=
  {memp_closed : P memp;
   tensor_closed : forall {A B : X}, P A -> P B -> P (A ⊗ B)}.
Hint Mode MonClosed ! - - ! : typeclass_instances.
Definition tens_sig `{MonSet X} (P : X -> Prop) `{!MonClosed P}
           (s1 s2 : sig P) : sig P
  := match s1, s2 with a1 ↾ H1, a2 ↾ H2 => (a1 ⊗ a2) ↾ tensor_closed H1 H2 end.
Arguments tens_sig {_ _ _} P {_} !_ !_ /.
Instance sig_monoidal `{MonSet X} {P : X -> Prop} `{!MonClosed P} :
  Monoidal (sig_rel pro_le P) (tens_sig P) (memp ↾ memp_closed).
Proof.
  constructor; rewrite /core.
  - move=> [A H_A] [A' H_A'] [B H_B] [B' H_B'] /=; apply: bimap.
  - move=> [A H_A] /=; apply: lunit.
  - move=> [A H_A] /=; apply: runit.
  - move=> [A H_A] [B H_B] [C H_C] /=; apply: massoc.
Qed.
Instance sig_sym `{SymMonSet X} {P : X -> Prop} `{!MonClosed P} :
  Sym (sig_rel pro_le P) (tens_sig P).
Proof. move=> [A H_A] [B H_B] /=; apply: sym. Qed.
Instance sig_mset `{MonSet X} {P : X -> Prop} `{!MonClosed P} :
  MonSet (sig P) := {| pro_tens := tens_sig P |}.
Instance sig_smset  `{SymMonSet X} {P : X -> Prop} `{!MonClosed P} :
  SymMonSet (sig P) := {}.
Instance sval_functor `{Proset X} {P : X -> Prop} : Functor (proj1_sig (P:=P)).
Proof. firstorder. Qed.
Instance sval_full `{Proset X} {P : X -> Prop} : Full (proj1_sig (P:=P)).
Proof. firstorder. Qed.
Instance sval_strongmon `{MonSet X} {P : X -> Prop} `{!MonClosed P}
  : StrongMon (proj1_sig (P:=P)).
Proof. constructor; constructor=> // -[A H_A] [B H_B] //. Qed.
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
Instance restrict_cod_functor `{Functor X Y F} {P : Y -> Prop} {I : forall A, P (F A)}
  : Functor (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_full `{Full X Y F} {P : Y -> Prop} {I : forall A, P (F A)}
  : Full (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_laxmon `{LaxMon X Y F} {P : Y -> Prop}
         `{!MonClosed P} {I : forall A, P (F A)}
  : LaxMon (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_oplaxmon `{OplaxMon X Y F} {P : Y -> Prop}
         `{!MonClosed P} {I : forall A, P (F A)}
  : OplaxMon (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_strongmon `{StrongMon X Y F} {P : Y -> Prop}
         `{!MonClosed P} {I : forall A, P (F A)}
  : StrongMon (restrict_cod P F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_functor `{Functor X Y F} {P : Y -> Prop} {I : forall A, P (F A)}
         {ph : phant (sig P)}
  : Functor (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_full `{Full X Y F} {P : Y -> Prop} {I : forall A, P (F A)}
         {ph : phant (sig P)}
  : Full (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_laxmon `{LaxMon X Y F} {P : Y -> Prop} {ph : phant (sig P)}
         `{!MonClosed P} {I : forall A, P (F A)}
  : LaxMon (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_oplaxmon `{OplaxMon X Y F} {P : Y -> Prop} {ph : phant (sig P)}
         `{!MonClosed P} {I : forall A, P (F A)}
  : OplaxMon (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.
Instance restrict_cod_ph_strongmon `{StrongMon X Y F} {P : Y -> Prop} {ph : phant (sig P)}
         `{!MonClosed P} {I : forall A, P (F A)}
  : StrongMon (restrict_cod_ph ph F (H:=I)).
Proof. firstorder. Qed.

Instance id_functor `{Proset X} : Functor (@id X).
Proof. firstorder. Qed.
Instance id_strongmon `{MonSet X} : StrongMon (@id X).
Proof. firstorder. Qed.
Instance compose_functor `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         `{!Functor F, !Functor G} : Functor (F ∘ G) | 0.
Proof. firstorder. Qed.
Instance compose_laxmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Functor F, !Functor G, !LaxMon F, !LaxMon G}
  : LaxMon (F ∘ G).
Proof.
  constructor=> [| A B] /=.
  - setoid_rewrite <- pres_memp; apply: pres_memp.
  - setoid_rewrite <- pres_tens; apply: pres_tens.
Qed.
Instance compose_oplaxmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Functor F, !Functor G, !OplaxMon F, !OplaxMon G}
  : OplaxMon (F ∘ G).
Proof.
  constructor=> [| A B] /=.
  - setoid_rewrite pres_memp_op; apply: pres_memp_op.
  - setoid_rewrite pres_tens_op; apply: pres_tens_op.
Qed.
Instance compose_strongmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Functor F, !Functor G, !StrongMon F, !StrongMon G}
  : StrongMon (F ∘ G).
Proof. constructor; typeclasses eauto. Qed.
Instance const_functor {Y} `{Proset X} : Functor (@const X Y).
Proof. firstorder. Qed.
Instance const_strongmon {Y} `{MonSet X} : StrongMon (@const X Y).
Proof. constructor; by constructor. Qed.
Instance subst_functor1 {Y Y'} `{Proset X} {f : Y' -> Y} : Functor (X:=Y -> X) (.∘ f).
Proof. firstorder. Qed.
Instance subst_strongmon1 {Y Y'} `{MonSet X} {f : Y' -> Y} :
  StrongMon (X:=Y -> X) (.∘ f).
Proof. constructor; by constructor. Qed.
Instance postcomp_functor {Y} `{Proset X, Proset X'} {f : X -> X'} `{!Functor f} :
  Functor (X:=Y -> X) (f ∘.).
Proof. firstorder. Qed.
Instance postcomp_laxmon {Y} `{MonSet X, MonSet X'}
         {f : X -> X'} `{!Functor f, !LaxMon f} : LaxMon (X:=Y -> X) (f ∘.).
Proof. firstorder. Qed.
Instance postcomp_oplaxmon {Y} `{MonSet X, MonSet X'}
         {f : X -> X'} `{!Functor f, !OplaxMon f} : OplaxMon (X:=Y -> X) (f ∘.).
Proof. firstorder. Qed.
Instance postcomp_strongmon {Y} `{MonSet X, MonSet X'}
         {f : X -> X'} `{!Functor f, !StrongMon f} : StrongMon (X:=Y -> X) (f ∘.).
Proof. firstorder. Qed.
Definition eval_at {X Y} (y : Y) : (Y -> X) -> X := fun f => f y.
Arguments eval_at {_ _} _ _ /.
Instance subst_functor2 {Y} `{Proset X} {y : Y} : Functor (X:=Y -> X) (eval_at y).
Proof. firstorder. Qed.
Instance subst_strongmon2 {Y} `{MonSet X} {y : Y} : StrongMon (X:=Y -> X) (eval_at y).
Proof. constructor; by constructor. Qed.
Instance fst_functor `{Proset X, Proset Y} : Functor (@fst X Y).
Proof. firstorder. Qed.
Instance fst_strongmon `{MonSet X, MonSet Y} : StrongMon (@fst X Y).
Proof. by compute. Qed.
Instance snd_functor `{Proset X, Proset Y} : Functor (@snd X Y).
Proof. firstorder. Qed.
Instance snd_strongmon `{MonSet X, MonSet Y} : StrongMon (@snd X Y).
Proof. by compute. Qed.
Instance pair_functor `{Proset X, Proset Y} : Functor (@pair X Y).
Proof. by compute. Qed.
Instance pair_functor' `{Proset X, Proset Y} {A} : Functor (@pair X Y A).
Proof. by compute. Qed.
Definition r_pair {X Y} (B : Y) : X -> X * Y := fun A => (A, B).
Arguments r_pair {_ _} _ _ /.
Instance r_pair_functor' `{Proset X, Proset Y} {B} : Functor (@r_pair X Y B).
Proof. by compute. Qed.
Instance memp_pair_strongmon `{MonSet X, MonSet Y} : StrongMon (@pair X Y memp).
Proof.
  constructor; constructor=> [| B B']; rewrite /= /prod_relation //=;
    (split; [apply (pro_lunit memp) | done]).
Qed.
Instance pair_memp_strongmon `{MonSet X, MonSet Y} : StrongMon (@r_pair X Y memp).
Proof.
  constructor; constructor=> [| A A']; rewrite /= /prod_relation //=;
    (split; [done | apply (pro_lunit memp)]).
Qed.
Instance prod_map_functor `{Proset X, Proset X', Proset Y, Proset Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Functor F, !Functor G} : Functor (prod_map F G).
Proof. firstorder. Qed.
Instance prod_map_laxmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Functor F, !Functor G, !LaxMon F, !LaxMon G}
  : LaxMon (prod_map F G).
Proof. firstorder. Qed.
Instance prod_map_oplaxmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Functor F, !Functor G, !OplaxMon F, !OplaxMon G}
  : OplaxMon (prod_map F G).
Proof. firstorder. Qed.
Instance prod_map_strongmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Functor F, !Functor G, !StrongMon F, !StrongMon G}
  : StrongMon (prod_map F G).
Proof. firstorder. Qed.
Definition r_prod_map {X X' Y Y'} (G : Y -> Y') : (X -> X') -> X * Y -> X' * Y'
  := fun F => prod_map F G.
Arguments r_prod_map {_ _ _ _} _ _ /.
Instance prod_map_functor' `{Proset X, Proset X', Proset Y, Proset Y'}
         {F : X -> X'} `{!Functor F} : Functor (prod_map (B:=Y) (B':=Y') F).
Proof. move=> G G' D [A B] /=; firstorder. Qed.
Instance r_prod_map_functor `{Proset X, Proset X', Proset Y, Proset Y'}
         {G : Y -> Y'} `{!Functor G} : Functor (r_prod_map (X:=X) (X':=X') G).
Proof. move=> F F' D [A B] /=; firstorder. Qed.
Instance prod_map_functor'' `{Proset X, Proset X', Proset Y, Proset Y'}
  : Functor (prod_map (A:=X) (A':=X') (B:=Y) (B':=Y')).
Proof. move=> F F' D G [A B] /=; firstorder. Qed.
Instance curry_functor `{Proset X, Proset Y, Proset Z} {F : X -> Y -> Z}
         `{!Functor F, !forall x, Functor (F x)}
  : Functor (curry F).
Proof. move=> [A B] [A' B'] /= [D1 D2]; setoid_rewrite D2; apply: (fmap' (F:=F) D1). Qed.
Instance uncurry_functor `{Proset X, Proset Y, Proset Z} {F : X * Y -> Z} `{!Functor F}
  : Functor (uncurry F).
Proof.
  move=> A A' D B; change (F (r_pair B A) ⊢ F (r_pair B A')); by setoid_rewrite D.
Qed.
Instance uncurry_functor' `{Proset X, Proset Y, Proset Z}
         {F : X * Y -> Z} `{!Functor F} {A}
  : Functor (uncurry F A).
Proof. move=> B B' D; unfold uncurry; by setoid_rewrite D. Qed.


Definition greatest `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ forall B, P B -> B ⊢ A.
Definition least `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ forall B, P B -> A ⊢ B.
Instance greatest_proper `{Proset X}
  : Proper ((core pro_le ==> iff) ==> core pro_le ==> iff) (greatest (X:=X)).
Proof.
  apply proper_sym_impl_iff_2; [firstorder | typeclasses eauto |].
  move=> P P' E_P A A' E_A [PA U]; split; first by firstorder.
  move=> B /(E_P _ _ (reflexivity B)); setoid_rewrite <- (proj1 E_A); apply: U.
Qed.
Instance least_proper `{Proset X}
  : Proper ((core pro_le ==> iff) ==> core pro_le ==> iff) (least (X:=X)).
Proof.
  apply proper_sym_impl_iff_2; [firstorder | typeclasses eauto |].
  move=> P P' E_P A A' E_A [PA U]; split; first by firstorder.
  move=> B /(E_P _ _ (reflexivity B)); setoid_rewrite (proj2 E_A); apply: U.
Qed.
Lemma greatest_unique : forall `{Proset X} {P : X -> Prop}
                          `{!Proper (core pro_le ==> iff) P} {A A'},
    greatest P A -> greatest P A' -> A ⟛ A'.
Proof. firstorder. Qed.
Lemma least_unique : forall `{Proset X} {P : X -> Prop}
                       `{!Proper (core pro_le ==> iff) P} {A A'},
    least P A -> least P A' -> A ⟛ A'.
Proof. firstorder. Qed.

Definition lower_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, A ⊢ J r.
Definition upper_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, J r ⊢ A.
Instance lower_bound_proper `{Proset X} {R}
  : Proper (pro_le ++> pro_le --> impl) (lower_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 D_A L r.
  setoid_rewrite <- D_A; by setoid_rewrite <- (D_J r).
Qed.
Instance upper_bound_proper `{Proset X} {R}
  : Proper (pro_le --> pro_le ++> impl) (upper_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 D_A L r.
  setoid_rewrite <- D_A; by setoid_rewrite (D_J r).
Qed.
Instance lower_bound_proper' `{Proset X} {R}
  : Proper (pro_le --> pro_le ++> flip impl) (lower_bound (X:=X) (R:=R)).
Proof. move=> ? ? ? ? ? ?; by apply: lower_bound_proper. Qed.
Instance lower_bound_proper'' `{Proset X} {R}
  : Proper (core pro_le ==> core pro_le ==> iff) (lower_bound (X:=X) (R:=R)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: lower_bound_proper.
Qed.
Instance upper_bound_proper' `{Proset X} {R}
  : Proper (pro_le ++> pro_le --> flip impl) (upper_bound (X:=X) (R:=R)).
Proof. move=> ? ? ? ? ? ?; by apply: upper_bound_proper. Qed.
Instance upper_bound_proper'' `{Proset X} {R}
  : Proper (core pro_le ==> core pro_le ==> iff) (upper_bound (X:=X) (R:=R)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: upper_bound_proper.
Qed.
Notation glb J A := (greatest (lower_bound J) A).
Notation lub J A := (least (upper_bound J) A).
Class HasInf `{Proset X} {R} (J : R -> X) :=
  {inf : X; is_inf : glb J inf}.
Class HasSup `{Proset X} {R} (J : R -> X) :=
  {sup : X; is_sup : lub J sup}.
Hint Mode HasInf ! - ! ! : typeclass_instances.
Hint Mode HasSup ! - ! ! : typeclass_instances.
Arguments inf {X _ R} J {_}.
Arguments sup {X _ R} J {_}.
Arguments is_inf {X _ R} J {_}.
Arguments is_sup {X _ R} J {_}.

(* TODO Lots of stuff! *)
Definition inf_lb `{Proset X} {R} {J : R -> X} `{!HasInf J} : lower_bound J (inf J)
  := proj1 (is_inf J).
Definition inf_left `{Proset X} {R} {J : R -> X} `{!HasInf J} (r : R) {A}
  : J r ⊢ A -> inf J ⊢ A
  := fun D => transitivity (inf_lb r) D.
Definition inf_right `{Proset X} {R} {J : R -> X} `{!HasInf J} {A : X}
  : lower_bound J A -> A ⊢ inf J
  := proj2 (is_inf J) A.
Lemma inf_universal : forall `{Proset X} {R} {J : R -> X} `{!HasInf J} {A : X},
    lower_bound J A <-> A ⊢ inf J.
Proof.
  move=> *; split; first by apply/inf_right.
  move=> D; setoid_rewrite D; apply: inf_lb.
Qed.
Definition sup_ub `{Proset X} {R} {J : R -> X} `{!HasSup J} : upper_bound J (sup J)
  := proj1 (is_sup J).
Definition sup_left `{Proset X} {R} {J : R -> X} `{!HasSup J} {A : X}
  : upper_bound J A -> sup J ⊢ A
  := proj2 (is_sup J) A.
Definition sup_right `{Proset X} {R} {J : R -> X} `{!HasSup J} (r : R) {A}
  : A ⊢ J r -> A ⊢ sup J
  := fun D => transitivity D (sup_ub r).
Lemma sup_universal : forall `{Proset X} {R} {J : R -> X} `{!HasSup J} {A : X},
    upper_bound J A <-> sup J ⊢ A.
Proof.
  move=> *; split; first by apply/sup_left.
  move=> D; setoid_rewrite <- D; apply: sup_ub.
Qed.

(*
Definition InfsOfShape (R X : Type) `{!Proset R, !Proset X} : Type
  := forall J : R -> X, Functor J -> HasInf J.
Definition SupsOfShape (R X : Type) `{!Proset R, !Proset X} : Type
  := forall J : R -> X, Functor J -> HasSup J.
Definition DInfsOfShape (R X : Type) `{!Proset X} : Type
  := forall J : R -> X, HasInf J.
Definition DSupsOfShape (R X : Type) `{!Proset X} : Type
  := forall J : R -> X, HasSup J.
Existing Class InfsOfShape.
Existing Class SupsOfShape.
Existing Class DInfsOfShape.
Existing Class DSupsOfShape.
Hint Mode InfsOfShape ! ! - - : typeclass_instances.
Hint Mode SupsOfShape ! ! - - : typeclass_instances.
Hint Mode DInfsOfShape ! ! - : typeclass_instances.
Hint Mode DSupsOfShape ! ! - : typeclass_instances.
Instance ios_def `{IOS : InfsOfShape R X} {J : R -> X} `{!Functor J} : HasInf J
  := IOS J _.
Instance sos_def `{SOS : SupsOfShape R X} {J : R -> X} `{!Functor J} : HasSup J
  := SOS J _.
Instance dios_def `{DIOS : DInfsOfShape R X} {J : R -> X} : HasInf J
  := DIOS J.
Instance dsos_def `{DSOS : DSupsOfShape R X} {J : R -> X} : HasSup J
  := DSOS J.
*)

Notation InfsOfShape R X := (forall J : R -> X, Functor J -> HasInf J).
Notation SupsOfShape R X := (forall J : R -> X, Functor J -> HasSup J).
Notation DInfsOfShape R X := (forall J : R -> X, HasInf J).
Notation DSupsOfShape R X := (forall J : R -> X, HasSup J).

Lemma inf_from_discrete : forall {R} `{Proset X} {J : R -> X},
    HasInf (J ∘ get_discrete) -> HasInf J.
Proof. done. Defined.
Lemma sup_from_discrete : forall {R} `{Proset X} {J : R -> X},
    HasSup (J ∘ get_discrete) -> HasSup J.
Proof. done. Defined.
Lemma infs_from_discrete : forall `{Proset X, Proset R},
    InfsOfShape (discrete R) X -> DInfsOfShape R X.
Proof. move=> X ? R ? IOS J.
       exists (inf (J ∘ get_discrete)); apply: is_inf. Defined.
Lemma sups_from_discrete : forall `{Proset X, Proset R},
    SupsOfShape (discrete R) X -> DSupsOfShape R X.
Proof. move=> X ? R ? SOS J; exists (sup (J ∘ get_discrete)); apply: is_sup. Defined.

Notation MeetSemilattice X := (forall `{EqDecision R}, Finite R -> DInfsOfShape R X).
Notation JoinSemilattice X := (forall `{EqDecision R}, Finite R -> DSupsOfShape R X).
Class Lattice (X : Type) `{!Proset X, !MeetSemilattice X, !JoinSemilattice X}.
Hint Mode Lattice ! - - - : typeclass_instances.
Instance lattice_def `{Proset X, !MeetSemilattice X, !JoinSemilattice X}
  : Lattice X := {}.
Notation InfLattice X := (forall R, DInfsOfShape R X).
Notation SupLattice X := (forall R, DSupsOfShape R X).
Class Complete (X : Type) `{!Proset X, !InfLattice X, !SupLattice X}.
Hint Mode Complete ! - - - : typeclass_instances.
Instance complete_def `{Proset X, !InfLattice X, !SupLattice X}
  : Complete X := {}.

Class Directed (X : Type) `{!Proset X} :=
  direct : forall `{Finite R} (J : R -> X), exists A, upper_bound J A.
Instance join_semilattice_directed `{Proset X, !JoinSemilattice X} : Directed X.
Proof. move=> R ? ? J; exists (sup J); apply/sup_ub. Qed.
Notation DirectedComplete X := (forall `{Proset R}, Directed R -> SupsOfShape R X).

Program Instance prop_inflattice {R} {J : R -> Prop} : HasInf J := {| inf := all J |}.
Solve All Obligations with firstorder.
Program Instance prop_suplattice {R} {J : R -> Prop} : HasSup J := {| sup := ex J |}.
Solve All Obligations with firstorder.

(* This could probably follow by some abstract nonsense if we moved it *after*
   presheaf stuff... Hmm. Oh well. *)
Definition ub_diagram `{Proset X} {R} (J : R -> X) : sig (upper_bound J) -> X
  := sval.
Definition lb_diagram `{Proset X} {R} (J : R -> X) : sig (lower_bound J) -> X
  := sval.
Arguments ub_diagram _ /.
Arguments lb_diagram _ /.
Lemma ub_diagram_spec : forall `{Proset X} {R} {J : R -> X} {A},
    glb (ub_diagram J) A <-> lub J A.
Proof.
  move=> X ? R J A; split=> [Glb | Lub].
  - pose H := {| inf := A; is_inf := Glb |}; change A with (inf (ub_diagram J)); split.
    + move=> r; apply/inf_right => -[B UB] //=.
    + move=> B UB; by apply/(inf_left (B ↾ UB)).
  - pose H := {| sup := A; is_sup := Lub |}; change A with (sup J); split.
    + move=> [B UB]; apply/sup_left => r //=.
    + move=> B LB; apply/(LB (sup J ↾ _))/sup_ub.
Qed.
Lemma lb_diagram_spec : forall `{Proset X} {R} {J : R -> X} {A},
    lub (lb_diagram J) A <-> glb J A.
Proof.
  move=> X ? R J A; split=> [Lub | Glb].
  - pose H := {| sup := A; is_sup := Lub |}; change A with (sup (lb_diagram J)); split.
    + move=> r; apply/sup_left => -[B LB] //=.
    + move=> B LB; by apply/(sup_right (B ↾ LB)).
  - pose H := {| inf := A; is_inf := Glb |}; change A with (inf J); split.
    + move=> [B LB]; apply/inf_right => r //=.
    + move=> B UB; apply/(UB (inf J ↾ _))/inf_lb.
Qed.
Definition infs_sufficient `{Proset X, !InfLattice X} : SupLattice X
  := fun R J => {| sup := inf (ub_diagram J); is_sup := proj1 ub_diagram_spec (is_inf _) |}.
Definition sups_sufficient `{Proset X, !SupLattice X} : InfLattice X
  := fun R J => {| inf := sup (lb_diagram J); is_inf := proj1 lb_diagram_spec (is_sup _) |}.

Lemma inf_unique : forall `{Proset X} {R} {A} {J : R -> X} `{!HasInf J},
    glb J A <-> A ⟛ inf J.
Proof.
  move=> ? ? ? ? ? J; split.
  - move=> H; apply/(greatest_unique H (is_inf _)).
  - move=> E; rewrite E; apply: is_inf.
Qed.
Lemma sup_unique : forall `{Proset X} {R} {A} {J : R -> X} `{!HasSup J},
    lub J A <-> A ⟛ sup J.
Proof.
  move=> ? ? ? ? ? J; split.
  - move=> H; apply/(least_unique H (is_sup _)).
  - move=> E; rewrite E; apply: is_sup.
Qed.

Program Instance pw_inf {X} `{Proset Y} {R} {J : R -> X -> Y} `{!forall x, HasInf (flip J x)}
  : HasInf J
  := {| inf x := inf (flip J x) |}.
Next Obligation.
  move=> X Y ? R J ?; split=> [r | F LB] A.
  - apply/inf_lb.
  - apply/inf_right; firstorder.
Qed.
Program Instance pw_sup {X} `{Proset Y} {R} {J : R -> X -> Y} `{!forall x, HasSup (flip J x)}
  : HasSup J
  := {| sup x := sup (flip J x) |}.
Next Obligation.
  move=> X Y ? R J ?; split=> [r | F UB] A.
  - apply/sup_ub.
  - apply/sup_left; firstorder.
Qed.
Program Instance op_inf `{Proset X} {R} {J : R -> op X} `{!HasSup (get_op ∘ J)}
  : HasInf J
  := {| inf := Op (sup (get_op ∘ J)) |}.
Next Obligation.
  move=> X ? R J ?; split=> [r | [A] LB] /=.
  - apply/sup_right; by simpl.
  - apply/sup_left; firstorder.
Qed.
Program Instance op_sup `{Proset X} {R} {J : R -> op X} `{!HasInf (get_op ∘ J)}
  : HasSup J
  := {| sup := Op (inf (get_op ∘ J)) |}.
Next Obligation.
  move=> X ? R J ?; split=> [r | [A] UB] /=.
  - apply/inf_left; by simpl.
  - apply/inf_right; firstorder.
Qed.
Lemma curry_dep : forall {A B} {P : A * B -> Prop}, (forall p, P p) <-> (forall a b, P (a, b)).
Proof. move=> A B P; split=> [H a b | H [a b]] //. Qed.
Lemma uncurry_dep : forall {A B} {P : A -> B -> Prop}, (forall a b, P a b) <-> (forall p, P p.1 p.2).
Proof. move=> A B P; split=> [H p | H a b] //; apply: (H (a, b)). Qed.
Lemma prod_lb : forall `{Proset X, Proset Y} {R} {p} {J : R -> X * Y},
    lower_bound J p <-> lower_bound (fst ∘ J) p.1 /\ lower_bound (snd ∘ J) p.2.
Proof. firstorder. Qed.
Lemma prod_ub : forall `{Proset X, Proset Y} {R} {J : R -> X * Y} {p},
    upper_bound J p <-> upper_bound (fst ∘ J) p.1 /\ upper_bound (snd ∘ J) p.2.
Proof. firstorder. Qed.
Program Instance prod_inf `{Proset X, Proset Y} {R} {J : R -> X * Y}
        `{!HasInf (fst ∘ J), !HasInf (snd ∘ J)}
  : HasInf J
  := {| inf := (inf (fst ∘ J), inf (snd ∘ J)) |}.
Next Obligation.
  move=> ? ? ? ? ? J ? ?.
  rewrite /greatest curry_dep; setoid_rewrite (prod_lb (J:=J)); simpl.
  setoid_rewrite inf_universal; firstorder.
Qed.
Program Instance prod_sup `{Proset X, Proset Y} {R} {J : R -> X * Y}
        `{!HasSup (fst ∘ J), !HasSup (snd ∘ J)}
  : HasSup J
  := {| sup := (sup (fst ∘ J), sup (snd ∘ J)) |}.
Next Obligation.
  move=> ? ? ? ? ? J ? ?.
  rewrite /least curry_dep; setoid_rewrite (prod_ub (J:=J)); simpl.
  setoid_rewrite sup_universal; firstorder.
Qed.
(*
Lemma op_lb_ub : forall `{Proset X} {R},
*)

Notation Top X := (DInfsOfShape void X).
Notation Bot X := (DSupsOfShape void X).
Notation BinMeets X := (DInfsOfShape bool X).
Notation BinJoins X := (DSupsOfShape bool X).
Definition top (X : Type) `{!Proset X, !Top X} : X :=
  inf (of_void _).
Definition bot (X : Type) `{!Proset X, !Bot X} : X :=
  sup (of_void _).
Notation "⊤" := (top _) : proset_scope.
Notation "⊥" := (bot _) : proset_scope.
Definition meet `{Proset X, !BinMeets X} (A B : X) : X :=
  inf (fun b : bool => if b then A else B).
Definition join `{Proset X, !BinJoins X} (A B : X) : X :=
  sup (fun b : bool => if b then A else B).
Infix "⩕" := meet (at level 40, left associativity) : proset_scope.
Infix "⩖" := join (at level 40, left associativity) : proset_scope.
(* TODO This type could technically be less strict... *)
Definition embed_prop `{Complete X} (P : Prop) : X := sup (fun H : P => ⊤).
Notation "⌜ P ⌝" := (embed_prop P) : proset_scope.
Arguments top : simpl never.
Arguments bot : simpl never.
Arguments meet : simpl never.
Arguments join : simpl never.
Arguments embed_prop : simpl never.

Definition top_right `{Proset X, !Top X} {A : X} : A ⊢ ⊤ :=
  inf_right (Empty_set_ind _).
Definition bot_left `{Proset X, !Bot X} {A : X} : ⊥ ⊢ A :=
  sup_left (Empty_set_ind _).
Definition meet_proj1 `{Proset X, !BinMeets X} {A B : X} : A ⩕ B ⊢ A
  := inf_lb true.
Definition meet_proj2 `{Proset X, !BinMeets X} {A B : X} : A ⩕ B ⊢ B
  := inf_lb false.
Definition meet_left1 `{Proset X, !BinMeets X} {A B C : X} : A ⊢ C -> A ⩕ B ⊢ C
  := transitivity meet_proj1.
Definition meet_left2 `{Proset X, !BinMeets X} {A B C : X} : B ⊢ C -> A ⩕ B ⊢ C
  := transitivity meet_proj2.
Definition meet_right `{Proset X, !BinMeets X} {C A B : X} (D1 : C ⊢ A) (D2 : C ⊢ B)
  : C ⊢ A ⩕ B
  := inf_right (fun b => if b as b0 return C ⊢ (if b0 then A else B) then D1 else D2).
Definition join_inj1 `{Proset X, !BinJoins X} {A B : X} : A ⊢ A ⩖ B
  := sup_ub true.
Definition join_inj2 `{Proset X, !BinJoins X} {A B : X} : B ⊢ A ⩖ B
  := sup_ub false.
Definition join_right1 `{Proset X, !BinJoins X} {C A B : X} : C ⊢ A -> C ⊢ A ⩖ B
  := fun H => transitivity H join_inj1.
Definition join_right2 `{Proset X, !BinJoins X} {C A B : X} : C ⊢ B -> C ⊢ A ⩖ B
  := fun H => transitivity H join_inj2.
Definition join_left `{Proset X, !BinJoins X} {A B C : X} (D1 : A ⊢ C) (D2 : B ⊢ C)
  : A ⩖ B ⊢ C
  := sup_left (fun b => if b as b0 return (if b0 then A else B) ⊢ C then D1 else D2).
Lemma embed_prop_left : forall `{Complete X} {P : Prop} {Q : X},
    (P -> ⊤ ⊢ Q) -> ⌜ P ⌝ ⊢ Q.
Proof. move=> X ? ? ? ? P Q D; by apply: sup_left. Qed.
Lemma embed_prop_right : forall `{Complete X} {P : X} {Q : Prop},
    Q -> P ⊢ embed_prop Q.
Proof. move=> *; apply/sup_right/top_right. Qed.

Program Definition build_meet_semilattice (X : Type) `{!Proset X, !Top X, !BinMeets X}
  : MeetSemilattice X
  := fun R _ _ J => {| inf := foldr meet ⊤ (map J (enum R)) |}.
Next Obligation.
  move=> X ? ? ? R ? ? J.
  rewrite /greatest /lower_bound; setoid_rewrite <- Forall_finite.
  elim: (enum R) => /= [| r rs [IH1 IH2]]; split.
  - done.
  - move=> *; apply/top_right.
  - constructor.
    + apply/meet_proj1.
    + apply: Forall_impl IH1 (fun _ => meet_left2).
  - move=> B /Forall_cons [? /IH2 ?]; by apply/meet_right.
Qed.
Program Definition build_join_semilattice (X : Type) `{!Proset X, !Bot X, !BinJoins X}
  : JoinSemilattice X
  := fun R _ _ J => {| sup := foldr join ⊥ (map J (enum R)) |}.
Next Obligation.
  move=> X ? ? ? R ? ? J.
  rewrite /least /upper_bound; setoid_rewrite <- Forall_finite.
  elim: (enum R) => /= [| r rs [IH1 IH2]]; split.
  - done.
  - move=> *; apply/bot_left.
  - constructor.
    + apply/join_inj1.
    + apply: Forall_impl IH1 (fun _ => join_right2).
  - move=> B /Forall_cons [? /IH2 ?]; by apply/join_left.
Qed.

Program Instance nat_join_semilattice : JoinSemilattice nat
  := @build_join_semilattice nat _ (fun _ => {| sup := 0 |})
                             (fun J => {| sup := max (J true) (J false) |}).
Next Obligation. compute; dintuition. Qed.
Next Obligation.
  move=> J; split.
  - move=> []; [apply: Nat.le_max_l | apply: Nat.le_max_r].
  - move=> n UB; apply: Nat.max_lub; apply: UB.
Qed.
Program Instance bool_meet_semilattice : MeetSemilattice bool
  := @build_meet_semilattice bool _ (fun _ => {| inf := true |})
                             (fun J => {| inf := andb (J true) (J false) |}).
Next Obligation. compute; split; [dintuition | case; dintuition]. Qed.
Next Obligation.
  move=> J; split.
  - move=> []; apply/implyP => /andP [//].
  - move=> b LB; apply/implyP => H; apply/andP; split; by apply/(implyP (LB _)).
Qed.
Program Instance bool_join_semilattice : JoinSemilattice bool
  := @build_join_semilattice bool _ (fun _ => {| sup := false |})
                             (fun J => {| sup := orb (J true) (J false) |}).
Next Obligation. compute; split; [dintuition | case; dintuition]. Qed.
Next Obligation.
  move=> J; split.
  - move=> []; apply/implyP => H; apply/orP; auto.
  - move=> b UB; apply/implyP => /orP [] /(implyP (UB _)) //.
Qed.

Instance cartesian_monoidal `{Proset X, !MeetSemilattice X}
  : Monoidal (X:=X) pro_le meet ⊤.
Proof.
  constructor.
  - move=> A A' B B' D1 D2; apply/meet_right.
    + by apply/meet_left1.
    + by apply/meet_left2.
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
  : Monoidal (X:=X) pro_le join ⊥.
Proof.
  constructor.
  - move=> A A' B B' D1 D2; apply/join_left.
    + by apply/join_right1.
    + by apply/join_right2.
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
Instance cartesian_sym `{Proset X, !MeetSemilattice X} : Sym (X:=X) pro_le meet.
Proof. move=> A B; apply/(meet_right meet_proj2 meet_proj1). Qed.
Instance cocartesian_sym `{Proset X, !JoinSemilattice X} : Sym (X:=X) pro_le join.
Proof. move=> A B; apply/(join_left join_inj2 join_inj1). Qed.

Class PreservesInf `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  preserve_inf : forall A, glb J A -> glb (F ∘ J) (F A).
Class PreservesSup `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  preserve_sup : forall A, lub J A -> lub (F ∘ J) (F A).
Hint Mode PreservesInf ! - ! - ! ! ! : typeclass_instances.
Hint Mode PreservesSup ! - ! - ! ! ! : typeclass_instances.
Lemma preserves_inf_alt1 : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                            `{!Functor F, !HasInf J},
    PreservesInf F J <-> glb (F ∘ J) (F (inf J)).
Proof.
  move=> *; split.
  - move=> ?; apply/preserve_inf/is_inf.
  - move=> Glb A /inf_unique E; rewrite E //.
Qed.
Lemma preserves_sup_alt1 : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                             `{!Functor F, !HasSup J},
    PreservesSup F J <-> lub (F ∘ J) (F (sup J)).
Proof.
  move=> *; split.
  - move=> ?; apply/preserve_sup/is_sup.
  - move=> Lub A /sup_unique E; rewrite E //.
Qed.
Lemma preserves_inf_alt2 : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                             `{!Functor F, !HasInf J, !HasInf (F ∘ J)},
    PreservesInf F J <-> F (inf J) ⟛ inf (fun r => F (J r)).
Proof. move=> *; rewrite preserves_inf_alt1; apply: inf_unique. Qed.
Lemma preserves_sup_alt2 : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                             `{!Functor F, !HasSup J, !HasSup (F ∘ J)},
    PreservesSup F J <-> F (sup J) ⟛ sup (fun r => F (J r)).
Proof. move=> *; rewrite preserves_sup_alt1; apply: sup_unique. Qed.
Lemma distrib_inf : forall `{Proset X, Proset Y} {R} (J : R -> X)
                      {F : X -> Y} `{!PreservesInf F J} `{!HasInf J, !HasInf (F ∘ J)},
    F (inf J) ⟛ inf (fun r => F (J r)).
Proof. move=> *; apply/inf_unique/preserve_inf/is_inf. Qed.
Lemma distrib_sup : forall `{Proset X, Proset Y} {R} (J : R -> X)
                      {F : X -> Y} `{!PreservesSup F J} `{!HasSup J, !HasSup (F ∘ J)},
    F (sup J) ⟛ sup (fun r => F (J r)).
Proof. move=> *; apply/sup_unique/preserve_sup/is_sup. Qed.

Notation PresInfsOfShape R F := (forall J, Functor J -> PreservesInf (R:=R) F J).
Notation PresSupsOfShape R F := (forall J, Functor J -> PreservesSup (R:=R) F J).
Notation PresDInfsOfShape R F := (forall J, PreservesInf (R:=R) F J).
Notation PresDSupsOfShape R F := (forall J, PreservesSup (R:=R) F J).
Notation Continuous F := (forall R, PresDInfsOfShape R F).
Notation Cocontinuous F := (forall R, PresDSupsOfShape R F).
Notation Lex F := (forall `{H : EqDecision R}, @Finite R H -> PresDInfsOfShape R F).
Notation Rex F := (forall `{H : EqDecision R}, @Finite R H -> PresDSupsOfShape R F).
Notation ScottContinuous F :=
  (forall `{H : Proset R}, @Directed R H -> PresSupsOfShape R F).

(* Example *)
Definition fixed_point `{Proset X} (F : X -> X) (A : X) : Prop
  := F A ⟛ A.
Definition kleene_chain `{Proset X, !Bot X} (F : X -> X) : nat -> X
  := fun n => Nat.iter n F ⊥.
Lemma kleene_chain_increasing : forall `{Proset X, !Bot X} {F : X -> X} `{!Functor F} {n},
    kleene_chain F n ⊢ F (kleene_chain F n).
Proof. move=> X ? ? F ?; elim=> /= [| n]; [apply/bot_left | apply/fmap']. Qed.
Instance kleene_chain_chain `{Proset X, !Bot X} {F : X -> X} `{!Functor F}
  : Functor (kleene_chain F).
Proof. apply/nat_functor/@kleene_chain_increasing. Qed.
Theorem kleene : forall `{Proset X, !DirectedComplete X, !Bot X} {F : X -> X}
                   `{!Functor F, !ScottContinuous F},
    least (fixed_point F) (sup (kleene_chain F)).
Proof.
  move=> X ? ? ? F ? ?; split.
  - rewrite /fixed_point distrib_sup; split; apply/sup_left => n.
    + by apply/(sup_right (S n)).
    + apply/(sup_right n)/kleene_chain_increasing.
  - move=> A FP; apply/sup_left; elim=> /= [| n].
    + apply/bot_left.
    + move=> D; unfold fixed_point in FP.
      setoid_rewrite <- (proj1 FP); by apply/fmap'.
Qed.
(*
Class Continuous `{Proset X, Proset Y} (F : X -> Y) :=
  distrib_glb : forall {R} (J : R -> X) `{!HasInf J}, glb (F ∘ J) (F (inf J)).
Class Cocontinuous `{Proset X, Proset Y} (F : X -> Y) :=
  distrib_lub : forall {R} (J : R -> X) `{!HasSup J}, lub (F ∘ J) (F (sup J)).
Hint Mode Continuous ! - ! - ! : typeclass_instances.
Hint Mode Cocontinuous ! - ! - ! : typeclass_instances.
*)

Lemma F_inf : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                `{!Functor F, !HasInf J, !HasInf (F ∘ J)},
    F (inf J) ⊢ inf (fun r => F (J r)).
Proof. move=> *; apply/inf_right => r; apply/fmap'/inf_lb. Qed.
Lemma F_sup : forall `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
                `{!Functor F, !HasSup J, !HasSup (F ∘ J)},
    sup (fun r => F (J r)) ⊢ F (sup J).
Proof. move=> *; apply/sup_left => r; apply/fmap'/sup_ub. Qed.
Lemma distrib_inf_sufficient : forall `{Complete X, Complete Y} {F : X -> Y} `{!Functor F},
    (forall {R} (J : R -> X), inf (F ∘ J) ⊢ F (inf J)) -> Continuous F.
Proof.
  move=> X ? ? ? ? Y ? ? ? ? F ? Distr R J.
  apply/preserves_inf_alt2; split; [apply/F_inf | apply/Distr].
Qed.
Lemma distrib_sup_sufficient : forall `{Complete X, Complete Y} {F : X -> Y} `{!Functor F},
    (forall {R} (J : R -> X), F (sup J) ⊢ sup (F ∘ J)) -> Cocontinuous F.
Proof.
  move=> X ? ? ? ? Y ? ? ? ? F ? Distr R J.
  apply/preserves_sup_alt2; split; [apply/Distr | apply/F_sup].
Qed.

Lemma full_reflects_inf : forall `{Functor X Y F, !Full F} {R} (J : R -> X) A,
    glb (F ∘ J) (F A) -> glb J A.
Proof.
  move=> X ? Y ? F ? ? R J A Glb; split=> [r | A' LB].
  - apply/(unfmap (F:=F))/(proj1 Glb).
  - apply/(unfmap (F:=F))/(proj2 Glb) => r /=; apply/fmap'/LB.
Qed.
Lemma full_reflects_sup : forall `{Functor X Y F, !Full F} {R} (J : R -> X) A,
    lub (F ∘ J) (F A) -> lub J A.
Proof.
  move=> X ? Y ? F ? ? R J A Lub; split=> [r | A' UB].
  - apply/(unfmap (F:=F))/(proj1 Lub).
  - apply/(unfmap (F:=F))/(proj2 Lub) => r /=; apply/fmap'/UB.
Qed.
Lemma full_undistrib_inf : forall `{Functor X Y F, !Full F} {R} (J : R -> X)
                             `{!HasInf (F ∘ J)} A,
    F A ⟛ inf (F ∘ J) -> glb J A.
Proof. move=> ? ? ? ? ? ? ? ? ? ? ? /inf_unique; apply: full_reflects_inf. Qed.
Lemma full_undistrib_sup : forall `{Functor X Y F, !Full F} {R} (J : R -> X)
                             `{!HasSup (F ∘ J)} A,
    F A ⟛ sup (F ∘ J) -> lub J A.
Proof. move=> ? ? ? ? ? ? ? ? ? ? ? /sup_unique; apply: full_reflects_sup. Qed.

(*
Instance op_continuous1 `{Functor X Y F, !Continuous F}
  : Cocontinuous (Op ∘ F ∘ get_op).
Proof.
  move=> R J A [C U].
  split=> [r | [A']] /=.
  - move: (C r); move: (A) (J r) => [?] [?] /=; apply/fmap'.
  - apply: C'. (U (Op (F (get_op A)))). A')).
*)

Instance inf_functor {R} `{Proset X, !DInfsOfShape R X}
  : Functor (fun J : R -> X => inf J).
Proof. move=> A B D; apply/inf_right => r; by apply/inf_left. Qed.
Instance inf_laxmon {R} `{MonSet X, !DInfsOfShape R X} : LaxMon (fun J : R -> X => inf J).
Proof.
  constructor=> [| A B].
  - apply: inf_right => A //.
  - apply: inf_right => r; apply: bimap; apply/inf_lb.
Qed.
Instance sup_functor {R} `{Proset X, !DSupsOfShape R X}
  : Functor (fun J : R -> X => sup J).
Proof. move=> A B D; apply/sup_left => r; by apply/sup_right. Qed.
Instance sup_oplaxmon {R} `{MonSet X, !DSupsOfShape R X}
  : OplaxMon (fun J : R -> X => sup J).
Proof.
  constructor=> [| A B].
  - apply: sup_left => A //.
  - apply: sup_left => r; apply: bimap; apply/sup_ub.
Qed.

(*
Instance lex_def `{Proset X, Proset Y} {F : X -> Y} `{!Lex F} `{Finite R} {J : R -> X}
  : PreservesInf F J := preserve_inf.
*)
Lemma distrib_top : forall `{Proset X, Proset Y, !Top X, !Top Y}
                      {F : X -> Y} `{!Lex F},
    F ⊤ ⟛ ⊤.
Proof. move=> *; rewrite distrib_inf; by apply/(fmap_core (H1:=inf_functor))/pw_core'. Qed.
Lemma distrib_bot : forall `{Proset X, Proset Y, !Bot X, !Bot Y}
                      {F : X -> Y} `{!Rex F},
    F ⊥ ⟛ ⊥.
Proof. move=> *; rewrite distrib_sup; by apply/(fmap_core (H1:=sup_functor))/pw_core'. Qed.
Lemma distrib_meet : forall `{Proset X, Proset Y, !BinMeets X, !BinMeets Y}
                       {F : X -> Y} `{!Lex F} {A B},
    F (A ⩕ B) ⟛ F A ⩕ F B.
Proof.
  move=> *; rewrite distrib_inf; apply/(fmap_core (H1:=inf_functor))/pw_core' => -[] //.
Qed.
Lemma distrib_join : forall `{Proset X, Proset Y, !BinJoins X, !BinJoins Y}
                       {F : X -> Y} `{!Rex F} {A B},
    F (A ⩖ B) ⟛ F A ⩖ F B.
Proof.
  move=> *; rewrite distrib_sup; apply/(fmap_core (H1:=sup_functor))/pw_core' => -[] //.
Qed.
Lemma distrib_embed_prop : forall `{Complete X, Complete Y} {F : X -> Y}
                             `{!Lex F, !Cocontinuous F} {P},
    F (embed_prop P) ⟛ embed_prop P.
Proof.
  move=> *; rewrite distrib_sup; apply/(fmap_core (H1:=sup_functor))/pw_core' => H /=.
  apply/distrib_top.
Qed.

Instance id_continuous `{Proset X} : Continuous (@id X).
Proof. firstorder. Qed.
Instance id_cocontinuous `{Proset X} : Cocontinuous (@id X).
Proof. firstorder. Qed.
Instance compose_continuous `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         `{!Functor F, !Functor G, !Continuous F, !Continuous G} : Continuous (F ∘ G) | 0.
Proof. move=> ? ? ? ? /=; by apply/(preserve_inf (F:=F))/(preserve_inf (F:=G)). Qed.
Instance compose_cocontinuous `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         `{!Functor F, !Functor G, !Cocontinuous F, !Cocontinuous G}
  : Cocontinuous (F ∘ G) | 0.
Proof. move=> ? ? ? ? /=; by apply/(preserve_sup (F:=F))/(preserve_sup (F:=G)). Qed.
Instance subst_continuous1 {Y Y'} `{Complete X} {f : Y' -> Y}
  : Continuous (fun g : Y -> X => g ∘ f).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance subst_cocontinuous1 {Y Y'} `{Complete X} {f : Y' -> Y}
  : Cocontinuous (fun g : Y -> X => g ∘ f).
Proof. by apply/distrib_sup_sufficient. Qed.
Instance subst_continuous2 {Y} `{Complete X} {y : Y} : Continuous (eval_at (X:=X) y).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance subst_cocontinuous2 {Y} `{Complete X} {y : Y}
  : Cocontinuous (eval_at (X:=X) y).
Proof. by apply/distrib_sup_sufficient. Qed.
(*
Instance fst_continuous `{Proset X, Proset Y} : Continuous (@fst X Y).
Proof. move=> R [A B] J /=; rewrite prod_inf_cone /=; tauto. Qed.
Instance fst_cocontinuous `{Proset X, Proset Y} : Cocontinuous (@fst X Y).
Proof. move=> R J [A B] /=; rewrite prod_colim_cocone /=; tauto. Qed.
Instance snd_continuous `{Proset X, Proset Y} : Continuous (@snd X Y).
Proof. move=> R [A B] J /=; rewrite prod_lim_cone /=; tauto. Qed.
Instance snd_cocontinuous `{Proset X, Proset Y} : Cocontinuous (@snd X Y).
Proof. move=> R J [A B] /=; rewrite prod_colim_cocone /=; tauto. Qed.
Instance prod_map_continuous `{Proset X, Proset X', Proset Y, Proset Y'} {F : X -> X'}
         {G : Y -> Y'} `{!Functor F, !Functor G, !Continuous F, !Continuous G}
  : Continuous (prod_map F G).
Proof.
  move=> R [A B] J /= /prod_lim_cone /= [L1 L2].
  apply/prod_lim_cone; split; simpl; by apply/distrib_lim_cone.
Qed.
Instance prod_map_cocontinuous `{Proset X, Proset X', Proset Y, Proset Y'} {F : X -> X'}
         {G : Y -> Y'} `{!Functor F, !Functor G, !Cocontinuous F, !Cocontinuous G}
  : Cocontinuous (prod_map F G).
Proof.
  move=> R J [A B] /= /prod_colim_cocone /= [L1 L2].
  apply/prod_colim_cocone; split; simpl.
  - by apply/(distrib_colim_cocone (F:=F)).
  - by apply/(distrib_colim_cocone (F:=G)).
Qed.
*)


Class ClosedMonoidal {X} (R : X -> X -> Prop) (T : X -> X -> X) (H : X -> X -> X) :=
  tensor_hom A B C : R (T A B) C <-> R A (H B C).
Hint Mode ClosedMonoidal ! ! ! - : typeclass_instances.
Hint Mode ClosedMonoidal ! ! - ! : typeclass_instances.
Class LClosedMonoidal {X} (R : X -> X -> Prop) (T : X -> X -> X) (H : X -> X -> X) :=
  l_tensor_hom A B C : R (T B A) C <-> R A (H B C).
Hint Mode LClosedMonoidal ! ! ! - : typeclass_instances.
Hint Mode LClosedMonoidal ! ! - ! : typeclass_instances.
Class ClosedMonSet (X : Type) `{MonSet X} :=
  {internal_hom : X -> X -> X;
   pro_tensor_hom :> ClosedMonoidal pro_le pro_tens internal_hom}.
Hint Mode ClosedMonSet ! - - : typeclass_instances.
Infix "⊸" := internal_hom (at level 40) : proset_scope.
Class LClosedMonSet (X : Type) `{MonSet X} :=
  {l_internal_hom : X -> X -> X;
   pro_l_tensor_hom :> LClosedMonoidal pro_le pro_tens l_internal_hom}.
Hint Mode LClosedMonSet ! - - : typeclass_instances.
Infix "⊸̂" := l_internal_hom (at level 40) : proset_scope.
Class Exponents (X : Type) `{!Proset X, !BinMeets X} :=
  {exponential : X -> X -> X;
   meet_exponential A B C : A ⩕ B ⊢ C <-> A ⊢ exponential B C}.
Hint Mode Exponents ! - - : typeclass_instances.
Infix "⟿" := exponential (at level 40) : proset_scope.
Program Instance sym_lclosed `{SymMonSet X, !ClosedMonSet X} : LClosedMonSet X | 2
  := {| l_internal_hom := internal_hom |}.
Next Obligation.
  move=> X ? ? ? ? A B C; split.
  - setoid_rewrite <- (proj2 (pro_sym' _ _)); apply pro_tensor_hom.
  - setoid_rewrite pro_sym'; apply pro_tensor_hom.
Qed.
(*
Set Printing Universes.
Set Printing All.
Program Instance prop_frame : @Frame Prop prop_proset prop_bicomplete
  := {| exponential (P Q : Prop) := P -> Q |}.
Proof.
  move=> A B C; split.
  - move=> D H1 H2; apply: D => -[] //.
  - move=> D H1; apply: D; [apply: (H1 true) | apply: (H1 false)].
Defined.
*)
Program Instance prop_cmset : ClosedMonSet Prop
  := {| internal_hom (P Q : Prop) := P -> Q |}.
Next Obligation. firstorder. Qed.

(* TODO Move these *)
Instance internal_hom_proper `{ClosedMonSet X}
  : Proper (pro_le --> pro_le ++> pro_le) (internal_hom (X:=X)).
Proof.
  move=> A A' /= D1 B B' D2; rewrite -tensor_hom.
  setoid_rewrite D1; setoid_rewrite <- D2; rewrite tensor_hom //.
Qed.
Instance internal_hom_proper' `{ClosedMonSet X}
  : Proper (pro_le ++> pro_le --> flip pro_le) (internal_hom (X:=X)).
Proof. move=> ? ? ? ? ? ? /=; by apply: internal_hom_proper. Qed.
Instance l_internal_hom_proper `{LClosedMonSet X}
  : Proper (pro_le --> pro_le ++> pro_le) (l_internal_hom (X:=X)).
Proof.
  move=> A A' /= D1 B B' D2; rewrite -l_tensor_hom.
  setoid_rewrite D1; setoid_rewrite <- D2; rewrite l_tensor_hom //.
Qed.
Instance l_internal_hom_proper' `{LClosedMonSet X}
  : Proper (pro_le ++> pro_le --> flip pro_le) (l_internal_hom (X:=X)).
Proof. move=> ? ? ? ? ? ? /=; by apply: l_internal_hom_proper. Qed.

(*
Record discrete (A : Type) := Discrete {get_discrete : A}.
Add Printing Constructor discrete.
Arguments Discrete {_}.
Arguments get_discrete {_}.
Instance discrete_proset {A} : Proset (discrete A) := {| pro_le := eq |}.
Instance discrete_functor {A} `{Proset Y} {F : discrete A -> Y} : Functor F | 3.
Proof. move=> [a1] [a2] /= -> //. Qed.
Instance get_discrete_functor `{Proset A} : Functor (@get_discrete A).
Proof. move=> [a1] [a2] /= [->] //. Qed.
*)

Instance unit_proset : Proset () := {| pro_le _ _ := True |}.
Program Instance unit_mset : MonSet () := {| memp := (); pro_tens _ _ := () |}.
Next Obligation. done. Qed.
Program Instance unit_smset : SymMonSet () := {}.
Next Obligation. done. Qed.

(* This brings Z into scope, which I tend to use as a variable name sometimes,
   so this dummy definition will prevent me from accidentally using that Z when I thought
   I was doing an implicit binder. *)
Definition Z : () := ().
Instance list_proset `{Proset X} : Proset (list X) :=
  {| pro_le := Forall2 pro_le |}.
Instance app_monoidal `{PreOrder X R}
  : Monoidal (Forall2 R) app nil.
Proof.
  constructor.
  - move=> As As' Bs Bs' D1 D2; by apply: Forall2_app.
  - done.
  - move=> As; rewrite app_nil_r //.
  - move=> As Bs Cs; rewrite app_assoc //.
Qed.
Instance list_mset `{Proset X} : MonSet (list X)
  := {| pro_tens := app |}.
Instance list_map_functor `{Proset X, Proset Y} : Functor (fmap (M:=list) (A:=X) (B:=Y)).
Proof. move=> F G D As; apply/Forall2_fmap/Forall2_impl; firstorder. Qed.
Instance list_map_functor' `{Functor X Y F} : Functor (X:=list X) (fmap F).
Proof. move=> As Bs D; apply/Forall2_fmap/Forall2_impl; [apply: D | done]. Qed.
Instance list_map_strongmon `{Proset X, Proset Y} {F : X -> Y}
  : StrongMon (fmap (M:=list) F).
Proof. constructor; constructor=> // As Bs; rewrite fmap_app //. Qed.
Instance cons_functor `{Proset X} : Functor (@cons X).
Proof. by constructor. Qed.
Instance cons_functor' `{Proset X} {A : X} : Functor (cons A).
Proof. by constructor. Qed.
Definition tens_all `{MonSet X} : list X -> X
  := foldr pro_tens memp.
Instance tens_all_functor `{MonSet X} : Functor (tens_all (X:=X)).
Proof. move=> ? ?; elim=> //= A B As Bs D _ IH; setoid_rewrite D; by setoid_rewrite IH. Qed.
Instance tens_all_strongmon `{MonSet X} : StrongMon (tens_all (X:=X)).
Proof.
  constructor; constructor=> //; elim=> /= [| A As IH] Bs.
  - rewrite {2}/pro_tens /= pro_lunit //.
  - rewrite -pro_massoc; by setoid_rewrite IH.
  - rewrite {1}/pro_tens /=; apply pro_lunit.
  - setoid_rewrite IH; rewrite pro_massoc //.
Qed.
Fixpoint tens_all' `{MonSet X} (l : list X) : X :=
  match l with
  | [] => memp
  | [A] => A
  | A :: As => A ⊗ tens_all' As
  end.
Lemma tens_all'_alt : forall `{MonSet X} {l : list X},
    tens_all' l ⟛ tens_all l.
Proof.
  move=> X ? ?; elim=> //= A [| A' As] /= IH.
  - rewrite pro_runit //.
  - rewrite IH //.
Qed.
Instance tens_all'_functor `{MonSet X} : Functor (tens_all' (X:=X)).
Proof.
  move=> *; rewrite tens_all'_alt; setoid_rewrite <- (proj2 tens_all'_alt); by apply/fmap'.
Qed.
Instance tens_all'_strongmon `{MonSet X} : StrongMon (tens_all' (X:=X)).
Proof.
  constructor; constructor=> // *.
  - rewrite 2!tens_all'_alt; setoid_rewrite <- (proj2 tens_all'_alt); apply/pres_tens.
  - rewrite tens_all'_alt; setoid_rewrite <- (proj2 tens_all'_alt); apply/pres_tens_op.
Qed.
Instance mret_functor `{Proset X} : Functor (mret (M:=list) (A:=X)).
Proof. by constructor. Qed.
Definition list_sharp {X} `{MonSet Y} (F : X -> Y) : list X -> Y
  := tens_all' ∘ fmap F.
Definition list_flat {X Y} (F : list X -> Y) : X -> Y
  := F ∘ mret.
Fact list_sharp_signature `{Proset X, MonSet Y} {F : list X -> Y} `{!Functor F}
  : TCAnd (Functor (list_sharp F)) (StrongMon (list_sharp F)).
Proof. typeclasses eauto. Qed.
Fact list_flat_signature `{Proset X, MonSet Y} {F : list X -> Y} `{!Functor F, !StrongMon F}
  : Functor (list_flat F).
Proof. typeclasses eauto. Qed.
Lemma list_free_monoid1 : forall `{Proset X, MonSet Y} {F : list X -> Y} `{!StrongMon F},
    list_sharp (list_flat F) ⟛ F.
Proof.
  move=> X ? Y ? ? F ?; apply/pw_core' => As.
  rewrite /list_sharp; setoid_rewrite tens_all'_alt.
  elim: As => /= [| A As IH].
  - rewrite /list_sharp /list_flat /=; split.
    + apply: (pres_memp (F:=F)).
    + apply: (pres_memp_op (F:=F)).
  - rewrite /list_sharp /list_flat /= -/fmap.
    change (A :: As) with (mret A ⊗ As).
    split.
    + setoid_rewrite <- pres_tens; apply bimap; firstorder.
    + setoid_rewrite pres_tens_op; apply bimap; firstorder.
Qed.
Lemma list_free_monoid2 : forall {X} `{MonSet Y} {F : X -> Y},
    list_flat (list_sharp F) ⟛ F.
Proof. split=> ? //=; apply pro_runit. Qed.


(* !!!
   IMPORTANT NOTE: Constraints for adjunctions should generally be placed BEFORE
   Functor, LaxMon, etc constraints (as far as I can tell, so far) because resolving them
   can instantiate evars that would otherwise cause resolution of those other classes
   to fail! Hence, this ordering allows more powerful inference.
   !!! *)
Class Adjoint `{Proset X, Proset Y} (F : X -> Y) (G : Y -> X)
  : Prop := {adj_unit : id ⊢ G ∘ F; adj_counit : F ∘ G ⊢ id}.
(* TODO This is probably worth putting some more careful thought into! *)
Hint Mode Adjoint ! - ! - ! - : typeclass_instances.
Hint Mode Adjoint ! - ! - - ! : typeclass_instances.
Infix "⊣" := Adjoint (no associativity, at level 70) : proset_scope.
Lemma transpose : forall `{Adjoint X Y F G, !Functor F, !Functor G}
                    {A : X} {B : Y},
    F A ⊢ B <-> A ⊢ G B.
Proof.
  move=> X Pr_X Y Pr_Y F G Adj Funct_F Funct_G A B; split=> D.
  - setoid_rewrite (adj_unit (Adjoint:=Adj) A); simpl; by apply: fmap'.
  - setoid_rewrite <- (adj_counit (Adjoint:=Adj) B); simpl; by apply: fmap'.
Qed.
Arguments transpose {_ _ _ _ _ _ Adj _ _ _ _} : rename.
Lemma transpose_sufficient : forall `{Proset X, Proset Y, !Functor F, !Functor G},
    (forall (A : X) (B : Y), F A ⊢ B <-> A ⊢ G B) -> F ⊣ G.
Proof.
  move=> X Pr_X Y Pr_Y F Funct_F G Funct_G Transpose.
  constructor=> A /=; by apply/Transpose.
Qed.

Lemma full_left_adjoint : forall `{Adjoint X Y F G, !Full F}, G ∘ F ⟛ id.
Proof.
  move=> X ? Y ? F G Adj ?; split=> A /=.
  - apply/(unfmap (F:=F))/(adj_counit (F:=F)).
  - apply/(adj_unit (F:=F)).
Qed.
Lemma full_right_adjoint : forall `{Adjoint X Y F G, !Full G}, F ∘ G ⟛ id.
Proof.
  move=> X ? Y ? F G Adj ?; split=> A /=.
  - apply/(adj_counit (F:=F)).
  - apply/(unfmap (F:=G))/(adj_unit (F:=F)).
Qed.

Instance left_adjoint_cocontinuous `{Proset X, Proset Y} {F : X -> Y} {G : Y -> X}
         `{!F ⊣ G, !Functor F, !Functor G}
  : Cocontinuous F | 2.
Proof.
  move=> R J A [C U]; split=> [r | A' C'] /=; first by apply: fmap'.
  apply/transpose/U => r; apply/(transpose (F:=F))/C'.
Qed.
Instance right_adjoint_continuous `{Proset X, Proset Y} {F : X -> Y} {G : Y -> X}
         `{!F ⊣ G, !Functor F, !Functor G}
  : Continuous G | 2.
Proof.
  move=> R J A [C U]; split=> [r | A' C'] /=; first by apply: fmap'.
  apply/(transpose (F:=F))/U => r; apply/transpose/C'.
Qed.

(* TODO Move this. *)
(*
Instance cone_proper `{Proset X} {R}
  : Proper (core pro_le ==> core pro_le ==> iff) (cone (R:=R) (X:=X)).
Proof.
  move=> A A' E_A J J' E_J.
  rewrite /cone; split.
  - setoid_rewrite (proj2 E_A); by setoid_rewrite E_J.
  - setoid_rewrite E_A; by setoid_rewrite (proj2 E_J).
Qed.
Instance cocone_proper `{Proset X} {R}
  : Proper (core pro_le ==> core pro_le ==> iff) (cocone (R:=R) (X:=X)).
Proof.
  move=> A A' E_A J J' E_J.
  rewrite /cocone; split.
  - setoid_rewrite (proj2 E_A); by setoid_rewrite (proj1 E_J).
  - setoid_rewrite E_A; by setoid_rewrite (proj2 E_J).
Qed.
*)
Lemma full_left_adjoint_glb : forall `{Adjoint Y X F G, !Functor F, !Functor G, !Full F}
                                {R} {J : R -> Y} {A},
    glb (F ∘ J) A -> glb J (G A).
Proof.
  move=> Y ? X ? F G Adj ? ? ? R J A Glb.
  unfold greatest; setoid_replace J with (G ∘ F ∘ J).
  - apply: preserve_inf Glb.
  - split=> r /=; apply (pw_core full_left_adjoint (J r)).
Qed.
Lemma full_right_adjoint_lub : forall `{Adjoint X Y F G, !Functor F, !Functor G, !Full G}
                                 {R} {J : R -> Y} {A},
    lub (G ∘ J) A -> lub J (F A).
Proof.
  move=> X ? Y ? F G Adj ? ? ? R J A Lub.
  unfold least; setoid_replace J with (F ∘ G ∘ J).
  - apply: preserve_sup Lub.
  - split=> r /=; apply (pw_core full_right_adjoint (J r)).
Qed.
(* TODO be more fine-grained *)
Definition reflective_suplattice
           `{Adjoint X Y F G, !Functor F, !Functor G, !Full G, !SupLattice X}
  : SupLattice Y
  := fun R J => {| sup := F (sup (G ∘ J));
                is_sup := full_right_adjoint_lub (is_sup (G ∘ J)) |}.
(*
Definition reflective_inflattice
           `{Adjoint X Y F G, !Functor F, !Functor G, !Full G, !SupLattice X}
  : InfLattice Y
  := @sups_sufficient Y _ (reflective_suplattice (F:=F) (G:=G)).
*)
Definition coreflective_inflattice
           `{Adjoint Y X F G, !Functor F, !Functor G, !Full F, !InfLattice X}
  : InfLattice Y
  := fun R J => {| inf := G (inf (F ∘ J));
                is_inf := full_left_adjoint_glb (is_inf (F ∘ J)) |}.

Definition universal_left_adjoint `{Proset X, Complete Y} (G : Y -> X) (A : X) : Y
  := inf (fun B : {B0 | A ⊢ G B0} => `B).
Definition universal_right_adjoint `{Complete X, Proset Y} (F : X -> Y) (B : Y) : X
  := sup (fun A : {A0 | F A0 ⊢ B} => `A).
Arguments universal_left_adjoint {_ _ _ _ _ _ _} G A /.
Arguments universal_right_adjoint {_ _ _ _ _ _ _} F B /.
Instance ula_functor `{Proset X, Complete Y} {G : Y -> X}
  : Functor (universal_left_adjoint G).
Proof.
  move=> A B D /=.
  apply/inf_right => -[B0 ?] /=; apply/(inf_lb (B0 ↾ _)); by etransitivity.
Qed.
Instance ura_functor `{Complete X, Proset Y} {F : X -> Y}
  : Functor (universal_right_adjoint F).
Proof.
  move=> A B D /=.
  apply/sup_left => -[A0 ?] /=; apply/(sup_ub (A0 ↾ _)); by etransitivity.
Qed.
(* These are not instances because we don't want them to conflict with other ones when we
   give more useful/explicit definitions. But they should be suitable for using to make
   instances very quickly! *)
Lemma universal_adjunction1 : forall `{Proset X, Complete Y}
                                {G : Y -> X} `{!Functor G, !Continuous G},
    universal_left_adjoint G ⊣ G.
Proof.
  move=> X ? Y ? ? ? ? G ? ?; constructor=> [A | B] /=.
  - case: (proj1 (preserves_inf_alt1 (F:=G) (J:=fun B : {B0 | A ⊢ G B0} => `B))) => LB U.
    apply/U => -[B0 ?] //.
  - by apply: (inf_lb (B ↾ _)).
Qed.
Lemma universal_adjunction2 : forall `{Complete X, Proset Y}
                                {F : X -> Y} `{!Functor F, !Cocontinuous F},
    F ⊣ universal_right_adjoint F.
Proof.
  move=> X ? ? ? ? Y ? F ? ?; constructor=> [A | B] /=.
  - by apply: (sup_ub (A ↾ _)).
  - case: (proj1 (preserves_sup_alt1 (F:=F) (J:=fun A : {A0 | F A0 ⊢ B} => `A))) => UB U.
    apply/U => -[B0 ?] //.
Qed.

Instance compose_adjoint `{Proset X, Proset Y, Proset Z'}
         {F : Y -> Z'} {G : Z' -> Y} {F' : X -> Y} {G' : Y -> X}
         `{!F ⊣ G, F' ⊣ G', !Functor F, !Functor G, !Functor F', !Functor G'}
  : F ∘ F' ⊣ G' ∘ G.
Proof. apply/transpose_sufficient => * /=; rewrite 2!transpose //. Qed.
Instance postcomp_adjoint `{Proset X, Proset X'} {Y}
         {F : X -> X'} {G : X' -> X}
         `{!F ⊣ G, !Functor F, !Functor G}
  : Adjoint (X:=Y -> X) (F ∘.) (G ∘.).
Proof. firstorder. Qed.
(* TODO fixme
Instance const_inf_adjoint `{Complete X} {Y} : @const X Y ⊣ inf.
Proof.
  constructor=> [A | P y] /=.
  - apply: inf_right => y; by simpl.
  - apply/lim_left.
Qed.
Instance colim_const_adjoint `{Complete X} {Y} : colim ⊣ @const X Y.
Proof.
  constructor=> [P y | A] /=.
  - apply/colim_right.
  - apply: colim_left => y; by simpl.
Qed.
*)

Lemma oplax_adjoint_lax : forall `{MonSet X, MonSet Y} {F : X -> Y} {G : Y -> X}
                            `{!F ⊣ G, !Functor F, !Functor G},
    OplaxMon F <-> LaxMon G.
Proof.
  move=> X Pr_X MS_X Y Pr_Y MS_Y F G Adj Funct_F Funct_G.
  split=> [Oplax | Lax]; constructor=> [| A B]; apply/(transpose (Adj:=Adj)).
  - apply: pres_memp_op.
  - setoid_rewrite pres_tens_op; apply bimap; apply/(adj_counit (Adjoint:=Adj)).
  - apply/pres_memp.
  - setoid_rewrite <- pres_tens; apply bimap; apply/(adj_unit (Adjoint:=Adj)).
Qed.
Corollary adjoint_equivalence_strong : forall `{MonSet X, MonSet Y} {F : X -> Y} {G : Y -> X}
                                         `{!F ⊣ G, !G ⊣ F, !Functor F, !Functor G},
    StrongMon F <-> StrongMon G.
Proof. split; constructor; try apply/oplax_adjoint_lax. Qed.
(* The next one may only work because we are in prosets---I should go check. *)
Corollary triple_strong : forall `{MonSet X, MonSet Y} {F : X -> Y} {G : Y -> X} {H : X -> Y}
                            `{!F ⊣ G, !G ⊣ H, !Functor F, !Functor G, !Functor H},
    TCAnd (OplaxMon F) (LaxMon H) <-> StrongMon G.
Proof. split=> [[Oplax Lax] | Strong]; split; apply/oplax_adjoint_lax. Qed.

Definition r_meet `{Proset X, !BinMeets X} (B : X) : X -> X := fun A => A ⩕ B.
Definition r_tensor `{MonSet X} (B : X) : X -> X := fun A => A ⊗ B.
Arguments r_meet {_ _ _} _ _ /.
Arguments r_tensor {_ _ _} _ _ /.
Instance meet_functor `{Proset X, !BinMeets X} : Functor (meet (X:=X)).
Proof. move=> A A' D B; apply/meet_right; [apply/meet_left1/D | apply/meet_proj2]. Qed.
Instance meet_functor' `{Proset X, !BinMeets X} {A : X} : Functor (meet A).
Proof. move=> B B' D; apply/meet_right; [apply/meet_proj1 | apply/meet_left2/D]. Qed.
Instance join_functor `{Proset X, !BinJoins X} : Functor (join (X:=X)).
Proof. move=> A A' D B; apply/join_left; [apply/join_right1/D | apply/join_inj2]. Qed.
Instance join_functor' `{Proset X, !BinJoins X} {A : X} : Functor (join A).
Proof. move=> B B' D; apply/join_left; [apply/join_inj1 | apply/join_right2/D]. Qed.
Instance tensor_functor `{MonSet X} : Functor (pro_tens (X:=X)).
Proof. move=> A A' D1 B; by apply: bimap. Qed.
Instance tensor_functor' `{MonSet X} {A : X} : Functor (pro_tens A).
Proof. move=> B B' D /=; by apply: bimap. Qed.
Instance r_meet_functor `{Proset X, !BinMeets X} {B : X} : Functor (r_meet B).
Proof. move=> A A' D /=; by apply: meet_functor. Qed.
Instance r_tensor_functor `{MonSet X} {B : X} : Functor (r_tensor B).
Proof. move=> A A' D /=; by apply: bimap. Qed.
Instance exponential_functor `{Exponents X} {A : X} : Functor (exponential A).
Proof.
  move=> B B' D.
  apply/meet_exponential; setoid_rewrite <- D; by apply/meet_exponential.
Qed.
Instance internal_hom_functor `{ClosedMonSet X} {A : X} : Functor (internal_hom A).
Proof.
  move=> B B' D.
  apply tensor_hom; setoid_rewrite <- D; by apply tensor_hom.
Qed.
Instance l_internal_hom_functor `{LClosedMonSet X} {A : X} : Functor (l_internal_hom A).
Proof.
  move=> B B' D.
  apply l_tensor_hom; setoid_rewrite <- D; by apply l_tensor_hom.
Qed.
Instance r_meet_exponential_adjoint `{Exponents X} {A : X}
  : r_meet A ⊣ exponential A.
Proof. apply transpose_sufficient => * /=; apply/meet_exponential. Qed.
Instance r_tensor_internal_hom_adjoint `{ClosedMonSet X} {A : X}
  : r_tensor A ⊣ internal_hom A.
Proof. apply transpose_sufficient => * /=; apply/tensor_hom. Qed.
Instance tensor_l_internal_hom_adjoint `{LClosedMonSet X} {A : X}
  : pro_tens A ⊣ l_internal_hom A.
Proof. apply transpose_sufficient => * /=; apply/l_tensor_hom. Qed.

(* TODO Fix these *)
(*
Definition r_meet_exponential_adjoint_sufficient `{!BinMeets X}
           (exponential' : X -> X -> X) `{forall A, Functor (exponential' A)}
           (Adj : forall (A : X), r_product A ⊣ exponential' A) : Frame X
  := {| exponential := exponential';
        product_exponential A B C := transpose (Adj:=Adj B) |}.
Definition r_product_cocontinuous_sufficient `{Complete X}
           `(Cocont : forall A, Cocontinuous (r_product A))
  : Frame X
  := {| exponential A := universal_right_adjoint (r_product A);
        product_exponential A B C :=
          transpose (Adj:=universal_adjunction2 (F:=r_product B)) |}.
Definition r_tensor_internal_hom_adjoint_sufficient `{MonSet X}
           (internal_hom' : X -> X -> X) `{forall A, Functor (internal_hom' A)}
           (Adj : forall (A : X), r_tensor A ⊣ internal_hom' A) : ClosedMonSet X
  := {| internal_hom := internal_hom'; pro_tensor_hom A B C := transpose (Adj:=Adj B) |}.
Definition r_tensor_cocontinuous_sufficient `{Complete X, !MonSet X}
           `(Cocont : forall A, Cocontinuous (r_tensor A))
  : ClosedMonSet X
  := {| internal_hom A := universal_right_adjoint (r_tensor A);
        pro_tensor_hom A B C :=
          transpose (Adj:=universal_adjunction2 (F:=r_tensor B)) |}.
Definition tensor_l_internal_hom_adjoint_sufficient `{MonSet X}
           (l_internal_hom' : X -> X -> X) `{forall A, Functor (l_internal_hom' A)}
           (Adj : forall (A : X), pro_tens A ⊣ l_internal_hom' A) : LClosedMonSet X
  := {| l_internal_hom := l_internal_hom'; pro_l_tensor_hom A B C := transpose |}.
Definition tensor_cocontinuous_sufficient `{Complete X, !MonSet X}
           `(Cocont : forall A, Cocontinuous (pro_tens A))
  : LClosedMonSet X
  := {| l_internal_hom A := universal_right_adjoint (pro_tens A);
        pro_l_tensor_hom A B C :=
          transpose (Adj:=universal_adjunction2 (F:=pro_tens B)) |}.
*)

Lemma left_adjoint_unique : forall `{Proset X, Proset Y} {F F' : X -> Y} {G : Y -> X}
                              `{!F ⊣ G, !Functor F, !Functor F', !Functor G},
    F' ⊣ G -> F' ⟛ F.
Proof.
  move=> X Pr_X Y Pr_Y F F' G Adj1 Funct_F Funct_F' Funct_G Adj2.
  enough (H : forall (F F' : X -> Y) `{!Functor F, !Functor F'}, F ⊣ G -> F' ⊣ G -> F ⊢ F')
    by by split; apply H.
  move=> {F F' Adj1 Adj2 Funct_F Funct_F'} F F' ? ? Adj1 Adj2 A.
  apply/(transpose (Adj:=Adj1))/(adj_unit (Adjoint:=Adj2)).
Qed.
Lemma right_adjoint_unique : forall `{Proset X, Proset Y} {F : X -> Y} {G G' : Y -> X}
                               `{!F ⊣ G, !Functor F, !Functor G, !Functor G'},
    F ⊣ G' -> G' ⟛ G.
Proof.
  move=> X Pr_X Y Pr_Y F G G' Adj1 Funct_F Funct_G Funct_G' Adj2.
  enough (H : forall (G G' : Y -> X) `{!Functor G, !Functor G'}, F ⊣ G -> F ⊣ G' -> G ⊢ G')
    by by split; apply H.
  move=> {G G' Adj1 Adj2 Funct_G Funct_G'} G G' ? ? Adj1 Adj2 A.
  apply/(transpose (Adj:=Adj2))/(adj_counit (Adjoint:=Adj1)).
Qed.

Record Adjunction {X Y : Type} `{Proset X, Proset Y} : Type :=
  {LeftAdjoint : X -> Y; RightAdjoint : Y -> X;
   LAdj_Functor : Functor LeftAdjoint; RAdj_Functor : Functor RightAdjoint;
   Adjunction_adjoint : LeftAdjoint ⊣ RightAdjoint}.
Arguments Adjunction _ _ {_ _}.
Existing Instances LAdj_Functor RAdj_Functor Adjunction_adjoint | 10.
Definition adj_compose {Z} `{Proset X, Proset Y, Proset Z}
        (Adj1 : Adjunction Y Z) (Adj2 : Adjunction X Y) : Adjunction X Z
  := {| LeftAdjoint := LeftAdjoint Adj1 ∘ LeftAdjoint Adj2;
        RightAdjoint := RightAdjoint Adj2 ∘ RightAdjoint Adj1 |}.


Definition Hom (X Y : Type) `{Proset X, Proset Y} : Type :=
  sig (Functor (X:=X) (Y:=Y)).
Definition ap_Hom (X Y : Type) `{Proset X, Proset Y} : Hom X Y -> X -> Y
  := sval.
Arguments ap_Hom {_ _ _ _} !_.
Coercion ap_Hom : Hom >-> Funclass.
Instance ap_Hom_functor `{Proset X, Proset Y} : Functor (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> [F ?] [G ?] //. Qed.
Instance ap_Hom_proper `{Proset X, Proset Y}
  : Proper (pro_le ++> pro_le ++> pro_le) (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> [? ?] [? ?] /= D ? ? D'; by setoid_rewrite D'. Qed.
Instance ap_Hom_proper' `{Proset X, Proset Y}
  : Proper (pro_le --> pro_le --> flip pro_le) (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> [? ?] [? ?] /= D ? ? D' /=; by setoid_rewrite D'. Qed.
Instance functorial `{Proset X, Proset Y} (F : Hom X Y) : Functor F := proj2_sig _.
Definition hom_map : forall `{Proset X, Proset Y} {F F' : Hom X Y} {A},
    F ⊢ F' -> F A ⊢ F' A.
Proof. intros *; apply. Qed.
Definition in_Hom `{Proset X, Proset Y} (F : X -> Y) `{!Functor F} : Hom X Y :=
  F packed_with Functor.
Arguments in_Hom {_ _ _ _} F {_} /.
Lemma ap_Hom_in_Hom : forall `{Functor X Y F}, ap_Hom (in_Hom F) = F.
Proof. done. Qed.
(* WARNING: This is brittle. It won't work in cases where the implicit arguments are filled
            differently from how Coq has inferred them here. *)
Lemma in_Hom_ap_Hom : forall `{Proset X, Proset Y} {F : Hom X Y}, in_Hom (ap_Hom F) = F.
Proof. move=> *; rewrite /= -sig_eta //. Qed.
Lemma Hom_core : forall `{Proset X, Proset Y} {F G : Hom X Y}, (forall A, F A ⟛ G A) <-> F ⟛ G.
Proof. compute; firstorder. Qed.
Definition Hom_id `{Proset X} : Hom X X := in_Hom id.
Definition Hom_compose `{Proset X, Proset Y, Proset Z'}
           (F : Hom Y Z') (G : Hom X Y) : Hom X Z' := in_Hom (F ∘ G).
Infix "○" := Hom_compose (at level 40) : proset_scope.
Notation "( f ○.)" := (Hom_compose f) (only parsing) : proset_scope.
Notation "(.○ f )" := (fun g => Hom_compose g f) (only parsing) : proset_scope.
Instance Hom_compose_functor1 {Z} `{Proset X, Proset Y, Proset Z} {F : Hom Y Z}
  : Functor (X:=Hom X Y) (F ○.).
Proof. move=> f g D x /=; by setoid_rewrite D. Qed.
Instance Hom_compose_functor2 {Z} `{Proset X, Proset Y, Proset Z} {G : Hom X Y}
  : Functor (X:=Hom Y Z) (.○ G).
Proof. move=> f g D x /=; by setoid_rewrite D. Qed.
Definition Hom_id_lident : forall `{Proset X, Proset Y} {F : Hom X Y},
    Hom_id ○ F ⟛ F.
Proof. by compute. Qed.
Definition Hom_id_rident : forall `{Proset X, Proset Y} {F : Hom X Y},
    F ○ Hom_id ⟛ F.
Proof. by compute. Qed.
Definition Hom_compose_assoc : forall `{Proset X, Proset Y, Proset Z', Proset W}
                                 {F : Hom Z' W} {G : Hom Y Z'} {H : Hom X Y},
    F ○ (G ○ H) ⟛ (F ○ G) ○ H.
Proof. by compute. Qed.

Program Instance Hom_bicomplete `{Proset X, Complete Y} : Complete (Hom X Y)
  := {| lim R J := lim (ap_Hom ∘ J) ↾ _; colim R J := colim (ap_Hom ∘ J) ↾ _ |}.
Next Obligation.
  move=> X Pr_X Y Pr_Y Comp R J A B D /=.
  apply: fmap' => r; by apply: functorial.
Qed.
Next Obligation.
  move=> X Pr_X Y Pr_Y Comp R J; rewrite /lim /=; split=> [r | A' Cone] y /=.
  - apply: lim_left.
  - apply: lim_right => r; apply: Cone.
Qed.
Next Obligation.
  move=> X Pr_X Y Pr_Y Comp R J A B D /=.
  apply: fmap' => r; by apply: functorial.
Qed.
Next Obligation.
  move=> X Pr_X Y Pr_Y Comp R J; rewrite /colim /=; split=> [r | A' Cocone] y /=.
  - rewrite -/ap_Hom; by setoid_rewrite <- colim_right.
  - apply: colim_left => r; apply: Cocone.
Qed.
Instance ap_Hom_bicomplete_continuous `{Proset X, Complete Y}
  : Continuous (ap_Hom (X:=X) (Y:=Y)).
Proof. by apply/distrib_lim_sufficient. Qed.
Instance ap_Hom_bicomplete_cocontinuous `{Proset X, Complete Y}
  : Cocontinuous (ap_Hom (X:=X) (Y:=Y)).
Proof. by apply/distrib_colim_sufficient. Qed.
(* Hmm. *)
Instance flip_functoriality {R} `{Proset Y, Proset X}
         {F : R -> Y -> X} `{!forall r, Functor (F r)}
  : Functor (flip F).
Proof. firstorder. Qed.
Lemma Hom_lim : forall `{Proset Y, Complete X} {R} (J : R -> Hom Y X),
    lim J ⟛ in_Hom (lim ∘ flip J).
Proof. by compute. Qed.
Lemma Hom_colim : forall `{Proset Y, Complete X} {R} (J : R -> Hom Y X),
    colim J ⟛ in_Hom (colim ∘ flip J).
Proof. by compute. Qed.
Instance Hom_compose_continuous `{Proset Y, Proset Y', Complete X} {F : Hom Y' Y}
  : Continuous (X:=Hom Y X) (.○ F).
Proof. apply/distrib_lim_sufficient; by simpl. Qed.
Instance Hom_compose_cocontinuous `{Proset Y, Proset Y', Complete X} {F : Hom Y' Y}
  : Cocontinuous (X:=Hom Y X) (.○ F).
Proof. apply/distrib_colim_sufficient; by simpl. Qed.

Definition Hom_eval_at `{Proset X, Proset Y} (y : Y) : Hom Y X -> X := fun F => F y.
Arguments Hom_eval_at {_ _ _ _} _ _ /.
Instance subst_functor3 `{Proset X, Proset Y} {y : Y}
  : Functor (X:=Hom Y X) (Hom_eval_at y).
Proof. compute; firstorder. Qed.
Instance subst_continuous3 `{Proset Y, Complete X} {y : Y}
  : Continuous (X:=Hom Y X) (Hom_eval_at y).
Proof. by apply/distrib_lim_sufficient. Qed.
Instance subst_cocontinuous3 `{Proset Y, Complete X} {y : Y}
  : Cocontinuous (X:=Y -> X) (eval_at y).
Proof. by apply/distrib_colim_sufficient. Qed.

Definition local_lan `{Proset X, Proset X', Proset Y}
           (p : X -> X') (F : X -> Y) (F' : X' -> Y) : Prop
  := forall (G : X' -> Y), Functor G -> F' ⊢ G <-> F ⊢ G ∘ p.
Definition local_ran `{Proset X, Proset X', Proset Y}
           (p : X -> X') (F : X -> Y) (F' : X' -> Y) : Prop
  := forall (G : X' -> Y), Functor G -> G ⊢ F' <-> G ∘ p ⊢ F.
Definition global_lan `{Proset X, Proset X', Proset Y}
           (p : X -> X') `{!Functor p} (lan_p : Hom X Y -> Hom X' Y) : Prop
  := lan_p ⊣ (.○ in_Hom p).
Definition global_ran `{Proset X, Proset X', Proset Y}
           (p : X -> X') `{!Functor p} (ran_p : Hom X Y -> Hom X' Y) : Prop
  := (.○ in_Hom p) ⊣ ran_p.
Lemma local_global_lan : forall `{Functor X X' p, Proset Y} {lan_p} `{!Functor lan_p},
    global_lan p lan_p <-> forall F : Hom X Y, local_lan p F (lan_p F).
Proof.
  move=> X ? X' ? p ? Y ? lan_p ?; split.
  - move=> Glob F G ?.
    change (ap_Hom (lan_p F) ⊢ _) with (lan_p F ⊢ in_Hom G).
    rewrite (transpose (Adj:=Glob)) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (lan_p F ⊢ G) with (ap_Hom (lan_p F) ⊢ ap_Hom G).
    rewrite Loc //=.
Qed.
Lemma local_global_ran : forall `{Functor X X' p, Proset Y} {ran_p} `{!Functor ran_p},
    global_ran p ran_p <-> forall F : Hom X Y, local_ran p F (ran_p F).
Proof.
  move=> X ? X' ? p ? Y ? ran_p ?; split.
  - move=> Glob F G ?.
    change (_ ⊢ ap_Hom (ran_p F)) with (in_Hom G ⊢ ran_p F).
    rewrite -(transpose (Adj:=Glob)) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (F ⊢ ran_p G) with (ap_Hom F ⊢ ap_Hom (ran_p G)).
    rewrite Loc //=.
Qed.

Definition local_lift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) (F : X -> Y) (F' : X -> Y') : Prop
  := forall (G : X -> Y'), Functor G -> F' ⊢ G <-> F ⊢ p ∘ G.
Definition local_rift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) (F : X -> Y) (F' : X -> Y') : Prop
  := forall (G : X -> Y'), Functor G -> G ⊢ F' <-> p ∘ G ⊢ F.
Definition global_lift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) `{!Functor p} (lift_p : Hom X Y -> Hom X Y') : Prop
  := lift_p ⊣ (in_Hom p ○.).
Definition global_rift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) `{!Functor p} (rift_p : Hom X Y -> Hom X Y') : Prop
  := (in_Hom p ○.) ⊣ rift_p.
Lemma local_global_lift : forall `{Proset X, Functor Y' Y p} {lift_p} `{!Functor lift_p},
    global_lift p lift_p <-> forall F : Hom X Y, local_lift p F (lift_p F).
Proof.
  move=> X ? X' ? p ? Y ? lift_p ?; split.
  - move=> Glob F G ?.
    change (ap_Hom (lift_p F) ⊢ _) with (lift_p F ⊢ in_Hom G).
    rewrite (transpose (Adj:=Glob)) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (lift_p F ⊢ G) with (ap_Hom (lift_p F) ⊢ ap_Hom G).
    rewrite Loc //=.
Qed.
Lemma local_global_rift : forall `{Proset X, Functor Y' Y p} {rift_p} `{!Functor rift_p},
    global_rift p rift_p <-> forall F : Hom X Y, local_rift p F (rift_p F).
Proof.
  move=> X ? X' ? p ? Y ? rift_p ?; split.
  - move=> Glob F G ?.
    change (_ ⊢ ap_Hom (rift_p F)) with (in_Hom G ⊢ rift_p F).
    rewrite -(transpose (Adj:=Glob)) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (F ⊢ rift_p G) with (ap_Hom F ⊢ ap_Hom (rift_p G)).
    rewrite Loc //=.
Qed.

Instance precomp_adjoint `{Proset X, Proset X', Proset Y}
         {p : Hom X X'} {p' : Hom X' X} `{!p ⊣ p'}
  : ((.○ p') : Hom X Y -> _) ⊣ (.○ p).
Proof.
  constructor=> f y /=.
  - apply/fmap'/adj_unit.
  - apply/fmap'/adj_counit.
Qed.
Instance postcomp_adjoint' `{Proset X, Proset Y', Proset Y}
         {p : Hom Y' Y} {p' : Hom Y Y'} `{!p ⊣ p'}
  : ((p ○.) : Hom X Y' -> _) ⊣ (p' ○.).
Proof.
  constructor=> f y /=.
  - apply/adj_unit.
  - apply/adj_counit.
Qed.

Program Definition universal_lan {X} `{Proset X', Complete Y}
        (p : X -> X') (F : X -> Y) : Hom X' Y
  := fun x' => colim (fun y : {y0 | p y0 ⊢ x'} => F (`y)).
Next Obligation.
  move=> X X' ? Y ? ? p F A B D.
  apply/colim_left => -[y D'] /=.
  apply/(colim_right _ (y ↾ _)).
    by etransitivity.
Qed.
Arguments universal_lan {_ _ _ _ _ _} p F /.
Program Definition universal_ran {X} `{Proset X', Complete Y}
        (p : X -> X') (F : X -> Y) : Hom X' Y
  := fun x' => lim (fun y : {y0 | x' ⊢ p y0} => F (`y)).
Next Obligation.
  move=> X X' ? Y ? ? p F A B D.
  apply/lim_right => -[y D'] /=.
  apply/(lim_left _ (y ↾ _)).
    by etransitivity.
Qed.
Arguments universal_ran {_ _ _ _ _ _} p F /.
Lemma universal_lan_global_lan : forall `{Functor X X' p, Complete Y},
    global_lan (Y:=Y) p (universal_lan p).
Proof.
  move=> X ? X' ? p ? Y ? ?; constructor=> f x /=.
  - by apply/(colim_right _ (x ↾ _)).
  - apply/colim_left => -[y D] /=.
      by setoid_rewrite D.
Qed.
Lemma universal_ran_global_ran : forall `{Functor X X' p, Complete Y},
    global_ran (Y:=Y) p (universal_ran p).
Proof.
  move=> X ? X' ? p ? Y ? ?; constructor=> f x /=.
  - apply/lim_right => -[y D] /=.
      by setoid_rewrite D.
  - by apply/(lim_left _ (x ↾ _)).
Qed.


Class Quantale (X : Type)
      `{!Proset X, !Complete X, !MonSet X, !ClosedMonSet X, !LClosedMonSet X}.
Hint Mode Quantale ! - - - - - : typeclass_instances.
Instance quantale_def
         `{Proset X, !Complete X, !MonSet X, !ClosedMonSet X, !LClosedMonSet X}
  : Quantale X := {}.

Instance prop_quantale : Quantale Prop := {}.

Definition Endo (X : Type) `{Proset X} := Hom X X.
Identity Coercion endo_to_hom : Endo >-> Hom.
Instance compose_monoidal `{Proset X} :
  Monoidal (pro_le (X:=Endo X)) Hom_compose Hom_id.
Proof.
  constructor.
  - move=> F F' G G' D1 D2 A /=.
    setoid_rewrite D1; by setoid_rewrite D2.
  - by setoid_rewrite Hom_id_lident.
  - by setoid_rewrite Hom_id_rident.
  - by setoid_rewrite Hom_compose_assoc.
Qed.
Instance endo_mset `{Proset X} : MonSet (Endo X)
  := {| pro_tens := Hom_compose |}.
Program Instance endo_cmset `{Complete X} : ClosedMonSet (Endo X)
  := r_tensor_internal_hom_adjoint_sufficient (fun (p F : Endo X) => universal_ran p F) _.
Next Obligation. move=> *; apply: universal_ran_global_ran. Qed.

(* TODO Put this in the right place. *)
Program Instance pw_frame {Y} `{Frame X} : Frame (Y -> X)
  := {| exponential F G A := F A ⟿ G A |}.
Next Obligation.
  move=> Y X ? ? ? F G H; split.
  - move=> Uncurried A.
    rewrite -product_exponential -(distrib_product (F:=eval_at A)); apply/Uncurried.
  - move=> Curried A.
    setoid_rewrite (distrib_product (F:=eval_at A)); rewrite product_exponential.
    apply/Curried.
Qed.
Program Instance Hom_frame `{Proset Y, Frame X} : Frame (Hom Y X)
  := {| exponential F G A := lim (fun B : {B0 | A ⊢ B0} => F (` B) ⟿ G (` B)) |}.
Next Obligation.
  move=> Y ? X ? ? ? F G A B D.
  apply/lim_right => -[B' D'] /=.
  apply/(lim_left _ (_ ↾ _)); by etransitivity.
Qed.
Next Obligation.
  move=> Y ? X ? ? ? F G H; split.
  - move=> Uncurried A /=; apply/lim_right => -[B D] /=; setoid_rewrite D.
    rewrite -product_exponential -(distrib_product (F:=Hom_eval_at B)); apply/Uncurried.
  - move=> /= Curried A; specialize (Curried A); simpl in Curried.
    setoid_rewrite (lim_left _ (A ↾ reflexivity _)) in Curried; simpl in Curried.
    setoid_rewrite (distrib_product (F:=Hom_eval_at A)); by rewrite product_exponential.
Qed.
Instance pw_closed_monoidal {Y} `{ClosedMonoidal X R T H} :
  ClosedMonoidal (pointwise_relation Y R) (fun f g y => T (f y) (g y))
                 (fun f g y => H (f y) (g y)).
Proof. firstorder. Qed.
Instance pw_l_closed_monoidal {Y} `{LClosedMonoidal X R T H} :
  LClosedMonoidal (pointwise_relation Y R) (fun f g y => T (f y) (g y))
                  (fun f g y => H (f y) (g y)).
Proof. firstorder. Qed.
Instance pw_cmset {Y} `{ClosedMonSet X} : ClosedMonSet (Y -> X) :=
  {| internal_hom := fun f g y => internal_hom (f y) (g y) |}.
Instance pw_lcmset {Y} `{LClosedMonSet X} : LClosedMonSet (Y -> X) :=
  {| l_internal_hom := fun f g y => l_internal_hom (f y) (g y) |}.
Instance pw_quantale `{Quantale X} {Y} : Quantale (Y -> X) := {}.

Lemma quantale_tensor_prop :
  forall `{Quantale X} {P Q}, embed_prop (X:=X) P ⊗ embed_prop Q ⟛ embed_prop (P ∧ Q).
Proof.
  move=> X Pr Comp MS CMS LCMS Quant P Q; split.
  - rewrite tensor_hom; apply: embed_prop_left => H1; rewrite -tensor_hom.
    rewrite l_tensor_hom; apply: embed_prop_left => H2; rewrite -l_tensor_hom.
      by apply: embed_prop_right.
  - apply: embed_prop_left => -[H1 H2].
    transitivity (⊤ ⊗ ⊤ : X). (* wat *)
    + setoid_rewrite <- terminal_right at 2; by setoid_rewrite <- (proj2 (pro_lunit _)).
    + apply: bimap; by apply: embed_prop_right.
Qed.
(* TODO Put these in the right place. *)
Lemma modus_ponens : forall `{Frame X} {A B : X},
    (A ⟿ B) × A ⊢ B.
Proof. move=> X ? ? ? A B; by rewrite product_exponential. Qed.
Lemma l_modus_ponens : forall `{Frame X} {A B : X},
    A × (A ⟿ B) ⊢ B.
Proof.
  move=> X ? ? ? A B.
  setoid_rewrite (cartesian_sym A); rewrite product_exponential //.
Qed.
Instance embed_prop_functor `{Complete X} : Functor (embed_prop (X:=X)).
Proof. move=> P Q D; apply: embed_prop_left => ?; by apply/embed_prop_right/D. Qed.
Lemma mon_modus_ponens : forall `{ClosedMonSet X} {A B : X},
    (A ⊸ B) ⊗ A ⊢ B.
Proof. move=> X Pr MS CM A B; by rewrite tensor_hom. Qed.
Lemma l_mon_modus_ponens : forall `{LClosedMonSet X} {A B : X},
    A ⊗ (A ⊸̂ B) ⊢ B.
Proof. move=> X Pr MS CM A B; by rewrite l_tensor_hom. Qed.
Lemma prop_loop :
  forall `{Frame X} {P Q : X} {R : Prop},
    (P ⊢ embed_prop R) -> (R -> P ⊢ Q) -> P ⊢ Q.
Proof.
  move=> X Pr Comp CCl P Q R D1 D2.
  setoid_rewrite (product_right D1 (reflexivity _)).
  apply/product_exponential/embed_prop_left => H.
  apply/product_exponential; setoid_rewrite product_left2; by apply: D2.
Qed.

Definition mon_embed_prop `{MonSet X, !Complete X} (P : Prop) : X :=
  colim (fun H : P => memp).
Arguments mon_embed_prop : simpl never.
Lemma mon_embed_prop_left : forall `{MonSet X, !Complete X} {P : Prop} {Q : X},
    (P -> memp ⊢ Q) -> mon_embed_prop P ⊢ Q.
Proof. move=> X Pr Comp P Q D; by apply: colim_left. Qed.
Lemma mon_embed_prop_right : forall `{MonSet X, !Complete X} {P : X} {Q : Prop},
    Q -> P ⊢ memp -> P ⊢ mon_embed_prop Q.
Proof. move=> X Pr MS Comp P Q H D; by setoid_rewrite <- colim_right. Qed.
Instance mon_embed_prop_functor `{MonSet X, !Complete X}
  : Functor (mon_embed_prop (X:=X)).
Proof.
  move=> P Q D.
  apply: mon_embed_prop_left => ?; apply/mon_embed_prop_right.
  - by apply: D.
  - reflexivity.
Qed.

Lemma mon_tensor_prop :
  forall `{ClosedMonSet X, !Complete X} {P Q},
    mon_embed_prop (X:=X) P ⊗ mon_embed_prop Q ⟛ mon_embed_prop (P ∧ Q).
Proof.
  move=> X Pr MS CMS Comp P Q; split.
  - rewrite tensor_hom; apply: mon_embed_prop_left => H1; rewrite -tensor_hom pro_lunit.
      by apply: fmap'.
  - apply: mon_embed_prop_left => -[H1 H2].
    rewrite -(pro_runit memp); apply: bimap; by apply: mon_embed_prop_right.
Qed.

Lemma mon_prop_loop :
  forall `{ClosedMonSet X, !Complete X} {P Q R : X} {S : Prop},
    (P ⊢ mon_embed_prop S) -> (S -> Q ⊢ R) -> P ⊗ Q ⊢ R.
Proof.
  move=> X Pr MS CM Comp P Q R S D1 D2.
  setoid_rewrite D1; apply/tensor_hom/mon_embed_prop_left => H.
  apply/tensor_hom; rewrite pro_lunit; by apply: D2.
Qed.
Lemma l_mon_prop_loop :
  forall `{LClosedMonSet X, !Complete X} {P Q R : X} {S : Prop},
    (Q ⊢ mon_embed_prop S) -> (S -> P ⊢ R) -> P ⊗ Q ⊢ R.
Proof.
  move=> X Pr MS CM Comp P Q R S D1 D2.
  setoid_rewrite D1; apply/l_tensor_hom/mon_embed_prop_left => H.
  apply/l_tensor_hom; rewrite pro_runit; by apply: D2.
Qed.

(* TODO Move this *)
Instance const_functor' `{Proset X, Proset Y} {B : Y} : Functor (@const Y X B).
Proof. move=> A A' D //=. Qed.


Class Monoid `{MonSet X} (M : X) :=
  {eta : memp ⊢ M; mu : M ⊗ M ⊢ M}.
Hint Mode Monoid ! - - ! : typeclass_instances.
Class Comonoid `{MonSet X} (W : X) :=
  {epsilon : W ⊢ memp; delta : W ⊢ W ⊗ W}.
Hint Mode Comonoid ! - - ! : typeclass_instances.

Instance lax_pres_monoid `{LaxMon X Y F, !Functor F} {M : X} `{!Monoid M}
  : Monoid (F M) | 2.
Proof.
  constructor.
  - setoid_rewrite (pres_memp (F:=F)); apply/fmap'/eta.
  - setoid_rewrite pres_tens; apply/fmap'/mu.
Qed.
Instance oplax_pres_comonoid `{OplaxMon X Y F, !Functor F} {W : X} `{!Comonoid W}
  : Comonoid (F W) | 2.
Proof.
  constructor.
  - setoid_rewrite <- (pres_memp_op (F:=F)); apply/fmap'/epsilon.
  - setoid_rewrite <- pres_tens_op; apply/fmap'/delta.
Qed.

(* TODO MonClosed for {,co}kleisli and {,co}EM *)
Class Monad `{Proset X} (M : X -> X) `{!Functor M} :=
  {ret : forall A, A ⊢ M A;
   join : forall {A}, M (M A) ⊢ M A}.
Hint Mode Monad ! - ! - : typeclass_instances.
(* TODO Is it worth defining this (and maybe other concepts later too)
        by duality instead? *)
Class Comonad `{Proset X} (W : X -> X) `{!Functor W} :=
  {extract : forall A, W A ⊢ A;
   duplicate : forall {A}, W A ⊢ W (W A)}.
Hint Mode Comonad ! - ! - : typeclass_instances.
Lemma bind : forall `{Monad X M} {P Q},
    P ⊢ M Q -> M P ⊢ M Q.
Proof. move=> *; setoid_rewrite <- join at 2; by apply fmap'. Qed.
Lemma extend : forall `{Comonad X W} {P Q},
    W P ⊢ Q -> W P ⊢ W Q.
Proof. move=> *; setoid_rewrite duplicate at 1; by apply fmap'. Qed.

Lemma monad_monoid : forall `{Proset X} {M : X -> X} `{!Functor M},
    Monad M <-> Monoid (in_Hom M).
Proof.
  move=> X ? M ?; split=> ?; constructor.
  - apply: ret.
  - move=> ? /=; apply: join.
  - apply: (eta (M:=in_Hom M)).
  - apply: (mu (M:=in_Hom M)).
Qed.
Lemma comonad_comonoid : forall `{Proset X} {W : X -> X} `{!Functor W},
    Comonad W <-> Comonoid (in_Hom W).
Proof.
  move=> X ? W ?; split=> ?; constructor.
  - apply: extract.
  - move=> ? /=; apply: duplicate.
  - apply: (epsilon (W:=in_Hom W)).
  - apply: (delta (W:=in_Hom W)).
Qed.
Instance act_monad `{MonSet E, Proset X} {L : E -> Endo X} `{!LaxMon L, !Functor L}
         {M : E} `{!Monoid M}
  : Monad (L M).
Proof. apply monad_monoid; rewrite in_Hom_ap_Hom; typeclasses eauto. Qed.
Instance act_comonad `{MonSet E, Proset X} {R : E -> Endo X} `{!OplaxMon R, !Functor R}
         {W : E} `{!Comonoid W}
  : Comonad (R W).
Proof. apply comonad_comonoid; rewrite in_Hom_ap_Hom; typeclasses eauto. Qed.

Instance adjunction_monad `{Adjoint X Y F G, !Functor F, !Functor G} : Monad (G ∘ F)
  := {| ret := adj_unit; join _ := fmap' (F:=G) (adj_counit _) |}.
Instance adjunction_comonad `{Adjoint X Y F G, !Functor F, !Functor G} : Comonad (F ∘ G)
  := {| extract := adj_counit; duplicate _ := fmap' (F:=F) (adj_unit _) |}.

Record kleisli {X} (M : X -> X) := Kleisli {get_kleisli : X}.
Add Printing Constructor kleisli.
Arguments Kleisli {_}.
Arguments get_kleisli {_ _}.
Definition pro_kleisli `{Proset X} (M : X -> X) : kleisli M -> kleisli M -> Prop :=
  fun '(Kleisli _ a1) '(Kleisli _ a2) => a1 ⊢ M a2.
Arguments pro_kleisli {X _} M !a1 !a2 /.
Instance pro_kleisli_pro `{Monad X M} : PreOrder (pro_kleisli M).
Proof.
  constructor.
  - move=> [A] /=; apply: ret.
  - move=> [A] [B] [C] /= D1 D2.
    setoid_rewrite D1; setoid_rewrite D2; by setoid_rewrite join.
Qed.
Definition tens_kleisli {X} (M : X -> X) (T : X -> X -> X) (a1 a2 : kleisli M) : kleisli M
  := Kleisli M (T (get_kleisli a1) (get_kleisli a2)).
Arguments tens_kleisli {X} M T !a1 !a2 /.
Instance kleisli_monoidal `{Monad X M, !MonSet X, !LaxMon M} :
  Monoidal (pro_kleisli M) (tens_kleisli M pro_tens) (Kleisli M memp).
Proof.
  constructor.
  - move=> [A] [A'] [B] [B'] /= D1 D2; setoid_rewrite <- pres_tens; by apply: bimap.
  - move=> [A]; split=> /=; [setoid_rewrite (pro_lunit A) |
                           setoid_rewrite <- (proj2 (pro_lunit A))]; apply: ret.
  - move=> [A]; split=> /=; [setoid_rewrite (pro_runit A) |
                           setoid_rewrite <- (proj2 (pro_runit A))]; apply: ret.
  - move=> [A] [B] [C]; split=> /=; [setoid_rewrite (pro_massoc A B C) |
                                   setoid_rewrite <- (proj2 (pro_massoc A B C))];
                                apply: ret.
Qed.
Instance kleisli_sym `{Monad X M, !MonSet X, !SymMonSet X, !LaxMon M} :
  Sym (pro_kleisli M) (tens_kleisli M pro_tens).
Proof. move=> [A] [B] /=; setoid_rewrite pro_sym' at 1; apply: ret. Qed.
Instance kleisli_proset `{Monad X M} : Proset (kleisli M)
  := {| pro_le := pro_kleisli M |}.
Instance kleisli_mset `{Monad X M, !MonSet X, !LaxMon M} :
  MonSet (kleisli M) := {| pro_tens := tens_kleisli M pro_tens |}.
Instance kleisli_smset `{Monad X M, !MonSet X, !SymMonSet X, !LaxMon M} :
  SymMonSet (kleisli M) := {}.
Instance Kleisli_functor `{Monad X M} : Functor (Kleisli M).
Proof. move=> A B D /=; by setoid_rewrite <- ret. Qed.
Instance Kleisli_strongmon `{Monad X M, !MonSet X, !LaxMon M} :
  StrongMon (Kleisli M).
Proof. done. Qed.
Definition dekleisli {X} {M : X -> X} : kleisli M -> X
  := fun '(Kleisli _ A) => M A.
Instance dekleisli_functor `{Monad X M} : Functor (dekleisli (M:=M)).
Proof. move=> [A] [B] /= D; setoid_rewrite D; apply: join. Qed.
Instance dekleisli_laxmon `{Monad X M, !MonSet X, !LaxMon M} :
  LaxMon (dekleisli (M:=M)).
Proof. constructor=> [| [A] [B]] //=; firstorder. Qed.
Instance dekleisli_strongmon `{Monad X M, !MonSet X, !StrongMon M} :
  StrongMon (dekleisli (M:=M)).
Proof. constructor; constructor=> [| [A] [B]] //=; firstorder. Qed.
Instance kleisli_adjunction `{Monad X M} : Kleisli M ⊣ dekleisli.
Proof. apply/transpose_sufficient => A [B] //. Qed.

(* okay, maybe we should just be dualizing *)
Record cokleisli {X} (F : X -> X) := Cokleisli {get_cokleisli : X}.
Add Printing Constructor cokleisli.
Arguments Cokleisli {_}.
Arguments get_cokleisli {_ _}.
Definition pro_cokleisli `{Proset X} (W : X -> X) : cokleisli W -> cokleisli W -> Prop :=
  fun '(Cokleisli _ a1) '(Cokleisli _ a2) => W a1 ⊢ a2.
Arguments pro_cokleisli {X _} W !a1 !a2 /.
Instance pro_cokleisli_pro `{Comonad X W} : PreOrder (pro_cokleisli W).
Proof.
  constructor.
  - move=> [A] /=; apply: extract.
  - move=> [A] [B] [C] /= D1 D2.
    setoid_rewrite duplicate; setoid_rewrite D1; by setoid_rewrite D2.
Qed.
(* TODO Is this monoidal? *)
Instance cokleisli_proset `{Comonad X W} : Proset (cokleisli W)
  := {| pro_le := pro_cokleisli W |}.
Instance Cokleisli_functor `{Comonad X W} : Functor (Cokleisli W).
Proof. move=> A B D /=; by setoid_rewrite extract. Qed.
Definition decokleisli {X} {W : X -> X} : cokleisli W -> X
  := fun '(Cokleisli _ A) => W A.
Instance decokleisli_functor `{Comonad X W} : Functor (decokleisli (W:=W)).
Proof. move=> [A] [B] /= D; setoid_rewrite <- D; apply: duplicate. Qed.
Instance cokleisli_adjunction `{Comonad X W} : decokleisli ⊣ Cokleisli W.
Proof. apply/transpose_sufficient => -[A] B //. Qed.

Class Alg `{Proset X} (F : X -> X) (A : X) : Prop :=
  alg : F A ⊢ A.
Class Coalg `{Proset X} (F : X -> X) (A : X) : Prop :=
  coalg : A ⊢ F A.
Hint Mode Alg ! - ! ! : typeclass_instances.
Hint Mode Coalg ! - ! ! : typeclass_instances.
Arguments alg {_ _ } _ _ {_}.
Arguments coalg {_ _} _ _ {_}.
Lemma alg_fixed_point : forall `{Monad X M} {A : X}, Alg M A <-> A ⟛ M A.
Proof. firstorder. Qed.
Lemma coalg_fixed_point : forall `{Comonad X W} {A : X}, Coalg W A <-> A ⟛ W A.
Proof. firstorder. Qed.
Instance adj_alg_coalg `{Proset X} {F G : X -> X}
         `{!F ⊣ G, !Functor F, !Functor G} `{!Alg F A}
  : Coalg G A | 3.
Proof. by apply transpose. Qed.
Instance adj_coalg_alg `{Proset X} {F G : X -> X}
         `{!F ⊣ G, !Functor F, !Functor G} `{!Coalg G A}
  : Alg F A | 3.
Proof. by apply transpose. Qed.
Instance free_alg `{Monad X M} {A} : Alg M (M A) := join.
Instance cofree_coalg `{Comonad X W} {A} : Coalg W (W A) := duplicate.
Instance adj_img_alg `{Adjoint X Y F G, !Functor G} {A} : Alg (G ∘ F) (G A)
  := fmap' (adj_counit (F:=F) (G:=G) _).
Instance adj_img_coalg `{Adjoint X Y F G, !Functor F} {A} : Coalg (F ∘ G) (F A)
  := fmap' (adj_unit (F:=F) (G:=G) _).
Lemma conecessitation : forall `{Alg X F Q, !Functor F} {P},
    P ⊢ Q -> F P ⊢ Q.
Proof.
  move=> X X_Pr F Q Alg_Q Funct_F P.
  setoid_rewrite <- (alg F Q) at 2; apply fmap'.
Qed.
Lemma necessitation : forall `{Coalg X F P, !Functor F} {Q},
    P ⊢ Q -> P ⊢ F Q.
Proof.
  move=> X X_Pr F P Coalg_P Funct_F Q.
  setoid_rewrite (coalg F P) at 2; apply fmap'.
Qed.
Lemma monad_free : forall `{Monad X M} {A B : X} `{!Alg M B},
    A ⊢ B <-> M A ⊢ B.
Proof.
  move=> *; split.
  - apply: conecessitation.
  - by setoid_rewrite <- ret.
Qed.
Lemma comonad_cofree : forall `{Comonad X W} {A B : X} `{!Coalg W A},
    A ⊢ B <-> A ⊢ W B.
Proof.
  move=> *; split.
  - apply: necessitation.
  - by setoid_rewrite extract.
Qed.

Definition pow `{MonSet X} (n : nat) (M : X) : X
  := Nat.iter n (pro_tens M) memp.
Instance pow_proper `{MonSet X}
  : Proper ((=) ==> pro_le ++> pro_le) (pow (X:=X)).
Proof.
  move=> n _ <- M M' D; elim: n => //= n D'.
  setoid_rewrite D at 1; by setoid_rewrite D'.
Qed.
Instance pow_proper' `{MonSet X}
  : Proper ((=) ==> pro_le --> flip pro_le) (pow (X:=X)).
Proof. move=> n _ <- M M'; by apply: pow_proper. Qed.
Lemma pow_assoc : forall `{MonSet X} {n m} {A : X},
    pow (n + m) A ⟛ pow n A ⊗ pow m A.
Proof.
  move=> X ? ? n m A; elim: n => /= [| n IH].
  - rewrite pro_lunit //.
  - split.
    + setoid_rewrite (proj1 IH); rewrite pro_massoc //.
    + setoid_rewrite <- (proj2 IH); rewrite -pro_massoc //.
Qed.
Instance pow_functor `{MonSet X} {n : nat} : Functor (pow (X:=X) n).
Proof. by apply: pow_proper. Qed.
Instance monoid_pow_alg `{Monoid X M} {n : nat} : Alg (pow n) M.
Proof.
  elim: n.
  - apply: eta.
  - move=> n IH; rewrite /Alg /=.
    setoid_rewrite IH; apply: mu.
Qed.
Instance comonoid_pow_coalg `{Comonoid X W} {n : nat} : Coalg (pow n) W.
Proof.
  elim: n.
  - apply: epsilon.
  - move=> n IH; rewrite /Coalg /=.
    setoid_rewrite <- IH; apply: delta.
Qed.

Definition free_monoid `{MonSet X, !Complete X} (A : X) : X
  := colim (fun n => pow n A).
Instance free_monoid_functor `{MonSet X, !Complete X} : Functor (free_monoid (X:=X)).
Proof. move=> A B D; unfold free_monoid; apply/fmap'; by setoid_rewrite D. Qed.
Instance free_monoid_monoid `{Quantale X} {A : X} : Monoid (free_monoid A).
Proof.
  constructor.
  - apply/(colim_right _ 0).
  - rewrite tensor_hom; apply/colim_left => n; rewrite -tensor_hom.
    rewrite l_tensor_hom; apply/colim_left => m; rewrite -l_tensor_hom.
    rewrite -pow_assoc; apply (colim_right _ (n + m)%nat).
Qed.
Lemma free_monoid_reflector : forall `{MonSet X, !Complete X} {A : X},
    A ⊢ free_monoid A.
Proof. move=> *; setoid_rewrite <- (colim_right _ 1); apply pro_runit. Qed.
Lemma free_monoid_free_monoid : forall `{MonSet X, !Complete X} {A : X} {M : X} `{!Monoid M},
    A ⊢ M <-> free_monoid A ⊢ M.
Proof.
  move=> X ? ? ? A M ?; split=> D.
  - setoid_rewrite D; apply/colim_left => n; apply: alg.
  - by etransitivity; first apply: free_monoid_reflector.
Qed.
Definition monoids (X : Type) `{MonSet X} : Type := sig (Monoid (X:=X)).
Definition free_monoid' `{Quantale X} : X -> monoids X
  := free_monoid ↑.
Instance monoids_monoid `{MonSet X} {M : monoids X} : Monoid (`M).
Proof. apply: proj2_sig. Qed.
Instance free_monoid'_reflection `{Quantale X} : (free_monoid' (X:=X)) ⊣ sval.
Proof. apply/transpose_sufficient => * /=; by rewrite free_monoid_free_monoid. Qed.

Definition EM `{Proset X} (M : X -> X) : Type :=
  sig (Alg M).
Instance EM_alg `{Proset X} {M : X -> X} (A : EM M) : Alg M (`A) := proj2_sig _.
Definition free_EM `{Monad X M} : X -> EM M := M ↑.
Arguments free_EM {_ _} M {_ _} _ /.
Instance EM_reflection `{Monad X M} : free_EM M ⊣ sval.
Proof. constructor=> [A | [A Alg_A]] /=; [apply: ret | apply: alg]. Qed.
Instance EM_bicomplete `{Monad X M, !Complete X} : Complete (EM M) | 0
  := reflective_cocomplete (F:=free_EM M) (G:=sval).

Definition free_monad `{Complete X} (F : X -> X) : Endo X
  := universal_ran (X:=EM F) sval sval.
Instance free_monad_monad `{Complete X} {F : X -> X} : Monad (free_monad F).
Proof.
  constructor.
  - move=> A; apply: (adj_unit (Adjoint:=universal_ran_global_ran (p:=sval)) Hom_id A).
  - enough (free_monad F ○ free_monad F ⊢ free_monad F) as D by apply: D.
    apply/(transpose (B:=in_Hom sval) (Adj:=universal_ran_global_ran)) => -[A ?] /=.
      by do 2 apply/(lim_left _ ((_ ↾ _) ↾ _)).
Qed.
Instance free_monad_functor' `{Complete X} : Functor (free_monad (X:=X)).
Proof.
  move=> F F' D A /=.
  apply/lim_right => -[[B Al] /= D'].
  unfold Alg in Al; setoid_rewrite <- (D _) in Al; change (Alg F B) in Al.
  apply/(lim_left _ ((B ↾ _) ↾ D')).
Qed.
Lemma free_monad_reflector : forall `{Complete X} {F : X -> X} `{!Functor F},
    in_Hom F ⊢ free_monad F.
Proof.
  move=> X ? ? F ?; change (in_Hom F ⊢ universal_ran (X:=EM F) sval (in_Hom sval)).
  apply/(transpose (Adj:=universal_ran_global_ran)) => -[A ?] //=.
Qed.
Lemma free_monad_free_monad : forall `{Complete X} {F M : X -> X}
                                `{!Functor F, !Functor M, !Monad M},
    F ⊢ M <-> free_monad F ⊢ in_Hom M.
Proof.
  move=> X ? ? F M ? ? ?; split.
  - move=> D; setoid_rewrite D; move=> A /=.
    apply/(lim_left _ ((_ ↾ _) ↾ _))/ret.
  - by etransitivity; first apply: free_monad_reflector.
Qed.
Instance free_monad_monad' `{Complete X} : Monad (X:=Endo X) (free_monad (X:=X)).
Proof.
  constructor.
  - move=> F; apply/free_monad_reflector.
  - move=> F; rewrite -free_monad_free_monad //.
Qed.
Instance free_monad_alg `{Complete X} {F : X -> X} {A} `{!Alg F A}
  : Alg (free_monad F) A.
Proof. rewrite /Alg /=; by apply/(lim_left _ ((_ ↾ _) ↾ _)). Qed.
Lemma un_free_monad_alg `{Complete X} {F : X -> X} `{!Functor F} {A}
         `{!Alg (free_monad F) A}
  : Alg F A.
Proof.
  unfold Alg; setoid_rewrite <- (alg (free_monad F) A) at 2.
  apply: free_monad_reflector.
Qed.
Definition fm_EM `{Complete X} {F : X -> X} : EM F -> EM (free_monad F)
  := sval ↑.
Arguments fm_EM {_ _ _} {F} _ /.
Definition un_fm_EM `{Complete X} {F : X -> X} `{!Functor F} : EM (free_monad F) -> EM F.
  refine (sval ↑) => -[? ?] /=; apply: un_free_monad_alg.
Defined.
Arguments un_fm_EM {_ _ _} {F _} _ /.
Instance fm_adj1 `{Complete X} {F : X -> X} `{!Functor F}
  : fm_EM (F:=F) ⊣ un_fm_EM.
Proof. constructor=> -[] //=. Qed.
Instance fm_adj2 `{Complete X} {F : X -> X} `{!Functor F}
  : un_fm_EM (F:=F) ⊣ fm_EM.
Proof. constructor=> -[] //=. Qed.
Instance EM_bicomplete' `{Complete X} {F : X -> X} `{!Functor F} : Complete (EM F) | 3
  := bireflective_bicomplete (G:=fm_EM).

Definition coEM `{Proset X} (W : X -> X) : Type :=
  sig (Coalg W).
Instance coEM_alg `{Proset X} {W : X -> X} (A : coEM W) : Coalg W (`A) := proj2_sig _.
Definition cofree_coEM `{Comonad X W} : X -> coEM W := W ↑.
Arguments cofree_coEM {_ _} W {_ _} /.
Instance coEM_coreflection `{Comonad X W} : sval ⊣ cofree_coEM W.
Proof. constructor=> [[A Coalg_A] | A] /=; [apply: coalg | apply: extract]. Qed.
Instance coEM_bicomplete `{Comonad X W, !Complete X} : Complete (coEM W)
  := coreflective_complete (F:=sval) (G:=cofree_coEM W).
Program Definition cofree_coEM' `{Complete X} (F : X -> X) `{!Functor F} : X -> coEM F
  := fun A => colim (fun A : {A0 : coEM F | `A0 ⊢ A}  => ``A).
Next Obligation.
  move=> X ? ? F ? A.
  apply/colim_left => S; setoid_rewrite <- (colim_right _ S).
  apply: coalg.
Qed.

Definition cofree_comonad `{Complete X} (F : X -> X) : Endo X
  := universal_lan (X:=coEM F) sval sval.
Instance cofree_comonad_comonad `{Complete X} {F : X -> X} : Comonad (cofree_comonad F).
Proof.
  constructor.
  - move=> A; apply: (adj_counit (Adjoint:=universal_lan_global_lan (p:=sval)) Hom_id A).
  - enough (cofree_comonad F ⊢ cofree_comonad F ○ cofree_comonad F) as D by apply: D.
    apply/(transpose (A:=in_Hom sval) (Adj:=universal_lan_global_lan)) => -[A ?] /=.
      by do 2 apply/(colim_right _ ((_ ↾ _) ↾ _)).
Qed.
Instance cofree_comonad_functor' `{Complete X} : Functor (cofree_comonad (X:=X)).
Proof.
  move=> F F' D A /=.
  apply/colim_left => -[[B Coal] /= D'].
  unfold Coalg in Coal; setoid_rewrite (D _) in Coal; change (Coalg F' B) in Coal.
  apply/(colim_right _ ((B ↾ _) ↾ D')).
Qed.
Lemma cofree_comonad_coreflector : forall `{Complete X} {F : X -> X} `{!Functor F},
    cofree_comonad F ⊢ in_Hom F.
Proof.
  move=> X ? ? F ?; change (universal_lan (X:=coEM F) sval (in_Hom sval) ⊢ in_Hom F).
  apply/(transpose (Adj:=universal_lan_global_lan)) => -[A ?] //=.
Qed.
Lemma cofree_comonad_cofree_comonad : forall `{Complete X} {F W : X -> X}
                                        `{!Functor F, !Functor W, !Comonad W},
    W ⊢ F <-> in_Hom W ⊢ cofree_comonad F.
Proof.
  move=> X ? ? F W ? ? ?; split.
  - move=> D; setoid_rewrite <- D; move=> A /=.
    apply/(colim_right _ ((_ ↾ _) ↾ _))/extract.
  - by etransitivity; last apply: cofree_comonad_coreflector.
Qed.
Instance cofree_comonad_comonad' `{Complete X}
  : Comonad (X:=Endo X) (cofree_comonad (X:=X)).
Proof.
  constructor.
  - move=> F; apply/cofree_comonad_coreflector.
  - move=> F; rewrite -cofree_comonad_cofree_comonad //.
Qed.
Instance cofree_comonad_coalg `{Complete X} {F : X -> X} {A} `{!Coalg F A}
  : Coalg (cofree_comonad F) A.
Proof. rewrite /Coalg /=; by apply/(colim_right _ ((_ ↾ _) ↾ _)). Qed.
Lemma un_cofree_comonad_coalg `{Complete X} {F : X -> X} `{!Functor F} {A}
         `{!Coalg (cofree_comonad F) A}
  : Coalg F A.
Proof.
  unfold Coalg; setoid_rewrite (coalg (cofree_comonad F) A) at 1.
  apply: cofree_comonad_coreflector.
Qed.
Definition cofm_coEM `{Complete X} {F : X -> X}
  : coEM F -> coEM (cofree_comonad F)
  := sval ↑.
Arguments cofm_coEM {_ _ _} {F} _ /.
Definition un_cofm_coEM `{Complete X} {F : X -> X} `{!Functor F}
  : coEM (cofree_comonad F) -> coEM F.
  refine (sval ↑) => -[? ?] /=; apply: un_cofree_comonad_coalg.
Defined.
Arguments un_cofm_coEM {_ _ _} {F _} _ /.
Instance cofm_adj1 `{Complete X} {F : X -> X} `{!Functor F}
  : cofm_coEM (F:=F) ⊣ un_cofm_coEM.
Proof. constructor=> -[] //=. Qed.
Instance cofm_adj2 `{Complete X} {F : X -> X} `{!Functor F}
  : un_cofm_coEM (F:=F) ⊣ cofm_coEM.
Proof. constructor=> -[] //=. Qed.
Instance coEM_bicomplete' `{Complete X} {F : X -> X} `{!Functor F}
  : Complete (coEM F) | 3
  := bireflective_bicomplete (G:=cofm_coEM).

Lemma lambek : forall `{Proset X} {F : X -> X} `{!Functor F} {I : EM F},
    colim_cocone (fun H : Empty_set => match H with end) I ->
    F (`I) ⟛ `I.
Proof.
  move=> X ? F ? I [_ U]; split; first by apply: alg.
  have ? : Alg F (F (`I)) by apply/fmap'/alg.
  apply: (U (F (`I) ↾ _)) => -[].
Qed.
Lemma colambek : forall `{Proset X} {F : X -> X} `{!Functor F} {I : coEM F},
    lim_cone I (fun H : Empty_set => match H with end) ->
    F (`I) ⟛ `I.
Proof.
  move=> X ? F ? I [_ U]; split; last by apply: coalg.
  have ? : Coalg F (F (`I)) by apply/fmap'/coalg.
  apply: (U (F (`I) ↾ _)) => -[].
Qed.

Definition least_fixed_point `{Complete X} (F : X -> X) : X
  := ` (initial (EM (free_monad F))).
Definition greatest_fixed_point `{Complete X} (F : X -> X) : X
  := ` (terminal (coEM (cofree_comonad F))).
Lemma lfp_alt : forall `{Complete X} {F : X -> X} `{!Functor F},
    least_fixed_point F ⟛ ` (initial (EM F)).
Proof. move=> *; apply (fmap_core (F:=sval) (distrib_initial (F:=un_fm_EM))). Qed.
Lemma gfp_alt : forall `{Complete X} {F : X -> X} `{!Functor F},
    greatest_fixed_point F ⟛ ` (terminal (coEM F)).
Proof. move=> *; apply (fmap_core (F:=sval) (distrib_terminal (F:=un_cofm_coEM))). Qed.

(* TODO Do this right (and move it). *)
Instance Alg_proper `{Proset X} {F : X -> X} `{!Functor F}
  : Proper (core pro_le ==> iff) (Alg F).
Proof.
  move=> A A' E; rewrite /Alg; split.
  - rewrite {2}E; by setoid_rewrite <- (proj2 E).
  - rewrite {1}E; by setoid_rewrite <- (proj2 E).
Qed.
Instance Coalg_proper `{Proset X} {F : X -> X} `{!Functor F}
  : Proper (core pro_le ==> iff) (Coalg F).
Proof.
  move=> A A' E; rewrite /Coalg; split.
  - rewrite {2}E; by setoid_rewrite <- (proj2 E).
  - rewrite {1}E; by setoid_rewrite <- (proj2 E).
Qed.
Instance lfp_alg `{Complete X} {F : X -> X} `{!Functor F}
  : Alg F (least_fixed_point F).
Proof. apply/(Alg_proper _ _ lfp_alt). Qed.
Instance lfp_coalg `{Complete X} {F : X -> X} `{!Functor F}
  : Coalg F (least_fixed_point F).
Proof. apply (Coalg_proper _ _ lfp_alt), lambek, is_colim. Qed.
Instance gfp_alg `{Complete X} {F : X -> X} `{!Functor F}
  : Alg F (greatest_fixed_point F).
Proof. apply (Alg_proper _ _ gfp_alt), colambek, is_lim. Qed.
Instance gfp_coalg `{Complete X} {F : X -> X} `{!Functor F}
  : Coalg F (greatest_fixed_point F).
Proof. apply/(Coalg_proper _ _ gfp_alt). Qed.
Lemma lfp_unfold_ : forall `{Complete X} {F : X -> X} `{!Functor F} A,
    A = least_fixed_point F -> A ⟛ F A.
Proof. split; subst; [apply: coalg | apply: alg]. Qed.
Notation lfp_unfold A := (lfp_unfold_ A erefl).
Lemma gfp_unfold_ : forall `{Complete X} {F : X -> X} `{!Functor F} A,
    A = greatest_fixed_point F -> A ⟛ F A.
Proof. split; subst; [apply: coalg | apply: alg]. Qed.
Notation gfp_unfold A := (gfp_unfold_ A erefl).
Lemma lfp_ind : forall `{Complete X} {F : X -> X} `{!Functor F} {A : X},
    Alg F A -> least_fixed_point F ⊢ A.
Proof.
  move=> X ? ? F ? A Alg_A; rewrite lfp_alt; change (⊥ ⊢ A ↾ Alg_A); apply/initial_left.
Qed.
Lemma gfp_coind : forall `{Complete X} {F : X -> X} `{!Functor F} {A : X},
    Coalg F A -> A ⊢ greatest_fixed_point F.
Proof.
  move=> X ? ? F ? A Coalg_A.
  setoid_rewrite <- (proj2 gfp_alt); change (A ↾ Coalg_A ⊢ ⊤).
  apply/terminal_right.
Qed.
Definition lfp_ind' : forall `{Complete X} {F : X -> X} `{!Functor F} {A : X},
    F A ⊢ A -> least_fixed_point F ⊢ A
  := @lfp_ind.
Definition gfp_coind' : forall `{Complete X} {F : X -> X} `{!Functor F} {A : X},
    A ⊢ F A -> A ⊢ greatest_fixed_point F
  := @gfp_coind.
Instance least_fixed_point_functor `{Complete X}
  : Functor (X:=Hom X X) (least_fixed_point (X:=X)).
Proof. move=> F G D; apply lfp_ind; unfold Alg; setoid_rewrite D; apply: alg. Qed.
Instance greatest_fixed_point_functor `{Complete X}
  : Functor (X:=Hom X X) (greatest_fixed_point (X:=X)).
Proof. move=> F G D; apply gfp_coind; unfold Coalg; setoid_rewrite <- D; apply: coalg. Qed.

Section AdjZero.
  Context `{Proset X, Proset Y} {F : X -> Y} {G : Y -> X}
          `{!F ⊣ G, !Functor F, !Functor G}.
  Let M : X -> X := G ∘ F.
  Local Notation I := (kleisli M).
  Local Notation T := (EM M).

  Definition from_kleisli : I -> Y := F ∘ dekleisli.
  Definition to_kleisli   : Y -> I := Kleisli M ∘ G.
  Lemma from_kleisli_triangle : G ∘ from_kleisli ⟛ dekleisli.
  Proof.
    apply/pw_core0 => -[A]; rewrite /from_kleisli /=.
    split; [apply (join (M:=M)) | apply (ret (M:=M))].
  Qed.
  Lemma to_kleisli_triangle : to_kleisli ∘ F ⟛ Kleisli M.
  Proof. split=> A //=; setoid_rewrite <- ret; apply (adj_unit A). Qed.
  Lemma from_kleisli_unique : forall `{!Functor FK},
      G ∘ FK ⟛ dekleisli -> FK ⟛ from_kleisli.
  Proof.
  Abort.
End AdjZero.

Section AdjointMW.
  Context `{Proset X} {M : X -> X} {W : X -> X}
          `{Adj : M ⊣ W, !Functor M, !Functor W, !Monad M, !Comonad W}.

  Definition cofree_EM : X -> EM M := W ↑.
  Definition free_coEM : X -> coEM W := M ↑.
  Global Instance EM_coreflection : sval ⊣ cofree_EM.
  Proof.
    constructor=> [[A Coalg_A] | A] /=; [by apply transpose, alg | apply extract].
  Qed.
  Global Instance coEM_reflection : free_coEM ⊣ sval.
  Proof.
    constructor=> [A | [A Alg_A]] /=; [apply ret | by apply transpose, coalg].
  Qed.

  Definition transpose_EM : EM M -> coEM W := sval ↑.
  Definition transpose_coEM : coEM W -> EM M := sval ↑.
  Lemma transpose_EM_inverse : transpose_EM ∘ transpose_coEM ⟛ id.
  Proof. by compute. Qed.
  Lemma transpose_coEM_inverse : transpose_coEM ∘ transpose_EM ⟛ id.
  Proof. by compute. Qed.
  Global Instance transpose_EM_adjunction : transpose_EM ⊣ transpose_coEM.
  Proof. constructor; by compute. Qed.
  Global Instance transpose_coEM_adjunction : transpose_coEM ⊣ transpose_EM.
  Proof. constructor; by compute. Qed.
  Lemma transpose_EM_triple_iso :
    [/\ transpose_EM ∘ free_EM M ⟛ free_coEM, sval ∘ transpose_EM ⟛ sval &
        transpose_EM ∘ cofree_EM ⟛ cofree_coEM W].
    Proof. by compute. Qed.
  Lemma transpose_coEM_triple_iso :
    [/\ transpose_coEM ∘ free_coEM ⟛ free_EM M, sval ∘ transpose_coEM ⟛ sval &
        transpose_coEM ∘ cofree_coEM W ⟛ cofree_EM].
    Proof. by compute. Qed.
End AdjointMW.
Arguments cofree_EM {_ _} M {_ _ _ _ _}.
Arguments free_coEM {_ _ _} W {_ _ _ _}.
(* So any F ⊣ G ⊣ H between X and Y (F : X -> Y) can be resliced into either
   for F and H and same codomain for G, in either of the forms
   free_EM ⊣ sval ⊣ cofree_EM or free_coEM ⊣ sval ⊣ cofree_coEM, which are isomorphic;
   and ... TODO Finish working out the details of this! *)


Class FinPow (T : Type -> Type) `{forall `{Proset X}, Proset (T X)} :=
  {Ix : Type;
   index : forall {X}, T X -> Ix -> X;
   tabulate : forall {X}, (Ix -> X) -> T X;
   tabulate_proper :> forall {X}, Proper (pointwise_relation _ eq ==> eq) (@tabulate X);
   index_functor :> forall `{Proset X}, Functor (@index X);
   tabulate_functor :> forall `{Proset X}, Functor (@tabulate X);
   tabulate_index_cancel :> forall {X}, Cancel eq (@tabulate X) index;
   index_tabulate_cancel :> forall {X}, Cancel (pointwise_relation _ eq) (@index X) tabulate;
   fp_map {X Y} (F : X -> Y) : T X -> T Y := tabulate ∘ (F ∘.) ∘ index;

   multiply : forall `{MonSet X}, T X -> X;
   multiply_functor :> forall `{MonSet X}, Functor (multiply (X:=X));
   multiply_natural_lax : forall `{Functor X Y F, !MonSet X, !MonSet Y, !LaxMon F}
                            {L : T X},
       multiply (fp_map F L) ⊢ F (multiply L);
   multiply_natural_oplax : forall `{Functor X Y F, !MonSet X, !MonSet Y, !OplaxMon F}
                              {L : T X},
       F (multiply L) ⊢ multiply (fp_map F L)
  }.
Hint Mode FinPow ! ! : typeclass_instances.
Arguments Ix T {_ _}.
Lemma multiply_natural : forall `{FinPow T, Functor X Y F, !MonSet X, !MonSet Y, !StrongMon F}
                           {L : T X},
    multiply (fp_map F L) ⟛ F (multiply L).
Proof. move=> *; split; [apply: multiply_natural_lax | apply: multiply_natural_oplax]. Qed.
Instance index_full `{FinPow T, Proset X} : Full (index (T:=T) (X:=X)).
Proof. move=> A B /(fmap' (F:=tabulate)); rewrite !cancel //. Qed.
Instance tabulate_full `{FinPow T, Proset X} : Full (tabulate (T:=T) (X:=X)).
Proof. move=> A B /(fmap' (F:=index)) D i; move: (D i); rewrite !cancel //. Qed.

Local Instance compose_proper'1 {X Y Z} {RY : Y -> Y -> Prop} {RZ : Z -> Z -> Prop}
  : Proper ((RY ==> RZ) ==> pointwise_relation X RY ==> pointwise_relation X RZ) compose.
Proof. firstorder. Qed.
Local Instance compose_proper'2 {X Y Z} {RX : X -> X -> Prop} {RZ : Z -> Z -> Prop}
  : Proper (pointwise_relation Y RZ ==> (RX ==> eq) ==> (RX ==> RZ)) compose.
Proof. move=> f f' E_f g g' E_g x x' E_x /=; rewrite (E_g _ _ E_x) //. Qed.
Local Instance compose_proper'12 {X Y Z} {RZ : Z -> Z -> Prop}
  : Proper (pointwise_relation Y RZ ==> pointwise_relation X eq
                               ==> pointwise_relation X RZ) compose.
Proof. move=> f f' E_f g g' E_g x /=; rewrite (E_g x) //. Qed.
(*
Local Instance pw_respectful_subrel {X Y} {R : Y -> Y -> Prop}
  : subrelation (pointwise_relation X R) (eq ==> R)%signature.
Proof. firstorder. Qed.
*)
Lemma fp_map_id : forall `{FinPow T} {X} {As : T X}, fp_map id As = As.
Proof. move=> *; rewrite /fp_map /compose /= cancel //. Qed.
Lemma fp_map_compose : forall `{FinPow T} {X Y Z} {F : Y -> Z} {G : X -> Y} {As : T X},
    fp_map (F ∘ G) As = fp_map F (fp_map G As).
Proof.
  move=> ? ? ? X Y Z ? ? ?; rewrite /fp_map /compose /=.
    by setoid_rewrite index_tabulate_cancel.
Qed.
Definition fp_pure (T : Type -> Type) `{FinPow T} {X} : X -> T X
  := tabulate ∘ const.
Lemma fp_map_pure : forall `{FinPow T} {X Y} {F : X -> Y} {A : X},
    fp_map F (fp_pure T A) = fp_pure T (F A).
Proof.
  move=> T ? ? X Y F A; rewrite /fp_map /fp_pure /=.
    by setoid_rewrite (index_tabulate_cancel _).
Qed.
Definition fp_zipwith `{FinPow T} {X Y Z} (F : X -> Y -> Z) (As : T X) (Bs : T Y) : T Z
  := tabulate (fun i : Ix T => F (index As i) (index Bs i)).
Instance fp_zipwith_functor1 `{FinPow T} `{Proset X} {Y} `{Proset Z'} {F : X -> Y -> Z'}
         `{!Functor F}
  : Functor (fp_zipwith (T:=T) F).
Proof.
  move=> As As' D Bs.
  rewrite /fp_zipwith.
  apply fmap' => i; apply: (fmap' (F:=F)); by apply index_functor.
Qed.
Instance fp_zipwith_functor2 `{FinPow T} {X} `{Proset Y, Proset Z'} {F : X -> Y -> Z'}
         `{!forall As, Functor (F As)} {As : T X}
  : Functor (fp_zipwith F As).
Proof.
  move=> Bs Bs' D.
  rewrite /fp_zipwith.
  apply fmap' => i; apply: (fmap' (F:=F _)); by apply index_functor.
Qed.
Lemma fp_zipwith_pure_l : forall `{FinPow T} {X Y Z} {F : X -> Y -> Z} {A : X} {Bs : T Y},
    fp_zipwith F (fp_pure T A) Bs = fp_map (F A) Bs.
Proof.
  move=> T ? ? X Y Z F A Bs; rewrite /fp_zipwith /fp_pure /fp_map /=.
    by setoid_rewrite index_tabulate_cancel.
Qed.
Lemma fp_zipwith_pure_r : forall `{FinPow T} {X Y Z} {F : X -> Y -> Z} {As : T X} {B : Y},
    fp_zipwith F As (fp_pure T B) = fp_map (flip F B) As.
Proof.
  move=> T ? ? X Y Z F As B; rewrite /fp_zipwith /fp_pure /fp_map /=.
    by setoid_rewrite index_tabulate_cancel.
Qed.
Lemma fp_zipwith_assoc1 : forall `{FinPow T} {X Y Z W U} {G : Y -> Z -> W} {F : X -> W -> U}
                            {As Bs Cs},
    fp_zipwith (T:=T) F As (fp_zipwith G Bs Cs) =
    fp_zipwith apply (fp_zipwith (fun A B C => F A (G B C)) As Bs) Cs.
Proof.
  move=> *; rewrite /fp_zipwith /=; apply: tabulate_proper => i /=; rewrite !cancel //.
Qed.
Lemma fp_zipwith_assoc2 : forall `{FinPow T} {X Y Z W U} {G : X -> Y -> Z} {F : Z -> W -> U}
                           {As Bs Cs},
    fp_zipwith (T:=T) F (fp_zipwith G As Bs) Cs =
    fp_zipwith eval_at As (fp_zipwith (fun B C A => F (G A B) C) Bs Cs).
Proof.
  move=> *; rewrite /fp_zipwith /=; apply: tabulate_proper => i /=.
  rewrite !cancel //.
Qed.
Lemma fp_map_zipwith : forall `{FinPow T} {X Y Z Z'} {F : Z -> Z'} {G : X -> Y -> Z} {As Bs},
    fp_map (T:=T) F (fp_zipwith G As Bs) = fp_zipwith (fun A B => F (G A B)) As Bs.
Proof. move=> *; rewrite /fp_map /fp_zipwith /=; rewrite cancel //. Qed.
(*
Class TensIx (J : Type) :=
  {multiply : forall `{MonSet X}, (J -> X) -> X;
   multiply_natural : forall `{Functor X Y F, !MonSet X, !MonSet Y, !StrongMon F} {L : J -> X},
       multiply (F ∘ L) ⟛ F (multiply L)}.
Hint Mode TensIx ! : typeclass_instances.
Instance multiply_functor `{TensIx J, MonSet X} : Functor (multiply (X:=X)).
Proof.
  move=> L1 L2 D.
  generalize (multiply_natural (F:=list_sharp (L1 ∘ get_discrete)) (L:=mret ∘ Discrete)).
  generalize (multiply_natural (F:=list_sharp (L2 ∘ get_discrete)) (L:=mret ∘ Discrete)).
  rewrite /list_sharp /= /compose /= => -[_ D2] [D1 _].
  setoid_rewrite D1; setoid_rewrite <- D2; apply/fmap'/list_map_functor => ? //.
Qed.
Program Instance tens_ix0 : TensIx Empty_set := {| multiply _ _ _ L := memp |}.
Next Obligation. firstorder. Qed.
Program Instance tens_ix1 : TensIx unit := {| multiply _ _ _ L := L () |}.
Next Obligation. firstorder. Qed.
Program Instance tens_ix_plus {I} `{TensIx I, TensIx J} : TensIx (I + J)
  := {| multiply _ _ _ L := multiply (L ∘ inl) ⊗ multiply (L ∘ inr) |}.
Next Obligation.
  move=> I ? J ? X ? Y ? F ? ? ? ? L /=.
  rewrite (multiply_natural (L:=L ∘ inl)) (multiply_natural (L:=L ∘ inr)); split.
  - apply: pres_tens.
  - apply: pres_tens_op.
Qed.
 *)
Program Instance finpow0 : FinPow (fun _ => unit)
  := {| Ix := Empty_set; index _ _ a := match a with end; tabulate _ _ := ();
        multiply _ _ _ _ := memp |}.
Solve All Obligations with firstorder.
Next Obligation. compute=> ? [] //. Qed.
Next Obligation. by compute. Qed.
Program Instance finpow1 : FinPow id
  := {| Ix := (); index _ x _ := x; tabulate _ L := L (); multiply _ _ _ A := A |}.
Solve All Obligations with done.
Next Obligation. firstorder. Qed.
Next Obligation. compute=> ? ? [] //. Qed.
Definition pprod (T1 T2 : Type -> Type) : Type -> Type
  := fun X => (T1 X * T2 X)%type.
Program Instance finpow_plus `{FinPow T1, FinPow T2}
  : FinPow (pprod T1 T2)
  := {| Ix := Ix T1 + Ix T2;
        index X xy := sum_rect (fun _ => X) (index xy.1) (index xy.2);
        tabulate _ L := (tabulate (L ∘ inl), tabulate (L ∘ inr));
        multiply _ _ _ xy := multiply xy.1 ⊗ multiply xy.2 |}.
Next Obligation. move=> * ? ? -> //. Qed.
Next Obligation. move=> * A B D [] i /=; apply/index_functor; by setoid_rewrite D. Qed.
Next Obligation. move=> * A B D /=; split; by apply/tabulate_functor/subst_functor1. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? [? ?] /=; rewrite !cancel //. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? | ?] /=; rewrite cancel //. Qed.
Next Obligation. move=> * A B D; by setoid_rewrite D. Qed.
Next Obligation.
  move=> * /=.
  setoid_rewrite <- pres_tens; by setoid_rewrite multiply_natural_lax.
Qed.
Next Obligation.
  move=> * /=.
  setoid_rewrite pres_tens_op; by setoid_rewrite <- multiply_natural_oplax.
Qed.
Definition square (X : Type) : Type := X * X.
(* Instance finpow2 : FinPow square. typeclasses eauto. := finpow_plus. *)

Definition convolve `{FinPow T, MonSet X, MonSet Y, !Complete Y}
  : Hom (T X) Y -> Hom X Y
  := universal_lan multiply.
Definition convolve' `{FinPow T, MonSet X, MonSet Y, !Complete Y}
  : (T X -> Y) -> Hom X Y
  := universal_lan multiply.
Instance convolve_global_lan `{FinPow T, MonSet X, MonSet Y, !Complete Y}
  : convolve (T:=T) (X:=X) (Y:=Y) ⊣ (.○ in_Hom multiply) := universal_lan_global_lan.
(* hmm. *)
Instance convolve'_global_lan_ish `{FinPow T, MonSet X, MonSet Y, !Complete Y}
  : convolve' (T:=T) (X:=X) (Y:=Y) ⊣ (.∘ multiply).
Proof.
  constructor=> F A /=.
  - by apply/(colim_right _ (_ ↾ _)).
  - apply/colim_left => -[As D] /=; by setoid_rewrite D.
Qed.

Program Definition ext_tens `{Proset X, MonSet Y, FinPow T}
        (Fs : T (Hom X Y)) : Hom (T X) Y
  := multiply ∘ fp_zipwith ap_Hom Fs.
Definition ext_tens' `{Proset X, MonSet Y, FinPow T}
           (Fs : T (X -> Y)) : T X -> Y
  := multiply ∘ fp_zipwith apply Fs.
Definition gday `{FinPow T, MonSet X, MonSet Y, !Complete Y} : T (Hom X Y) -> Hom X Y
  := convolve ∘ ext_tens.
Lemma gday_left : forall `{FinPow T, MonSet X, MonSet Y, !Complete Y} {Fs : T (Hom X Y)} {G},
    gday Fs ⊢ G <-> ext_tens Fs ⊢ G ○ in_Hom multiply.
Proof. move=> *; rewrite /gday /= transpose //. Qed.
Lemma gday_right : forall `{FinPow T, MonSet X, MonSet Y, !Complete Y} {F} {Gs : T (Hom X Y)},
    F ⊢ gday Gs <->
    forall A : X, F A ⊢ colim (fun As : {As0 : T X | multiply As0 ⊢ A} => ext_tens Gs (`As)).
Proof. done. Qed.
Definition gday2 `{MonSet X, MonSet Y, !Complete Y} : Hom X Y -> Hom X Y -> Hom X Y
  := uncurry (gday (T:=square)).
Lemma gday2_left : forall `{MonSet X, MonSet Y, !Complete Y} {F1 F2 : Hom X Y} {G},
    gday2 F1 F2 ⊢ G <-> forall x1 x2, F1 x1 ⊗ F2 x2 ⊢ G (x1 ⊗ x2).
Proof.
  move=> *; rewrite gday_left /= /compose /=; split.
  - move=> D x1 x2; apply: (D (x1, x2)).
  - firstorder.
Qed.
Lemma gday2_right : forall `{FinPow T, MonSet X, MonSet Y, !Complete Y} {F} {G1 G2 : Hom X Y},
    F ⊢ gday2 G1 G2 <->
    forall A : X, F A ⊢ colim (fun As : {As0 : square X | As0.1 ⊗ As0.2 ⊢ A} =>
                            G1 (`As).1 ⊗ G2 (`As).2).
Proof. done. Qed.
Instance gday2_functor `{MonSet X, MonSet Y, !Complete Y}
  : Functor (gday2 (X:=X) (Y:=Y)).
Proof. move=> F F' D G A /=; apply fmap' => ?; by setoid_rewrite D. Qed.
Instance gday2_functor' `{MonSet X, MonSet Y, !Complete Y} {F : Hom X Y}
  : Functor (gday2 F).
Proof. move=> G G' D A /=; apply fmap' => ?; by setoid_rewrite D. Qed.
Program Definition mon_coyo `{Proset X, MonSet Y, !Complete Y} (A : op X) : Hom X Y
  := fun B => mon_embed_prop (get_op A ⊢ B).
Next Obligation.
  move=> X ? Y ? ? ? A B B' D.
  apply/fmap'; by setoid_rewrite D.
Qed.
Instance mon_coyo_functor `{Proset X, MonSet Y, !Complete Y}
  : Functor (mon_coyo (X:=X) (Y:=Y)).
Proof. move=> A A' D B /=; apply/fmap'; by apply: transitivity. Qed.
Definition gday2_memp `{MonSet X, MonSet Y, !Complete Y} : Hom X Y
  := mon_coyo memp.
Instance gday2_monoidal `{MonSet X, Quantale Y}
  : Monoidal pro_le (gday2 (X:=X) (Y:=Y)) gday2_memp.
Proof.
  constructor.
  - move=> F F' G G' D1 D2; setoid_rewrite D2; by apply gday2_functor.
  - move=> F; split.
    + apply/gday2_left => A1 A2 /=.
      rewrite tensor_hom; apply/mon_embed_prop_left => D; rewrite -tensor_hom.
      rewrite pro_lunit; setoid_rewrite <- D; by setoid_rewrite <- (proj2 (pro_lunit _)).
    + apply/gday_right => A.
      unshelve setoid_rewrite <- (colim_right _ ((memp, A) ↾ _)); simpl.
      * apply pro_lunit.
      * setoid_rewrite <- mon_embed_prop_right; try reflexivity.
        apply pro_lunit.
  - move=> F; split.
    + apply/gday2_left => A1 A2 /=.
      rewrite l_tensor_hom; apply/mon_embed_prop_left => D; rewrite -l_tensor_hom.
      rewrite pro_runit; setoid_rewrite <- D; by setoid_rewrite <- (proj2 (pro_runit _)).
    + apply/gday_right => A.
      unshelve setoid_rewrite <- (colim_right _ ((A, memp) ↾ _)); simpl.
      * apply pro_runit.
      * setoid_rewrite <- mon_embed_prop_right; try reflexivity.
        apply pro_runit.
  - move=> F G H'; split.
    + apply/gday2_left => A1 A2; rewrite l_tensor_hom; move: A2.
      change (forall A2, ?L A2 ⊢ @?R A2) with (L ⊢ in_Hom R).
      apply gday2_left => A21 A22 /=; rewrite -l_tensor_hom pro_massoc.
      setoid_rewrite <- (colim_right _ ((A1 ⊗ A21, A22) ↾ proj2 (pro_massoc _ _ _))).
      simpl; by unshelve setoid_rewrite <- (colim_right _ ((A1, A21) ↾ _)).
    + apply/gday2_left => A1 A2; rewrite tensor_hom; move: A1.
      change (forall A1, ?L A1 ⊢ @?R A1) with (L ⊢ in_Hom R).
      apply gday2_left => A11 A12 /=; rewrite -tensor_hom -pro_massoc.
      setoid_rewrite <- (colim_right _ ((A11, A12 ⊗ A2) ↾ proj1 (pro_massoc _ _ _))).
      simpl; by unshelve setoid_rewrite <- (colim_right _ ((A12, A2) ↾ _)).
Qed.
Instance gday2_sym `{SymMonSet X, Quantale Y, !SymMonSet Y}
  : Sym pro_le (gday2 (X:=X) (Y:=Y)).
Proof.
  move=> F G A /=.
  apply/colim_left => -[[A1 A2] /= D].
  unshelve setoid_rewrite <- (colim_right _ ((A2, A1) ↾ _));
    rewrite /= pro_sym' //.
Qed.
(* Not an instance! We don't want to conflict with other instances! *)
Definition gday2_mset `{MonSet X, Quantale Y} : MonSet (Hom X Y)
  := {| pro_tens := gday2 |}.
Lemma mon_coyo_strongmon `{MonSet X, Quantale Y}
  : StrongMon (H2:=gday2_mset) (mon_coyo (X:=X) (Y:=Y)).
Proof.
  constructor; constructor=> // A B.
  - apply/gday2_left => C1 C2 /=.
    rewrite mon_tensor_prop; apply/fmap' => -[D1 D2].
    setoid_rewrite D1; by setoid_rewrite D2.
  - move=> C; apply/mon_embed_prop_left => Cov /=.
    unshelve setoid_rewrite <- (colim_right _ ((get_op A, get_op B) ↾ _)); [done | simpl].
    setoid_rewrite <- (proj2 mon_tensor_prop); by apply/mon_embed_prop_right.
Qed.
Instance gday_subst_laxmon `{MonSet X, Quantale Y} {A : X} `{!Monoid A}
  : LaxMon (H0:=gday2_mset) (Hom_eval_at (X:=Y) A).
Proof.
  constructor.
  - apply/mon_embed_prop_right => //=.
    apply/eta.
  - move=> F G /=.
    apply/(colim_right _ ((A, A) ↾ _))/mu.
Qed.
Definition factor_le `{MonSet X} (A : X) : Prop
  := forall A1 A2, A1 ⊗ A2 ⊢ A -> A1 ⊢ A /\ A2 ⊢ A.
Lemma gday_subst_oplaxmon : forall `{MonSet X, Quantale Y} {A : X},
    factor_le A ->
    OplaxMon (H0:=gday2_mset) (Hom_eval_at (X:=Y) A).
Proof.
  move=> X ? ? Y ? ? ? ? ? ? A Factor; constructor.
  - apply/mon_embed_prop_left => //=.
  - move=> F G; apply/colim_left => -[[A1 A2] /= D].
    apply bimap; apply/fmap'; firstorder.
Qed.
Lemma gday_subst_strongmon : forall `{MonSet X, Quantale Y} {A : X} `{!Monoid A},
    factor_le A ->
    StrongMon (H0:=gday2_mset) (Hom_eval_at (X:=Y) A).
Proof.
  constructor.
  - typeclasses eauto.
  - by apply/gday_subst_oplaxmon.
Qed.
Instance gday_colim_strongmon `{MonSet X, Quantale Y}
  : StrongMon (H0:=gday2_mset) (colim (R:=X) (X:=Y)).
Proof.
  constructor; constructor.
  - simpl; setoid_rewrite <- (colim_right _ memp); by apply/mon_embed_prop_right.
  - move=> F G.
    rewrite tensor_hom; apply/colim_left => A1; rewrite -tensor_hom.
    rewrite l_tensor_hom; apply/colim_left => A2; rewrite -l_tensor_hom.
    setoid_rewrite <- (colim_right _ (A1 ⊗ A2)); simpl.
      by apply/(colim_right _ ((A1, A2) ↾ _)).
  - simpl; apply/colim_left => A; by apply/mon_embed_prop_left.
  - move=> F G; apply/colim_left => A; apply/colim_left => -[[A1 A2] /= D].
    apply bimap; apply/colim_right.
Qed.

(* TODO Move these *)
Instance lim_congr `{Complete X} {R}
  : Proper (pointwise_relation R pro_le ++> pro_le) (lim (X:=X) (R:=R)).
Proof. move=> J J' E; by apply/fmap'. Qed.
Instance lim_congr' `{Complete X} {R}
  : Proper (pointwise_relation R pro_le --> flip pro_le) (lim (X:=X) (R:=R)).
Proof. move=> J J' E; by apply/fmap'. Qed.
Instance colim_congr `{Complete X} {R}
  : Proper (pointwise_relation R pro_le ++> pro_le) (colim (X:=X) (R:=R)).
Proof. move=> J J' E; by apply/fmap'. Qed.
Instance colim_congr' `{Complete X} {R}
  : Proper (pointwise_relation R pro_le --> flip pro_le) (colim (X:=X) (R:=R)).
Proof. move=> J J' E; by apply/fmap'. Qed.
Definition r_coproduct `{Complete X} (B : X) : X -> X := fun A => A + B.
Arguments r_coproduct {_ _ _} B _ /.
Instance r_coproduct_functor `{Complete X} {B : X} : Functor (r_coproduct B).
Proof.
  move=> A A' D /=.
  apply: coproduct_left.
  - by etransitivity; last apply: coproduct_right1.
  - apply: coproduct_right2.
Qed.
Instance product_proper `{Complete X}
  : Proper (pro_le ++> pro_le ++> pro_le) (product (X:=X)).
Proof. move=> ? ? D1 ? ? D2; setoid_rewrite D2; by apply/r_product_functor. Qed.
Instance product_proper' `{Complete X}
  : Proper (pro_le --> pro_le --> flip pro_le) (product (X:=X)).
Proof. move=> ? ? ? ? ? ? /=; by apply: product_proper. Qed.
Instance product_proper_core `{Complete X}
  : Proper (core pro_le ==> core pro_le ==> core pro_le) (product (X:=X)).
Proof. move=> ? ? D1 ? ? D2; setoid_rewrite D2; by apply/(fmap_core (F:=r_product _)). Qed.
Instance coproduct_proper `{Complete X}
  : Proper (pro_le ++> pro_le ++> pro_le) (coproduct (X:=X)).
Proof. move=> ? ? D1 ? ? D2; setoid_rewrite D2; by apply/r_coproduct_functor. Qed.
Instance coproduct_proper' `{Complete X}
  : Proper (pro_le --> pro_le --> flip pro_le) (coproduct (X:=X)).
Proof. move=> ? ? ? ? ? ? /=; by apply: coproduct_proper. Qed.
Instance coproduct_proper_core `{Complete X}
  : Proper (core pro_le ==> core pro_le ==> core pro_le) (coproduct (X:=X)).
Proof. move=> ? ? D1 ? ? D2; setoid_rewrite D2; by apply/(fmap_core (F:=r_coproduct _)). Qed.
(* TODO Move these *)
Instance Op_proper : forall `{Proset X}, Proper (pro_le --> pro_le) (@Op X).
Proof. firstorder. Qed.
Instance Op_proper' : forall `{Proset X}, Proper (pro_le ++> flip pro_le) (@Op X).
Proof. firstorder. Qed.
Instance get_op_proper : forall `{Proset X}, Proper (pro_le --> pro_le) (@get_op X).
Proof. firstorder. Qed.
Instance get_op_proper' : forall `{Proset X}, Proper (pro_le ++> flip pro_le) (@get_op X).
Proof. firstorder. Qed.
Instance cons_proper : forall `{Proset X}, Proper (pro_le ++> pro_le ++> pro_le) (@cons X).
Proof. by constructor. Qed.
Instance cons_proper' : forall `{Proset X}, Proper (pro_le --> pro_le --> flip pro_le) (@cons X).
Proof. by constructor. Qed.

(*
Instance functor_monclosed : forall `{Proset X, MonSet Y}, MonClosed (Functor (X:=X) (Y:=Y)).
Proof. constructor=> F G //= ? ? A B D; rewrite /pro_tens /=; by setoid_rewrite D. Qed.
Definition pow `{MonSet X} (T : Type -> Type) `{FinPow T} : X -> X
  := multiply ∘ fp_pure T.
*)
(*
Definition indices (T : Type -> Type) `{FinPow T} : list (Ix T)
  := let ix_T_discrete : Proset (Ix T) := {| pro_le := eq |} in
     multiply (fp_map mret (tabulate id)).
Lemma multiply_via_list : forall `{FinPow T, MonSet X} {L : T X},
    multiply L ⟛ tens_all (index L <$> indices T).
Proof.
  move=> T ? ? X ? ? L.
  set ix_T_discrete : Proset (Ix T) := {| pro_le := eq |}.
  assert (forall `{Proset Y} {F : Ix T -> Y}, Functor F) as ix_T_functor by move=> Y ? F A B <- //.
  rewrite -tens_all'_alt -[tens_all' _]/(list_sharp _ _) /indices -multiply_natural
          -fp_map_compose /fp_map /compose /list_sharp /=.
  setoid_rewrite index_tabulate_cancel; by setoid_rewrite tabulate_index_cancel.
Qed.
(*
Instance In_proper `{Proset X, !AntiSymm eq (pro_le (X:=X))}
  : Proper (core pro_le ==> core pro_le ==> iff) (@In X).
Proof.
  move=> A A' E_A L L' [D1 D2].
  elim: L L' / D1 D2 => //= B B' Bs Bs' D1 D1s IH /(Forall2_cons_inv _ _ _ _) [D2 D2s].
*)
Lemma indices_enumeration : forall `{FinPow T} {i : Ix T}, In i (indices T).
Proof.
  move=> T ? ? i.
  set ix_T_discrete : Proset (Ix T) := {| pro_le := eq |}.
  have eq_as : AntiSymm eq eq by firstorder.
  set prop_mset' := {| pro_tens := or |}.
  have ? : Functor (In i) by give_up.
  have ? : LaxMon (In i) by give_up.
  apply: (@multiply_natural_lax T _ _ (list (Ix T)) _ Prop _ (In i) _ _ _ _ _ _).
  rewrite -fp_map_compose /compose /fp_map /compose /=.
  setoid_rewrite index_tabulate_cancel.
  generalize (multiply_via_list (L:=fp_map (mret (M:=list)) (tabulate id))) => -[D1 D2].
  rewrite /indices (anti_symm _ _ _ D1 D2).
  rewrite /indices. rewrite (multiply_via_list (L:=fp_map (mret (M:=list)) (tabulate id))). multiply_via_list.
Qed.
 *)
(*
Lemma foo : forall `{Proset R, Quantale X, FinPow T} {J : T (Hom R X)},
    multiply (fp_map (colim ∘ ap_Hom) J) ⟛ colim (ext_tens J).
Proof.
  move=> R ? X ? ? ? ? ? ? T ? ? J.
  set ix_T_discrete : Proset (Ix T) := {| pro_le := eq |}.
  (*
  split.
  - rewrite multiply_via_list /= {2}/compose.
    setoid_rewrite <- ((fun x => proj2 (multiply_via_list)) : pointwise_relation _ pro_le _ _).
    move E: (indices T) => Ixes; elim: Ixes E => /= [| i is_ IH] E.
    + rewrite /indices in E.
      give_up.
    + move=> i is_ IH; setoid_rewrite IH.
      rewrite /fp_map /= cancel /= tensor_hom; apply/colim_left => r; rewrite -tensor_hom.
      rewrite l_tensor_hom; apply/colim_left => rs; rewrite -l_tensor_hom.
*)

  assert (forall `{Proset Y} {F : Ix T -> Y}, Functor F) as ix_T_functor by move=> Y ? F A B <- //.
  split.
  - (* colim (F ∘ @sval _ P) (fun z : sig P => F `(z)). *)
    set (img_colim F i (Ps : Ix T -> R -> Prop) := colim (fun z : sig (Ps i) => F (`z))).
    have ? : forall F i, Functor (img_colim F i). {
      move=> F i P Q D; rewrite /img_colim.
      apply/colim_left => -[r Pir] /=; by apply/(colim_right _ (r ↾ _))/D.
    }
    transitivity (multiply (fp_map (colim ∘ ap_Hom) (fp_zipwith (fun (F : Hom _ _) i =>
                  in_Hom (img_colim F i)) J (tabulate id)))). {
      apply/fmap'; rewrite fp_map_zipwith /fp_map /fp_zipwith /=; apply fmap' => i /=.
      apply/colim_left => r; setoid_rewrite <- (colim_right _ (const (eq r))).
      rewrite /img_colim /=; by apply/(colim_right _ (_ ↾ _)).
    }
    set prop_mset' := {| pro_tens := or |}.
    rewrite (multiply_natural (MonSet0:=gday2_mset)); apply/colim_left => rs.
    have /gday_subst_oplaxmon Oplax : factor_le rs by firstorder.
    setoid_rewrite (multiply_natural_oplax (OplaxMon0:=Oplax)).
    rewrite fp_map_zipwith /= /img_colim /=.
    have [i D] : exists i, rs i = collision by give_up.
    apply/fmap'; rewrite fp_map_zipwith /= /fp_zipwith; apply/fmap' => i.
    rewrite cancel //.


  - transitivity (multiply (fp_map (colim ∘ ap_Hom) (fp_zipwith (fun (F : Hom _ _) i =>
                  in_Hom (resource_elim F ∘ eval_at i)) J (tabulate id)))). {
      apply/fmap'; rewrite fp_map_zipwith /fp_map /fp_zipwith /=; apply fmap' => i /=.
      apply/colim_left => r; by setoid_rewrite <- (colim_right _ (const (taken r))).
    }
    rewrite (multiply_natural (MonSet0:=gday2_mset)); apply/colim_left => rs.
    have /gday_subst_oplaxmon Oplax : factor_le rs. {
      move=> rs1 rs2 D; split=> i.
      - move: (D i); rewrite /pro_tens /=.
        case: (rs1 i); [constructor | | rewrite collision_lzero //] => r1.
        case: (rs2 i); first done; simpl; etransitivity; eauto; constructor.
      - move: (D i); rewrite /pro_tens /=.
        case: (rs2 i); [constructor | | rewrite collision_rzero //] => r2.
        case: (rs1 i); first done; simpl; etransitivity; eauto; constructor.
    }
    setoid_rewrite (multiply_natural_oplax (OplaxMon0:=Oplax)).
    rewrite fp_map_zipwith /=.
    have [i D] : exists i, rs i = collision by give_up.
    apply/fmap'; rewrite fp_map_zipwith /= /fp_zipwith; apply/fmap' => i.
    rewrite cancel //.
  - rewrite /= /fp_zipwith /fp_map /=.
    apply/colim_left => rs /=.
    apply fmap', fmap' => i.
    apply/colim_right.
Qed.
  split.
  - transitivity (multiply (fp_map (colim ∘ ap_Hom) (fp_zipwith
                 (fun F i => F ○ in_Hom (eval_at i ∘ index)) J (tabulate id)))). {
      apply/fmap'; rewrite fp_map_zipwith /fp_map /fp_zipwith /=; apply fmap' => i /=.
      apply/colim_left => r; setoid_rewrite <- (colim_right _ (fp_pure T r)); simpl.
      rewrite cancel /= cancel //.
    }
    have Foo : MonSet (T R) by give_up.
    rewrite (multiply_natural (MonSet0:=gday2_mset)); apply/fmap' => rs.
    have /gday_subst_oplaxmon Bar : factor_le rs by give_up.
    setoid_rewrite (multiply_natural_oplax (OplaxMon0:=Bar)).
    apply/fmap'; rewrite fp_map_zipwith /= /fp_zipwith; apply/fmap' => i.
    rewrite cancel //.
Lemma foo : forall `{Proset R, Quantale X, FinPow T} {J : T (Hom R X)},
    multiply (fp_map (colim ∘ ap_Hom) J) ⟛ colim (ext_tens J).
Proof.
  move=> R ? X ? ? ? ? ? ? T ? ? J.
  set ix_T_discrete : Proset (Ix T) := {| pro_le := eq |}.
  assert (forall `{Proset Y} {F : Ix T -> Y}, Functor F) as ix_T_functor by move=> Y ? F A B <- //.
  split.
  - transitivity (multiply (fp_map colim (fp_zipwith
                 (fun F i => ap_Hom F ∘ eval_at i ∘ index) J (tabulate id)))). {
      apply/fmap'; rewrite fp_map_zipwith /fp_map /fp_zipwith /=; apply fmap' => i /=.
      apply/colim_left => r; setoid_rewrite <- (colim_right _ (fp_pure T r)); simpl.
      rewrite cancel /= cancel //.
    }
    unshelve erewrite @multiply_natural; only 1,4: typeclasses eauto. 2: {
      apply/fmap' => rs.
      rewrite /=; etransitivity; first by apply (multiply_natural (F:=eval_at rs)).
      apply fmap'; rewrite fp_map_zipwith /= /fp_zipwith /=.
      apply fmap' => i; rewrite cancel //.
    }




    etransitivity. {
      apply/multiply_functor.
      instantiate (1 := fp_map (fun iF : Ix T * Hom R X => colim (iF.2 ∘ eval_at iF.1 ∘ index))
                               (fp_zipwith pair (tabulate id) J)).
      rewrite /fp_map /fp_zipwith /=; apply fmap' => i /=.
      apply/colim_left => r; setoid_rewrite <- (colim_right _ (fp_pure T r)); simpl.
        by setoid_rewrite <- (adj_unit (Adjoint:=tabulate_index_adj) _ _).
    }
    etransitivity. {
      unshelve eapply multiply_natural.
      - typeclasses eauto.
      - move=> [A1 A2] [B1 B2] /= [D1 D2]; apply fmap' => Rs /=.
        setoid_rewrite D1; by setoid_rewrite D2.
      - give_up.
      - constructor; constructor=> //=.
        + give_up.
        + give_up.
        + give_up.
        + move=> [A1 A2] [B1 B2] /=.
          apply/colim_left => Rs /=.
          setoid_rewrite <- (colim_right _ Rs); simpl.
          give_up.
    }
    apply fmap' => Rs /=.
    apply/colim_l


    rewrite /= /fp_zipwith. /ext_tens. simpl.


    simpl.
    assert (OplaxMon (colim ∘ ap_Hom (X:=R) (Y:=X))) as H by give_up.
    generalize (multiply_natural_oplax (OplaxMon0:=H) (L:=J)) => /= E.
    rewrite E; apply/colim_left => r. apply fmap'.
  - rewrite /= /fp_zipwith /fp_map /=.
    apply/colim_left => rs /=.
    apply fmap', fmap' => i.
    apply/colim_right.
Qed.
Lemma foo : forall `{Quantale X, FinPow T} {R} {J : R -> X},
    pow T (colim J) ⟛ colim (fun rs : T R => multiply (fp_map J rs)).
Proof.
  move=> X ? ? ? ? ? ? T ? ? R J; split.
  - set r_discrete : Proset R := {| pro_le := eq |}.
    assert (forall `{Proset Y} {F : R -> Y}, Functor F) as r_functor by move=> Y ? F A B <- //.


    (*
    evar (L : T X).
    generalize (multiply_natural (F:=mon_coyo) (StrongMon0:=mon_coyo_strongmon) (L:=L)).
     *)



    etransitivity. 2: {
      apply/colim_functor => rs.
      apply/(fmap' (F:=multiply))/(proj1 (fp_zipwith_pure_l (F:=ap_Hom) (A:=in_Hom J))).
    }
    change (fun rs => _) with (ap_Hom (ext_tens (fp_pure T (in_Hom J)))).
    rewrite /pow /compose.
    fold ext_tens.
    rewrite -[multiply _]/(ext_tens _).

    etransitivity. 2: {
      apply/colim_functor => rs.
      generalize (multiply_natural (F:=list_sharp (J ∘ get_discrete))
                                   (L:=fp_map (mret ∘ Discrete) rs)).
      rewrite -[fp_map _ (fp_map _ rs)](pw_core fp_map_compose rs) => E.
      rewrite {1}/list_sharp {1}/compose /= in E.
      apply: (proj2 E).
    }
    rewrite /list_sharp /=.
    have H : Cocontinuous tens_all' by give_up.
    etransitivity; last by apply (proj1 (distrib_colim (Cocontinuous0:=H) _)).
    setoid_rewrite <- distrib_colim.
    rewrite /list_sharp.


    generalize (adj_counit (Adjoint:=index_tabulate_adj)
                           (mret (M:=list) ∘ Discrete ∘ index ?L)) => /= E.
    setoid_rewrite E in D2; rewrite {4}/compose /= in D2.
    generalize (multiply_natural (T:=T) (F:=const (B:=nat)) (L:=fp_map J L)).
    give_up.
  - rewrite /pow /fp_map /=.
    apply/colim_left => rs.
    apply fmap', fmap' => i /=.
    apply/colim_right.
Qed.
*)


Definition PSh (X : Type) `{Proset X} : Type := Hom (op X) Prop.
Identity Coercion psh_to_hom : PSh >-> Hom.
(*
Lemma psh_ext : forall `{Proset X} {F G : PSh X}, (forall A, F A <-> G A) <-> F = G.
Proof. setoid_rewrite <- Hom_ext; firstorder using Axioms.prop_ext. Qed.
*)

Lemma pfunctorial : forall `{Proset X} {F : PSh X} {A B : op X},
    A ⊢ B -> F A -> F B.
Proof. move=> X Pr F A B; apply: (functorial F). Qed.
Hint Resolve pfunctorial.

Program Definition yo `{Proset X} (A : X) : PSh X :=
  fun B => Op A ⊢ B.
Next Obligation. move=> * ? * ?; by etransitivity. Qed.
Lemma yoneda : forall `{Proset X} {A : X} {F : PSh X}, yo A ⊢ F <-> F (Op A).
Proof.
  move=> X ND A F; split.
  - apply; by simpl.
  - move=> FA A' D; by apply: pfunctorial FA.
Qed.
Instance yo_functor `{Proset X} : Functor (yo (X:=X)).
Proof. move=> * [?] /= ?; by etransitivity. Qed.
Instance yo_full `{Proset X} : Full (yo (X:=X)).
Proof. move=> A B /(_ (Op A)) /=; by apply. Qed.
Instance yo_continuous `{Proset X} : Continuous (yo (X:=X)).
Proof.
  move=> R A J [C U]; split=> [r | A' C'] [B] /=.
  - move=> D; by etransitivity.
  - move=> /yoneda D; apply: U => r; apply/yo_full; etransitivity; firstorder.
Qed.
Definition representable `{Proset X} (F : PSh X) : Prop :=
  exists A, F ⟛ yo A.

Definition opped {X Y} (F : X -> Y) : op X -> op Y
  := Op ∘ F ∘ get_op.
Arguments opped {_ _} _ /.
Instance opped_functor `{Functor X Y F} : Functor (opped F).
Proof. move=> [A] [B] /=; apply/fmap'. Qed.
Instance opped_proper `{Proset X, Proset Y}
  : Proper (pro_le --> pro_le) (opped (X:=X) (Y:=Y)).
Proof. move=> F F' D [A] //=. Qed.
Instance opped_proper' `{Proset X, Proset Y}
  : Proper (pro_le ++> flip pro_le) (opped (X:=X) (Y:=Y)).
Proof. move=> F F' D [A] //=. Qed.
Definition psh_subst `{Proset X, Proset Y} (F : Hom X Y) : Hom (PSh Y) (PSh X)
  := in_Hom (.○ in_Hom (opped F)).
Arguments psh_subst {_ _ _ _} F /.
Lemma psh_subst_id : forall `{Proset X}, psh_subst Hom_id ⟛ Hom_id (X:=PSh X).
Proof. move=> X ?; apply/pw_core' => P; apply/Hom_core => -[A] //=. Qed.
Lemma psh_subst_compose : forall `{Proset X, Proset Y} {Z} `{Proset Z}
                            {F : Hom Y Z} {G : Hom X Y},
    psh_subst (F ○ G) ⟛ psh_subst G ○ psh_subst F.
Proof. move=> X ? Y ? Z ? F G; apply/pw_core' => P; apply/Hom_core => -[A] //=. Qed.

(* PSh as a free cocompletion. *)
Definition yo_extend `{Proset X, Complete Y} : (X -> Y) -> Hom (PSh X) Y
  := universal_lan yo.
Arguments yo_extend {_ _ _ _ _} _ /.
Definition yo_restrict `{Proset X, Proset Y} : Hom (PSh X) Y -> Hom X Y
  := (.○ in_Hom yo).
Arguments yo_restrict {_ _ _ _} _ /.
Lemma yo_extend_transpose : forall `{Proset X, Complete Y} {F : Hom X Y} {G : Hom (PSh X) Y},
    yo_extend F ⊢ G <-> F ⊢ yo_restrict G.
Proof. move=> *; apply: (transpose (Adj:=universal_lan_global_lan)). Qed.
(* These next four lemmas are "primitive". From them, we can derive the rest of the
   adjunction by reasoning that applies in any categories. *)
Definition yo_preimage `{Proset X, Proset Y} (F : Hom X Y) : Hom Y (PSh X)
  := yo_restrict (psh_subst F).
Arguments yo_preimage {_ _ _ _} F /.
Instance yo_extend_yo_preimage_adjoint `{Proset X, Complete Y} {F : X -> Y} `{!Functor F}
  : yo_extend F ⊣ yo_preimage (in_Hom F).
Proof.
  constructor.
  - move=> P [A] /= /yoneda PA; apply/(colim_right _ (A ↾ PA)).
  - move=> B /=; apply/colim_left => -[A /= D]; by apply: (D (Op A)).
Qed.
Lemma yo_extend_natural_post : forall `{Proset X, Complete Y, Complete Y'}
                                 {F : Hom Y Y'} {G : X -> Y} `{!Cocontinuous F},
    yo_extend (F ∘ G) ⟛ F ○ yo_extend G.
Proof.
  move=> X ? Y ? ? Y' ? ? F G ?; apply/Hom_core => P /=.
  symmetry; apply/distrib_colim.
Qed.
Lemma yo_restrict_extend : forall `{Proset X, Complete Y} {F : Hom X Y},
    yo_restrict (yo_extend F) ⟛ F.
Proof.
  move=> X Pr_X Y Pr_Y ? F; split=> A.
  - apply/colim_left => -[A' D] /=; apply/fmap'/yo_full/D.
  - by unshelve apply/(colim_right _ (_↾ _)).
Qed.
Lemma yo_extend_restrict : forall `{Proset X, Complete Y} {F : Hom (PSh X) Y}
                             `{!Cocontinuous F},
    yo_extend (yo_restrict F) ⟛ F.
Proof.
  move=> X ? Y ? ? F; split=> P.
  - apply/colim_left => -[A D] /=; apply/fmap'/D.
  - simpl; setoid_rewrite <- (proj1 (distrib_colim _)).
    apply/fmap' => -[A] /= /yoneda PA; by exists (A ↾ PA).
Qed.

Instance yo_extend_full `{Proset X, Complete Y} : Full (X:=Hom X Y) yo_extend.
Proof.
  move=> F G /(fmap' (F:=yo_restrict)) D.
  setoid_rewrite yo_restrict_extend in D at 2.
    by setoid_rewrite <- (proj2 yo_restrict_extend) in D.
Qed.
Instance yo_restrict_full `{Proset X, Complete Y} : Full (yo_restrict (X:=X) (Y:=Y)).
Proof.
  move=> F G /(fmap' (F:=yo_extend)) D.
Abort. (* dammit *)
Definition psh_map `{Proset X, Proset Y} (F : X -> Y) : Hom (PSh X) (PSh Y)
  := yo_extend (yo_restrict Hom_id ∘ F).
Arguments psh_map {_ _ _ _} F /.
Lemma yo_restrict_natural_post : forall `{Proset X, Proset Y, Proset Y'}
                                   {F : Hom Y Y'} {G : Hom (PSh X) Y},
    yo_restrict (F ○ G) ⟛ F ○ yo_restrict G.
Proof. by compute. Qed.
Lemma yo_extend_natural_pre : forall `{Proset X, Proset Y, Complete Y'}
                                {F : Hom Y Y'} {G : X -> Y},
    yo_extend (F ∘ G) ⟛ yo_extend F ○ psh_map G.
Proof.
  move=> X ? Y ? Y' ? ? F G; unfold psh_map.
  rewrite -yo_extend_natural_post; apply/fmap_core.
  change (F ∘ G ⟛ yo_restrict (yo_extend F) ∘ G).
  apply/(fmap_core (F:=(.∘ G)))/(symmetry yo_restrict_extend).
Qed.
Lemma yo_restrict_natural_pre : forall `{Proset X, Proset Y, Complete Y'}
                                  {F : Hom (PSh Y) Y'} {G : Hom X Y} `{!Cocontinuous F},
    yo_restrict (F ○ psh_map G) ⟛ yo_restrict F ○ G.
Proof.
  move=> X ? Y ? Y' ? ? F G ?.
  apply/(unfmap_core (H1:=yo_extend_full)).
  rewrite yo_extend_restrict yo_extend_natural_pre.
  apply/(fmap_core (F:=(.○ psh_map G)))/(symmetry yo_extend_restrict).
Qed.
Lemma psh_map_id : forall `{Proset X}, psh_map id ⟛ Hom_id (X:=PSh X).
Proof. move=> X ?; unfold psh_map; rewrite yo_extend_restrict //. Qed.
Lemma psh_map_compose : forall `{Proset X, Proset Y} {Z} `{Proset Z}
                          {F : Hom Y Z} {G : X -> Y},
    psh_map (F ∘ G) ⟛ psh_map F ○ psh_map G.
Proof.
  move=> X ? Y ? Z ? F G.
  unfold psh_map; rewrite -yo_extend_natural_post; apply/fmap_core.
  change (yo_restrict Hom_id ○ F ∘ G ⟛
                      yo_extend (yo_restrict Hom_id ○ F) ○ yo_restrict Hom_id ∘ G).
  apply/(fmap_core (F:=(.∘ G))).
  rewrite -yo_restrict_natural_post Hom_id_rident; symmetry; apply: yo_restrict_extend.
Qed.
(* hmm. *)
Lemma psh_map_alt : forall `{Proset X, Proset Y} {F : X -> Y},
    psh_map F ⟛ in_Hom (universal_lan (opped F) : PSh X -> PSh Y).
Proof.
  move=> X ? Y ? F; apply/pw_core' => P; split=> -[B] /=.
  - move=> [[A /= /yoneda PA] D]; by unshelve eexists (Op A ↾ _).
  - move=> [[[A] /= D] /yoneda PA]; by unshelve eexists (A ↾ _).
Qed.
Instance psh_map_psh_subst_adjoint `{Proset X, Proset Y} {F : Hom X Y}
  : psh_map F ⊣ psh_subst F.
Proof.
  pose proof (universal_lan_global_lan : _ ⊣ psh_subst F).
  constructor=> A.
  - setoid_rewrite <- (proj2 psh_map_alt); apply/adj_unit.
  - rewrite psh_map_alt; apply/adj_counit.
Qed.

(* TODO Move these. *)
Instance adjoint_proper `{Proset X, Proset Y}
  : Proper ((core pro_le ==> core pro_le) ==> (core pro_le ==> core pro_le) ==> impl)
           (Adjoint (X:=X) (Y:=Y)).
Proof.
  move=> F F' E_F G G' E_G Adj; constructor=> A /=.
  - etransitivity.
    + apply: (adj_unit (Adjoint:=Adj)).
    + by apply E_G, E_F.
  - etransitivity.
    + by apply E_F, E_G.
    + apply: (adj_counit (Adjoint:=Adj)).
Qed.
Instance adjoint_proper' `{Proset X, Proset Y}
  : Proper ((core pro_le ==> core pro_le) ==> (core pro_le ==> core pro_le) ==> iff)
           (Adjoint (X:=X) (Y:=Y)).
Proof. eapply proper_sym_impl_iff_2; [firstorder | firstorder | typeclasses eauto]. Qed.
Lemma functor_core : forall `{Proset X, Proset Y} {F G : X -> Y} `{!Functor F, !Functor G},
    F ⟛ G <-> (core pro_le ==> core pro_le)%signature F G.
Proof.
  move=> X ? Y ? F G ? ?; split.
  - move=> E A A' E_A; rewrite E_A E //.
  - move=> E; apply/pw_core' => A; by apply: E.
Qed.
Definition unyo `{Complete X} : PSh X -> X
  := yo_extend Hom_id.
Arguments unyo {_ _ _} _ /.
(* TODO Derive this from above results. *)
Instance unyo_yo_adjoint `{Complete X} : unyo (X:=X) ⊣ yo.
Proof.
  constructor.
  - move=> P [A] /= /yoneda PA; apply/(colim_right _ (A ↾ PA)).
  - move=> A /=; apply/colim_left => -[A' D] /=; by apply: (D (Op A')).
Qed.
Lemma unyo_yo_id : forall `{Complete X}, unyo ∘ yo ⟛ @id X.
Proof. move=> *; apply: full_right_adjoint. Qed.
Definition closure `{Complete X} : PSh X -> PSh X
  := yo ∘ unyo.
Arguments closure {_ _ _} _ /.
Fact closure_monad `{Complete X} : Monad (closure (X:=X)).
Proof. typeclasses eauto. Qed.
Lemma closure_alg_rep : forall `{Complete X} {P : PSh X} `{!Alg closure P},
    representable P.
Proof. move=> X ? ? P ?; exists (unyo P); apply/(alg_fixed_point (M:=closure)). Qed.
Lemma rep_closure_alg : forall `{Complete X} {P : PSh X},
    representable P -> Alg closure P.
Proof. move=> X ? ? P [A E]; apply/(Alg_proper _ _ E). Qed.
Lemma coyoneda : forall `{Proset X}, yo_extend (in_Hom yo) ⟛ Hom_id (X:=PSh X).
Proof. move=> *; apply: (yo_extend_restrict (F:=Hom_id)). Qed.
Lemma coyoneda' : forall `{Proset X} {P : PSh X},
    P ⟛ colim (fun A : {A0 | yo A0 ⊢ P} => yo (`A)).
Proof. move=> *; symmetry; apply: (proj2 Hom_core coyoneda). Qed.

Definition psh_mapr `{Proset X, Proset Y} (F : X -> Y) : PSh X -> PSh Y
  := universal_ran (opped F).
Arguments psh_mapr {_ _ _ _} F _ /.
Instance psh_subst_psh_mapr_adjoint `{Proset X, Proset Y} {F : X -> Y} `{!Functor F}
  : psh_subst (in_Hom F) ⊣ psh_mapr F.
Proof. apply/universal_ran_global_ran. Qed.
(* TODO
Lemma psh_mapr_alt : forall `{Functor X Y F} {P : PSh X},
    psh_mapr F P ⟛ ... *)
Lemma restrict_psh_map : forall `{Proset X, Proset Y} {F : Hom X Y},
    yo_restrict (psh_map F) ⟛ yo_restrict Hom_id ○ F.
Proof. move=> *; apply: (yo_restrict_extend (F:=in_Hom _)). Qed.
Lemma psh_map_yo : forall `{Functor X Y F} {A},
    psh_map F (yo A) ⟛ yo (F A).
Proof. move=> X ? Y ? F ?;  apply/pw_core/(restrict_psh_map (F:=in_Hom F)). Qed.
Lemma psh_map_representable : forall `{Functor X Y F} {P},
    representable P -> representable (psh_map F P).
Proof. move=> X ? Y ? F ? P [B H]; eexists; rewrite H psh_map_yo //. Qed.

Lemma yo_colim : forall `{Complete X} {R} {J : R -> X},
    yo (colim J) ⟛ closure (colim (yo ∘ J)).
Proof.
  move=> *.
  apply/fmap_core; rewrite distrib_colim; apply/fmap_core.
  apply/pw_core' => ?; symmetry; apply/(pw_core unyo_yo_id).
Qed.
Lemma yo_colim2 : forall `{Complete X} {R} {J : R -> X},
    colim (yo ∘ J) ⟛ yo (colim J) <-> representable (colim (yo ∘ J)).
Proof.
  move=> X ? ? Y A; split=> [| /rep_closure_alg Rep]; first by eexists.
  rewrite yo_colim; apply/alg_fixed_point.
Qed.
Lemma bicomplete_rep : forall `{Complete X} {P : PSh X},
    representable P <-> Continuous P.
Proof.
  move=> X ? ? P; split.
  - move=> [A E]; apply/distrib_lim_sufficient => R J.
    setoid_rewrite E at 1; setoid_rewrite <- (proj2 (proj2 Hom_core E _)).
    apply: colim_left.
  - move=> Cont; exists (unyo P); enough (Alg closure P) by apply/(alg_fixed_point (M:=closure)).
    apply/yoneda/((distrib_lim (F:=P) (Op ∘ sval))) => -[A /yoneda D] //=.
Qed.

Program Definition day `{MonSet X} (F G : PSh X) : PSh X :=
  fun A => exists A1 A2, A1 ⊗ A2 ⊢ A /\ F A1 /\ G A2.
Next Obligation.
  move=> X Pr SMS F G A B D [A1] [A2] [Cov_A] [F_A1] G_A2.
  exists A1, A2; intuition by etransitivity.
Qed.
Lemma day_alt : forall `{MonSet X} {F G : PSh X},
    day F G ⟛ gday2 F G.
Proof.
  move=> X ? ? F G; split=> A /=.
  - move=> [A1] [A2] /= [Cov] [F_A1] G_A2; by (exists ((A1, A2) ↾ Cov)).
  - move=> [[As /= Cov] [F_A1 G_A2]]; eauto.
Qed.
Lemma day_unit_alt : forall `{MonSet X},
    yo (X:=X) memp ⟛ gday2_memp.
Proof. firstorder. Qed.
Instance day_monoidal `{MonSet X} : Monoidal pro_le (day (X:=X)) (yo memp).
Proof.
  constructor.
  - setoid_rewrite day_alt at 1; setoid_rewrite <- (proj2 day_alt).
    eapply @bimap; typeclasses eauto.
  - setoid_rewrite day_alt; setoid_rewrite day_unit_alt; apply: lunit.
  - setoid_rewrite day_alt; setoid_rewrite day_unit_alt; apply: runit.
  - setoid_rewrite day_alt; setoid_rewrite day_alt; apply: massoc.
Qed.
Instance day_sym `{SymMonSet X} : Sym pro_le (day (X:=X)).
Proof.
  move=> F G A [A1] [A2] [Cov] [F_A1] G_A2.
  exists A2, A1; split; last by done.
  etransitivity; [apply sym | done].
Qed.
Instance psh_mset `{MonSet X} : MonSet (PSh X)
  := {| pro_tens := day |}.
Instance psh_smset `{SymMonSet X} : SymMonSet (PSh X) := {}.
Instance yo_strongmon `{MonSet X} : StrongMon (yo (X:=X)).
Proof.
  constructor; constructor=> [| A B] [C] //=.
  - move=> [A1] [A2] [Cov] [D1] D2; by eapply transitivity, bimap.
  - move=> D; by exists (Op A), (Op B).
Qed.

Program Definition day_hom `{MonSet X} (F G : PSh X) : PSh X :=
  fun A => forall A1 A2, A ⊗ A1 ⊢ A2 -> F A1 -> G A2.
Next Obligation.
  move=> X Pr MS F G A B D H A1 A2 Cov F_A1.
  apply: H.
  - by setoid_rewrite D.
  - done.
Qed.
Instance day_closed_monoidal `{MonSet X}
  : ClosedMonoidal pro_le (day (X:=X)) day_hom.
Proof.
  move=> F G H'; split.
  - move=> Curried A FA A1 A2 Cov G_A1.
    apply: Curried => /=; exists A, A1; by split; last split.
  - move=> Uncurried A /= [A1] [A2] [Cov] [F_A1] G_A2.
      by apply: Uncurried.
Qed.
Program Definition day_l_hom `{MonSet X} (F G : PSh X) : PSh X :=
  fun A => forall A1 A2, A1 ⊗ A ⊢ A2 -> F A1 -> G A2.
Next Obligation.
  move=> X Pr MS F G A B D H A1 A2 Cov F_A1.
  apply: H.
  - by setoid_rewrite D.
  - done.
Qed.
Instance day_l_closed_monoidal `{MonSet X}
  : LClosedMonoidal pro_le (day (X:=X)) day_l_hom.
Proof.
  move=> F G H'; split.
  - move=> Curried A FA A1 A2 Cov G_A1.
    apply: Curried => /=; exists A1, A; by split; last split.
  - move=> Uncurried A /= [A1] [A2] [Cov] [F_A1] G_A2.
      by apply: Uncurried.
Qed.
Instance psh_cmset `{MonSet X} : ClosedMonSet (PSh X) := {}.
Instance psh_lcmset `{MonSet X} : LClosedMonSet (PSh X) := {}.
Instance psh_quantale `{MonSet X} : Quantale (PSh X) := {}.

Program Definition psh_conj `{Proset X} (F G : PSh X) : PSh X
  := fun A => F A /\ G A.
Next Obligation. move=> X ? F G A B /= D; eapply bimap; by apply/fmap'. Qed.
Program Definition psh_disj `{Proset X} (F G : PSh X) : PSh X
  := fun A => F A \/ G A.
Next Obligation. move=> X ? F G A B /= D; eapply bimap; by apply/fmap'. Qed.
Lemma psh_product : forall `{Proset X} {F G : PSh X},
    F × G ⟛ psh_conj F G.
Proof.
  split.
  - move=> ? /= Prod; by move: (Prod true) (Prod false).
  - apply/product_right; firstorder.
Qed.
Lemma psh_coproduct : forall `{Proset X} {F G : PSh X},
    F + G ⟛ psh_disj F G.
Proof.
  split.
  - apply/coproduct_left; firstorder.
  - by move=> ? /= [Disj1 | Disj2]; [exists true | exists false].
Qed.

Example app_eq_inv_plusplus : forall `{Proset X} {P Q P' Q' : PSh (list X)},
    P ⊗ Q × P' ⊗ Q' ⟛
      colim (fun m => (P × P' ⊗ yo m) ⊗ (Q × (yo m ⊸̂ Q')) +
                   (P × (yo m ⊸ P')) ⊗ (Q × yo m ⊗ Q')).
Proof.
  move=> X ? P Q P' Q'.
  split.
  - rewrite psh_product; setoid_rewrite <- (fmap' (F:=colim)). 2: {
      move=> m.
      setoid_rewrite <- (proj2 psh_product) at 2 3 4 5 6.
      setoid_rewrite <- (proj2 psh_coproduct) at 2.
      eapply reflexivity.
    }
    move=> [L] /= [[[Ps]]]  [[Qs]]  /= [Cov]  [PPs]   QQs
                 [[P's]]   [[Q's]] /= [Cov'] [P'P's] Q'Q's.
    move: Cov Cov' => /Forall2_app_inv_r [Ps0]  [Qs0]  [D_Ps]  [D_Qs]  E_L
                     /Forall2_app_inv_r [Ps'0] [Qs'0] [D_Ps'] [D_Qs'].
    change (Forall2 pro_le ?A ?B) with (A ⊢ B) in *.
    subst L => /app_eq_inv [] [m] [?] ?; subst; exists m.
    + left; exists (Op (Ps'0 ++ m)), (Op Qs0); repeat split; try done.
      * by setoid_rewrite D_Ps.
      * eexists _, _; repeat split; try done; by apply/bimap.
      * by setoid_rewrite D_Qs.
      * move=> [m0] [Q's00] /= D1 D2.
        setoid_rewrite D1; setoid_rewrite D2; by setoid_rewrite D_Qs'.
    + right; exists (Op Ps0), (Op (m ++ Qs'0)); repeat split; try done.
      * by setoid_rewrite D_Ps.
      * move=> [m0] [Q's00] /= D1 D2.
        setoid_rewrite D1; setoid_rewrite D2; by setoid_rewrite D_Ps'.
      * by setoid_rewrite D_Qs.
      * eexists _, _; repeat split; try done; by apply/bimap.
  - apply/colim_left => m; apply/coproduct_left; apply/product_right.
    + by setoid_rewrite product_left1.
    + setoid_rewrite product_left2.
      rewrite -pro_massoc; by setoid_rewrite l_mon_modus_ponens.
    + by setoid_rewrite product_left1.
    + setoid_rewrite product_left2.
      rewrite pro_massoc; by setoid_rewrite mon_modus_ponens.
Qed.

Lemma act_map : forall `{Proset E, Proset X} (F : E -> Endo X) `{!Functor F} {M N A},
    M ⊢ N -> F M A ⊢ F N A.
Proof. move=> ? ? ? ? F *; by apply: (fmap' (F:=F)). Qed.

(* The left and right regular actegories. *)
Definition lreg `{MonSet X} (A : X) : Endo X := in_Hom (pro_tens A).
Instance lreg_functor `{MonSet X} : Functor (lreg (X:=X)).
Proof. move=> A A' D B /=; by apply bimap. Qed.
Instance lreg_strongmon `{MonSet X} : StrongMon (lreg (X:=X)).
Proof.
  constructor; constructor=> [A | A B C] /=.
  - apply pro_lunit.
  - apply pro_massoc.
  - apply pro_lunit.
  - apply pro_massoc.
Qed.
Definition sig_lreg `{MonSet X} {P : X -> Prop} `{!MonClosed P} : sig P -> Endo X
  := lreg ∘ sval.
Definition rreg `{MonSet X} (B : X) : Endo X := in_Hom (r_tensor B).
Instance rreg_functor `{MonSet X} : Functor (rreg (X:=X)).
Proof. move=> B B' D A /=; by apply bimap. Qed.
Instance rreg_strongmon `{SymMonSet X} : StrongMon (rreg (X:=X)).
Proof.
  constructor; constructor=> [A | A B C] /=.
  - apply pro_runit.
  - setoid_rewrite <- pro_massoc; by setoid_rewrite (pro_sym B A).
  - apply pro_runit.
  - setoid_rewrite <- (proj1 (pro_massoc C B A)); by setoid_rewrite (pro_sym A B).
Qed.


Definition DProp : Type := sigT Decision.
Coercion dtag := tag : DProp -> Prop.
Arguments dtag _ /.
Instance dprop_decision {P : DProp} : Decision (tag P) := tagged P.
Definition in_DProp (P : Prop) `{H : !Decision P} : DProp := existT P H.
Definition pro_dprop : DProp -> DProp -> Prop :=
  fun s1 s2 => dtag s1 ⊢ dtag s2.
Arguments pro_dprop !_ !_ /.
Instance pro_dprop_pro : PreOrder pro_dprop.
Proof. firstorder. Qed.
Instance dprop_proset : Proset DProp := {| pro_le := pro_dprop |}.
Definition tens_dprop (s1 s2 : DProp) : DProp
  := in_DProp (dtag s1 ⊗ dtag s2).
Arguments tens_dprop !_ !_ /.
Instance tens_dprop_monoidal :
  Monoidal pro_le tens_dprop (in_DProp memp).
Proof. compute; firstorder. Qed.
Instance dprop_sym : Sym pro_le tens_dprop.
Proof. compute; firstorder. Qed.
Instance dprop_mset : MonSet DProp := {| pro_tens := tens_dprop |}.
Instance dprop_smset : SymMonSet DProp := {}.
Instance dtag_functor : Functor dtag.
Proof. firstorder. Qed.
Instance dtag_full : Full dtag.
Proof. firstorder. Qed.
Instance dtag_strongmon : StrongMon dtag.
Proof. compute; firstorder. Qed.
Notation Omniscient R := (DInfsOfShape R DProp).

Lemma dtag_continuous : forall {R} {J : R -> DProp} `{!HasInf J},
    dtag (inf J) <-> all (dtag ∘ J).
Proof.
  move=> R J ?; split=> H.
  - move=> r /=; by apply: (proj1 (is_inf J) r).
  - have ? : Decision (all (dtag ∘ J)) by constructor.
    apply: (proj2 (is_inf J) (in_DProp (all (dtag ∘ J)))); firstorder.
Qed.
Definition omniscient_alt1 `{Omniscient R} : forall (P : R -> DProp), Decision (all P)
  := fun P =>
       match tagged (inf P) with
       | left H => left (proj1 dtag_continuous H)
       | right H => right (H ∘ proj2 dtag_continuous)
       end.
Program Definition omniscient_alt2 {R} (AllDec : forall (P : R -> DProp), Decision (all P))
  : Omniscient R
  := fun P => {| inf := in_DProp (all P) |}.
Next Obligation. move=> *; by apply: (undistrib_inf (F:=dtag)). Qed.

(*
CoInductive conat := coO | coS (u : conat).
Instance conat_omniscient' {P : conat -> DProp} : Decision (all P).
 (∀ P : conat → DProp, Decision (all (λ x : conat, P x))).
Program Instance conat_omniscient : Omniscient conat := omniscient_alt2 _.
  := fun J _ => {| inf := ⊥ |}.
Proof.
  constructor.
Qed.
*)


Class Profunctor {X Y} `{Proset X, Proset Y} (P : X -> Y -> Prop) :=
  dimap : forall {A' A B B'}, A' ⊢ A -> B ⊢ B' -> P A B -> P A' B'.
Hint Mode Profunctor ! ! - - ! : typeclass_instances.
Definition lmap `{Profunctor X Y P} {A' A : X} {B : Y} (H : A' ⊢ A) : P A B -> P A' B :=
  dimap H (reflexivity _).
Definition rmap `{Profunctor X Y P} {A} {B B'} (H : B ⊢ B') : P A B -> P A B' :=
  dimap (reflexivity _) H.
(* TODO Double check that I haven't spuriously dropped conditions that still exist
        in the proset case!!!! *)
Class Tambara {E X Y} `{!Proset X, !Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
      (P : X -> Y -> Prop) :=
  tamb : forall M {A B}, P A B -> P (L M A) (R M B).
Arguments tamb {_ _ _ _ _} L R {_ _} M {_ _}.
Hint Mode Tambara ! ! ! - - ! ! ! : typeclass_instances.

Lemma pro_core : forall {X Y} {P Q : X -> Y -> Prop},
    P ⟛ Q -> (forall A B, P A B <-> Q A B).
Proof. firstorder. Qed.
Lemma pro_core' : forall {X Y} {P Q : X -> Y -> Prop},
    P ⟛ Q <-> (forall A B, P A B <-> Q A B).
Proof. firstorder. Qed.

Instance profunctor_proper `{Profunctor X Y P} : Proper (pro_le --> pro_le ++> impl) P.
Proof. move=> ? ? ? ? ? ?; by apply: dimap. Qed.
Instance profunctor_proper' `{Profunctor X Y P}
  : Proper (pro_le ++> pro_le --> flip impl) P.
Proof. move=> ? ? ? ? ? ?; by apply: dimap. Qed.
Instance profunctor_proper_core `{Profunctor X Y P}
  : Proper (core pro_le ==> core pro_le ==> iff) P.
Proof. move=> ? ? [? ?] ? ? [? ?]; split; by apply: dimap. Qed.
Instance profunctor_proper_core' `{Profunctor X Y P}
  : Proper (core pro_le --> core pro_le --> iff) P.
Proof. move=> ? ? [? ?] ? ? [? ?]; split; by apply: dimap. Qed.

(* TODO This is an instance of something more general... *)
Instance tambara_compose `{Tambara E X Y L R P} {E'} {F : E' -> E}
  : Tambara (L ∘ F) (R ∘ F) P | 1.
Proof. move=> M A B /(tamb L R (F M)) //. Qed.
Lemma tambara_triple `{Proset E, Proset E', Proset X, Proset Y}
      {L : E -> Endo X} {R : E -> Endo Y} `{!Functor L, !Functor R}
      {Ψ_L : E' -> E} {Ψ_R : E' -> E} {Φ : E -> E'}
      `{!Φ ⊣ Ψ_L, !Ψ_R ⊣ Φ, !Functor Ψ_L, !Functor Ψ_R, !Functor Φ}
      `{!Tambara (L ∘ Ψ_L) (R ∘ Ψ_R) P, !Profunctor P}
  : Tambara L R P.
Proof.
  move=> M A B /(tamb _ _ (Φ M)); apply dimap; simpl.
  + apply/act_map/adj_unit.
  + apply/act_map/adj_counit.
Qed.

Instance tambara_rreg_rreg `{SymMonSet X} {P : X -> X -> Prop}
         `{!Profunctor P, !Tambara lreg lreg P}
  : Tambara rreg rreg P | 1.
Proof.
  move=> M A B PAB /=.
  apply: dimap; only 1,2: apply: sym.
    by apply: tamb.
Qed.
Instance tambara_lreg_rreg `{SymMonSet X} {P : X -> X -> Prop}
         `{!Profunctor P, !Tambara lreg lreg P}
  : Tambara lreg rreg P.
Proof.
  move=> M A B PAB /=.
  apply: rmap; first by apply: sym.
    by apply: tamb.
Qed.
Instance tambara_rreg_lreg `{SymMonSet X} {P : X -> X -> Prop}
         `{!Profunctor P, !Tambara lreg lreg P}
  : Tambara rreg lreg P.
Proof.
  move=> M A B PAB /=.
  apply: lmap; first by apply: sym.
    by apply: tamb.
Qed.

Instance hom_profunctor `{Proset X} : Profunctor (pro_le (X:=X)).
Proof. move=> A' A B B' H1 H2 H3; by etransitivity; first etransitivity. Qed.
Instance hom_tambara_F_F {E} `{Proset X} {F : E -> Endo X} : Tambara F F pro_le | 0.
Proof. move=> * /=; by apply fmap'. Qed.

Definition first `{SymMonSet X} `{!Profunctor P, !Tambara lreg lreg P}
           F {A B} (m : P A B) : P (A ⊗ F) (B ⊗ F)
  := tamb rreg rreg F m.
Definition second `{MonSet X} `{!Profunctor P, !Tambara lreg lreg P}
           F {A B : X} (m : P A B) : P (F ⊗ A) (F ⊗ B)
  := tamb lreg lreg F m.

Definition conjugate `{Proset E, Proset X, Proset X'}
         (L : E -> Endo X) `{!Functor L}
         (F : X' -> X) (G : X -> X') `{!Functor F, !Functor G}
         (M : E) : Endo X'
  := in_Hom (G ∘ L M ∘ F).
Instance conjugate_functor `{Proset E, Proset X, Proset X'}
         {L : E -> Endo X} `{!Functor L}
         {F : X' -> X} {G : X -> X'} `{!Functor F, !Functor G}
  : Functor (conjugate L F G).
Proof. move=> M1 M2 D B /=; apply/fmap'/act_map/D. Qed.
Instance conjugate_laxmon `{MonSet E, Proset X, Proset X'}
         {L : E -> Endo X} `{!Functor L, !LaxMon L}
         {F : X' -> X} {G : X -> X'} `{!F ⊣ G, !Functor F, !Functor G}
  : LaxMon (conjugate L F G).
Proof.
  constructor=> [B | M1 M2 B] /=.
  - apply transpose; apply: (pres_memp (F:=L)).
  - apply/fmap'.
    setoid_rewrite <- pres_tens; simpl; by apply fmap', transpose.
Qed.
Instance conjugate_oplaxmon `{MonSet E, Proset X, Proset X'}
         {L : E -> Endo X} `{!Functor L, !OplaxMon L}
         {F : X -> X'} {G : X' -> X} `{!F ⊣ G, !Functor F, !Functor G}
  : OplaxMon (conjugate L G F).
Proof.
  constructor=> [B | M1 M2 B] /=.
  - apply transpose; apply: (pres_memp_op (F:=L)).
  - apply/fmap'.
    setoid_rewrite pres_tens_op; simpl; by apply fmap', transpose.
Qed.

Definition pro_compose {X Y Z} (P : X -> Y -> Prop) (Q : Y -> Z -> Prop) : X -> Z -> Prop
  := fun x z => exists y, P x y /\ Q y z.
Arguments pro_compose {_ _ _} P Q _ _ /.
Infix "⦾" := pro_compose (at level 40) : proset_scope.
Instance pro_compose_proper {X Y Z}
  : Proper (pro_le (X:=X -> Y -> Prop) ++> pro_le (X:=Y -> Z -> Prop) ++> pro_le) pro_compose.
Proof. move=> P P' D1 Q Q' D2 A C /=. setoid_rewrite D1; by setoid_rewrite D2. Qed.
Instance pro_compose_proper' {X Y Z}
  : Proper (pro_le (X:=X -> Y -> Prop) --> pro_le (X:=Y -> Z -> Prop) --> flip pro_le) pro_compose.
Proof. move=> P P' /= D1 Q Q' /= D2 A C /=; setoid_rewrite D1; by setoid_rewrite D2. Qed.
Instance pro_compose_proper'' {X Y Z}
  : Proper (core pro_le (X:=X -> Y -> Prop) ++> core pro_le (X:=Y -> Z -> Prop) ++> core pro_le)
           pro_compose.
Proof. move=> ? ? E1 ? ? E2; split; [rewrite E1 E2 // | rewrite -E1 -E2 //]. Qed.
Instance compose_profunctor {Z} `{Proset X, Proset Y, Proset Z}
         {P : X -> Y -> Prop} {Q : Y -> Z -> Prop} `{!Profunctor P, !Profunctor Q}
  : Profunctor (P ⦾ Q) | 0.
Proof.
  move=> A' A C C' D1 D2 [B [PAB QBC]] /=.
  exists B; by split; [setoid_rewrite D1 | setoid_rewrite <- D2].
Qed.
(* TODO See if there's a way to get this to work better without sacrificing the
        right mode on Tambara. *)
Instance compose_tambara {Z} `{Tambara E X Y L LR P, Proset Z, !Tambara (Y:=Z) LR R Q}
  : Tambara L R (P ⦾ Q) | 0.
Proof. move=> M A C [B [/(tamb _ _ M) PAB /(tamb _ _ M) QBC]]; by eexists. Qed.
Lemma pro_compose_assoc : forall {X Y Z W} {P : X -> Y -> Prop} {Q : Y -> Z -> Prop} {R : Z -> W -> Prop},
    (P ⦾ Q) ⦾ R ⟛ P ⦾ (Q ⦾ R).
Proof. firstorder. Qed.

Definition star `{Proset X} {Y} (F : Y -> X) : X -> Y -> Prop
  := fun A B => A ⊢ F B.
Definition costar {X} `{Proset Y} (G : X -> Y) : X -> Y -> Prop
  := fun A B => G A ⊢ B.
Arguments star {_ _ _} F _ _ /.
Arguments costar {_ _ _} G _ _ /.
(* UGH *)
Instance star_proper `{Proset X} {Y} : Proper (pro_le (X:=Y -> X) ++> pro_le) star.
Proof. move=> F F' D A B /=; by setoid_rewrite D. Qed.
Instance star_proper' `{Proset X} {Y} : Proper (pro_le (X:=Y -> X) --> flip pro_le) star.
Proof. move=> F F' /= D A B /=; by setoid_rewrite D. Qed.
Instance star_proper'' `{Proset X} {Y}
  : Proper (core pro_le (X:=Y -> X) ==> core pro_le) star.
Proof. move=> F F' /= E; apply/pro_core' => A B /=; by setoid_rewrite E. Qed.
Instance costar_proper {X} `{Proset Y}
  : Proper (pro_le (X:=X -> Y) ++> flip pro_le) costar.
Proof. move=> F F' D A B /=; by setoid_rewrite D. Qed.
Instance costar_proper' {X} `{Proset Y} : Proper (pro_le (X:=X -> Y) --> pro_le) costar.
Proof. move=> F F' /= D A B /=; by setoid_rewrite D. Qed.
Instance costar_proper'' {X} `{Proset Y}
  : Proper (core pro_le (X:=X -> Y) ==> core pro_le) costar.
Proof. move=> F F' /= E; apply/pro_core' => A B /=; by setoid_rewrite E. Qed.

Lemma adj_star_costar : forall `{Adjoint X Y F G, !Functor F, !Functor G},
    costar F ⟛ star G.
Proof. move=> *; apply/pro_core' => ? ?; apply/transpose. Qed.
Instance star_profunctor `{Functor X Y F} : Profunctor (star F).
Proof. move=> A' A B B' D1 D2 /=; by setoid_rewrite D1 at 1; setoid_rewrite D2 at 1. Qed.
Instance costar_profunctor `{Functor X Y F} : Profunctor (costar F).
Proof. move=> A' A B B' D1 D2 /=; by setoid_rewrite D1 at 1; setoid_rewrite D2 at 1. Qed.
Definition starred {X Y Z} (P : X -> Y -> Prop) (F : Z -> Y) : X -> Z -> Prop
  := fun A C => P A (F C).
Definition costarred {X Y Z} (G : X -> Y) (P : Y -> Z -> Prop) : X -> Z -> Prop
  := fun A C => P (G A) C.
Arguments starred {_ _ _} P F _ _ /.
Arguments costarred {_ _ _} G P _ _ /.
Instance starred_profunctor {Z} `{Profunctor X Y P, Proset Z} {F : Z -> Y} `{!Functor F}
  : Profunctor (starred P F).
Proof. move=> ? ? ? ? D1 D2 /=; by setoid_rewrite D1; setoid_rewrite D2. Qed.
Instance costarred_profunctor {Z} `{Proset X, Profunctor Y Z P} {G : X -> Y} `{!Functor G}
  : Profunctor (costarred G P).
Proof. move=> ? ? ? ? D1 D2 /=; by setoid_rewrite D1; setoid_rewrite D2. Qed.
Lemma star_right : forall `{Profunctor X Y P} {Z} {F : Z -> Y},
    P ⦾ star F ⟛ starred P F.
Proof.
  move=> X Y ? ? P ? Z F; split=> A C /=.
  - move=> [B [PAB BFC]]; by setoid_rewrite <- BFC.
  - move=> PAFC; by exists (F C).
Qed.
Lemma costar_left : forall {X Z} `{Profunctor Y Z P} {G : X -> Y},
    costar G ⦾ P ⟛ costarred G P.
Proof.
  move=> X Y Z ? ? P ? G; split=> A C /=.
  - move=> [B [GAB PBC]]; by setoid_rewrite GAB.
  - move=> PGAC; by exists (G A).
Qed.
Lemma pro_hom_left_id : forall `{Profunctor X Y P},
    pro_le ⦾ P ⟛ P.
Proof. move=> *; apply: costar_left. Qed.
Lemma pro_hom_right_id : forall `{Profunctor X Y P},
    P ⦾ pro_le ⟛ P.
Proof. move=> *; apply: star_right. Qed.

Class LaxActMorph {E E'} `{Proset X}
      (F : E -> Endo X) (F' : E' -> Endo X) (Φ : E -> E') : Prop :=
  act_triangle : F ⊢ F' ∘ Φ.
Hint Mode LaxActMorph ! ! ! - ! ! ! : typeclass_instances.
Class OplaxActMorph {E E'} `{Proset X}
      (F : E -> Endo X) (F' : E' -> Endo X) (Φ : E -> E') : Prop :=
  act_triangle_op : F' ∘ Φ ⊢ F.
Hint Mode OplaxActMorph ! ! ! - ! ! ! : typeclass_instances.
Class StrongActMorph {E E'} `{Proset X}
      (F : E -> Endo X) (F' : E' -> Endo X) (Φ : E -> E') : Prop :=
  {strong_am_lax :> LaxActMorph F F' Φ;
   strong_am_oplax :> OplaxActMorph F F' Φ}.
Hint Mode StrongActMorph ! ! ! - ! ! ! : typeclass_instances.
Class LaxEquivariant {E} `{Proset X, Proset X'}
      (F : E -> Endo X) (F' : E -> Endo X') (Φ : X -> X') : Prop :=
  act_square M : F' M ∘ Φ ⊢ Φ ∘ F M.
Hint Mode LaxEquivariant ! ! - ! - ! ! ! : typeclass_instances.
Class OplaxEquivariant {E} `{Proset X, Proset X'}
      (F : E -> Endo X) (F' : E -> Endo X') (Φ : X -> X') : Prop :=
  act_square_op M : Φ ∘ F M ⊢ F' M ∘ Φ.
Hint Mode OplaxEquivariant ! ! - ! - ! ! ! : typeclass_instances.
Class StrongEquivariant {E} `{Proset X, Proset X'}
      (F : E -> Endo X) (F' : E -> Endo X') (Φ : X -> X') : Prop :=
  {strong_equ_lax :> LaxEquivariant F F' Φ;
   strong_equ_oplax :> OplaxEquivariant F F' Φ}.
Hint Mode StrongEquivariant ! ! - ! - ! ! ! : typeclass_instances.
Instance adjoint_lax_act_morph `{Adjoint E E' Φ Ψ, Proset X}
         {F : E -> Endo X} `{!Functor F}
  : LaxActMorph F (F ∘ Ψ) Φ.
Proof. move=> M /=; apply/fmap'/adj_unit. Qed.
Instance adjoint_oplax_act_morph `{Adjoint E' E Ψ Φ, Proset X}
         {F : E -> Endo X} `{!Functor F}
  : OplaxActMorph F (F ∘ Ψ) Φ.
Proof. move=> M /=; apply/fmap'/adj_counit. Qed.
Instance adjoint_lax_equivariant `{Proset E, Adjoint X X' Φ Ψ}
         {F : E -> Endo X'} `{!Functor F, !Functor Φ, !Functor Ψ}
  : LaxEquivariant F (conjugate F Φ Ψ) Ψ.
Proof. move=> M A /=; apply/fmap'/fmap'/adj_counit. Qed.
Instance adjoint_oplax_equivariant `{Proset E, Adjoint X X' Φ Ψ}
         {F : E -> Endo X} `{!Functor F, !Functor Ψ, !Functor Φ}
  : OplaxEquivariant F (conjugate F Ψ Φ) Φ.
Proof. move=> M A /=; apply/fmap'/fmap'/adj_unit. Qed.

Instance star_tambara  {E} `{Functor Y X Φ} {L : E -> Endo X} {R : E -> Endo Y}
         `{!LaxEquivariant R L Φ}
  : Tambara L R (star Φ).
Proof. move=> M A B /= /(tamb L L M) D; setoid_rewrite D; apply: act_square. Qed.
Lemma star_tambara_iff : forall {E} `{Functor Y X Φ} {L : E -> Endo X} {R : E -> Endo Y},
    LaxEquivariant R L Φ <-> Tambara L R (star Φ).
Proof.
  move=> E Y ? X ? Φ ? L R; split; first by typeclasses eauto.
  move=> Tamb M B /=; apply: tamb; by simpl.
Qed.
Instance costar_tambara  {E} `{Functor X Y Φ} {L : E -> Endo X} {R : E -> Endo Y}
         `{!OplaxEquivariant L R Φ}
  : Tambara L R (costar Φ).
Proof. move=> M A B /= /(tamb R R M) D; setoid_rewrite <- D; apply: act_square_op. Qed.
Lemma costar_tambara_iff : forall {E} `{Functor X Y Φ} {L : E -> Endo X} {R : E -> Endo Y},
    OplaxEquivariant L R Φ <-> Tambara L R (costar Φ).
Proof.
  move=> E X ? Y ? Φ ? L R; split; first by typeclasses eauto.
  move=> Tamb M B /=; apply: tamb; by simpl.
Qed.

Instance starred_tambara {Z} `{Tambara E X Y L LR P, Proset Z} `{!Profunctor P}
         {Φ : Z -> Y} `{!Functor Φ} {R : E -> Endo Z} `{!LaxEquivariant R LR Φ}
  : Tambara L R (starred P Φ).
Proof.
  assert (Tambara L R (P ⦾ star Φ)) by apply: (compose_tambara (LR:=LR)).
    by unfold Tambara; setoid_rewrite <- (pro_core star_right).
Qed.
Instance costarred_tambara {Z} `{Proset X, Tambara E Y Z LR R P} `{!Profunctor P}
         {Φ : X -> Y} `{!Functor Φ} {L : E -> Endo X} `{!OplaxEquivariant L LR Φ}
  : Tambara L R (costarred Φ P).
Proof.
  assert (Tambara L R (costar Φ ⦾ P)) by apply: (compose_tambara (LR:=LR)).
    by unfold Tambara; setoid_rewrite <- (pro_core costar_left).
Qed.

(* TODO This is a preorder!!! *)
Definition optic {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
           (S : X) (T : Y) (A : X) (B : Y) : Prop :=
  forall P, Profunctor P -> Tambara L R P -> P A B -> P S T.

Definition optic_id {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y} {S T}
  : optic L R S T S T
  := fun _ _ _ => id.
(* TODO We could get a (semi?)lattice of kinds of optic like in Haskell... Hmm. *)
Definition optic_compose {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
           {S T A B W Z} (l : optic L R S T A B) (m : optic L R A B W Z)
  : optic L R S T W Z
  := fun _ _ _ => l _ _ _ ∘ m _ _ _.
Infix "∘∘" := optic_compose (at level 40) : optic_scope.
Definition optic_frame {E} `{Proset X, Proset Y}
           {L : E -> Endo X} {R : E -> Endo Y} {M A B}
  : optic L R (L M A) (R M B) A B
  := fun P _ _ => tamb _ _ (P:=P) M.
Definition first_optic `{SymMonSet X} {P P' Q : X}
  : optic lreg lreg (P ⊗ Q) (P' ⊗ Q) P P'
  := fun _ _ _ => first _.
Definition second_optic `{MonSet X} {P Q Q' : X}
  : optic lreg lreg (P ⊗ Q) (P ⊗ Q') Q Q'
  := fun _ _ _ => second _.

(* TODO This is a crappy name. *)
Lemma yoneda_ish :
  forall `{Proset E, Proset E', Proset X, Proset Y}
    {L : E -> Endo X} {R : E -> Endo Y} {L' : E' -> Endo X} {R' : E' -> Endo Y},
    (forall {S T A B}, optic L R S T A B -> optic L' R' S T A B) <->
    (forall `{!Profunctor P}, Tambara L' R' P -> Tambara L R P).
Proof.
  split.
  - move=> Conv P Pro Tamb M A B.
    apply: (Conv _ _ _ _ optic_frame).
  - move=> Inst S T A B l P Pro Tamb /l //.
Qed.

Definition opticP1 {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
           (A : X) (B : Y) (S : X) (T : Y) : Prop := optic L R S T A B.
Instance optic_profunctor1 {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
         {A B} : Profunctor (opticP1 L R A B).
Proof.
  move=> S' S T T' D1 D2 l P Pro Tamb PAB.
  apply: (dimap D1 D2 _); by apply: l.
Qed.
Instance optic_tambara1 {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
         {A B} : Tambara L R (opticP1 L R A B).
Proof. move=> M S T l P Pro Tamb /l /(tamb _ _ M) //. Qed.

Definition opticP2 {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
           (S : X) (T : Y) (B : Y) (A : X) : Prop := optic L R S T A B.
Instance optic_profunctor2 {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
  {S T} : Profunctor (opticP2 L R S T).
Proof.
  move=> B B' A' A D1 D2 l P Pro Tamb PAB.
  apply: l; by apply: (dimap D2 D1 _).
Qed.

Definition smap {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y} {S' S T A B}
  : S' ⊢ S -> optic L R S T A B -> optic L R S' T A B := lmap (P:=opticP1 L R A B).
Definition tmap {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y} {S T T' A B}
  : T ⊢ T' -> optic L R S T A B -> optic L R S T' A B := rmap (P:=opticP1 L R A B).
Definition amap {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y} {S T A A' B}
  : A ⊢ A' -> optic L R S T A B -> optic L R S T A' B := rmap (P:=opticP2 L R S T).
Definition bmap {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y} {S T A B' B}
  : B' ⊢ B -> optic L R S T A B -> optic L R S T A B' := lmap (P:=opticP2 L R S T).

(* wait, some kind of weird mixture of lax and oplax going on here *)
Definition lax_action_2sided_morph `{Proset E, Proset E', Proset X, Proset X'}
           (Φ : E -> E') (F : X -> X') (L : E -> Endo X) (L' : E' -> Endo X') : Prop
  := forall M, F ∘ L M ⊢ L' (Φ M) ∘ F.
Definition oplax_action_2sided_morph `{Proset E, Proset E', Proset Y, Proset Y'}
           (Φ : E -> E') (G : Y -> Y') (R : E -> Endo Y) (R' : E' -> Endo Y') : Prop
  := forall M, R' (Φ M) ∘ G ⊢ G ∘ R M.
Definition exymap `{Proset E, Proset E', Proset X, Proset X', Proset Y, Proset Y'}
           {L : E -> Endo X} {L' : E' -> Endo X'} {R : E -> Endo Y} {R' : E' -> Endo Y'}
           (Φ : E -> E') (F : X -> X') (G : Y -> Y') `{!Functor Φ, !Functor F, !Functor G}
  : lax_action_2sided_morph Φ F L L' -> oplax_action_2sided_morph Φ G R R' ->
    forall {S T A B}, optic L R S T A B -> optic L' R' (F S) (G T) (F A) (G B).
Proof.
  move=> LaxAct OplaxAct S T A B l P Pro Tamb PFAGB; apply l, PFAGB.
  - move=> {l PFAGB A B} A' A B B' D1 D2.
    apply dimap; by apply fmap'.
  - move=> {l PFAGB A B} M A B /(tamb _ _ (Φ M)).
    apply: dimap; [apply: LaxAct | apply: OplaxAct].
Qed.

Definition emap `{Proset E, Proset E', Proset X, Proset Y}
           {L : E -> Endo X} {L' : E' -> Endo X} {R : E -> Endo Y} {R' : E' -> Endo Y}
           (Φ : E -> E') `{!Functor Φ, !LaxActMorph L L' Φ, !OplaxActMorph R R' Φ}
  : forall {S T A B}, optic L R S T A B -> optic L' R' S T A B.
Proof. apply: exymap; [apply: act_triangle | apply: act_triangle_op]. Qed.
Definition xmap `{Proset E, Proset X, Proset X', Proset Y}
           {L : E -> Endo X} {L' : E -> Endo X'} {R : E -> Endo Y}
           (Φ : X -> X') `{!Functor Φ, !OplaxEquivariant L L' Φ}
  : forall {S T A B}, optic L R S T A B -> optic L' R (Φ S) T (Φ A) B.
Proof. apply: (exymap id); [apply: act_square_op | by hnf]. Qed.
Definition ymap `{Proset E, Proset X, Proset Y, Proset Y'}
           {L : E -> Endo X} {R : E -> Endo Y} {R' : E -> Endo Y'}
           (Φ : Y -> Y') `{!Functor Φ, !LaxEquivariant R R' Φ}
  : forall {S T A B}, optic L R S T A B -> optic L R' S (Φ T) A (Φ B).
Proof. apply: (exymap id); [by hnf | apply: act_square]. Qed.

Definition emap_adj `{Proset E, Proset E', Proset X, Proset Y}
           {L : E -> Endo X} {R : E -> Endo Y} `{!Functor L, !Functor R}
           (Ψ_L : E' -> E) (Ψ_R : E' -> E) {Φ : E -> E'}
           `{!Φ ⊣ Ψ_L, !Ψ_R ⊣ Φ, !Functor Ψ_L, !Functor Ψ_R, !Functor Φ}
  : forall {S T A B}, optic L R S T A B -> optic (L ∘ Ψ_L) (R ∘ Ψ_R) S T A B.
Proof. apply: emap. Qed.
Definition xmap_adj `{Proset E, Proset X, Proset X', Proset Y}
           {L : E -> Endo X} {R : E -> Endo Y} `{!Functor L, !Functor R}
           (Φ : X -> X') {Ψ : X' -> X} `{!Φ ⊣ Ψ, !Functor Φ, !Functor Ψ}
  : forall {S T A B}, optic L R S T A B -> optic (conjugate L Ψ Φ) R (Φ S) T (Φ A) B.
Proof. apply: xmap. Qed.
Definition ymap_adj `{Proset E, Proset X, Proset Y, Proset Y'}
           {L : E -> Endo X} {R : E -> Endo Y} `{!Functor L, !Functor R}
           (Φ : Y -> Y') {Ψ : Y' -> Y} `{!Ψ ⊣ Φ, !Functor Φ, !Functor Ψ}
  : forall {S T A B}, optic L R S T A B -> optic L (conjugate R Ψ Φ) S (Φ T) A (Φ B).
Proof. apply: ymap. Qed.

Definition eunmap {E E'} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
           {F : E' -> E} {S T A B} (l : optic (L ∘ F) (R ∘ F) S T A B)
  : optic L R S T A B
  := fun _ _ _ => l _ _ _.

Definition eoptic {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
           (A : X) (B : Y) : X -> Y -> Prop
  := fun S T => exists2 M, S ⊢ L M A & R M B ⊢ T.
Instance eoptic_profunctor {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
         {A B} : Profunctor (eoptic L R A B).
Proof.
  move=> S' S T T' D1 D2 [M Open Close].
  exists M; by etransitivity.
Qed.
Instance eoptic_tambara `{MonSet E, Proset X, Proset Y}
         {L : E -> Endo X} {R : E -> Endo Y}
         `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {A B}
  : Tambara L R (eoptic L R A B).
Proof.
  move=> M S T [M' Open Close].
  exists (M ⊗ M').
  - setoid_rewrite <- pres_tens; by apply: functorial.
  - setoid_rewrite pres_tens_op; simpl; by apply: functorial.
Qed.

Definition optic_to_eoptic `{MonSet E, Proset X, Proset Y}
           {L : E -> Endo X} {R : E -> Endo Y}
           `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {S T A B}
           (l : optic L R S T A B)
  : eoptic L R A B S T.
Proof. apply: l; exists memp; [apply: (pres_memp (F:=L)) |
                          apply: (pres_memp_op (F:=R))]. Qed.
Definition eoptic_to_optic {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
           {S T A B} (e : eoptic L R A B S T)
  : optic L R S T A B.
Proof.
  move: e => [M Open Close] P Pro Tamb PAB.
  apply (dimap Open Close), (tamb L R), PAB.
Qed.
Definition optic_iff_eoptic :
  forall `{MonSet E, Proset X, Proset Y}
    {L : E -> Endo X} {R : E -> Endo Y}
    `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {S T A B},
    optic L R S T A B <-> eoptic L R A B S T.
Proof. move=> *; split; [apply: optic_to_eoptic | apply: eoptic_to_optic]. Qed.

(* Maybe I should learn how Yoneda reduction works. *)
Theorem optic_concrete :
  forall `{MonSet E, Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
    `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {B}
    R_B `{!Hom_eval_at B ∘ R ⊣ R_B, !Functor R_B} {S T A},
    optic L R S T A B <-> S ⊢ L (R_B T) A.
Proof.
  move=> E Pr_E MS X Pr_X Y Pr_Y L R Funct_L Funct_R Lax Oplax B R_B Adj Funct_R_B S T A.
  rewrite optic_iff_eoptic /eoptic; split.
  - move=> [M Open /(transpose (Adj:=Adj)) Close].
    setoid_rewrite Open; by setoid_rewrite Close.
  - move=> D.
    eexists; last apply/(transpose (Adj:=Adj)); done.
Qed.
Arguments optic_concrete {_ _ _ _ _ _ _ _ _ _ _ _ _ _} R_B Adj {_ _ _ _} : rename.


(* TODO eoptic instance? *)
Class ProRepresentable {X Y} `{!Proset X, !Proset Y}
      (P : X -> Y -> Prop) `{!Profunctor P} : Prop :=
  represent B : exists P_B, forall A, P A B <-> A ⊢ P_B.
Hint Mode ProRepresentable ! ! - - ! - : typeclass_instances.
Class ProCorepresentable {X Y} `{!Proset X, !Proset Y}
      (P : X -> Y -> Prop) `{!Profunctor P} : Prop :=
  corepresent A : exists P_A, forall B, P A B <-> P_A ⊢ B.
Hint Mode ProCorepresentable ! ! - - ! - : typeclass_instances.
Program Definition pro_psh {X Y} (P : X -> Y -> Prop) `{Profunctor X Y P} (B : Y) : PSh X :=
  fun A => P (get_op A) B.
Next Obligation. move=> X Y P Pr_X Pr_Y Pro B [A] [A'] /= D; apply: lmap D. Qed.
Program Definition pro_copsh {X Y} (P : X -> Y -> Prop) `{Profunctor X Y P} (A : op X)
  : PSh (op Y) :=
  fun B => P (get_op A) (get_op (get_op B)).
Next Obligation. move=> X Y P Pr_X Pr_Y Pro [A] [[B]] [[B']] /= D; apply: rmap D. Qed.
Instance pro_psh_functor `{Profunctor X Y P} : Functor (pro_psh P).
Proof. move=> B B' /= D [A] /=; apply: rmap D. Qed.
Instance pro_copsh_functor `{Profunctor X Y P} : Functor (pro_copsh P).
Proof. move=> [A] [A'] /= D [[B]] /=; apply: lmap D. Qed.
Lemma pro_yoneda : forall `{Profunctor X Y P} {A B},
    P A B <-> yo A ⊢ pro_psh P B.
Proof. move=> *; rewrite yoneda //. Qed.
Lemma pro_yoneda_op : forall `{Profunctor X Y P} {A B},
    P A B <-> yo (Op B) ⊢ pro_copsh P (Op A).
Proof. move=> *; rewrite yoneda //. Qed.
Lemma prorepresentable_alt : forall `{Profunctor X Y P},
    ProRepresentable P <-> forall B, representable (pro_psh P B).
Proof.
  move=> X Y Pr_X Pr_Y P Pro.
  apply: forall_proper => B; apply: exist_proper => P_B; rewrite -Hom_core /=.
  split=> [H [A] | H A] /=; [firstorder | apply: (H (Op A))].
Qed.
Lemma procorepresentable_alt : forall `{Profunctor X Y P},
    ProCorepresentable P <-> forall B, representable (pro_copsh P (Op B)).
Proof.
  move=> X Y Pr_X Pr_Y P Pro.
  apply: forall_proper => A; split=> [[P_A Repr_A] | [[P_A] /Hom_core E]].
  - exists (Op P_A); apply/Hom_core => -[[?]] /=; apply: Repr_A.
  - exists P_A => B; apply: (E (Op (Op B))).
Qed.

Instance hom_representable `{Proset X} : ProRepresentable (pro_le (X:=X)).
Proof. firstorder. Qed.
Instance hom_corepresentable `{Proset X} : ProCorepresentable (pro_le (X:=X)).
Proof. firstorder. Qed.
Instance compose_representable {Z} `{ProRepresentable X Y P, Proset Z}
         {Q : Y -> Z -> Prop} `{!Profunctor Q, !ProRepresentable Q}
  : ProRepresentable (P ⦾ Q).
Proof.
  move=> C.
  case: (represent C) => P_C Repr_C; case: (represent P_C) => P_P_C Repr_P_C /=.
  setoid_rewrite Repr_C; setoid_rewrite (pro_core star_right); eauto.
Qed.
Instance compose_corepresentable {Z} `{ProCorepresentable X Y P, Proset Z}
         {Q : Y -> Z -> Prop} `{!Profunctor Q, !ProCorepresentable Q}
  : ProCorepresentable (P ⦾ Q).
Proof.
  move=> C.
  case: (corepresent C) => P_C Repr_C; case: (corepresent P_C) => P_P_C Repr_P_C /=.
  setoid_rewrite Repr_C; setoid_rewrite (pro_core costar_left); eauto.
Qed.
Instance star_representable `{Functor Y X F} : ProRepresentable (star F).
Proof. move=> B; rewrite /star; eauto. Qed.
Instance costar_corepresentable `{Functor X Y G} : ProCorepresentable (costar G).
Proof. move=> A; rewrite /costar; eauto. Qed.
Instance starred_representable {Z} `{ProRepresentable X Y P} `{Proset Z}
         {F : Z -> Y} `{!Functor F}
  : ProRepresentable (starred P F).
Proof.
  assert (ProRepresentable (P ⦾ star F)) by typeclasses eauto.
    by unfold ProRepresentable; setoid_rewrite <- (pro_core star_right) at 1.
Qed.
Instance costarred_representable {Z} `{Proset X} `{ProCorepresentable Y Z P}
         {G : X -> Y} `{!Functor G}
  : ProCorepresentable (costarred G P).
Proof.
  assert (ProCorepresentable (costar G ⦾ P)) by typeclasses eauto.
    by unfold ProCorepresentable; setoid_rewrite <- (pro_core costar_left) at 1.
Qed.

(* TODO Maybe this shouldn't be an 'Instance'---it doesn't seem terribly inferrable. *)
Instance optic_representable1 `{MonSet E, Proset X, Proset Y}
         {L : E -> Endo X} {R : E -> Endo Y}
         `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {A B}
         {R_B : Y -> E} `{!Hom_eval_at B ∘ R ⊣ R_B, !Functor R_B}
  : ProRepresentable (opticP1 L R A B).
Proof. move=> T; eexists=> S; by apply optic_concrete. Qed.

(* Coyoneda facts in disguise! *)
Definition extractable `{Complete X, Proset Y} (P : X -> Y -> Prop) `{!Profunctor P} : Prop
  := forall T (A : T -> X) B, (forall y, P (A y) B) -> P (colim A) B.
Definition coextractable `{Proset X, Complete Y} (P : X -> Y -> Prop) `{!Profunctor P} : Prop
  := forall T A (B : T -> Y), (forall y, P A (B y)) -> P A (lim B).

Lemma representable_extractable :
  forall `{Complete X, Proset Y} {P : X -> Y -> Prop} `{!Profunctor P, !ProRepresentable P},
    extractable P.
Proof.
  move=> X Pr_X Comp Y Pr_Y P Pro Rep T A B PAB.
  case: (represent (P:=P) B) => P_B Repr_B.
  apply Repr_B, colim_left => x; apply Repr_B, PAB.
Qed.
Lemma extractable_representable :
  forall `{Complete X, Proset Y} {P : X -> Y -> Prop} `{!Profunctor P},
    extractable P -> ProRepresentable P.
Proof.
  move=> X Pr_X Comp Y Pr_Y P Pro Extr B.
  exists (colim (fun A : sig (pro_psh P B ∘ Op) => `A)) => A; split.
  - move=> PAB; rewrite /compose /=; by apply: (colim_right _ (A ↾ PAB)).
  - move=> D; apply (lmap D), Extr => -[A'] //.
Qed.
Lemma extractable_iff_representable :
  forall `{Complete X, Proset Y} {P : X -> Y -> Prop} `{!Profunctor P},
    extractable P <-> ProRepresentable P.
Proof. move=> *; split; [apply: extractable_representable |
                        apply @representable_extractable]. Qed.

Lemma corepresentable_coextractable :
  forall `{Proset X, Complete Y} {P : X -> Y -> Prop} `{!Profunctor P, !ProCorepresentable P},
    coextractable P.
Proof.
  move=> X Pr_X Y Pr_Y Comp P Pro Corep T A B PAB.
  case: (corepresent (P:=P) A) => P_A Repr_A.
  apply Repr_A, lim_right => x; apply Repr_A, PAB.
Qed.
Lemma coextractable_corepresentable :
  forall `{Proset X, Complete Y} {P : X -> Y -> Prop} `{!Profunctor P},
    coextractable P -> ProCorepresentable P.
Proof.
  move=> X Pr_X Y Pr_Y Comp P Pro Extr A.
  exists (lim (fun B : sig (pro_copsh P (Op A) ∘ Op) => get_op (`B))) => B; split.
  - move=> PAB; rewrite /compose /=; by apply: (lim_left _ (Op B ↾ PAB)).
  - move=> D; apply (rmap D), Extr => -[B'] //.
Qed.
Lemma coextractable_iff_corepresentable :
  forall `{Proset X, Complete Y} {P : X -> Y -> Prop} `{!Profunctor P},
    coextractable P <-> ProCorepresentable P.
Proof. move=> *; split; [apply: coextractable_corepresentable |
                        apply @corepresentable_coextractable]. Qed.

Definition rep_optic {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
           (S : X) (T : Y) (A : X) (B : Y) : Prop :=
  forall P `(!Profunctor P), Tambara L R P -> ProRepresentable P -> P A B -> P S T.
Definition extend_rep
      `{MonSet E, Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
      `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R} {B}
      (R_B : Y -> E) `{!Hom_eval_at B ∘ R ⊣ R_B, !Functor R_B} {S T A}
      (l : rep_optic L R S T A B) : optic L R S T A B
  := l (opticP1 L R A B) _ _ _ optic_id.

Definition psh_act {E} `{Proset X} (F : E -> Endo X) : E -> Endo (PSh X)
  := psh_map ∘ F.
Arguments psh_act {_ _ _} F _ /.
Instance psh_map_local_functor `{Proset X, Proset Y} : Functor (psh_map (X:=X) (Y:=Y)).
Proof. typeclasses eauto. Qed.
Opaque psh_map.
Instance psh_act_laxmon `{MonSet E, Proset X} {F : E -> Endo X} `{!Functor F, !LaxMon F}
  : LaxMon (psh_act F).
Proof.
  constructor=> [| M N] /=.
  - etransitivity; last by apply/fmap'/(pres_memp (F:=F)).
    rewrite psh_map_id //.
  - etransitivity; last by apply/fmap'/(pres_tens (F:=F)).
    rewrite [R in _ ⊢ R]psh_map_compose //.
Qed.
Instance psh_act_oplaxmon `{MonSet E, Proset X}
         {F : E -> Endo X} `{!Functor F, !OplaxMon F}
  : OplaxMon (psh_act F).
Proof.
  constructor=> [| M N] /=.
  - etransitivity; first by apply/fmap'/(pres_memp_op (F:=F)).
    rewrite psh_map_id //.
  - etransitivity; first by apply/fmap'/(pres_tens_op (F:=F)).
    rewrite [L in L ⊢ _]psh_map_compose //.
Qed.
Instance psh_act_strongmon `{MonSet E, Proset X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F}
  : StrongMon (psh_act F).
Proof. constructor; typeclasses eauto. Qed.

Lemma tambara_alt :
  forall {E} `{Proset X, Proset Y}
    {L : E -> Endo X} {R : E -> Endo Y}
    {P : X -> Y -> Prop} `{!Profunctor P},
    Tambara L R P <-> LaxEquivariant R (psh_act L) (pro_psh P).
Proof.
  move=> E X ? Y ? L R P ?; split.
  - move=> Tamb M B [A] /= [[A' PAB] /= D]; setoid_rewrite D.
    apply: (tamb L R M); change (pro_psh P B (Op A')); by apply/yoneda.
  - move=> LaxACM M A B.
    rewrite pro_yoneda [R in _ -> R]pro_yoneda => /(fmap' (F:=psh_map (L M))).
    rewrite psh_map_yo => D; setoid_rewrite D; apply: (act_square (Φ:=pro_psh P)).
Qed.


Record irel (X Y : Type) := Irel {ap_irel :> Y -> Y -> X}.
Add Printing Constructor irel.
Arguments Irel {_ _}.
Arguments ap_irel {_ _}.
Definition pro_irel {X} (R : X -> X -> Prop) (Y : Type) : irel X Y -> irel X Y -> Prop :=
  fun R1 R2 => pointwise_relation Y (pointwise_relation Y R) (ap_irel R1) (ap_irel R2).
Arguments pro_irel {X} R Y !a1 !a2 /.
Instance pro_irel_pro `{PreOrder X R} {Y} : PreOrder (pro_irel R Y).
Proof.
  constructor; first by firstorder.
  move=> [x] [y] [z] /=; etransitivity; eauto.
Qed.
Instance irel_proset `{Proset X} {Y} : Proset (irel X Y)
  := {| pro_le := pro_irel pro_le Y |}.
Lemma irel_core : forall `{Proset X} {Y} {R S : irel X Y},
    R ⟛ S <-> (forall rho rho', R rho rho' ⟛ S rho rho').
Proof. firstorder. Qed.
Instance ap_irel_functor `{Proset X} {Y} : Functor (ap_irel (X:=X) (Y:=Y)).
Proof. move=> [R] [S] //. Qed.
Instance ap_irel_proper `{Proset X} {Y}
  : Proper (pro_le ++> (=) ==> (=) ==> pro_le) (ap_irel (X:=X) (Y:=Y)).
Proof. move=> [R] [R'] /= D ? _ <- ? _ <-; apply: D. Qed.
Instance ap_irel_proper' `{Proset X} {Y}
  : Proper (pro_le --> (=) ==> (=) ==> flip pro_le) (ap_irel (X:=X) (Y:=Y)).
Proof. move=> [R] [R'] /= D ? _ <- ? _ <-; apply: D. Qed.
Instance Irel_functor `{Proset X} {Y} : Functor (Irel (X:=X) (Y:=Y)).
Proof. move=> R S //. Qed.
Instance irel_adjunction1 `{Proset X} {Y} : Irel (X:=X) (Y:=Y) ⊣ ap_irel.
Proof. constructor=> [R | [R]] //=. Qed.
Instance irel_adjunction2 `{Proset X} {Y} : ap_irel (X:=X) (Y:=Y) ⊣ Irel.
Proof. constructor=> [[R] | R] //=. Qed.
(*
Instance irel_core' `{Proset X} {Y}
: subrelation (core (pro_le (X:=Y -> X))) (pointwise_relation Y (core (pro_le (X:=X)))).
Proof. firstorder. Qed.
 *)
Definition tens_irel `{MonSet X, !Complete X} (Y : Type) (R1 R2 : irel X Y)
  : irel X Y :=
  Irel (fun rho rho'' => colim (fun rho' : Y => R1 rho rho' ⊗ R2 rho' rho'')).
Arguments tens_irel {X _ _ _} Y !R1 !R2 /.
Instance irel_monoidal `{Quantale X} {Y}
  : Monoidal (pro_le (X:=irel X Y)) (tens_irel Y)
             (Irel (fun a b => mon_embed_prop (a = b))).
Proof.
  constructor.
  - move=> [R] [R'] [S] [S'] /= D1 D2 rho rho''.
    apply: fmap' => rho'; apply/bimap; firstorder.
  - move=> [R]; apply/irel_core=> rho rho' /=; split.
    + apply: colim_left => rho''.
      apply/tensor_hom/mon_embed_prop_left => <-.
      apply/tensor_hom; rewrite pro_lunit //.
    + setoid_rewrite <- colim_right.
      setoid_rewrite <- (mon_embed_prop_right erefl (reflexivity _)).
        by setoid_rewrite <- (proj2 (pro_lunit _)).
  - move=> [R]; apply/irel_core=> rho rho' /=; split.
    + apply: colim_left=> rho''.
      apply/l_tensor_hom/mon_embed_prop_left => <-.
      apply/l_tensor_hom; rewrite pro_runit //.
    + setoid_rewrite <- colim_right.
      setoid_rewrite <- (mon_embed_prop_right erefl (reflexivity _)).
        by setoid_rewrite <- (proj2 (pro_runit _)).
  - move=> [R] [S] [T]; apply/irel_core=> rho0 rho /=; split.
    + apply: colim_left=> rho1; setoid_rewrite distrib_colim; apply: colim_left=> rho2 /=.
      rewrite pro_massoc; setoid_rewrite <- colim_right; apply: bimap; last by done.
        by setoid_rewrite <- colim_right.
    + apply: colim_left=> rho2; rewrite -/(r_tensor _ _).
      setoid_rewrite (distrib_colim (F:=r_tensor _)).
      simpl; apply: colim_left=> rho1 /=; rewrite -pro_massoc.
      setoid_rewrite <- colim_right; apply: bimap; first by done.
        by setoid_rewrite <- colim_right.
Qed.
Instance irel_mset `{Quantale X} {Y}
  : MonSet (irel X Y)
  := {| pro_tens := tens_irel Y |}.
Program Instance irel_bicomplete `{Complete X} {Y} : Complete (irel X Y)
  := {| lim R J := Irel (lim (ap_irel ∘ J)); colim R J := Irel (colim (ap_irel ∘ J)) |}.
Next Obligation.
  move=> X Pr_X Comp Y R J; rewrite /lim /=; split=> [r | A' Cone] rho rho' /=.
  - apply: lim_left.
  - apply: lim_right => r; apply: Cone.
Qed.
Next Obligation.
  move=> X Pr_X Comp Y R J; rewrite /colim /=; split=> [r | A' Cocone] rho rho' /=.
  - rewrite -/ap_Hom; by setoid_rewrite <- colim_right.
  - apply: colim_left => r; apply: Cocone.
Qed.
(* TODO Maybe define the actual internal homs directly? *)
Instance irel_tensor_cocont `{Quantale X} {Y} {R : irel X Y}
  : Cocontinuous (pro_tens R).
Proof.
  apply/distrib_colim_sufficient => R' J rho rho'' /=.
  apply/colim_left => rho'; rewrite distrib_colim; apply/colim_left => r /=.
  setoid_rewrite <- colim_right; by setoid_rewrite <- colim_right.
Qed.
Instance irel_r_tensor_cocont `{Quantale X} {Y} {R : irel X Y}
  : Cocontinuous (r_tensor R).
Proof.
  apply/distrib_colim_sufficient => R' J rho rho'' /=.
  apply/colim_left => rho'; setoid_rewrite (distrib_colim (F:=r_tensor _)).
  apply/colim_left => r /=; setoid_rewrite <- colim_right.
    by setoid_rewrite <- colim_right.
Qed.
Instance irel_cmset `{Quantale X} {Y} : ClosedMonSet (irel X Y)
  := r_tensor_cocontinuous_sufficient _.
Instance irel_lcmset `{Quantale X} {Y} : LClosedMonSet (irel X Y)
  := tensor_cocontinuous_sufficient _.
Instance irel_quantale `{Quantale X} {Y} : Quantale (irel X Y).

(* TODO "basechange" is a misnomer *)
Definition irel_basechange {X X' Y} (f : X -> X') : irel X Y -> irel X' Y
  := Irel ∘ compose (compose f) ∘ ap_irel.
(* TODO This should be inferrable. *)
Instance irel_basechange_full `{Proset X, Proset X'} {F : X -> X'} `{!Full F} {Y}
  : Full (irel_basechange (Y:=Y) F).
Proof. move=> R S /= D rho rho'; apply/(unfmap (F:=F))/D. Qed.
Instance irel_basechange_laxmon `{Quantale X, Quantale X'}
         {F : X -> X'} `{!Functor F, !LaxMon F} {Y}
  : LaxMon (irel_basechange (Y:=Y) F).
Proof.
  constructor=> [| [R] [S]] rho rho' //=.
  - apply/colim_left=> <- //.
    setoid_rewrite (pres_memp (F:=F)); apply/fmap'; by setoid_rewrite <- colim_right.
  - apply/colim_left=> rho''.
    setoid_rewrite pres_tens; apply/fmap'; by setoid_rewrite <- colim_right.
Qed.
(* TODO Figure out whether cocontinuity of F is actually necessary. *)
Instance irel_basechange_oplaxmon `{Quantale X, Quantale X'}
         {F : X -> X'} `{!Functor F, !OplaxMon F, !Cocontinuous F} {Y}
  : OplaxMon (irel_basechange (Y:=Y) F).
Proof.
  constructor=> [| [R] [S]] rho rho'' //=.
  - rewrite distrib_colim; apply: fmap' => rho' /=; apply: pres_memp_op.
  - rewrite distrib_colim; apply: fmap' => rho' /=; apply: pres_tens_op.
Qed.
Instance irel_basechange_strongmon `{Quantale X, Quantale X'}
         {F : X -> X'} `{!Functor F, !StrongMon F, !Cocontinuous F} {Y}
  : StrongMon (irel_basechange (Y:=Y) F).
Proof. constructor; typeclasses eauto. Qed.

Definition rel_act `{MonSet X, !Complete X} (Y : Type) (R : irel X Y)
  : Endo (Y -> X)
  := in_Hom (fun Q rho => colim (fun rho' : Y => R rho rho' ⊗ Q rho')).
Instance rel_act_functor `{MonSet X, !Complete X} {Y}
  : Functor (rel_act (X:=X) Y).
Proof.
  move=> A B D P /= rho.
  apply: fmap' => rho'; apply/bimap; firstorder.
Qed.
Instance rel_act_strongmon `{Quantale X} {Y}
  : StrongMon (rel_act (X:=X) Y).
Proof.
  constructor; constructor.
  - move=> P rho /=; setoid_rewrite <- colim_right.
    setoid_rewrite <- mon_embed_prop_right; only 2-3: reflexivity.
      by setoid_rewrite <- (proj2 (pro_lunit _)).
  - move=> [R] [S] P rho /=.
    apply: colim_left => ?; setoid_rewrite distrib_colim; apply: colim_left => ? /=.
    setoid_rewrite <- colim_right; rewrite -[colim _ ⊗ _]/(r_tensor _ _).
    setoid_rewrite <- (proj2 (distrib_colim (F:=r_tensor _) _)).
    setoid_rewrite <- colim_right; rewrite pro_massoc //=.
  - move=> P rho /=; apply: colim_left => rho'.
    apply/(mon_prop_loop (reflexivity _)) => <- //.
  - move=> [R] [S] P rho /=.
    apply: colim_left => ?; rewrite -[colim _ ⊗ _]/(r_tensor _ _).
    rewrite (distrib_colim (F:=r_tensor _)); apply: colim_left => ? /=.
    setoid_rewrite <- colim_right; setoid_rewrite <- colim_right; rewrite -pro_massoc //=.
Qed.

Definition rel_act_op `{ClosedMonSet X, !Complete X} (Y : Type) (R : op (irel X Y))
  : Endo (Y -> X)
  := in_Hom (fun Q rho => lim (fun rho' : Y => get_op R rho rho' ⊸ Q rho')).
Instance rel_act_op_functor `{ClosedMonSet X, !Complete X} {Y}
  : Functor (rel_act_op (X:=X) Y).
Proof. move=> [A] [B] /= D P rho; apply: fmap' => rho'; by setoid_rewrite D. Qed.
Instance rel_act_op_strongmon `{Quantale X} {Y}
  : StrongMon (rel_act_op (X:=X) Y).
Proof.
  constructor; constructor=> [| [R] [S]] P rho /=.
  - apply/lim_right => rho'; apply/tensor_hom/l_mon_prop_loop => // <- //.
  - apply/lim_right => rho''; apply/tensor_hom/l_tensor_hom/colim_left => rho'.
    do 2 setoid_rewrite lim_left.
    rewrite -l_tensor_hom pro_massoc; by do 2 setoid_rewrite mon_modus_ponens.
  - setoid_rewrite lim_left; rewrite -[R in R ⊢ _]pro_runit.
    setoid_rewrite (mon_embed_prop_right erefl (reflexivity _)).
    apply/mon_modus_ponens.
  - apply/lim_right => rho'; apply/tensor_hom/lim_right => rho''.
    setoid_rewrite lim_left; setoid_rewrite <- colim_right.
    rewrite -tensor_hom -pro_massoc; by setoid_rewrite mon_modus_ponens.
Qed.


Example rel_act_optic : forall `{Quantale X} {R} {S T A B : R -> X},
    optic (rel_act R) (rel_act R) S T A B <->
    forall rho : R, S rho ⊢ colim (fun rho' : R => (B rho' ⊸ T rho) ⊗ A rho').
Proof.
  move=> X Pr Comp MS CMS LCMS Quant R S T A B.
  pose proof (_ : compose (colim ∘ r_tensor B) ∘ ap_irel ⊣ _) as Adj.
  rewrite optic_concrete //.
Qed.

(* TODO Move these to the right place. *)
Instance flip_functor {Y1 Y2} `{Proset X} : Functor (@flip Y1 Y2 X).
Proof. firstorder. Qed.
Instance flip_strongmon {Y1 Y2} `{MonSet X} : StrongMon (@flip Y1 Y2 X).
Proof. constructor; by constructor. Qed.
Instance flip_adjunction {Y1 Y2} `{Proset X} : @flip Y1 Y2 X ⊣ flip.
Proof. done. Qed.
(* TODO This could stand to compile faster; can I optimize at all? *)
Example rel_act_optic' :
  forall `{Quantale X} {R Y} {S : R -> X} {T : Y -> R -> X} {A : R -> X} {B : Y -> R -> X},
    optic (rel_act R) (conjugate (rel_act R) flip flip ∘ irel_basechange const)
          S T A B <->
    forall rho : R, S rho ⊢ colim (fun rho' : R => lim (fun y => B y rho' ⊸ T y rho) ⊗ A rho').
Proof.
  move=> X Pr Comp MS CMS LCMS Quant R Y S T A B.
  pose proof (_ : flip ∘ compose (colim ∘ flip ∘ r_tensor B ∘ flip) ∘
                       ap_irel ∘ irel_basechange const ⊣ _) as Adj.
  rewrite optic_concrete //.
Qed.

(* TODO Do we want to support alternate monoidal structures? *)
(* TODO Fiddle with the constraints. *)
Lemma monoid_ipro : forall `{Quantale X} {Y} {R : Y -> Y -> X},
    Monoid (Irel R) <-> (forall rho, memp ⊢ R rho rho) /\
                      (forall rho1 rho2 rho3, R rho1 rho2 ⊗ R rho2 rho3 ⊢ R rho1 rho3).
Proof.
  move=> X ? ? ? ? ? ? Y R; split=> [Mon | [IRefl ITrans]]; split.
  - move=> rho.
      by etransitivity; [apply: mon_embed_prop_right | apply: (eta (M:=Irel R))].
  - move=> rho1 rho2 rho3.
    etransitivity; last by apply: (mu (M:=Irel R)).
      by setoid_rewrite <- colim_right.
  - move=> rho rho' /=; apply: mon_embed_prop_left => <- //.
  - move=> rho1 rho3 /=; apply: colim_left => rho2 //.
Qed.
Definition mon_embed_rel (X : Type) `{MonSet X, !Complete X} {Y} (R : Y -> Y -> Prop)
  : Y -> Y -> X
  := fun a b => mon_embed_prop (R a b).
Arguments mon_embed_rel _ {_ _ _ _} _ _ _ /.
Definition prop_irel (X : Type) `{MonSet X, !Complete X} {Y} : (Y -> Y -> Prop) -> irel X Y
  := Irel ∘ mon_embed_rel X.
Arguments prop_irel _ {_ _ _ _} _ /.
Instance prop_irel_monoid `{Quantale X, PreOrder Y R}
  : Monoid (prop_irel X R).
Proof.
  constructor.
  - move=> rho rho' /=; apply/fmap' => <- //.
  - move=> rho1 rho3 /=; apply/colim_left => rho2.
    rewrite mon_tensor_prop; apply: fmap' => -[? ?]; by etransitivity.
Qed.

Definition box `{Quantale X} {Y} (Reach : irel X Y) : (Y -> X) -> Y -> X
  := rel_act_op _ (Op Reach).
Arguments box {_ _ _ _ _ _ _ _} Reach P /.
(* TODO Move this *)
Instance op_comonoid `{Monoid X M} : Comonoid (Op M).
Proof. firstorder. Qed.
Instance op_monoid `{Comonoid X W} : Monoid (Op W).
Proof. firstorder. Qed.
(* box is a comonad if Reach is a preorder *)
Example box_comonad `{Quantale X} {Y} {Reach : irel X Y}
         `{!Monoid Reach} : Comonad (box Reach).
Proof. typeclasses eauto. Qed.

(* Coalgebras of box *)
Notation Hereditary Reach := (Coalg (box Reach)).
Definition hpred `{Quantale X} {Y} (Reach : irel X Y) : Type := coEM (box Reach).
Lemma Hereditary_prop_irel : forall `{Quantale X} {Y} {Reach : Y -> Y -> Prop} {P : Y -> X},
    Hereditary (prop_irel X Reach) P <->
    forall {rho rho'}, Reach rho rho' -> P rho ⊢ P rho'.
Proof.
  move=> X Pr Comp MS CMS LCMS Quant Y Reach P; split.
  - move=> Hered rho rho' ReachStep.
    setoid_rewrite (Hered rho); setoid_rewrite lim_left; rewrite -[_ ⊸ _]pro_runit /=.
    setoid_rewrite (mon_embed_prop_right ReachStep (reflexivity _)).
    apply/mon_modus_ponens.
  - move=> Hered' rho; apply/lim_right => rho'.
    apply/tensor_hom/l_tensor_hom/mon_embed_prop_left => H.
    apply/l_tensor_hom; rewrite pro_runit; by apply/Hered'.
Qed.
(* TODO Move this *)
Instance mon_embed_prop_comonoid `{MonSet X, !Complete X} {P : Prop}
  : Comonoid (mon_embed_prop P).
Proof.
  constructor.
  - apply: mon_embed_prop_left => //.
  - apply: mon_embed_prop_left => PP.
    setoid_rewrite <- mon_embed_prop_right; try first [assumption | reflexivity].
    rewrite pro_runit //.
Qed.
(* Can we loosen the sym constraint at all? *)
Instance Hereditary_monclosed `{Quantale X, !SymMonSet X} {Y} {Reach : irel X Y}
         `{!forall rho1 rho2, Comonoid (Reach rho1 rho2)}
  : MonClosed (Hereditary Reach).
Proof.
  constructor.
  - move=> rho /=; apply/lim_right => rho'.
    setoid_rewrite epsilon; rewrite -tensor_hom pro_lunit //.
  - move=> P Q Hered1 Hered2 rho /=; apply/lim_right => rho'.
    rewrite /pro_tens /=; setoid_rewrite (Hered1 rho); setoid_rewrite (Hered2 rho).
    simpl; setoid_rewrite (lim_left _ rho').
    rewrite -tensor_hom -pro_massoc; setoid_rewrite delta at 3.
    setoid_rewrite pro_massoc at 2; setoid_rewrite mon_modus_ponens.
    rewrite [Q rho' ⊗ _]pro_sym' pro_massoc; by setoid_rewrite mon_modus_ponens.
Qed.
(* In any case, it's still true for prop_irel even if the quantale is non-commutative. *)
Instance Hereditary_prop_irel_monclosed `{Quantale X} {Y} {Reach : Y -> Y -> Prop}
  : MonClosed (Hereditary (prop_irel X Reach)).
Proof.
  constructor.
  - by apply/Hereditary_prop_irel.
  - move=> P Q /Hereditary_prop_irel Hered1 /Hereditary_prop_irel Hered2.
    apply/Hereditary_prop_irel => rho rho' ReachStep; apply: bimap; auto.
Qed.

Instance mon_embed_prop_hereditary `{Quantale X} {Y} {Reach : irel X Y}
         `{!forall rho1 rho2, Comonoid (Reach rho1 rho2)} {P : Prop}
  : Hereditary Reach (mon_embed_prop P).
Proof.
  move=> rho; apply/lim_right => rho' /=; apply/tensor_hom/mon_prop_loop; first by compute.
  move=> PP; apply/mon_embed_prop_right => //; apply/epsilon.
Qed.
Instance embed_prop_hereditary `{Quantale X} {Y} {Reach : irel X Y} {P : Prop}
  : Hereditary Reach (embed_prop P).
Proof.
  move=> *; apply/lim_right => rho' /=; apply: colim_left => ? /=; apply/tensor_hom.
  setoid_rewrite <- colim_right; [| done]; apply/lim_right => -[].
Qed.

Definition dia `{MonSet X, !Complete X} {Y} (Reach : irel X Y) : (Y -> X) -> Y -> X
  := rel_act _ Reach.
Arguments dia {_ _ _ _ _} _ _ /.
(* box is a monad if Reach is a preorder *)
Example dia_monad `{Quantale X} {Y} {Reach : irel X Y}
        `{!Monoid Reach} : Monad (dia Reach).
Proof. typeclasses eauto. Qed.

(* TODO *Should* I move this? *)
(* TODO Set up "flipped monoidal product". *)
Definition irel_flip {X Y} : irel X Y -> irel X Y := Irel ∘ flip ∘ ap_irel.
Instance flip_monoid `{Quantale X, !SymMonSet X} {Y} {R : irel X Y} `{Mon : !Monoid R}
  : Monoid (irel_flip R).
Proof.
  move: R Mon => [R] /monoid_ipro [IRefl ITrans]; apply/monoid_ipro; split.
  - move=> rho //=.
  - move=> rho1 rho2 rho3 /=; rewrite pro_sym' //.
Qed.
Instance flip_comonoid `{Quantale X, !SymMonSet X} {Y} {R : irel X Y}
         `{Comon : !Comonoid R}
  : Comonoid (irel_flip R).
Proof.
  constructor.
  - move=> rho rho'; setoid_rewrite (epsilon (W:=R)); simpl; apply/fmap' => ? //.
  - move=> rho rho'' /=; setoid_rewrite (delta (W:=R)) at 1; simpl; apply/fmap' => rho'.
    apply: pro_sym.
Qed.
Example dia_monad_flip `{Quantale X, !SymMonSet X} {Y} {Reach : irel X Y}
        `{!Monoid Reach} : Monad (dia (irel_flip Reach)).
Proof. typeclasses eauto. Qed.
(* TODO Reformulate this in terms of flipped monoidal product. *)
Instance dia_box_adjoint `{Quantale X, !SymMonSet X} {Y} {Reach : irel X Y} :
  dia (irel_flip Reach) ⊣ box Reach.
Proof.
  apply transpose_sufficient => P Q /=; rewrite /pro_le /= /pointwise_relation.
  setoid_rewrite (transpose (Adj:=colim_const_adjoint)).
  setoid_rewrite <- (transpose (Adj:=const_lim_adjoint)).
  rewrite /pro_le /= /pointwise_relation /=.
  setoid_rewrite <- (transpose (Adj:=r_tensor_internal_hom_adjoint)); simpl.
  setoid_rewrite pro_sym' at 1; firstorder.
Qed.

(* Algebas of dia *)
(* ...are the same as coalgebras of box, because we have an adjunction!
      So there is an adjoint triple. *)
Definition free_hpred `{Quantale X, !SymMonSet X} {Y} {Reach : irel X Y} `{!Monoid Reach}
  : (Y -> X) -> hpred Reach
  := free_coEM _.
Definition cofree_hpred `{Quantale X} {Y} {Reach : irel X Y} `{!Monoid Reach}
  : (Y -> X) -> hpred Reach
  := cofree_coEM _.
Arguments free_hpred {_ _ _ _ _ _ _ _ _} Reach {_}.
Arguments cofree_hpred {_ _ _ _ _ _ _ _} Reach {_}.


(* TODO Move these to the right place. *)
Definition Scomb {R X Y} (f : R -> X -> Y) (a : R -> X) : R -> Y := fun r => f r (a r).
Arguments Scomb {_ _ _} f a _ /.
Instance Scomb_functor `{Proset R, Proset X, Proset Y}
         {F : R -> X -> Y} {A : R -> X} `{!Functor F, !forall r, Functor (F r), !Functor A}
  : Functor (Scomb F A).
Proof.
  move=> r r' D /=.
  setoid_rewrite D at 2; generalize (A r'); change (F r ⊢ F r'); by apply/fmap'.
Qed.
Definition SScomb {R X Y Z} (f : R -> X -> Y -> Z) (a : R -> X) (b : R -> Y) : R -> Z
  := fun r => f r (a r) (b r).
Arguments SScomb {_ _ _ _} f a b _ /.
Instance SScomb_functor {Z} `{Proset R, Proset X, Proset Y, Proset Z}
         {F : R -> X -> Y -> Z} {A : R -> X} {B : R -> Y}
         `{!Functor F, !forall r, Functor (F r), !forall r x, Functor (F r x),
             !Functor A, !Functor B}
  : Functor (SScomb F A B).
Proof.
  move=> r r' D /=.
  etransitivity; first by apply: (fmap' (F:=F) D).
  etransitivity; first by apply: (fmap' (F:=F r') (fmap' D)).
    by apply/fmap'/fmap'.
Qed.
Definition liftR2 {R X Y Z} (f : X -> Y -> Z) (a : R -> X) (b : R -> Y) : R -> Z
  := fun r => f (a r) (b r).
Arguments liftR2 {_ _ _ _} f a b _ /.
Instance liftR2_functor {Z} `{Proset R, Proset X, Proset Y, Proset Z}
         {F : X -> Y -> Z} {A : R -> X} {B : R -> Y}
         `{!Functor F, !forall x, Functor (F x), !Functor A, !Functor B}
  : Functor (liftR2 F A B).
Proof.
  move=> r r' D /=.
  setoid_rewrite D at 2; by apply/(fmap' (F:=F))/fmap'.
Qed.
Lemma liftR2_adj : forall `{Proset R, Proset X, Proset Y, Proset R'}
                     {F : X -> Y -> R'}  {A : R -> X}  {B : R -> Y}
                     {F' : X -> Y -> R} {A' : R' -> X} {B' : R' -> Y}
                     `{!Functor F, !forall x, Functor (F x), !Functor A, !Functor B,
                         !Functor F', !forall x, Functor (F' x), !Functor A', !Functor B'},
    (forall x y r', F x y ⊢ r' ↔ x ⊢ A' r' ∧ y ⊢ B' r') ->
    (forall r x y, A r ⊢ x ∧ B r ⊢ y ↔ r ⊢ F' x y) ->
    liftR2 F A B ⊣ liftR2 F' A' B'.
Proof.
  move=> R ? X ? Y ? R' ? F A B F' A' B' ? ? ? ? ? ? ? ? H1 H2.
  change (liftR2 F A B) with (curry F ∘ (fun r => (A r, B r))).
  change (liftR2 F' A' B') with (curry F' ∘ (fun r' => (A' r', B' r'))).
  unshelve eapply compose_adjoint; try typeclasses eauto.
  - apply/transpose_sufficient => -[x y] r' //=.
  - apply/transpose_sufficient => r [x y] //=.
Qed.
Definition Scomb2 {R1 R2 X Y} (f : R1 -> R2 -> X -> Y) (a : R1 -> R2 -> X) : R1 -> R2 -> Y
  := fun r1 r2 => f r1 r2 (a r1 r2).
Arguments Scomb2 {_ _ _ _} f a _ _ /.
Instance Scomb2_functor `{Proset R1, Proset R2, Proset X, Proset Y}
         {F : R1 -> R2 -> X -> Y} {A : R1 -> R2 -> X}
         `{!Functor F, !forall r1 r2, Functor (F r1 r2), !Functor A}
  : Functor (Scomb2 F A).
Proof.
  move=> r1 r1' D r2 /=.
  etransitivity; first by apply: (fmap' (fmap' (F:=A) D r2)).
  generalize r2 (A r1' r2); change (F r1 ⊢ F r1'); by apply/fmap'.
Qed.
Instance Scomb2_functor' `{Proset R1, Proset R2, Proset X, Proset Y}
         {F : R1 -> R2 -> X -> Y} {A : R1 -> R2 -> X}
         `{!Functor F, !forall r1, Functor (F r1), !forall r1 r2, Functor (F r1 r2),
             !forall r1, Functor (A r1)} {r1}
  : Functor (Scomb2 F A r1).
Proof.
  move=> r2 r2' D /=.
  etransitivity; first by apply: (fmap' (fmap' (F:=A r1) D)).
  generalize (A r1 r2'); change (F r1 r2 ⊢ F r1 r2'); by apply/fmap'.
Qed.

(* TODO clean up all of the affine stuff, it's a mess *)
Record act_dualnum {E} `{Proset X} (F : E -> Endo X) : Type
  := ActDualnum {act_realpart : X; act_infpart : E}.
Add Printing Constructor act_dualnum.
Arguments ActDualnum {_ _ _}.
Arguments act_realpart {_ _ _ _}.
Arguments act_infpart {_ _ _ _}.
Definition pro_act_dualnum `{Proset E, Proset X} (F : E -> Endo X)
  : act_dualnum F -> act_dualnum F -> Prop :=
  fun a1 a2 => act_realpart a1 ⊢ act_realpart a2 /\
            act_infpart a1 ⊢ act_infpart a2.
Arguments pro_act_dualnum {E _ X _} F !a1 !a2 /.
Instance pro_act_dualnum_pro `{Proset E, Proset X} {F : E -> Endo X}
  : PreOrder (pro_act_dualnum F).
Proof.
  constructor.
  - firstorder.
  - move=> [A_r A_ε] [B_r B_ε] [C_r C_ε] /= [D1 D2] [D3 D4]; split; by etransitivity.
Qed.
Instance act_dualnum_proset `{Proset E, Proset X} {F : E -> Endo X}
  : Proset (act_dualnum F)
  := {| pro_le := pro_act_dualnum F |}.
Definition tens_act_dualnum `{MonSet E, Complete X}
           (F : E -> Endo X) (a1 a2 : act_dualnum F) : act_dualnum F
  := let (r1, ε1) := a1 in
     let (r2, ε2) := a2 in
     ActDualnum F (r1 + F ε1 r2) (ε1 ⊗ ε2).
Arguments tens_act_dualnum {E _ _ _ _ _} F !a1 !a2 /.
Instance pro_act_dualnum_monoidal `{MonSet E, Complete X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : Monoidal pro_le (tens_act_dualnum F) (ActDualnum F ⊥ memp).
Proof.
  constructor.
  - move=> [A_r A_ε] [A'_r A'_ε] [B_r B_ε] [B'_r B'_ε] /= [D1 D2] [D3 D4]; split.
    + unfold coproduct; apply/fmap' => -[] //; setoid_rewrite D2; by setoid_rewrite D3.
    + by apply/bimap.
  - move=> [A_r A_ε]; split; split => /=.
    + apply/coproduct_left; [apply/initial_left | apply/(pres_memp_op (F:=F))].
    + apply/(proj1 (pro_lunit _)).
    + setoid_rewrite <- coproduct_right2.
      apply/(pres_memp (F:=F)).
    + apply/(proj2 (pro_lunit _)).
  - move=> [A_r A_ε]; split; split => /=.
    + apply/coproduct_left; first by done.
      rewrite distrib_colim; apply/colim_left => -[].
    + apply/(proj1 (pro_runit _)).
    + apply/coproduct_right1.
    + apply/(proj2 (pro_runit _)).
  - move=> [A_r A_ε] [B_r B_ε] [C_r C_ε]; split; split => /=.
    + apply/coproduct_left.
      * etransitivity; apply/coproduct_right1.
      * rewrite distrib_colim; apply/colim_left => -[] /=.
        -- setoid_rewrite <- coproduct_right1; apply/coproduct_right2.
        -- setoid_rewrite <- coproduct_right2; apply/(pres_tens (F:=F)).
    + apply/(proj1 (pro_massoc _ _ _)).
    + apply/coproduct_left; first apply/coproduct_left.
      * setoid_rewrite <- coproduct_right2 at 2.
        apply/coproduct_right1.
      * setoid_rewrite <- coproduct_right2; apply/fmap'/coproduct_right1.
      * setoid_rewrite <- coproduct_right2; setoid_rewrite <- coproduct_right2.
        apply/(pres_tens_op (F:=F)).
    + apply/(proj2 (pro_massoc _ _ _)).
Qed.
Instance act_dualnum_mset `{MonSet E, Complete X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : MonSet (act_dualnum F) := {| pro_tens := tens_act_dualnum F |}.
Lemma act_dualnum_cone : forall `{Proset E, Proset X} {F : E -> Endo X}
                           {R} {d} {J : R -> act_dualnum F},
    cone d J <-> cone (act_realpart d) (act_realpart ∘ J) /\
               cone (act_infpart d) (act_infpart ∘ J).
Proof. firstorder. Qed.
Lemma act_dualnum_cocone : forall `{Proset E, Proset X} {F : E -> Endo X}
                             {R} {J : R -> act_dualnum F} {d},
    cocone J d <-> cocone (act_realpart ∘ J) (act_realpart d) /\
                 cocone (act_infpart ∘ J) (act_infpart d).
Proof. firstorder. Qed.
Lemma ad_curry_dep : forall {E} `{Proset X} {F : E -> Endo X} {P : act_dualnum F -> Prop},
    (forall d, P d) <-> (forall d_r d_ε, P (ActDualnum F d_r d_ε)).
Proof. move=> E X ? F P; split=> [H d_r d_ε | H [d_r d_ε]] //. Qed.
Lemma act_dualnum_lim_cone : forall `{Proset E, Proset X} {F : E -> Endo X}
                             {R} {d} {J : R -> act_dualnum F},
    lim_cone d J <-> lim_cone (act_realpart d) (act_realpart ∘ J) /\
                   lim_cone (act_infpart d) (act_infpart ∘ J).
Proof.
  move=> X Pr_X Y Pr_Y F R d J /=.
  rewrite /lim_cone ad_curry_dep /=; setoid_rewrite (act_dualnum_cone (J:=J));
    firstorder.
Qed.
Lemma act_dualnum_colim_cocone : forall `{Proset E, Proset X} {F : E -> Endo X}
                                 {R} {J : R -> act_dualnum F} {d},
    colim_cocone J d <-> colim_cocone (act_realpart ∘ J) (act_realpart d) /\
                       colim_cocone (act_infpart ∘ J) (act_infpart d).
Proof.
  move=> X Pr_X Y Pr_Y F R J d /=.
  rewrite /colim_cocone ad_curry_dep /=; setoid_rewrite (act_dualnum_cocone (J:=J));
    firstorder.
Qed.
Program Instance act_dualnum_bicomplete `{Complete E, Complete X} {F : E -> Endo X}
  : Complete (act_dualnum F)
  := {| lim R J := ActDualnum F (lim (act_realpart ∘ J)) (lim (act_infpart ∘ J));
        colim R J := ActDualnum F (colim (act_realpart ∘ J)) (colim (act_infpart ∘ J)) |}.
Next Obligation.
  move=> E Pr_E Comp_E X Pr_X Comp_X F R J /=.
  rewrite act_dualnum_lim_cone /=; split; apply: is_lim.
Qed.
Next Obligation.
  move=> E Pr_E Comp_E X Pr_X Comp_X F R J /=.
  rewrite act_dualnum_colim_cocone /=; split; apply: is_colim.
Qed.

Instance ActDualnum_functor `{Proset E, Proset X} {F : E -> Endo X}
  : Functor (ActDualnum F).
Proof. move=> A A' D B //=. Qed.
Instance ActDualnum_functor' `{Proset E, Proset X} {F : E -> Endo X} {A : X}
  : Functor (ActDualnum F A).
Proof. move=> B B' D //=. Qed.
Definition r_ActDualnum {E} `{Proset X} (F : E -> Endo X) (ε : E) : X -> act_dualnum F
  := fun r => ActDualnum F r ε.
Arguments r_ActDualnum {_ _ _} F ε _ /.
Instance r_ActDualnum_functor `{Proset E, Proset X} {F : E -> Endo X} {ε : E}
  : Functor (r_ActDualnum F ε).
Proof. move=> r r' D //=. Qed.
Instance ActDualnum_continuous `{Proset E, Proset X} {F : E -> Endo X}
  : Continuous (curry (ActDualnum F)).
Proof.
  move=> R [d_r d_ε] J [C U] /=; split=> [r | [d'_r d'_ε] C'] /=.
  - by setoid_rewrite <- (C r).
  - apply: (U (d'_r, d'_ε)) => r /=; move: (C' r) => /=; case: (J r) => //=.
Qed.
Instance ActDualnum_cocontinuous `{Proset E, Proset X} {F : E -> Endo X}
  : Cocontinuous (curry (ActDualnum F)).
Proof.
  move=> R J [d_r d_ε] [C U] /=; split=> [r | [d'_r d'_ε] C'] /=.
  - by setoid_rewrite (C r).
  - apply: (U (d'_r, d'_ε)) => r /=; move: (C' r) => /=; case: (J r) => //=.
Qed.
Instance act_realpart_functor `{Proset E, Proset X} {F : E -> Endo X}
  : Functor (act_realpart (F:=F)).
Proof. firstorder. Qed.
Instance act_infpart_functor `{Proset E, Proset X} {F : E -> Endo X}
  : Functor (act_infpart (F:=F)).
Proof. firstorder. Qed.
Instance act_realpart_continuous `{Proset E, Proset X} {F : E -> Endo X}
  : Continuous (act_realpart (F:=F)).
Proof.
  move=> R d J [C U]; split=> [r | d_r' C'] /=; first by firstorder.
  apply: (proj1 (U (ActDualnum F d_r' (act_infpart d)) _)) => r; firstorder.
Qed.
Instance act_realpart_cocontinuous `{Proset E, Proset X} {F : E -> Endo X}
  : Cocontinuous (act_realpart (F:=F)).
Proof.
  move=> R J d [C U]; split=> [r | d_r' C'] /=; first by firstorder.
  apply: (proj1 (U (ActDualnum F d_r' (act_infpart d)) _)) => r; firstorder.
Qed.
Instance act_infpart_continuous `{Proset E, Proset X} {F : E -> Endo X}
  : Continuous (act_infpart (F:=F)).
Proof.
  move=> R d J [C U]; split=> [r | d_ε' C'] /=; first by firstorder.
  apply: (proj2 (U (ActDualnum F (act_realpart d) d_ε') _)) => r; firstorder.
Qed.
Instance act_infpart_cocontinuous `{Proset E, Proset X} {F : E -> Endo X}
  : Cocontinuous (act_infpart (F:=F)).
Proof.
  move=> R J d [C U]; split=> [r | d_ε' C'] /=; first by firstorder.
  apply: (proj2 (U (ActDualnum F (act_realpart d) d_ε') _)) => r; firstorder.
Qed.
Instance ActDualnum0_act_infpart_adjoint `{Proset E, Complete X} {F : E -> Endo X}
  : ActDualnum F ⊥ ⊣ act_infpart.
Proof. constructor=> [M | [A_r A_ε]] //=; by split; first apply: initial_left. Qed.
Instance act_infpart_ActDualnum1_adjoint `{Proset E, Complete X} {F : E -> Endo X}
  : act_infpart ⊣ ActDualnum F ⊤.
Proof. constructor=> [[A_r A_ε] | M] //=; by split; first apply: terminal_right. Qed.
Instance r_ActDualnum0_act_realpart_adjoint `{Complete E, Proset X} {F : E -> Endo X}
  : r_ActDualnum F ⊥ ⊣ act_realpart.
Proof. constructor=> [M | [A_r A_ε]] //=; by split; last apply: initial_left. Qed.
Instance act_realpart_r_ActDualnum1_adjoint `{Complete E, Proset X} {F : E -> Endo X}
  : act_realpart ⊣ r_ActDualnum F ⊤.
Proof. constructor=> [[A_r A_ε] | M] //=; by split; last apply: terminal_right. Qed.
Instance ActDualnum0_strongmon `{MonSet E, Complete X} {F : E -> Endo X}
         `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : StrongMon (ActDualnum F ⊥).
Proof.
  constructor; constructor=> //= M N; (split; last by done).
  - apply: coproduct_left; first by done.
    rewrite distrib_colim; apply/colim_left => -[].
  - apply: initial_left.
Qed.
Instance ActDualnum1_strongmon `{MonSet E, Complete X} {F : E -> Endo X}
         `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : LaxMon (ActDualnum F ⊤).
Proof.
  constructor=> /= [| M N].
  - split; [apply: initial_left | done].
  - split; [apply: terminal_right | done].
Qed.
Instance act_infpart_strongmon `{MonSet E, Complete X} {F : E -> Endo X}
         `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : StrongMon (act_infpart (F:=F)).
Proof. apply/triple_strong. Qed.

Definition act_dualnum_emap {E E'} `{Proset X}
           {F : E -> Endo X} {F' : E' -> Endo X} (Φ : E -> E')
  : act_dualnum F -> act_dualnum F'
  := fun d => ActDualnum F' (act_realpart d) (Φ (act_infpart d)).
Instance act_dualnum_emap_functor `{Functor E E' Φ, Proset X}
         {F : E -> Endo X} {F' : E' -> Endo X}
  : Functor (act_dualnum_emap (F:=F) (F':=F') Φ).
Proof. move=> [A_r A_ε] [B_r B_ε] /= [D1 D2]; by split; last apply: fmap'. Qed.
Instance act_dualnum_emap_laxmon
         `{Functor E E' Φ, !MonSet E, !MonSet E', !LaxMon Φ, Complete X}
         {F : E -> Endo X} {F' : E' -> Endo X}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!OplaxActMorph F F' Φ}
  : LaxMon (act_dualnum_emap (F:=F) (F':=F') Φ).
Proof.
  constructor=> [| [A_r A_ε] [B_r B_ε]] /=.
  - split; [done | apply: pres_memp].
  - split; last by apply: pres_tens.
    apply/fmap'/act_triangle_op.
Qed.
Instance act_dualnum_emap_oplaxmon
         `{Functor E E' Φ, !MonSet E, !MonSet E', !OplaxMon Φ, Complete X}
         {F : E -> Endo X} {F' : E' -> Endo X}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!LaxActMorph F F' Φ}
  : OplaxMon (act_dualnum_emap (F:=F) (F':=F') Φ).
Proof.
  constructor=> [| [A_r A_ε] [B_r B_ε]] /=.
  - split; [done | apply: pres_memp_op].
  - split; last by apply: pres_tens_op.
    apply/fmap'/act_triangle.
Qed.
Instance act_dualnum_emap_strongmon
         `{Functor E E' Φ, !MonSet E, !MonSet E', !StrongMon Φ, Complete X}
         {F : E -> Endo X} {F' : E' -> Endo X}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!StrongActMorph F F' Φ}
  : StrongMon (act_dualnum_emap (F:=F) (F':=F') Φ).
Proof. constructor; typeclasses eauto. Qed.

Definition act_dualnum_xmap {E} `{Proset X, Proset X'}
           {F : E -> Endo X} {F' : E -> Endo X'} (Φ : X -> X')
  : act_dualnum F -> act_dualnum F'
  := fun d => ActDualnum F' (Φ (act_realpart d)) (act_infpart d).
Instance act_dualnum_xmap_functor `{Proset E, Functor X X' Φ}
         {F : E -> Endo X} {F' : E -> Endo X'}
  : Functor (act_dualnum_xmap (F:=F) (F':=F') Φ).
Proof. move=> [A_r A_ε] [B_r B_ε] /= [D1 D2]; by split; first apply: fmap'. Qed.
Instance act_dualnum_xmap_laxmon
         `{MonSet E, Functor X X' Φ, !Complete X, !Complete X'}
         {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!LaxEquivariant F F' Φ}
  : LaxMon (act_dualnum_xmap (F:=F) (F':=F') Φ).
Proof.
  constructor=> [| [A_r A_ε] [B_r B_ε]] /=.
  - split; [apply: initial_left | done].
  - split; last by done.
    apply/coproduct_left; first by setoid_rewrite <- coproduct_right1.
    setoid_rewrite <- coproduct_right2; apply/act_square.
Qed.
Instance act_dualnum_xmap_oplaxmon
         `{MonSet E, Functor X X' Φ, !Cocontinuous Φ, !Complete X, !Complete X'}
         {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!OplaxEquivariant F F' Φ}
  : OplaxMon (act_dualnum_xmap (F:=F) (F':=F') Φ).
Proof.
  constructor=> [| [A_r A_ε] [B_r B_ε]] /=.
  - split; last by done.
    rewrite distrib_colim; apply/colim_left => -[].
  - split; last by done.
    rewrite distrib_colim; apply/colim_left => -[] /=; first by apply/coproduct_right1.
    setoid_rewrite <- coproduct_right2; apply/act_square_op.
Qed.
Instance act_dualnum_xmap_strongmon
         `{MonSet E, Functor X X' Φ, !Cocontinuous Φ, !Complete X, !Complete X'}
         {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         `{!StrongEquivariant F F' Φ}
  : StrongMon (act_dualnum_xmap (F:=F) (F':=F') Φ).
Proof. constructor; typeclasses eauto. Qed.

Definition affinify {E} `{Complete X} (F : E -> Endo X) : act_dualnum F -> Endo X
  := (fun d A => act_realpart d + F (act_infpart d) A) ↑.
(* It turns out that in particular instances, instance resolution will try to use the
   '↑' instances instead of the subsequent 'affinify' instances unless we make 'affinify'
   typeclass opaque. The former instances are insufficient, so opacity is necessary. *)
Typeclasses Opaque affinify.
Instance affinify_functor `{MonSet E, Complete X} {F : E -> Endo X} `{!Functor F}
  : Functor (affinify F).
Proof.
  change (affinify F) with (liftR2 Hom_compose
    ((coproduct ∘ act_realpart (F:=F)) ↑) (F ∘ act_infpart)).
  apply: liftR2_functor. (* typeclasses eauto also works, but this is faster *)
Qed.
Instance affinify_strongmon `{MonSet E, Complete X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
  : StrongMon (affinify F).
Proof.
  constructor; constructor=> [| [A_r A_ε] [B_r B_ε]] C /=.
  - setoid_rewrite <- coproduct_right2; apply/(pres_memp (F:=F)).
  - rewrite -(massoc (Monoidal:=cocartesian_monoidal)); apply/fmap'.
    rewrite distrib_colim; apply/colim_left => -[] /=.
    + apply/coproduct_right1.
    + setoid_rewrite <- coproduct_right2; apply/(pres_tens (F:=F)).
  - apply/coproduct_left.
    + apply/initial_left.
    + apply/(pres_memp_op (F:=F)).
  - rewrite -(massoc (Monoidal:=cocartesian_monoidal)); apply/fmap'/coproduct_left.
    + apply/fmap'/coproduct_right1.
    + setoid_rewrite pres_tens_op; simpl; apply/fmap'/coproduct_right2.
Qed.

Definition prod_act {E} `{Proset X, Proset Y} (L : E -> Endo X) (R : E -> Endo Y)
  : E -> Endo (X * Y)
  := liftR2 prod_map L R ↑.
Instance prod_act_laxmon `{MonSet E, Proset X, Proset Y}
         {L : E -> Endo X} {R : E -> Endo Y}
         `{!Functor L, !LaxMon L, !Functor R, !LaxMon R}
  : LaxMon (prod_act L R).
Proof.
  constructor=> [| M N] [A B] /=; split.
  - apply: (pres_memp (F:=L)).
  - apply: (pres_memp (F:=R)).
  - apply: (pres_tens (F:=L)).
  - apply: (pres_tens (F:=R)).
Qed.
Instance prod_act_oplaxmon `{MonSet E, Proset X, Proset Y}
         {L : E -> Endo X} {R : E -> Endo Y}
         `{!Functor L, !OplaxMon L, !Functor R, !OplaxMon R}
  : OplaxMon (prod_act L R).
Proof.
  constructor=> [| M N] [A B] /=; split.
  - apply: (pres_memp_op (F:=L)).
  - apply: (pres_memp_op (F:=R)).
  - apply: (pres_tens_op (F:=L)).
  - apply: (pres_tens_op (F:=R)).
Qed.
Instance prod_act_strongmon `{MonSet E, Proset X, Proset Y}
         {L : E -> Endo X} {R : E -> Endo Y}
         `{!Functor L, !StrongMon L, !Functor R, !StrongMon R}
  : StrongMon (prod_act L R).
Proof. constructor; typeclasses eauto. Qed.

Instance fst_strong_acm {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
  : StrongEquivariant (prod_act L R) L fst.
Proof. constructor=> M [A B] //=. Qed.
Instance snd_strong_acm {E} `{Proset X, Proset Y} {L : E -> Endo X} {R : E -> Endo Y}
  : StrongEquivariant (prod_act L R) R snd.
Proof. constructor=> M [A B] //=. Qed.
(*
Instance act_dualnum_mset `{MonSet E, Complete X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
*)
Definition affinifyL {E} `{Complete X, Proset Y} (L : E -> Endo X) {R : E -> Endo Y}
  : act_dualnum (prod_act L R) -> Endo X
  := affinify L ∘ act_dualnum_xmap fst.
Definition affinifyR {E} `{Proset X, Complete Y} {L : E -> Endo X} (R : E -> Endo Y)
  : act_dualnum (prod_act L R) -> Endo Y
  := affinify R ∘ act_dualnum_xmap snd.

Instance affinify_lax_equivariant
         `{MonSet E, Complete X, Complete X'} {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         {Φ : X -> X'} `{!Functor Φ, !LaxEquivariant F F' Φ}
  : LaxEquivariant (affinify F) (affinify F' ∘ act_dualnum_xmap Φ) Φ.
Proof.
  move=> [A_r A_ε] B /=.
  apply/coproduct_left; first by setoid_rewrite <- coproduct_right1.
  setoid_rewrite <- coproduct_right2; apply/act_square.
Qed.
Instance affinify_oplax_equivariant
         `{MonSet E, Complete X, Complete X'} {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         {Φ : X -> X'} `{!Functor Φ, !Cocontinuous Φ, !OplaxEquivariant F F' Φ}
  : OplaxEquivariant (affinify F) (affinify F' ∘ act_dualnum_xmap Φ) Φ.
Proof.
  move=> [A_r A_ε] B /=.
  rewrite distrib_colim; apply/colim_left => -[] /=.
  + apply/coproduct_right1.
  + setoid_rewrite <- coproduct_right2; apply/act_square_op.
Qed.
Instance affinify_strong_equivariant
         `{MonSet E, Complete X, Complete X'} {F : E -> Endo X} {F' : E -> Endo X'}
         `{!Functor F, !Functor F', !StrongMon F, !StrongMon F',
           !forall M, Cocontinuous (F M), !forall M, Cocontinuous (F' M)}
         {Φ : X -> X'} `{!Functor Φ, !Cocontinuous Φ, !StrongEquivariant F F' Φ}
  : StrongEquivariant (affinify F) (affinify F' ∘ act_dualnum_xmap Φ) Φ.
Proof. constructor; typeclasses eauto. Qed.

Lemma liftR2_adj' : forall `{Complete R, Proset X, Proset Y, Complete R'}
                       {A : R -> X}  {B : R -> Y} {A_Adj : X -> R} {B_Adj : Y -> R}
                       {A' : R' -> X} {B' : R' -> Y} {A'_Adj : X -> R'} {B'_Adj : Y -> R'}
                       `{!A ⊣ A_Adj, !B ⊣ B_Adj, !A'_Adj ⊣ A', !B'_Adj ⊣ B',
                         !Functor A, !Functor B, !Functor A_Adj, !Functor B_Adj,
                         !Functor A', !Functor B', !Functor A'_Adj, !Functor B'_Adj},
    liftR2 (fun x y => A'_Adj x + B'_Adj y) A B ⊣ liftR2 (fun x y => A_Adj x × B_Adj y) A' B'.
Proof.
  move=> R ? ? X ? Y ? R' ? ? A B A_Adj B_Adj A' B' A'_Adj B'_Adj ? ? ? ? ? ? ? ? ? ? ? ?.
  constructor=> [r | r'] /=.
  - apply/product_right; apply/transpose;
      [setoid_rewrite <- coproduct_right1 | setoid_rewrite <- coproduct_right2];
      apply: adj_unit.
  - apply/coproduct_left; apply/transpose;
      [setoid_rewrite product_left1 | setoid_rewrite product_left2];
      apply: adj_counit.
Qed.

(* TODO Move these *)
Instance id_id_adjoint `{Proset X} : (@id X) ⊣ id.
Proof. done. Qed.
Instance pair0_snd_adjoint `{Complete X, Proset Y}
  : pair ⊥ ⊣ (@snd X Y).
Proof. constructor=> [B | [A B]] //=; by split; first apply: initial_left. Qed.
Instance snd_pair1_adjoint `{Complete X, Proset Y}
  : (@snd X Y) ⊣ pair ⊤.
Proof. constructor=> [[A B] | B] //=; by split; first apply: terminal_right. Qed.
Instance r_pair0_fst_adjoint `{Proset X, Complete Y}
  : r_pair ⊥ ⊣ (@fst X Y).
Proof. constructor=> [A | [A B]] //=; by split; last apply: initial_left. Qed.
Instance fst_r_pair1_adjoint `{Proset X, Complete Y}
  : (@fst X Y) ⊣ r_pair ⊤.
Proof. constructor=> [[A B] | A] //=; by split; last apply: terminal_right. Qed.

Theorem affinify_concrete :
  forall `{MonSet E, !Complete E, Complete X, Complete Y}
    {L : E -> Endo X} {R : E -> Endo Y}
    `{!Functor L, !Functor R, !StrongMon L, !StrongMon R,
      !forall M, Cocontinuous (L M), !forall M, Cocontinuous (R M)}
    {B : Y} (R_B : Y -> E) `{!Hom_eval_at B ∘ R ⊣ R_B, !Functor R_B}
    (Φ : X -> Y) (Ψ : Y -> X) `{!Φ ⊣ Ψ, !Functor Φ, !Functor Ψ, !OplaxEquivariant L R Φ}
    {S T A},
    optic (affinify L) (affinify R ∘ act_dualnum_xmap Φ) S T A B <->
    S ⊢ Ψ T + (L (R_B T) A).
Proof.
  move=> E Pr_E Comp_E MS X Pr_X Comp_X Y Pr_Y Comp_Y L R Funct_L Funct_R
    Strong_L Strong_R Cocont_L Cocont_R B R_B Adj1 Funct_R_B Φ Ψ Adj2
    Funct_Φ Funct_Ψ OplaxACM S T A.
  eassert (Hom_eval_at B ∘ affinify R ∘ act_dualnum_xmap Φ ⊣ (_ : Y -> act_dualnum L)). {
    change (Hom_eval_at _ ∘ _ ∘ _) with (
      liftR2 coproduct (Φ ∘ act_realpart (F:=L))
                       (Hom_eval_at B ∘ R ∘ act_infpart)).
    apply: liftR2_adj'.
  }
  simpl in H.
  rewrite optic_concrete; cbn; split.
  - move=> D; setoid_rewrite D; apply/coproduct_left.
    + apply/transpose; setoid_rewrite (lim_left _ true); simpl.
        by split; first apply: coproduct_right1.
    + setoid_rewrite <- coproduct_right2; apply/act_map/(lim_left _ false).
  - move=> D; setoid_rewrite D; apply/coproduct_left.
    + setoid_rewrite <- coproduct_right1; apply/lim_right => -[] //=.
      apply/terminal_right.
    + setoid_rewrite <- coproduct_right2; apply/act_map/lim_right => -[] //=.
      apply/terminal_right.
Qed.

Corollary affinify_concrete1 :
  forall `{MonSet E, !Complete E, Complete X}
    {F : E -> Endo X}
    `{!Functor F, !StrongMon F, !forall M, Cocontinuous (F M)}
    {S T A B : X} {R_B : X -> E} `{!Hom_eval_at B ∘ F ⊣ R_B, !Functor R_B},
    optic (affinify F) (affinify F) S T A B <-> S ⊢ T + F (R_B T) A.
Proof.
  move=> E Pr_E MS Comp_E X Pr_X Comp F Funct Strong Cont S T A B R_B Adj1 Funct_R_B.
  unshelve eapply (affinify_concrete R_B id id); try typeclasses eauto.
  move=> M //=.
Qed.

Example affine_rel_act_optic : forall `{Quantale X} {R} {S T A B : R -> X},
    optic (affinify (rel_act R)) (affinify (rel_act R)) S T A B <->
    forall rho : R, S rho ⊢ T rho + colim (fun rho' : R => (B rho' ⊸ T rho) ⊗ A rho').
Proof.
  move=> X Pr Comp MS CMS LCMS Quant R S T A B.
  pose proof (_ : compose (colim ∘ r_tensor B) ∘ ap_irel ⊣ _) as Adj.
  erewrite @affinify_concrete1; try typeclasses eauto.
  - split=> D rho; setoid_rewrite D.
    + apply/colim_left => -[] /=; [apply/coproduct_right1 | apply/coproduct_right2].
    + apply/coproduct_left; [apply/(colim_right _ true) | apply/(colim_right _ false)].
  - move=> [M] /=; apply/distrib_colim_sufficient => R' J rho /=.
    apply/colim_left => rho'; rewrite distrib_colim; apply/colim_left => r /=.
    setoid_rewrite <- colim_right; by setoid_rewrite <- colim_right.
Qed.

(* TODO Move this *)
Instance prod_map_adjoint
  `{Adjoint X Y F G, Adjoint X' Y' F' G'}
  : prod_map F F' ⊣ prod_map G G'.
Proof. firstorder. Qed.

Example affine_rel_act_optic' :
  forall `{Quantale X} {R Y} {S : R -> X} {T : Y -> R -> X} {A : R -> X} {B : Y -> R -> X},
    optic (affinify (rel_act R))
          (affinify (conjugate (rel_act R) flip flip ∘ irel_basechange const) ∘
             act_dualnum_xmap const) S T A B <->
    forall rho : R, S rho ⊢ lim (fun y : Y => T y rho) +
      colim (fun rho' : R => lim (fun y : Y => B y rho' ⊸ T y rho) ⊗ A rho').
Proof.
  move=> X Pr Comp MS CMS LCMS Quant R Y S T A B.
  evar (R_B : (Y -> R -> X) -> irel X R).
  eassert (Hom_eval_at B ∘ (conjugate (rel_act R) flip flip ∘ irel_basechange const)
                ⊣ R_B) as Adj. {
    change (Hom_eval_at B ∘ _) with (flip ∘ compose (colim ∘ flip ∘ r_tensor B ∘ flip) ∘
                       ap_irel ∘ irel_basechange const).
    subst R_B; typeclasses eauto.
  }
  erewrite @affinify_concrete.
  (* 😱 *)
  2-5, 9-13: typeclasses eauto.
  - rewrite /coproduct /=; apply/forall_proper => ?.
    split=> D; (etransitivity; [apply: D |]); apply/fmap' => -[] //=.
  - unshelve eapply compose_strongmon; try typeclasses eauto.
    constructor; typeclasses eauto.
  - move=> [M] /=; apply/distrib_colim_sufficient => R' J rho /=.
    apply/colim_left => rho'; rewrite distrib_colim; apply/colim_left => r /=.
    setoid_rewrite <- colim_right; by setoid_rewrite <- colim_right.
  - move=> [M]; apply/distrib_colim_sufficient => R' J y rho /=.
    apply/colim_left => rho'; rewrite /pro_tens /= distrib_colim; apply/colim_left => r /=.
    setoid_rewrite <- colim_right; by setoid_rewrite <- colim_right.
  - move=> [M] P y rho /=; apply/colim_left => rho'.
    rewrite {2}/pro_tens /=; apply/(colim_right _ rho').
Qed.


Definition add_d (a b : discrete nat) : discrete nat
  := Discrete (get_discrete a + get_discrete b)%nat.
Arguments add_d !_ !_ /.
Instance add_d_monoidal : Monoidal pro_le add_d (Discrete 0).
Proof.
  constructor.
  - firstorder.
  - move=> [n] //=.
  - move=> [n] /=; rewrite Nat.add_0_r //.
  - move=> [n] [m] [o] /=; rewrite Nat.add_assoc //.
Qed.
Instance add_d_sym : Sym pro_le add_d.
Proof. move=> [n] [m] /=; rewrite Nat.add_comm //. Qed.
Instance discrete_nat_mset : MonSet (discrete nat) := {| pro_tens := add_d |}.
Instance discrete_nat_smset : SymMonSet (discrete nat) := {}.

Definition series (E : Type) `{Proset E} : Type := Hom (discrete nat) E.
Identity Coercion series_to_hom : series >-> Hom.
(*
Record series (E : Type) := Series {get_coeff :> nat -> E}.
Add Printing Constructor series.
Arguments Series {_}.
Arguments get_coeff {_}.
Definition pro_series `{Proset E} : series E -> series E -> Prop :=
  fun a1 a2 => get_coeff a1 ⊢ get_coeff a2.
Arguments pro_series {E _} !a1 !a2 /.
Instance pro_series_pro `{Proset E} : PreOrder (pro_series (E:=E)).
Proof.
  constructor; first by firstorder.
  move=> [x] [y] [z] /=; etransitivity; eauto.
Qed.
Instance series_proset `{Proset E} : Proset (series E)
  := {| pro_le := pro_series |}.
Lemma series_core : forall `{Proset E} {a1 a2 : series E},
    a1 ⟛ a2 <-> (forall i, a1 i ⟛ a2 i).
Proof. firstorder. Qed.
Instance get_coeff_functor `{Proset E} : Functor (get_coeff (E:=E)).
Proof. firstorder. Qed.
Instance get_coeff_proper `{Proset E}
  : Proper (pro_le ++> (=) ==> pro_le) (get_coeff (E:=E)).
Proof. firstorder. Qed.
Instance get_coeff_proper' `{Proset E}
  : Proper (pro_le --> (=) ==> flip pro_le) (get_coeff (E:=E)).
Proof. move=> [?] [?] /= D ? _ <-; apply: D. Qed.
Instance Series_functor `{Proset E} : Functor (Series (E:=E)).
Proof. firstorder. Qed.
Instance series_adjunction1 `{Proset E} : Series (E:=E) ⊣ get_coeff.
Proof. constructor=> [? | [?]] //=. Qed.
Instance series_adjunction2 `{Proset E} : get_coeff (E:=E) ⊣ Series.
Proof. constructor=> [[?] | ?] //=. Qed.
Program Instance series_bicomplete `{Complete E}
  : Complete (series E)
  := {| lim R J := Series (lim (get_coeff ∘ J));
        colim R J := Series (colim (get_coeff ∘ J)) |}.
Next Obligation. move=> *; apply: (create_lim_cone (F:=Series)). Qed.
Next Obligation. move=> *; apply: (create_colim_cocone (F:=Series)). Qed.
*)

(*
Program Definition series_mul `{MonSet E, !Complete E} (a1 a2 : series E) : series E
  := (fun i => colim (fun ii : {ii | add_d ii.1 ii.2 = i} =>
                     a1 (`ii).1 ⊗ a2 (`ii).2)).
Arguments series_mul {E _ _ _} !a1 !a2 /.
Goal forall `{MonSet E, !Complete E} {a1 a2 : series E}, series_mul a1 a2 ⟛ gday a1 a2.
Proof. intros *. rewrite /series_mul /gday /convolve /universal_lan /= -Hom_core /=.
       move=> n; split; apply/colim_left.
       - move=> [[n1 n2] /= E']; by apply/(colim_right _ (paird _ _ ↾ E')).
       - move=> [ns /= E']; apply/(colim_right _ ((_, _) ↾ E')).
Qed.
Definition series_one `{MonSet E, !Complete E} : series E
  := Series (fun i => if Nat.eqb i 0 then memp else ⊥).
Instance series_mul_monoidal `{Quantale E}
  : Monoidal (pro_le (X:=series E)) (series_mul (E:=E)) series_one.
Proof.
  constructor.
  - move=> [A] [A'] [B] [B'] /= D1 D2 i; by setoid_rewrite D1; setoid_rewrite D2.
  - move=> [A]; apply/series_core => i /=; split.
    + apply/colim_left => -[[i1 i2] /= <-].
      case: PeanoNat.Nat.eqb_spec => [-> | NE] /=; first by rewrite pro_lunit.
      rewrite tensor_hom; apply/initial_left.
    + unshelve setoid_rewrite <- (colim_right _ ((0, i) ↾ _)); [done | simpl].
      rewrite pro_lunit //.
  - move=> [A]; apply/series_core => i /=; split.
    + apply/colim_left => -[[i1 i2] /= <-].
      case: PeanoNat.Nat.eqb_spec => [-> | NE] /=.
      * rewrite -plus_n_O pro_runit //.
      * rewrite l_tensor_hom; apply/initial_left.
    + unshelve setoid_rewrite <- (colim_right _ ((i, 0) ↾ _)); [done | simpl].
      rewrite pro_runit //.
  - move=> [A] [B] [C]; apply/series_core => i /=.
    split; apply/colim_left => -[[i1 i2] /= <-].
    + rewrite l_tensor_hom; apply/colim_left => -[[i21 i22] /= <-];
        rewrite -l_tensor_hom.
      unshelve setoid_rewrite <- (colim_right _ ((i1 + i21, i22)%nat ↾ _));
        first by rewrite /= PeanoNat.Nat.add_assoc.
      simpl; unshelve setoid_rewrite <- (colim_right _ ((i1, i21) ↾ _)); [done |].
      rewrite /= pro_massoc //.
    + rewrite tensor_hom; apply/colim_left => -[[i11 i12] /= <-];
        rewrite -tensor_hom.
      unshelve setoid_rewrite <- (colim_right _ ((i11, i12 + i2)%nat ↾ _));
        first by rewrite /= PeanoNat.Nat.add_assoc.
      simpl; unshelve setoid_rewrite <- (colim_right _ ((i12, i2) ↾ _)); [done |].
      rewrite /= pro_massoc //.
Qed.
*)
Definition series_pow `{MonSet E, !Complete E} (n : nat) (M : series E) : series E
  := Nat.iter n (gday2 M) gday2_memp.
Instance series_pow_proper `{MonSet E, !Complete E}
  : Proper ((=) ==> pro_le ++> pro_le) (series_pow (E:=E)).
Proof.
  move=> n _ <- M M' D; elim: n => //= n D'.
  setoid_rewrite D at 1; by setoid_rewrite D'.
Qed.
Instance series_pow_proper' `{MonSet E, !Complete E}
  : Proper ((=) ==> pro_le --> flip pro_le) (series_pow (E:=E)).
Proof. move=> n _ <- M M'; by apply: series_pow_proper. Qed.
Lemma series_pow_assoc : forall `{Quantale E} {n m} {A : series E},
    series_pow (n + m) A ⟛ gday2 (series_pow n A) (series_pow m A).
Proof.
  move=> E ? ? ? ? ? ? n m A; elim: n => /= [| n IH].
  - rewrite (lunit (R:=pro_le) (T:=gday2)) //.
  - split.
    + etransitivity; first by apply: (bimap (reflexivity A) (proj1 IH)).
      rewrite (massoc (R:=pro_le) (T:=gday2)) //.
    + etransitivity; last by apply: (bimap (reflexivity A) (proj2 IH)).
      rewrite (massoc (R:=pro_le) (T:=gday2)) //.
Qed.

Instance discrete_eqdecision `{EqDecision A} : EqDecision (discrete A).
Proof. move=> [x] [y] /=; case: (decide (x = y)); firstorder. Qed.

Program Definition scale `{MonSet E} (M : E) (a : series E) : series E
  := fun i => M ⊗ a i.
Definition tens_series `{Quantale E} (a1 a2 : series E) : series E
  := colim (fun i => scale (a1 (Discrete i)) (series_pow i a2)).
Arguments tens_series {E _ _ _ _ _ _} !a1 !a2 /.
Program Definition series_id `{MonSet E, !Complete E} : series E
  := fun i => if Nat.eqb (get_discrete i) 1 then memp else ⊥.
Lemma pow_id : forall `{Quantale E} {i j},
    series_pow i series_id j ⟛ if Nat.eqb i (get_discrete j) then memp else ⊥.
Proof.
  move=> E ? ? ? ? ? ?; elim=> [| i IH] [j].
  - case: j => [| j] /=; split.
    + by apply/mon_embed_prop_left.
    + by apply/mon_embed_prop_right.
    + by apply/mon_embed_prop_left.
    + by apply/initial_left.
  - simpl; split.
    + apply/colim_left => -[[[j1] [j2]] /= [<-]].
      case: PeanoNat.Nat.eqb_spec => [-> | NE] /=.
      * rewrite pro_lunit //=; apply IH.
      * rewrite tensor_hom; apply/initial_left.
    + case: j => [| j /=]; first by apply/initial_left.
      unshelve setoid_rewrite <- (colim_right _ ((Discrete 1, Discrete j) ↾ _));
        [done | simpl].
      rewrite pro_lunit IH //.
Qed.
(*
(* _do_ we need symmetry? *)
Lemma pow_tens : forall `{Quantale E, !SymMonSet E} {a1 a2 : series E} {n i},
    series_pow n (tens_series a1 a2) i ⟛
      colim (fun n' => series_pow n a1 n' ⊗ series_pow n' a2 i).
Proof.
  move=> E ? ? ? ? ? ? ? a1 a2; elim=> /= [| n IH] i.
  - case: i => /= [| i]; split.
    + setoid_rewrite <- (colim_right _ 0); rewrite /= pro_runit //.
    + apply/colim_left => -[| n'] /=.
      * rewrite pro_lunit //.
      * rewrite tensor_hom; apply/initial_left.
    + apply/initial_left.
    + apply/colim_left => -[| n'] /=.
      * rewrite pro_lunit //.
      * rewrite tensor_hom; apply/initial_left.
  - split.
    + apply/colim_left => -[[i1 i2] /= <-].
      rewrite tensor_hom; apply/colim_left => j; rewrite -tensor_hom.
      rewrite IH l_tensor_hom; apply/colim_left => j'; rewrite -l_tensor_hom.
      setoid_rewrite <- (colim_right _ (j + j')%nat) at 1.
      setoid_rewrite <- (proj2 series_pow_assoc).
      unshelve setoid_rewrite <- (colim_right _ ((j, j') ↾ _)) at 1; [done | simpl].
      unshelve setoid_rewrite <- (colim_right _ ((i1, i2) ↾ _)) at 1; [done | simpl].
      rewrite -pro_massoc; setoid_rewrite -> pro_massoc at 2.
      setoid_rewrite (proj1 (pro_sym' (_ i1) (_ j'))) at 1.
      rewrite -!pro_massoc //.
    + apply/colim_left => j.
      rewrite tensor_hom; apply/colim_left => -[[j1 j2] /= <-]; rewrite -tensor_hom.
      rewrite series_pow_assoc l_tensor_hom; apply/colim_left => -[[i1 i2] /= <-].
      rewrite -l_tensor_hom.
      unshelve setoid_rewrite <- (colim_right _ ((i1, i2) ↾ _)) at 1; [done | simpl].
      rewrite IH.
      setoid_rewrite <- (colim_right _ j1) at 1.
      setoid_rewrite <- (colim_right _ j2).
      rewrite -pro_massoc; setoid_rewrite -> pro_massoc at 2.
      setoid_rewrite (proj1 (pro_sym' (_ j2) (_ i1))) at 1.
      rewrite -!pro_massoc //.
Qed.
Instance series_monoidal `{Quantale E, !SymMonSet E}
  : Monoidal (pro_le (X:=series E)) (tens_series (E:=E)) series_id.
Proof.
  constructor.
  - move=> [A] [A'] [B] [B'] /= D1 D2 i; by setoid_rewrite D1; setoid_rewrite D2.
  - move=> A; apply/series_core => i /=; split.
    + apply/colim_left => j.
      case: PeanoNat.Nat.eqb_spec => [-> | NE].
      * change (memp ⊗ ((series_mul A series_one) i) ⊢ A i).
        rewrite pro_lunit (runit (R:=pro_le) (T:=series_mul)) //.
      * rewrite tensor_hom; apply/initial_left.
    + setoid_rewrite <- (colim_right _ 1).
      change (A i ⊢ memp ⊗ ((series_mul A series_one) i)).
      rewrite pro_lunit.
        by setoid_rewrite <- (proj2 (runit (R:=pro_le) (T:=series_mul) A)).
  - move=> A; apply/series_core => i /=; split.
    + apply/colim_left => j; rewrite l_tensor_hom; case: j => [| j].
      * simpl; case: PeanoNat.Nat.eqb_spec => [-> | NE].
        -- rewrite -l_tensor_hom pro_runit //.
        -- apply/initial_left.
      * simpl; apply/colim_left => -[[i1 i2] /= <-].
        case: PeanoNat.Nat.eqb_spec => [-> | NE].
        -- rewrite pro_lunit pow_id.
           case: PeanoNat.Nat.eqb_spec => [-> | NE].
           ++ rewrite -l_tensor_hom pro_runit //.
           ++ apply/initial_left.
        -- rewrite tensor_hom; apply/initial_left.
    + setoid_rewrite <- (colim_right _ i).
      rewrite pow_id PeanoNat.Nat.eqb_refl pro_runit //.
  - move=> A B C; apply/series_core => i /=; split.
    + apply/colim_left => j.
      rewrite pow_tens l_tensor_hom; apply/colim_left => j'; rewrite -l_tensor_hom.
      setoid_rewrite <- (colim_right _ j').
      setoid_rewrite <- (colim_right _ j).
      rewrite pro_massoc //.
    + apply/colim_left => j.
      rewrite tensor_hom; apply/colim_left => j'; rewrite -tensor_hom.
      setoid_rewrite <- (colim_right _ j').
      rewrite -pro_massoc pow_tens.
        by setoid_rewrite <- (colim_right _ j).
Qed.
Instance series_mset `{Quantale E, !SymMonSet E}
  : MonSet (series E) := {| pro_tens := tens_series |}.

Program Definition series_act {E} `{MonSet X, !Complete X} (F : E -> Endo X)
  : series E -> Endo X
  := fun a x => colim (fun i => F (a i) (pow i x)).
Next Obligation. move=> E X ? ? ? F a A B D; by setoid_rewrite D. Qed.
Instance series_act_functor `{Proset E, MonSet X, !Complete X} {F : E -> Endo X}
         `{!Functor F}
  : Functor (series_act F).
Proof. move=> a1 a2 D A /=; by setoid_rewrite D. Qed.
Instance series_act_laxmon `{Quantale E, !SymMonSet E, Quantale X}
         {F : E -> Endo X} `{!Functor F, !LaxMon F, !forall M, Cocontinuous (F M)}
         (Strength1 : forall M A B, A ⊗ F M B ⊢ F M (A ⊗ B))
         (Strength2 : forall M A B, F M A ⊗ B ⊢ F M (A ⊗ B))
  : LaxMon (series_act F).
Proof.
  constructor=> [| a1 a2] A /=.
  - setoid_rewrite <- (colim_right _ 1); simpl.
    setoid_rewrite <- pres_memp; rewrite /= pro_runit //.
  - apply/colim_left => i.
    etransitivity. 2: {
      apply: fmap' => j.
      setoid_rewrite <- (colim_right _ i) at 2.
      setoid_rewrite <- pres_tens; simpl.
      apply: reflexivity.
    }
    rewrite -distrib_colim; apply/fmap'.
    elim: i => /= [| i IH].
    + setoid_rewrite <- (colim_right _ 0); simpl.
        by setoid_rewrite <- pres_memp.
    + setoid_rewrite IH; rewrite tensor_hom; apply/colim_left => j.
      rewrite -tensor_hom l_tensor_hom; apply/colim_left => j'.
      rewrite -l_tensor_hom.
      setoid_rewrite <- (colim_right _ (j + j')%nat).
      unshelve setoid_rewrite <- (colim_right _ ((j, j') ↾ _)); [done | simpl].
      setoid_rewrite <- pres_tens; simpl.
      rewrite pow_assoc; setoid_rewrite <- Strength1; by setoid_rewrite <- Strength2.
Qed.
Instance series_act_oplaxmon `{Quantale E, !SymMonSet E, Quantale X}
         {F : E -> Endo X} `{!Functor F, !OplaxMon F, !Cocontinuous F}
         (Costrength1 : forall M A B, F M (A ⊗ B) ⊢ A ⊗ F M B)
         (Costrength2 : forall M A B, F M (A ⊗ B) ⊢ F M A ⊗ B)
  : OplaxMon (series_act F).
Proof.
  constructor=> [| a1 a2] A /=.
  - apply/colim_left => i /=.
    case: PeanoNat.Nat.eqb_spec => [-> | NE].
    + setoid_rewrite pres_memp_op; unfold pow; simpl; rewrite pro_runit //.
    + rewrite distrib_colim; apply/colim_left => -[].
  - apply/colim_left => i.
    rewrite distrib_colim; apply/colim_left => j /=.
    setoid_rewrite pres_tens_op; simpl.
    setoid_rewrite <- (colim_right _ j); apply/fmap'.
    elim: j i => /= [| j IH] i.
    + case: i => [| i] /=.
      * by setoid_rewrite pres_memp_op.
      * rewrite distrib_colim; apply/colim_left => -[].
    + rewrite distrib_colim; apply/colim_left => -[[i1 i2] /= <-].
      rewrite pow_assoc.
      setoid_rewrite pres_tens_op; simpl.
      setoid_rewrite <- (colim_right _ i1) at 1.
      setoid_rewrite Costrength1; setoid_rewrite Costrength2; apply/bimap; first by done.
        by setoid_rewrite IH.
Qed.
Instance series_act_strongmon `{Quantale E, !SymMonSet E, Quantale X}
         {F : E -> Endo X} `{!Functor F, !StrongMon F,
                            !Cocontinuous F, !forall M, Cocontinuous (F M)}
         (SStrength1 : forall M A B, F M (A ⊗ B) ⟛ A ⊗ F M B)
         (SStrength2 : forall M A B, F M (A ⊗ B) ⟛ F M A ⊗ B)
  : StrongMon (series_act F).
Proof.
  constructor.
  - apply/series_act_laxmon; firstorder.
  - apply/series_act_oplaxmon; firstorder.
Qed.

Theorem series_concrete :
  forall `{Quantale E, !SymMonSet E, Quantale X, Quantale Y}
    {L : E -> Endo X} {R : E -> Endo Y}
    `{!Functor L, !Functor R, !LaxMon L, !OplaxMon R,
      !forall M, Cocontinuous (L M), !Cocontinuous R}
    (Strength1 : forall M A B, A ⊗ L M B ⊢ L M (A ⊗ B))
    (Strength2 : forall M A B, L M A ⊗ B ⊢ L M (A ⊗ B))
    (Costrength1 : forall M A B, R M (A ⊗ B) ⊢ A ⊗ R M B)
    (Costrength2 : forall M A B, R M (A ⊗ B) ⊢ R M A ⊗ B)
    (R_Adj : Y -> Y -> E) `{!forall B, Hom_eval_at B ∘ R ⊣ R_Adj B,
                            !forall B, Functor (R_Adj B)}
    {S T A B},
    optic (series_act L) (series_act R) S T A B <->
    S ⊢ colim (fun i => L (R_Adj (pow i B) T) (pow i A)).
Proof.
  move=> E ? ? ? ? ? ? ? X ? ? ? ? ? ? Y ? ? ? ? ? ? L R ? ? ? ? ? ? ? ? ? ?
    R_Adj Adj ? S T A B.
  unshelve erewrite @optic_concrete; try typeclasses eauto.
  3: by apply: series_act_laxmon.
  3: by apply: series_act_oplaxmon.
  3: {
    instantiate (1:=fun C => Series (fun i => R_Adj (pow i B) C)).
    apply/transpose_sufficient.
    move=> a C /=.
    rewrite transpose {1}/pro_le /= /pointwise_relation /const.
      by setoid_rewrite (fun i => transpose (Adj:=Adj (pow i B))).
  }
  2: typeclasses eauto.
    by simpl.
Qed.
*)
