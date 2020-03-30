From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.list.
(* This brings Z into scope, which I tend to use as a variable name sometimes,
   so this dummy definition will prevent me from accidentally using that Z when I thought
   I was doing an implicit binder.
   TODO: Just fucking don't. *)
Definition Z : () := ().

(* TODO Params instances!! *)


Declare Scope proset_scope.
Declare Scope proset_util_scope.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.
(* Local Set Universe Polymorphism. *)

Class Le (X : Type) := pro_le : relation X.
Hint Mode Le ! : typeclass_instances.
Arguments pro_le {_ _} !_ !_ /.
Instance: Params (@pro_le) 2 := {}.
Infix "⊢" := pro_le (no associativity, at level 70) : proset_scope.
Notation "(⊢)" := pro_le (only parsing) : proset_scope.
Class Proset (X : Type) `{le : Le X} := proset_pro :> PreOrder le.
Hint Mode Proset ! - : typeclass_instances.
Instance pro_le_pro `{Proset X} : PreOrder (pro_le (X:=X)).
Proof. done. Qed.
Instance proset_rewrite `{Proset X} : RewriteRelation (pro_le (X:=X)) := {}.
Typeclasses Opaque flip.

Definition core_rel {X} (R : X -> X -> Prop) : X -> X -> Prop := fun a1 a2 => R a1 a2 /\ R a2 a1.
(* TODO Maybe it's bad to block rewriting in R? That could be confusing if we ever
        use core_rel not as pro_core? *)
Instance: Params (@core_rel) 2 := {}.
Instance core_rel_symmetric {X} {R : X -> X -> Prop} : Symmetric (core_rel R).
Proof. firstorder. Qed.
Instance core_rel_equivalence `{PreOrder X R} : Equivalence (core_rel R).
Proof.
  constructor.
  1,2: firstorder.
  move=> a1 a2 a3 [H1 H1'] [H2 H2']; split; etransitivity; eauto.
Qed.
Notation pro_core := (core_rel (⊢)).
Infix "⟛" := pro_core (no associativity, at level 70) : proset_scope.
Notation "(⟛)" := pro_core (only parsing) : proset_scope.
Instance pro_core_sub1 `{Proset X} : @subrelation X (⟛) (⊢). (* | 10. *)
Proof. firstorder. Qed.
Instance pro_core_sub2 `{Proset X} : @subrelation X (⟛) (flip (⊢)). (* | 10. *)
Proof. firstorder. Qed.
Lemma core_eq {X} {R : X -> X -> Prop} `{!Antisymmetric X (=) R} {A B} :
  core_rel R A B -> A = B.
Proof. firstorder. Qed.

Notation "F ⇀ G" := (((⊢) ++> (⊢))%signature F G)
                      (no associativity, at level 70) : proset_scope.
Notation "(⇀)" := ((⊢) ++> (⊢))%signature (only parsing) : proset_scope.
Notation "F ↼ G" := (((⊢) --> (⊢))%signature F G)
                      (no associativity, at level 70) : proset_scope.
Notation "(↼)" := ((⊢) --> (⊢))%signature (only parsing) : proset_scope.
Notation "F ⥊ G" := (((⟛) ==> (⟛))%signature F G)
                      (no associativity, at level 70) : proset_scope.
Notation "(⥊)" := ((⟛) ==> (⟛))%signature (only parsing) : proset_scope.
Notation "F ⥤ G" := (((⊢) ++> (⊢) ++> (⊢))%signature F G)
                      (no associativity, at level 70) : proset_scope.
Notation "(⥤)" := ((⊢) ++> (⊢) ++> (⊢))%signature (only parsing) : proset_scope.
Notation "F ⇋ G" := (((⊢) --> (⊢) ++> (⊢))%signature F G)
                      (no associativity, at level 70) : proset_scope.
Notation "(⇋)" := ((⊢) --> (⊢) ++> (⊢))%signature (only parsing) : proset_scope.
Notation Monotone := (Proper (⇀)).
Notation Antitone := (Proper (↼)).
(* TODO better names lmao *)
Notation Extensional := (Proper (⥊)).
Notation Bimonotone := (Proper (⥤)).
Notation Dimonotone := (Proper (⇋)).

Notation Reflecting := (Inj (⊢) (⊢)).
Notation Antireflecting := (Inj (flip (⊢)) (⊢)).

Lemma mono {X Y} `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F} {A B}
  : A ⊢ B -> F A ⊢ F B.
Proof. firstorder. Qed.
Arguments mono {_ _} & {_ _ _ _} F {_ _ _} _.
Lemma anti `{Proset X, Proset Y} (F : X -> Y) `{!Antitone F} {A B}
  : B ⊢ A -> F A ⊢ F B.
Proof. firstorder. Qed.
Lemma ext `{Proset X, Proset Y} (F : X -> Y) `{!Extensional F} {A B}
  : A ⟛ B -> F A ⟛ F B.
Proof. firstorder. Qed.
Lemma bi `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Bimonotone F} {A B P Q}
  : A ⊢ B -> P ⊢ Q -> F A P ⊢ F B Q.
Proof. firstorder. Qed.
Lemma di `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Dimonotone F} {A B P Q}
  : B ⊢ A -> P ⊢ Q -> F A P ⊢ F B Q.
Proof. firstorder. Qed.
Lemma bi_l `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Bimonotone F} {A B P}
  : A ⊢ B -> F A P ⊢ F B P.
Proof. move=> *; by apply: bi. Qed.
Lemma bi_r `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Bimonotone F} {A P Q}
  : P ⊢ Q -> F A P ⊢ F A Q.
Proof. move=> *; by apply: bi. Qed.
Lemma di_l `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Dimonotone F} {A B P}
  : B ⊢ A -> F A P ⊢ F B P.
Proof. move=> *; by apply: di. Qed.
Lemma di_r `{Proset X, Proset Y, Proset Z'} (F : X -> Y -> Z') `{!Dimonotone F} {A P Q}
  : P ⊢ Q -> F A P ⊢ F A Q.
Proof. move=> *; by apply: di. Qed.
Lemma reflect `{Proset X, Proset Y} (F : X -> Y) `{!Reflecting F} {A B}
  : F A ⊢ F B -> A ⊢ B.
Proof. firstorder. Qed.
Lemma antireflect `{Proset X, Proset Y} (F : X -> Y) `{!Antireflecting F} {A B}
  : F B ⊢ F A -> A ⊢ B.
Proof. firstorder. Qed.

Instance monotone_extensional `{Proset X, Proset Y} {F : X -> Y} `{!Monotone F}
  : Extensional F.
Proof. firstorder. Qed.
Instance antitone_extensional `{Proset X, Proset Y} {F : X -> Y} `{!Antitone F}
  : Extensional F.
Proof. firstorder. Qed.
Instance extensional_flipped `{Proset X, Proset Y} {F : X -> Y} `{!Extensional F}
  : Proper ((⟛) --> (⟛)) F.
Proof. move=> ? ? [? ?]; split; by apply ext. Qed.

Instance compose_proper' {A B C} {RA : relation A} {RB : relation B} {RC : relation C}
  : Proper ((RB --> RC) ++> (RA ++> RB) --> RA --> RC) compose.
Proof. move=> ? ? ? ? ? H; by apply: compose_proper; last apply/flip_respectful. Qed.
Instance compose_proper'' {A B C} {RA : relation A} {RB : relation B} {RC : relation C}
  : Proper ((RB --> RC) ++> (RA --> RB) --> RA ++> RC) compose.
Proof. move=> ? ? ? ? ? H; by apply: compose_proper'. Qed.

Lemma embed `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F, !Reflecting F} {A B}
  : F A ⊢ F B <-> A ⊢ B.
Proof. firstorder. Qed.
Lemma antiembed `{Proset X, Proset Y} (F : X -> Y) `{!Antitone F, !Antireflecting F} {A B}
  : F B ⊢ F A <-> A ⊢ B.
Proof. firstorder. Qed.
Lemma mono_core `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F} {A B}
  : A ⟛ B -> F A ⟛ F B.
Proof. firstorder. Qed.
Lemma anti_core `{Proset X, Proset Y} (F : X -> Y) `{!Antitone F} {A B}
  : A ⟛ B -> F A ⟛ F B.
Proof. firstorder. Qed.
Lemma reflect_core `{Proset X, Proset Y} (F : X -> Y) `{!Reflecting F} {A B}
  : F A ⟛ F B -> A ⟛ B.
Proof. firstorder. Qed.
Lemma antireflect_core `{Proset X, Proset Y} (F : X -> Y) `{!Antireflecting F} {A B}
  : F A ⟛ F B -> A ⟛ B.
Proof. firstorder. Qed.
Lemma embed_core `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F, !Reflecting F} {A B}
  : F A ⟛ F B <-> A ⟛ B.
Proof. firstorder. Qed.
Lemma antiembed_core `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F, !Reflecting F} {A B}
  : F A ⟛ F B <-> A ⟛ B.
Proof. firstorder. Qed.

(* Basic kinds of proset. *)

Definition core (X : Type) : Type := X.
Definition Core {X} (A : X) : core X := A.
Definition get_core {X} (A : core X) : X := A.
Instance: Params (@Core) 1 := {}.
Instance: Params (@get_core) 1 := {}.
Instance core_le `{H : Le X} : Le (core X)
  := @core_rel X (@pro_le X H).
Instance core_proset `{H : Proset X} : @Proset (core X) core_le
  := Equivalence_PreOrder _.
Typeclasses Opaque core Core get_core.
Opaque core Core get_core.
Instance Core_extensional `{Proset X} : Extensional (@Core X).
Proof. firstorder. Qed.
Instance Core_proper `{Proset X} : Proper ((⟛) ==> (⊢)) (@Core X).
Proof. firstorder. Qed.
Instance get_core_mono `{Proset X} : Monotone (@get_core X).
Proof. firstorder. Qed.
Instance get_core_proper `{Proset X} : Proper ((⊢) ==> (⟛)) (@get_core X).
Proof. firstorder. Qed.
Definition cored {X Y} (F : X -> Y) : core X -> Y := F ∘ get_core.
Arguments cored {_ _} _ _ /.
Instance: Params (@cored) 2 := {}.
Instance cored_proper `{Proset X, Proset Y} : Proper ((⥊) ++> (⇀)) (@cored X Y).
Proof. firstorder. Qed.
Definition uncored {X Y} (F : core X -> Y) : X -> Y := F ∘ Core.
Arguments uncored {_ _} _ _ /.
Instance: Params (@uncored) 2 := {}.
Instance uncored_proper `{Proset X, Proset Y}
  : Proper ((⇀) ++> (⟛) ++> (⊢)) (@uncored X Y).
Proof. firstorder. Qed.

Definition discrete (X : Type) : Type := X.
Definition Discrete {X} (A : X) : discrete X := A.
Definition get_discrete {X} (A : discrete X) : X := A.
Instance: Params (@Discrete) 1 := {}.
Instance: Params (@get_discrete) 1 := {}.
Typeclasses Opaque discrete Discrete get_discrete.
Opaque discrete Discrete get_discrete.
Instance discrete_le {X} : Le (discrete X) := eq.
Instance discrete_proset {X} : Proset (discrete X) := {}.
Instance discrete_mono {X} `{Proset Y} {F : discrete X -> Y} : Monotone F | 3.
Proof. move=> a1 a2 /= -> //. Qed.
Instance Discrete_proper `{Proset X, !Antisymmetric X (=) (⊢)}
  : Proper ((⟛) ==> (⊢)) (@Discrete X).
Proof. firstorder. Qed.

Definition indiscrete (X : Type) : Type := X.
Definition Indiscrete {X} (A : X) : indiscrete X := A.
Definition get_indiscrete {X} (A : indiscrete X) : X := A.
Instance: Params (@Indiscrete) 1 := {}.
Instance: Params (@get_indiscrete) 1 := {}.
Typeclasses Opaque indiscrete Indiscrete get_indiscrete.
Opaque indiscrete Indiscrete get_indiscrete.
Instance indiscrete_le {X} : Le (indiscrete X) := fun _ _ => True.
Instance indiscrete_proset {X} : Proset (indiscrete X).
Proof. done. Qed.
Instance indiscrete_mono `{Proset X} {Y} {F : X -> indiscrete Y} : Monotone F | 3.
Proof. done. Qed.

Definition op (X : Type) : Type := X.
Definition Op {X} (A : X) : op X := A.
Definition get_op {X} (A : op X) : X := A.
Instance: Params (@Op) 1 := {}.
Instance: Params (@get_op) 1 := {}.
Instance op_le `{H : Le X} : Le (op X)
  := @flip (op X) (op X) Prop (@pro_le X H).
Instance op_proset `{H : Proset X} : @Proset (op X) op_le.
Proof. rewrite /Proset /pro_le /op_le; typeclasses eauto. Qed.
Typeclasses Opaque op Op get_op.
Opaque op Op get_op.
Lemma op_def `{Proset X} {A B : X} : Op A ⊢ Op B <-> B ⊢ A.
Proof. done. Qed.
Lemma op_def' `{Proset X} {A B : op X} : A ⊢ B <-> get_op B ⊢ get_op A.
Proof. done. Qed.
Lemma op_core `{Proset X} {A B : X}
  : Op A ⟛ Op B <-> A ⟛ B.
Proof. done. Qed.
Lemma op_core' `{Proset X} {A B : op X}
  : A ⟛ B <-> get_op A ⟛ get_op B.
Proof. done. Qed.
Instance Op_anti `{Proset X} : Antitone (@Op X).
Proof. firstorder. Qed.
Instance get_op_anti `{Proset X} : Antitone (@get_op X).
Proof. firstorder. Qed.
Definition pre_opped {X Y} (F : X -> Y) : op X -> Y := F ∘ get_op.
Arguments pre_opped {_ _} _ _ /.
Instance: Params (@pre_opped) 2 := {}.
Instance pre_opped_proper1 `{Proset X, Proset Y} : Proper ((⇀) ++> (↼)) (@pre_opped X Y).
Proof. firstorder. Qed.
Instance pre_opped_proper2 `{Proset X, Proset Y} : Proper ((↼) ++> (⇀)) (@pre_opped X Y).
Proof. firstorder. Qed.
Definition post_opped {X Y} (F : X -> Y) : X -> op Y := Op ∘ F.
Arguments post_opped {_ _} _ _ /.
Instance: Params (@post_opped) 2 := {}.
Instance post_opped_proper1 `{Proset X, Proset Y} : Proper ((⇀) --> (↼)) (@post_opped X Y).
Proof. firstorder. Qed.
Instance post_opped_proper2 `{Proset X, Proset Y} : Proper ((↼) --> (⇀)) (@post_opped X Y).
Proof. firstorder. Qed.
Definition opped {X Y} (F : X -> Y) : op X -> op Y := Op ∘ F ∘ get_op.
Instance: Params (@opped) 2 := {}.
Arguments opped {_ _} _ _ /.
Instance opped_proper1 `{Proset X, Proset Y} : Proper ((⇀) --> (⇀)) (@opped X Y).
Proof. firstorder. Qed.
Instance opped_proper2 `{Proset X, Proset Y} : Proper ((↼) --> (↼)) (@opped X Y).
Proof. firstorder. Qed.

Instance pw_pro {X} `{PreOrder Y R} : PreOrder (pointwise_relation X R).
Proof. constructor; typeclasses eauto. Qed.
Instance pw_le {X} `{Le Y} : Le (X -> Y) := pointwise_relation X (⊢).
Instance pw_proset {X} `{Proset Y} : Proset (X -> Y) := {}.
Lemma pw_core0 {X Y} {R : Y -> Y -> Prop} {F G : X -> Y}
  : core_rel (pointwise_relation X R) F G <-> (forall A, core_rel R (F A) (G A)).
Proof. firstorder. Qed.
Lemma pw_core {X} `{Proset Y} {F G : X -> Y} : F ⟛ G -> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Lemma pw_core' {X} `{Proset Y} {F G : X -> Y} : F ⟛ G <-> (forall A, F A ⟛ G A).
Proof. firstorder. Qed.
Instance pw_core_subrel {X} `{Proset Y}
  : @subrelation (X -> Y) (⟛) (pointwise_relation X (⟛)).
Proof. firstorder. Qed.
Lemma pw_harpoon `{Proset X, Proset Y} {F G : X -> Y}
  : F ⇀ G /\ G ⇀ F <-> [/\ Monotone F, Monotone G & F ⟛ G].
Proof.
  split.
  - move=> [P1 P2]; split; last by firstorder.
    + move=> A B D; rewrite (P1 _ _ D); by apply: P2.
    + move=> A B D; rewrite (P2 _ _ D); by apply: P1.
  - move=> [? ? D]; split=> A B D'; rewrite D'.
    + rewrite D //.
    + rewrite -D //.
Qed.
Lemma pw_harpoon' `{Proset X, Proset Y} {F G : X -> Y}
  : F ⥊ G <-> [/\ Extensional F, Extensional G & F ⟛ G].
Proof.
  split.
  - move=> P; split.
    + move=> A B E; rewrite (P _ _ E); symmetry; by apply: P.
    + move=> A B E; rewrite <- (P _ _ E); symmetry; by apply: P.
    + split=> A; by apply (P A A).
  - move=> [? ? E] A B E'; rewrite E E' //.
Qed.
Instance const_proper `{Proset X, Proset Y} : Bimonotone (@const Y X).
Proof. firstorder. Qed.
Instance const_mono {X} `{Proset Y} : Monotone (@const Y X).
Proof. firstorder. Qed.
Instance precomp_mono {X X'} `{Proset Y} {f : X' -> X} : Monotone (fun g : X -> Y => g ∘ f).
Proof. firstorder. Qed.
Instance postcomp_proper {X} `{Proset Y, Proset Y'}
  : Proper ((⇀) ++> (⊢) ++> (⊢)) (@compose X Y Y').
Proof. firstorder. Qed.
Definition eval_at {X Y} (x : X) : (X -> Y) -> Y := fun f => f x.
Arguments eval_at {_ _} _ _ /.
Instance: Params (@eval_at) 2 := {}.
Instance eval_at_mono {X} `{Proset Y} {x : X} : Monotone (@eval_at X Y x).
Proof. firstorder. Qed.
Instance flip_mono {X1 X2} `{Proset Y} : Monotone (@flip X1 X2 Y).
Proof. firstorder. Qed.

Definition sig_rel {X} (R : X -> X -> Prop) (P : X -> Prop) : sig P -> sig P -> Prop :=
  fun s1 s2 => R (`s1) (`s2).
Arguments sig_rel {_} _ _ !_ !_ /.
Instance: Params (@sig_rel) 3 := {}.
Instance sig_reflexive `{Reflexive X R} {P} : Reflexive (sig_rel R P).
Proof. by compute. Qed.
Instance sig_transitive `{Transitive X R} {P} : Transitive (sig_rel R P).
Proof. move=> a b c; unfold sig_rel; by etransitivity. Qed.
Instance sig_symmetric `{Symmetric X R} {P} : Symmetric (sig_rel R P).
Proof. by compute. Qed.
Instance sig_le `{Le X} {P : X -> Prop} : Le (sig P) := sig_rel (⊢) P.
Arguments sig_le {_ _ _} /.
Instance sig_proset `{Proset X} {P : X -> Prop} : Proset (sig P).
Proof. constructor; typeclasses eauto. Defined.
(* TODO Think this one over. *)
Instance: Params (@sval) 2 := {}.
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
Instance: Params (@pack) 1 := {}.
Instance: Params (@pack_ph) 2 := {}.
Instance: Params (@restrict_cod) 2 := {}.
Instance: Params (@restrict_cod_ph) 3 := {}.
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

Definition Hom (X Y : Type) `{Proset X, Proset Y} : Type :=
  @sig (X -> Y) Monotone.
(* TODO Fix the brittleness with rewriting by Hom inequalities. *)
Definition ap_Hom (X Y : Type) `{Proset X, Proset Y} : Hom X Y -> X -> Y
  := sval.
Arguments ap_Hom {_ _ _ _ _ _} !_.
Instance: Params (@ap_Hom) 6 := {}.
Coercion ap_Hom : Hom >-> Funclass.
Instance ap_Hom_bi `{Proset X, Proset Y} : Bimonotone (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> [F ?] [G ?] /= D ? ? -> //. Qed.
(* TODO figure out the backwards rewrite issues!!
Instance ap_Hom_bi' `{Proset X, Proset Y}
  : Proper (pro_le --> pro_le --> flip pro_le) (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> [? ?] [? ?] /= D ? ? /= D'; rewrite D' //. Qed.
*)
Instance Hom_mono `{Proset X, Proset Y} (F : Hom X Y) : Monotone F := proj2_sig _.
Lemma ap_map `{Proset X, Proset Y} {F F' : Hom X Y} {A}
  : F ⊢ F' -> F A ⊢ F' A.
Proof. intros *; apply. Qed.
Definition in_Hom `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F} : Hom X Y :=
  F packed_with Monotone.
Arguments in_Hom {_ _ _ _ _ _} F {_} /.
Instance: Params (@in_Hom) 6 := {}.
Lemma ap_Hom_in_Hom `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F}
  : ap_Hom (in_Hom F) = F.
Proof. done. Qed.
(* WARNING: This is brittle. It won't work in cases where the implicit arguments are filled
            differently from how Coq has inferred them here. *)
Lemma in_Hom_ap_Hom `{Proset X, Proset Y} {F : Hom X Y} : in_Hom (ap_Hom F) = F.
Proof. move=> *; rewrite /= -sig_eta //. Qed.
Lemma Hom_core `{Proset X, Proset Y} {F G : Hom X Y} : (forall A, F A ⟛ G A) <-> F ⟛ G.
Proof. compute; firstorder. Qed.
Definition Hom_id `{Proset X} : Hom X X := in_Hom id.
Definition Hom_compose `{Proset X, Proset Y, Proset Z'}
           (F : Hom Y Z') (G : Hom X Y) : Hom X Z' := in_Hom (F ∘ G).
Infix "○" := Hom_compose (at level 40) : proset_scope.
Notation "( f ○.)" := (Hom_compose f) (only parsing) : proset_scope.
Notation "(.○ f )" := (flip Hom_compose f) (only parsing) : proset_scope.
Instance: Params (@Hom_id) 3 := {}.
Instance: Params (@Hom_compose) 9 := {}.
Instance Hom_compose_bi `{Proset X, Proset Y, Proset Z'}
  : Bimonotone (Hom_compose (X:=X) (Y:=Y) (Z':=Z')).
Proof. move=> f g D f' g' D' x /=; rewrite D D' //. Qed.
Lemma Hom_id_lident `{Proset X, Proset Y} {F : Hom X Y}
  : Hom_id ○ F ⟛ F.
Proof. compute; by fold (pro_le (X:=Y)). Qed.
Lemma Hom_id_rident `{Proset X, Proset Y} {F : Hom X Y}
  : F ○ Hom_id ⟛ F.
Proof. compute; by fold (pro_le (X:=Y)). Qed.
Lemma Hom_compose_assoc `{Proset X, Proset Y, Proset Z', Proset W}
      {F : Hom Z' W} {G : Hom Y Z'} {H' : Hom X Y}
  : F ○ (G ○ H') ⟛ (F ○ G) ○ H'.
Proof. compute; by fold (pro_le (X:=W)). Qed.
Definition Hom_eval_at `{Proset X, Proset Y} (x : X) : Hom X Y -> Y := fun F => F x.
Arguments Hom_eval_at {_ _ _ _ _ _} _ _ /.
Instance: Params (@Hom_eval_at) 6 := {}.
Instance Hom_eval_at_bi `{Proset X, Proset Y}
  : Bimonotone (Hom_eval_at (X:=X) (Y:=Y)).
Proof. move=> A B D F G D' /=; rewrite D D' //. Qed.

(* TODO Maybe shouldn't do this. *)
Arguments prod_relation {A B} R1 R2 !x !y /.
Instance: Params (@prod_relation) 4 := {}.
Instance prod_relation_pro `{PreOrder X R, PreOrder Y R'}
  : PreOrder (prod_relation R R').
Proof. constructor; typeclasses eauto. Qed.
Instance prod_le `{Le X, Le Y} : Le (X * Y) := prod_relation (⊢) (⊢).
Arguments prod_le {_ _ _ _} !x !y /.
Instance: Params (@prod_le) 4 := {}.
Instance prod_proset `{Proset X, Proset Y} : Proset (X * Y) := {}.
Instance fst_mono `{Proset X, Proset Y} : Monotone (@fst X Y).
Proof. typeclasses eauto. Qed.
Instance snd_mono `{Proset X, Proset Y} : Monotone (@snd X Y).
Proof. typeclasses eauto. Qed.
Instance pair_bi `{Proset X, Proset Y} : Bimonotone (@pair X Y).
Proof. typeclasses eauto. Qed.
Instance prod_map_proper `{Proset X, Proset X', Proset Y, Proset Y'}
  : Proper ((⇀) ++> (⇀) ++> (⇀)) (@prod_map X X' Y Y').
Proof. firstorder. Qed.
Instance curry_proper `{Proset X, Proset Y, Proset Z'}
  : Proper ((⥤) ++> (⇀)) (@curry X Y Z').
Proof. move=> F G D [A B] [A' B'] /=; firstorder. Qed.
Instance uncurry_proper `{Proset X, Proset Y, Proset Z'}
  : Proper ((⇀) ++> (⥤)) (@uncurry X Y Z').
Proof. firstorder. Qed.

Instance void_le : Le void := fun _ _ => True.
Instance void_proset : Proset void.
Proof. done. Qed.
Instance void_mono1 `{Proset X} {F : void -> X} : Monotone F | 3.
Proof. move=> []. Qed.
Instance void_mono2 `{Proset X} {F : X -> void} : Monotone F | 3.
Proof. firstorder. Qed.

Instance unit_le : Le () := fun _ _ => True.
Instance unit_proset : Proset ().
Proof. done. Qed.
Instance unit_mono1 `{Proset X} {F : unit -> X} : Monotone F | 3.
Proof. move=> [] [] //. Qed.
Instance unit_mono2 `{Proset X} {F : X -> unit} : Monotone F | 3.
Proof. done. Qed.

Instance prop_le : Le Prop := impl.
Instance prop_proset : Proset Prop.
Proof. firstorder. Qed.
Instance and_bi : Bimonotone and.
Proof. firstorder. Qed.
Instance or_bi : Bimonotone or.
Proof. firstorder. Qed.
Instance not_anti : Antitone not.
Proof. firstorder. Qed.
Instance impl_di : Dimonotone impl.
Proof. firstorder. Qed.

Instance nat_le : Le nat := Nat.le.
Instance nat_proset : Proset nat := {}.
Definition chain `{Proset X} (F : nat -> X) : Prop := forall n, F n ⊢ F (S n).
Instance: Params (@chain) 3 := {}.
Lemma chain_mono `{Proset X} {F : nat -> X} :
  Monotone F <-> chain F.
Proof.
  split.
  - move=> ? n; apply: mono; by constructor.
  - move=> Chain n m; elim: m / => //=; by etransitivity.
Qed.
Instance S_mono : Monotone S.
Proof. compute => *; lia. Qed.
Instance S_reflect : Reflecting S.
Proof. compute => *; lia. Qed.
Instance pred_mono : Monotone Nat.pred.
Proof. move=> -[| n] -[| m]; compute; lia. Qed.
Instance add_bi : Bimonotone Nat.add.
Proof. move=> ? ? ? ? ? ?; by apply: Nat.add_le_mono. Qed.
Instance mul_bi : Bimonotone Nat.mul.
Proof. move=> ? ? ? ? ? ?; by apply: Nat.mul_le_mono. Qed.

Instance bool_le : Le bool := implb.
Instance bool_proset : Proset bool.
Proof. constructor=> [[] | [] []] //=. Qed.
Instance andb_bi : Bimonotone andb.
Proof. move=> [] [] // _ [] [] //. Qed.
Instance orb_bi : Bimonotone orb.
Proof. move=> [] [] // _ [] [] //. Qed.
Instance notb_anti : Antitone negb.
Proof. move=> [] //. Qed.
Instance implb_di : Dimonotone implb.
Proof. move=> [] [] // _ [] [] //. Qed.

Instance list_le `{Le X} : Le (list X) := Forall2 (⊢).
Instance list_proset `{Proset X} : Proset (list X) := {}.
Instance list_map_mono `{Proset X, Proset Y} : Monotone (fmap (M:=list) (A:=X) (B:=Y)).
Proof. move=> F G D As; apply/Forall2_fmap/Forall2_impl; firstorder. Qed.
Instance list_map_proper `{Proset X, Proset Y}
  : Proper ((⇀) ++> (⇀)) (fmap (M:=list) (A:=X) (B:=Y)).
Proof. move=> F G D As Bs D'; apply/Forall2_fmap/Forall2_impl; by eauto. Qed.
Instance cons_bi `{Proset X} : Bimonotone (@cons X).
Proof. by constructor. Qed.
Instance mret_mono `{Proset X} : Monotone (mret (M:=list) (A:=X)).
Proof. by constructor. Qed.
