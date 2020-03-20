From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.

Require Import proset.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Definition lower_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, A ⊢ J r.
Definition upper_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, J r ⊢ A.
Instance lower_bound_proper `{Proset X} {R}
  : Proper ((⊢) ++> (↼)) (lower_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 D_A L r.
  setoid_rewrite <- D_A; by setoid_rewrite <- (D_J r).
Qed.
Instance lower_bound_ext `{Proset X} {R} {J : R -> X} : Extensional (lower_bound J).
Proof. typeclasses eauto. Qed.
Instance upper_bound_proper `{Proset X} {R}
  : Proper ((⊢) --> (⇀)) (upper_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 D_A U r.
  setoid_rewrite <- D_A; by setoid_rewrite (D_J r).
Qed.
Instance upper_bound_ext `{Proset X} {R} {J : R -> X} : Extensional (upper_bound J).
Proof. typeclasses eauto. Qed.
Instance lower_bound_proper' `{Proset X} {R}
  : Proper ((⊢) --> (⊢) ++> flip impl) (lower_bound (X:=X) (R:=R)).
Proof. move=> ? ? ? ? ? ?; by apply: lower_bound_proper. Qed.
Instance lower_bound_proper'' `{Proset X} {R}
  : Proper ((⟛) ==> (⥊)) (lower_bound (X:=X) (R:=R)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: lower_bound_proper.
Qed.
Instance upper_bound_proper' `{Proset X} {R}
  : Proper ((⊢) ++> (⊢) --> flip impl) (upper_bound (X:=X) (R:=R)).
Proof. move=> ? ? ? ? ? ?; by apply: upper_bound_proper. Qed.
Instance upper_bound_proper'' `{Proset X} {R}
  : Proper ((⟛) ==> (⥊)) (upper_bound (X:=X) (R:=R)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: upper_bound_proper.
Qed.

Definition pred_lower_bound `{Proset X} (P : X -> Prop) (A : X) : Prop
  := forall B, P B -> A ⊢ B.
Definition pred_upper_bound `{Proset X} (P : X -> Prop) (A : X) : Prop
  := forall B, P B -> B ⊢ A.
Instance pred_lower_bound_proper `{Proset X}
  : Proper ((⊢) --> (↼)) (pred_lower_bound (X:=X)).
Proof.
  move=> P1 P2 D_P A1 A2 D_A L B /D_P.
  setoid_rewrite <- D_A; apply: L.
Qed.
Instance pred_upper_bound_proper `{Proset X}
  : Proper ((⊢) --> (⇀)) (pred_upper_bound (X:=X)).
Proof.
  move=> P1 P2 D_P A1 A2 D_A U B /D_P ?.
  setoid_rewrite <- D_A; by apply: U.
Qed.
Instance pred_lower_bound_proper' `{Proset X}
  : Proper ((⊢) ++> (⊢) ++> flip impl) (pred_lower_bound (X:=X)).
Proof. move=> ? ? ? ? ? ?; by apply: pred_lower_bound_proper. Qed.
Instance pred_lower_bound_proper'' `{Proset X}
  : Proper ((⟛) ==> (⥊)) (pred_lower_bound (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: pred_lower_bound_proper.
Qed.
Instance pred_upper_bound_proper' `{Proset X}
  : Proper ((⊢) ++> (⊢) --> flip impl) (pred_upper_bound (X:=X)).
Proof. move=> ? ? ? ? ? ?; by apply: pred_upper_bound_proper. Qed.
Instance pred_upper_bound_proper'' `{Proset X}
  : Proper ((⟛) ==> (⥊)) (pred_upper_bound (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: pred_upper_bound_proper.
Qed.

Definition pred_diagram `{Proset X} (P : X -> Prop) : sig P -> X
  := sval.
Arguments pred_diagram {_ _} _ /.
Lemma pred_lb_lb `{Proset X} (P : X -> Prop) (A : X)
  : pred_lower_bound P A <-> lower_bound (pred_diagram P) A.
Proof.
  split.
  - move=> L [B P_B]; auto.
  - move=> L B P_B; apply: (L (B ↾ P_B)).
Qed.
Lemma pred_ub_ub `{Proset X} (P : X -> Prop) (A : X)
  : pred_upper_bound P A <-> upper_bound (pred_diagram P) A.
Proof.
  split.
  - move=> U [B P_B]; auto.
  - move=> U B P_B; apply: (U (B ↾ P_B)).
Qed.

Definition image `{Proset X} {R} (J : R -> X) : X -> Prop
  := fun A => exists r, J r ⟛ A.
Arguments image {_ _ _} _ _ /.
Instance image_proper `{Proset X} {R}
  : Proper ((⟛) ==> (⥊)) (image (X:=X) (R:=R)).
Proof.
  apply: proper_sym_impl_iff_2.
  move=> J J' E_J A A' E_A /= [r] E; exists r.
  rewrite -E_J -E_A //.
Qed.
Lemma lb_pred_lb `{Proset X} {R} (J : R -> X) (A : X)
  : lower_bound J A <-> pred_lower_bound (image J) A.
Proof.
  split.
  - move=> L B [r E]; by setoid_rewrite <- (proj1 E).
  - move=> L r; apply/L; by exists r.
Qed.
Lemma ub_pred_ub `{Proset X} {R} (J : R -> X) (A : X)
  : upper_bound J A <-> pred_upper_bound (image J) A.
Proof.
  split.
  - move=> U B [r E]; by setoid_rewrite (proj2 E).
  - move=> U r; apply/U; by exists r.
Qed.

Definition least `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ pred_lower_bound P A.
Definition greatest `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ pred_upper_bound P A.
Arguments least {_ _} _ _ /.
Arguments greatest {_ _} _ _ /.
Instance least_proper `{Proset X}
  : Proper ((⥊) ==> (⟛) ==> iff) (least (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2.
  - firstorder.
  - move=> ? ? /pw_harpoon' [? ? E1] ? ? E2 /= [H1 H2].
      by rewrite -> E1, E2 in H1, H2.
Qed.
Instance greatest_proper `{Proset X}
  : Proper ((⥊) ==> (⟛) ==> iff) (greatest (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2.
  - firstorder.
  - move=> ? ? /pw_harpoon' [? ? E1] ? ? E2 /= [H1 H2].
      by rewrite -> E1, E2 in H1, H2.
Qed.
Lemma least_unique `{Proset X} {P : X -> Prop} `{!Extensional P} {A A'}
  : least P A -> least P A' -> A ⟛ A'.
Proof. firstorder. Qed.
Lemma greatest_unique `{Proset X} {P : X -> Prop} `{!Extensional P} {A A'}
  : greatest P A -> greatest P A' -> A ⟛ A'.
Proof. firstorder. Qed.

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
Lemma inf_universal `{Proset X} {R} {J : R -> X} `{!HasInf J} {A : X}
  : lower_bound J A <-> A ⊢ inf J.
Proof.
  split; first by apply/inf_right.
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
Lemma sup_universal `{Proset X} {R} {J : R -> X} `{!HasSup J} {A : X}
  : upper_bound J A <-> sup J ⊢ A.
Proof.
  move=> *; split; first by apply/sup_left.
  move=> D; setoid_rewrite <- D; apply: sup_ub.
Qed.
(*
Definition InfsOfShape (R X : Type) `{!Proset R, !Proset X} : Type
  := forall J : R -> X, Monotone J -> HasInf J.
Definition SupsOfShape (R X : Type) `{!Proset R, !Proset X} : Type
  := forall J : R -> X, Monotone J -> HasSup J.
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
Instance ios_def `{IOS : InfsOfShape R X} {J : R -> X} `{!Monotone J} : HasInf J
  := IOS J _.
Instance sos_def `{SOS : SupsOfShape R X} {J : R -> X} `{!Monotone J} : HasSup J
  := SOS J _.
Instance dios_def `{DIOS : DInfsOfShape R X} {J : R -> X} : HasInf J
  := DIOS J.
Instance dsos_def `{DSOS : DSupsOfShape R X} {J : R -> X} : HasSup J
  := DSOS J.
*)

Notation InfsOfShape R X := (forall J : R -> X, Monotone J -> HasInf J).
Notation SupsOfShape R X := (forall J : R -> X, Monotone J -> HasSup J).
Notation DInfsOfShape R X := (forall J : R -> X, HasInf J).
Notation DSupsOfShape R X := (forall J : R -> X, HasSup J).

Lemma inf_from_discrete {R} `{Proset X} {J : R -> X}
  : HasInf (J ∘ get_discrete) -> HasInf J.
Proof. done. Defined.
Lemma sup_from_discrete {R} `{Proset X} {J : R -> X}
  : HasSup (J ∘ get_discrete) -> HasSup J.
Proof. done. Defined.
Lemma infs_from_discrete `{Proset X, Proset R}
  : InfsOfShape (discrete R) X -> DInfsOfShape R X.
Proof. move=> IOS J; exists (inf (J ∘ get_discrete)); apply: is_inf. Defined.
Lemma sups_from_discrete `{Proset X, Proset R}
  : SupsOfShape (discrete R) X -> DSupsOfShape R X.
Proof. move=> SOS J; exists (sup (J ∘ get_discrete)); apply: is_sup. Defined.

Definition einf `{Proset X} {R} `{!DInfsOfShape R X} (J : R -> X) : X := inf J.
Definition esup `{Proset X} {R} `{!DSupsOfShape R X} (J : R -> X) : X := sup J.
Arguments einf {_ _ _ _} _ /.
Arguments esup {_ _ _ _} _ /.
Instance inf_mono {R} `{Proset X, !DInfsOfShape R X}
  : Monotone (einf (X:=X) (R:=R)).
Proof. move=> A B D /=; apply/inf_right => r; by apply/inf_left. Qed.
Instance sup_mono {R} `{Proset X, !DSupsOfShape R X}
  : Monotone (esup (X:=X) (R:=R)).
Proof. move=> A B D /=; apply/sup_left => r; by apply/sup_right. Qed.

Notation MeetSemilattice X
  := (forall `{H : EqDecision R}, @Finite R H -> DInfsOfShape R X).
Notation JoinSemilattice X
  := (forall `{H : EqDecision R}, @Finite R H -> DSupsOfShape R X).
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
  direct `{Finite R} (J : R -> X) : exists A, upper_bound J A.
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
Lemma ub_diagram_spec `{Proset X} {R} {J : R -> X} {A}
  : glb (ub_diagram J) A <-> lub J A.
Proof.
  split=> [Glb | Lub].
  - pose HI := {| inf := A; is_inf := Glb |}; change A with (inf (ub_diagram J)); split.
    + move=> r; apply/inf_right => -[B UB] //=.
    + move=> B UB; by apply/(inf_left (B ↾ UB)).
  - pose HS := {| sup := A; is_sup := Lub |}; change A with (sup J); split.
    + move=> [B UB]; apply/sup_left => r //=.
    + move=> B LB; apply/(LB (sup J ↾ _))/sup_ub.
Qed.
Lemma lb_diagram_spec `{Proset X} {R} {J : R -> X} {A}
  : lub (lb_diagram J) A <-> glb J A.
Proof.
  split=> [Lub | Glb].
  - pose HS := {| sup := A; is_sup := Lub |}; change A with (sup (lb_diagram J)); split.
    + move=> r; apply/sup_left => -[B LB] //=.
    + move=> B LB; by apply/(sup_right (B ↾ LB)).
  - pose HI := {| inf := A; is_inf := Glb |}; change A with (inf J); split.
    + move=> [B LB]; apply/inf_right => r //=.
    + move=> B UB; apply/(UB (inf J ↾ _))/inf_lb.
Qed.
Definition infs_sufficient `{Proset X, !InfLattice X} : SupLattice X
  := fun R J => {| sup := inf (ub_diagram J); is_sup := proj1 ub_diagram_spec (is_inf _) |}.
Definition sups_sufficient `{Proset X, !SupLattice X} : InfLattice X
  := fun R J => {| inf := sup (lb_diagram J); is_inf := proj1 lb_diagram_spec (is_sup _) |}.

Lemma inf_unique `{Proset X} {R} {A} {J : R -> X} `{!HasInf J}
  : glb J A <-> A ⟛ inf J.
Proof.
  split.
  - move=> Glb; apply/(greatest_unique Glb (is_inf _)).
    (* TODO Why is rewrite hanging here?! *)
  - move=> E; apply/(greatest_proper _ _ proper_prf _ _ E); apply: is_inf.
Qed.
Lemma sup_unique `{Proset X} {R} {A} {J : R -> X} `{!HasSup J}
  : lub J A <-> A ⟛ sup J.
Proof.
  split.
  - move=> Lub; apply/(least_unique Lub (is_sup _)).
    (* TODO Why is rewrite hanging here?! *)
  - move=> E; apply/(least_proper _ _ proper_prf _ _ E); apply: is_sup.
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
  move=> X ? R J ?; split=> [r | A LB] /=.
  (* TODO Work out better utilities for working with op. *)
  - rewrite op_def; by apply/(sup_right r).
  - apply/sup_left; firstorder.
Qed.
Program Instance op_sup `{Proset X} {R} {J : R -> op X} `{!HasInf (get_op ∘ J)}
  : HasSup J
  := {| sup := Op (inf (get_op ∘ J)) |}.
Next Obligation.
  move=> X ? R J ?; split=> [r | A UB] /=.
  - rewrite op_def; by apply/(inf_left r).
  - apply/inf_right; firstorder.
Qed.
Lemma curry_dep {A B} {P : A * B -> Prop} : (forall p, P p) <-> (forall a b, P (a, b)).
Proof. split=> [H a b | H [a b]] //. Qed.
Lemma uncurry_dep {A B} {P : A -> B -> Prop} : (forall a b, P a b) <-> (forall p, P p.1 p.2).
Proof. split=> [H p | H a b] //; apply: (H (a, b)). Qed.
Lemma prod_lb `{Proset X, Proset Y} {R} {p} {J : R -> X * Y}
  : lower_bound J p <-> lower_bound (fst ∘ J) p.1 /\ lower_bound (snd ∘ J) p.2.
Proof. firstorder. Qed.
Lemma prod_ub `{Proset X, Proset Y} {R} {J : R -> X * Y} {p}
  : upper_bound J p <-> upper_bound (fst ∘ J) p.1 /\ upper_bound (snd ∘ J) p.2.
Proof. firstorder. Qed.
Program Instance prod_inf `{Proset X, Proset Y} {R} {J : R -> X * Y}
        `{!HasInf (fst ∘ J), !HasInf (snd ∘ J)}
  : HasInf J
  := {| inf := (inf (fst ∘ J), inf (snd ∘ J)) |}.
Next Obligation.
  move=> ? ? ? ? ? J ? ?.
  rewrite /greatest /pred_upper_bound curry_dep; setoid_rewrite (prod_lb (J:=J)); simpl.
  setoid_rewrite inf_universal; firstorder.
Qed.
Program Instance prod_sup `{Proset X, Proset Y} {R} {J : R -> X * Y}
        `{!HasSup (fst ∘ J), !HasSup (snd ∘ J)}
  : HasSup J
  := {| sup := (sup (fst ∘ J), sup (snd ∘ J)) |}.
Next Obligation.
  move=> ? ? ? ? ? J ? ?.
  rewrite /least /pred_lower_bound curry_dep; setoid_rewrite (prod_ub (J:=J)); simpl.
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
Lemma embed_prop_left `{Complete X} {P : Prop} {Q : X}
  : (P -> ⊤ ⊢ Q) -> ⌜ P ⌝ ⊢ Q.
Proof. move=> D; by apply: sup_left. Qed.
Lemma embed_prop_right `{Complete X} {P : X} {Q : Prop}
  : Q -> P ⊢ ⌜ Q ⌝.
Proof. move=> *; apply/sup_right/top_right. Qed.
Instance meet_bi `{Proset X, !BinMeets X} : Bimonotone (meet (X:=X)).
Proof.
  move=> A A' B B' D1 D2; apply/meet_right.
  + by apply/meet_left1.
  + by apply/meet_left2.
Qed.
Instance join_bi `{Proset X, !BinJoins X} : Bimonotone (join (X:=X)).
Proof.
  move=> A A' B B' D1 D2; apply/join_left.
  + by apply/join_right1.
  + by apply/join_right2.
Qed.
Instance embed_prop_mono `{Complete X} : Monotone (embed_prop (X:=X)).
Proof. move=> P Q D; apply/embed_prop_left => ?; by apply/embed_prop_right/D. Qed.

Program Definition build_meet_semilattice (X : Type) `{!Proset X, !Top X, !BinMeets X}
  : MeetSemilattice X
  := fun R _ _ J => {| inf := foldr meet ⊤ (map J (enum R)) |}.
Next Obligation.
  move=> X ? ? ? R ? ? J.
  rewrite /greatest /pred_upper_bound /lower_bound; setoid_rewrite <- Forall_finite.
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
  rewrite /least /pred_lower_bound /upper_bound; setoid_rewrite <- Forall_finite.
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

Class PreservesInf `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  preserve_inf A : glb J A -> glb (F ∘ J) (F A).
Class PreservesSup `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  preserve_sup A : lub J A -> lub (F ∘ J) (F A).
Hint Mode PreservesInf ! - ! - ! ! ! : typeclass_instances.
Hint Mode PreservesSup ! - ! - ! ! ! : typeclass_instances.
Lemma preserves_inf_alt1 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J}
  : PreservesInf F J <-> glb (F ∘ J) (F (inf J)).
Proof.
  split.
  - move=> ?; apply/preserve_inf/is_inf.
  - move=> Glb A /inf_unique E.
      by apply/(greatest_proper _ _ proper_prf); first rewrite E.
Qed.
Lemma preserves_sup_alt1 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J}
  : PreservesSup F J <-> lub (F ∘ J) (F (sup J)).
Proof.
  split.
  - move=> ?; apply/preserve_sup/is_sup.
  - move=> Lub A /sup_unique E.
      by apply/(least_proper _ _ proper_prf); first rewrite E.
Qed.
Lemma preserves_inf_alt2 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J, !HasInf (F ∘ J)}
  : PreservesInf F J <-> F (inf J) ⟛ inf (fun r => F (J r)).
Proof. rewrite preserves_inf_alt1; apply: inf_unique. Qed.
Lemma preserves_sup_alt2 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J, !HasSup (F ∘ J)}
  : PreservesSup F J <-> F (sup J) ⟛ sup (fun r => F (J r)).
Proof. rewrite preserves_sup_alt1; apply: sup_unique. Qed.
Lemma distrib_inf `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesInf F J} `{!HasInf J, !HasInf (F ∘ J)}
  : F (inf J) ⟛ inf (fun r => F (J r)).
Proof. apply/inf_unique/preserve_inf/is_inf. Qed.
Lemma distrib_sup `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesSup F J} `{!HasSup J, !HasSup (F ∘ J)}
  : F (sup J) ⟛ sup (fun r => F (J r)).
Proof. apply/sup_unique/preserve_sup/is_sup. Qed.

Notation PresInfsOfShape R F := (forall J, Monotone J -> PreservesInf (R:=R) F J).
Notation PresSupsOfShape R F := (forall J, Monotone J -> PreservesSup (R:=R) F J).
Notation PresDInfsOfShape R F := (forall J, PreservesInf (R:=R) F J).
Notation PresDSupsOfShape R F := (forall J, PreservesSup (R:=R) F J).
Notation Continuous F := (forall R, PresDInfsOfShape R F).
Notation Cocontinuous F := (forall R, PresDSupsOfShape R F).
Notation Lex F := (forall `{H : EqDecision R}, @Finite R H -> PresDInfsOfShape R F).
Notation Rex F := (forall `{H : EqDecision R}, @Finite R H -> PresDSupsOfShape R F).
Notation ScottContinuous F :=
  (forall `{H : Proset R}, @Directed R H -> PresSupsOfShape R F).

Lemma F_inf `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J, !HasInf (F ∘ J)}
  : F (inf J) ⊢ inf (fun r => F (J r)).
Proof. apply/inf_right => r; apply/mono/inf_lb. Qed.
Lemma F_sup `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J, !HasSup (F ∘ J)}
  : sup (fun r => F (J r)) ⊢ F (sup J).
Proof. apply/sup_left => r; apply/mono/sup_ub. Qed.
Lemma distrib_inf_sufficient `{Complete X, Complete Y} {F : X -> Y} `{!Monotone F}
  : (forall {R} (J : R -> X), inf (F ∘ J) ⊢ F (inf J)) -> Continuous F.
Proof. move=> Distr R J; apply/preserves_inf_alt2; split; [apply/F_inf | apply/Distr]. Qed.
Lemma distrib_sup_sufficient `{Complete X, Complete Y} {F : X -> Y} `{!Monotone F}
  : (forall {R} (J : R -> X), F (sup J) ⊢ sup (F ∘ J)) -> Cocontinuous F.
Proof. move=> Distr R J; apply/preserves_sup_alt2; split; [apply/Distr | apply/F_sup]. Qed.

(* A number of continuity results are over in adjunctions.v, because they drop out
   for free from adjunctions that we were proving anyway. *)
Instance id_continuous `{Proset X} : Continuous (@id X).
Proof. firstorder. Qed.
Instance id_cocontinuous `{Proset X} : Cocontinuous (@id X).
Proof. firstorder. Qed.
Instance compose_preserves_inf `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         {R} {J : R -> X}
         `{!Monotone F, !Monotone G, !PreservesInf G J, !PreservesInf F (G ∘ J)}
  : PreservesInf (F ∘ G) J | 0.
Proof. firstorder. Qed.
Instance compose_preserves_sup `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         {R} {J : R -> X}
         `{!Monotone F, !Monotone G, !PreservesSup G J, !PreservesSup F (G ∘ J)}
  : PreservesSup (F ∘ G) J | 0.
Proof. firstorder. Qed.

(*
Instance compose_continuous `{Proset X, Proset Y, Proset Z'} {F : Y -> Z'} {G : X -> Y}
         `{!Monotone F, !Monotone G, !Continuous F, !Continuous G}
  : Continuous (F ∘ G) | 0.
Proof. typeclasses eauto. Qed.
*)
Instance subst_continuous1 {Y Y'} `{Complete X} {f : Y' -> Y}
  : Continuous (fun g : Y -> X => g ∘ f).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance subst_cocontinuous1 {Y Y'} `{Complete X} {f : Y' -> Y}
  : Cocontinuous (fun g : Y -> X => g ∘ f).
Proof. by apply/distrib_sup_sufficient. Qed.
Instance eval_at_continuous {X} `{Complete Y} {x : X} : Continuous (eval_at (Y:=Y) x).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance eval_at_cocontinuous {X} `{Complete Y} {x : X}
  : Cocontinuous (eval_at (Y:=Y) x).
Proof. by apply/distrib_sup_sufficient. Qed.

Lemma reflecting_reflects_inf `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) A
  : glb (F ∘ J) (F A) -> glb J A.
Proof.
  move=> Glb; split=> [r | A' LB].
  - apply/(reflect F)/(proj1 Glb).
  - apply/(reflect F)/(proj2 Glb) => r /=; apply/mono/LB.
Qed.
Lemma reflecting_reflects_sup `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) A
  : lub (F ∘ J) (F A) -> lub J A.
Proof.
  move=> Lub; split=> [r | A' UB].
  - apply/(reflect F)/(proj1 Lub).
  - apply/(reflect F)/(proj2 Lub) => r /=; apply/mono/UB.
Qed.
Lemma reflecting_undistrib_inf `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) `{!HasInf (F ∘ J)} A
  : F A ⟛ inf (F ∘ J) -> glb J A.
Proof. move=> /inf_unique; apply: reflecting_reflects_inf. Qed.
Lemma reflecting_undistrib_sup `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) `{!HasSup (F ∘ J)} A
  : F A ⟛ sup (F ∘ J) -> lub J A.
Proof. move=> /sup_unique; apply: reflecting_reflects_sup. Qed.

(*
Instance lex_def `{Proset X, Proset Y} {F : X -> Y} `{!Lex F} `{Finite R} {J : R -> X}
  : PreservesInf F J := preserve_inf.
*)
Lemma distrib_top `{Proset X, Proset Y, !Top X, !Top Y} {F : X -> Y} `{!Lex F}
  : F ⊤ ⟛ ⊤.
Proof. rewrite distrib_inf; by apply/(mono_core einf)/pw_core'. Qed.
Lemma distrib_bot `{Proset X, Proset Y, !Bot X, !Bot Y} {F : X -> Y} `{!Rex F}
  : F ⊥ ⟛ ⊥.
Proof. rewrite distrib_sup; by apply/(mono_core esup)/pw_core'. Qed.
Lemma distrib_meet `{Proset X, Proset Y, !BinMeets X, !BinMeets Y}
      {F : X -> Y} `{!Lex F} {A B}
  : F (A ⩕ B) ⟛ F A ⩕ F B.
Proof. rewrite distrib_inf; apply/(mono_core einf)/pw_core' => -[] //. Qed.
Lemma distrib_join `{Proset X, Proset Y, !BinJoins X, !BinJoins Y}
      {F : X -> Y} `{!Rex F} {A B}
  : F (A ⩖ B) ⟛ F A ⩖ F B.
Proof. rewrite distrib_sup; apply/(mono_core esup)/pw_core' => -[] //. Qed.
Lemma distrib_embed_prop `{Complete X, Complete Y} {F : X -> Y}
      `{!Lex F, !Cocontinuous F} {P}
  : F (⌜ P ⌝) ⟛ ⌜ P ⌝.
Proof.
  rewrite distrib_sup; apply/(mono_core esup)/pw_core' => H_P /=.
  apply/distrib_top.
Qed.

Program Instance Hom_inf `{Proset X, Proset Y} {R} {J : R -> Hom X Y}
        `{!forall x, HasInf (flip J x)}
  : HasInf J
  := {| inf := inf (ap_Hom ∘ J) ↾ _ |}.
Next Obligation.
  move=> X ? Y ? R J ? A B D /=.
  apply/inf_right => r; apply/(inf_left r) => /=; by apply: Hom_mono.
Qed.
Next Obligation.
  move=> X ? Y ? R J ? /=; split=> [r | A' LB] A /=.
  - apply: (inf_lb r).
  - apply: inf_right => r; apply: LB.
Qed.
Program Instance Hom_sup `{Proset X, Proset Y} {R} {J : R -> Hom X Y}
        `{!forall x, HasSup (flip J x)}
  : HasSup J
  := {| sup := sup (ap_Hom ∘ J) ↾ _ |}.
Next Obligation.
  move=> X ? Y ? R J ? A B D /=.
  apply/sup_left => r; apply/(sup_right r) => /=; by apply: Hom_mono.
Qed.
Next Obligation.
  move=> X ? Y ? R J ? /=; split=> [r | A' UB] A /=.
  - apply: (sup_ub r).
  - apply: sup_left => r; apply: UB.
Qed.
(* TODO Make some of the subsequent stuff more fine-grained. *)
Instance ap_Hom_complete_continuous `{Proset X, Complete Y}
  : Continuous (ap_Hom (X:=X) (Y:=Y)).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance ap_Hom_complete_cocontinuous `{Proset X, Complete Y}
  : Cocontinuous (ap_Hom (X:=X) (Y:=Y)).
Proof. by apply/distrib_sup_sufficient. Qed.
(* Hmm. *)
Instance flip_functoriality {R} `{Proset Y, Proset X}
         {F : R -> Y -> X} `{!forall r, Monotone (F r)}
  : Monotone (flip F).
Proof. firstorder. Qed.
Lemma Hom_lim : forall `{Proset Y, Complete X} {R} (J : R -> Hom Y X),
    inf J ⟛ in_Hom (einf ∘ flip J).
Proof. by compute. Qed.
Lemma Hom_colim : forall `{Proset Y, Complete X} {R} (J : R -> Hom Y X),
    inf J ⟛ in_Hom (einf ∘ flip J).
Proof. by compute. Qed.
Instance Hom_compose_continuous `{Proset X, Proset X', Complete Y} {F : Hom X' X}
  : Continuous (fun G : Hom X Y => G ○ F).
Proof.
  apply: distrib_inf_sufficient.
  - move=> G G'; apply: bi_l.
  - move=> R J A /=; apply/(mono einf) => ? //=.
Qed.
Instance Hom_compose_cocontinuous `{Proset X, Proset X', Complete Y} {F : Hom X' X}
  : Cocontinuous (fun G : Hom X Y => G ○ F).
Proof.
  apply: distrib_sup_sufficient.
  - move=> G G'; apply: bi_l.
  - move=> R J A /=; apply/(mono esup) => ? //=.
Qed.
Instance Hom_eval_at_continuous `{Proset X, Complete Y} {x : X}
  : Continuous (Hom_eval_at (Y:=Y) x).
Proof. by apply/distrib_inf_sufficient. Qed.
Instance Hom_eval_at_cocontinuous `{Proset X, Complete Y} {x : X}
  : Cocontinuous (Hom_eval_at (Y:=Y) x).
Proof. by apply/distrib_sup_sufficient. Qed.


(* Example *)
Definition fixed_point `{Proset X} (F : X -> X) (A : X) : Prop
  := F A ⟛ A.
Definition kleene_chain `{Proset X, !Bot X} (F : X -> X) : nat -> X
  := fun n => Nat.iter n F ⊥.
Lemma kleene_chain_chain `{Proset X, !Bot X} {F : X -> X} `{!Monotone F}
  : chain (kleene_chain F).
Proof. elim=> /= [| n]; [apply/bot_left | apply/mono]. Qed.
Instance kleene_chain_mono `{Proset X, !Bot X} {F : X -> X} `{!Monotone F}
  : Monotone (kleene_chain F).
Proof. apply/chain_mono/kleene_chain_chain. Qed.
Theorem kleene `{Proset X, !DirectedComplete X, !Bot X} {F : X -> X}
        `{!Monotone F, !ScottContinuous F}
  : least (fixed_point F) (sup (kleene_chain F)).
Proof.
  split.
  - rewrite /fixed_point distrib_sup; split; apply/sup_left => n.
    + by apply/(sup_right (S n)).
    + apply/(sup_right n)/kleene_chain_chain.
  - move=> A FP; apply/sup_left; elim=> /= [| n].
    + apply/bot_left.
    + move=> D; unfold fixed_point in FP.
      setoid_rewrite <- (proj1 FP); by apply/mono.
Qed.
