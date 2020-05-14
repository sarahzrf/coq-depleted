From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.

Require Import depleted.proset.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Definition lower_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, A ⊢ J r.
Definition upper_bound `{Proset X} {R} (J : R -> X) (A : X) : Prop
  := forall r, J r ⊢ A.
Instance: Params (@lower_bound) 4 := {}.
Instance: Params (@upper_bound) 4 := {}.
Instance lower_bound_proper `{Proset X} {R}
  : Proper ((⊢) ++> (↼)) (lower_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 /= D_A L r.
  rewrite D_A -(D_J r) //.
Qed.
Instance lower_bound_mono `{Proset X} {R} : Monotone (lower_bound (X:=X) (R:=R)).
Proof. move=> J1 J2 D_J A L r; rewrite -(D_J r) //. Qed.
Instance lower_bound_ext `{Proset X} {R} : Extensional (lower_bound (X:=X) (R:=R)).
Proof. typeclasses eauto. Qed.
Instance lower_bound_anti `{Proset X} {R} {J : R -> X} : Antitone (lower_bound J).
Proof. typeclasses eauto. Qed.
Instance upper_bound_proper `{Proset X} {R}
  : Proper ((⊢) --> (⇀)) (upper_bound (X:=X) (R:=R)).
Proof.
  move=> J1 J2 D_J A1 A2 D_A U r.
  rewrite -D_A (D_J r) //.
Qed.
Instance upper_bound_anti `{Proset X} {R} : Antitone (upper_bound (X:=X) (R:=R)).
Proof. move=> J1 J2 /= D_J A L r; rewrite (D_J r) //. Qed.
Instance upper_bound_ext `{Proset X} {R} : Extensional (upper_bound (X:=X) (R:=R)).
Proof. typeclasses eauto. Qed.
Instance upper_bound_mono `{Proset X} {R} {J : R -> X} : Monotone (upper_bound J).
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
Instance: Params (@pred_lower_bound) 3 := {}.
Instance: Params (@pred_upper_bound) 3 := {}.
Instance pred_lower_bound_proper `{Proset X}
  : Proper ((⊢) --> (↼)) (pred_lower_bound (X:=X)).
Proof.
  move=> P1 P2 D_P A1 A2 /= D_A L B /D_P.
  rewrite D_A; apply: L.
Qed.
Instance pred_upper_bound_proper `{Proset X}
  : Proper ((⊢) --> (⇀)) (pred_upper_bound (X:=X)).
Proof.
  move=> P1 P2 D_P A1 A2 D_A U B /D_P ?.
  rewrite -D_A; by apply: U.
Qed.
(*
Instance pred_lower_bound_proper' `{Proset X}
  : Proper ((⊢) ++> (⊢) ++> flip impl) (pred_lower_bound (X:=X)).
Proof. move=> ? ? ? ? ? ?; by apply: pred_lower_bound_proper. Qed.
*)
Instance pred_lower_bound_proper'' `{Proset X}
  : Proper ((⟛) ==> (⥊)) (pred_lower_bound (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: pred_lower_bound_proper.
Qed.
(*
Instance pred_upper_bound_proper' `{Proset X}
  : Proper ((⊢) ++> (⊢) --> flip impl) (pred_upper_bound (X:=X)).
Proof. move=> ? ? ? ? ? ?; by apply: pred_upper_bound_proper. Qed.
*)
Instance pred_upper_bound_proper'' `{Proset X}
  : Proper ((⟛) ==> (⥊)) (pred_upper_bound (X:=X)).
Proof.
  apply: proper_sym_impl_iff_2 => ? ? [D ?] ? ? [D' ?] ?.
    by apply: pred_upper_bound_proper.
Qed.

Definition pred_diagram `{Proset X} (P : X -> Prop) : sig P -> X
  := sval.
Arguments pred_diagram {_ _ _} P /.
Instance: Params (@pred_diagram) 3 := {}.
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
Arguments image {_ _ _ _} J _ /.
Instance: Params (@image) 4 := {}.
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
  - move=> L B [r E]; rewrite -(proj1 E) //.
  - move=> L r; apply/L; by exists r.
Qed.
Lemma ub_pred_ub `{Proset X} {R} (J : R -> X) (A : X)
  : upper_bound J A <-> pred_upper_bound (image J) A.
Proof.
  split.
  - move=> U B [r E]; rewrite (proj2 E) //.
  - move=> U r; apply/U; by exists r.
Qed.

Definition least `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ pred_lower_bound P A.
Definition greatest `{Proset X} (P : X -> Prop) (A : X) : Prop
  := P A /\ pred_upper_bound P A.
Arguments least {_ _ _} P _ /.
Arguments greatest {_ _ _} P _ /.
Instance: Params (@least) 3 := {}.
Instance: Params (@greatest) 3 := {}.
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
Lemma least_unique `{Proset X} {P : X -> Prop} {A A'}
  : least P A -> least P A' -> A ⟛ A'.
Proof. firstorder. Qed.
Lemma greatest_unique `{Proset X} {P : X -> Prop} {A A'}
  : greatest P A -> greatest P A' -> A ⟛ A'.
Proof. firstorder. Qed.
Lemma least_unique_het `{Proset X} {P P' : X -> Prop} {A A'}
  : P ⟛ P' -> least P A -> least P' A' -> A ⟛ A'.
Proof. firstorder. Qed.
Lemma greatest_unique_het `{Proset X} {P P' : X -> Prop} {A A'}
  : P ⟛ P' -> greatest P A -> greatest P' A' -> A ⟛ A'.
Proof. firstorder. Qed.

Definition glb `{Proset X} {R} (J : R -> X) : X -> Prop := greatest (lower_bound J).
Definition lub `{Proset X} {R} (J : R -> X) : X -> Prop := least (upper_bound J).
Arguments glb {_ _ _ _} J /.
Arguments lub {_ _ _ _} J /.
Instance: Params (@glb) 4 := {}.
Instance: Params (@lub) 4 := {}.
Instance glb_proper `{Proset X} {R}
  : Proper ((⟛) ==> (⟛) ==> iff) (glb (X:=X) (R:=R)).
Proof.
  move=> ? ? E1 ? ? E2; rewrite /glb E1; apply/(greatest_proper _ _ proper_prf _ _ E2).
Qed.
Instance lub_proper `{Proset X} {R}
  : Proper ((⟛) ==> (⟛) ==> iff) (lub (X:=X) (R:=R)).
Proof.
  move=> ? ? E1 ? ? E2; rewrite /lub E1; apply/(least_proper _ _ proper_prf _ _ E2).
Qed.

Class HasInf `{Proset X} {R} (J : R -> X) :=
  {inf : X; is_inf : glb J inf}.
Class HasSup `{Proset X} {R} (J : R -> X) :=
  {sup : X; is_sup : lub J sup}.
Hint Mode HasInf ! - - ! ! : typeclass_instances.
Hint Mode HasSup ! - - ! ! : typeclass_instances.
Arguments inf {X _ _ R} J {Has} : rename.
Arguments sup {X _ _ R} J {Has} : rename.
Arguments is_inf {X _ _ R} J {_}.
Arguments is_sup {X _ _ R} J {_}.
(* TODO Figure out what kind of black magic is necessary for rewriting under an
        inf or sup. *)
Instance: Params (@inf) 6 := {}.
Instance: Params (@sup) 6 := {}.
Notation "'Inf' x .. y , p" := (inf (fun x => .. (inf (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Inf'  '/  ' x  ..  y ,  '/  ' p ']'")
  : proset_scope.
Notation "'Sup' x .. y , p" := (sup (fun x => .. (sup (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Sup'  '/  ' x  ..  y ,  '/  ' p ']'")
  : proset_scope.

Definition transport_inf `{Proset X} {R} {J J' : R -> X} (E : J ⟛ J') `{!HasInf J}
  : HasInf J'
  := {| inf := inf J;
        is_inf := proj1 (glb_proper _ _ E _ _ (reflexivity _)) (is_inf J) |}.
Definition transport_sup `{Proset X} {R} {J J' : R -> X} (E : J ⟛ J') `{!HasSup J}
  : HasSup J'
  := {| sup := sup J;
        is_sup := proj1 (lub_proper _ _ E _ _ (reflexivity _)) (is_sup J) |}.

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
  split; first by apply: inf_right.
  move=> ->; apply: inf_lb.
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
  move=> *; split; first by apply: sup_left.
  move=> <-; apply: sup_ub.
Qed.

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
Arguments einf {_ _ _ _ _} J /.
Arguments esup {_ _ _ _ _} J /.
Instance: Params (@einf) 5 := {}.
Instance: Params (@esup) 5 := {}.
Notation "'EInf' x .. y , p" := (einf (fun x => .. (einf (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'EInf'  '/  ' x  ..  y ,  '/  ' p ']'")
  : proset_scope.
Notation "'ESup' x .. y , p" := (esup (fun x => .. (esup (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'ESup'  '/  ' x  ..  y ,  '/  ' p ']'")
  : proset_scope.
Instance einf_mono {R} `{Proset X, !DInfsOfShape R X}
  : Monotone (einf (X:=X) (R:=R)).
Proof. move=> A B D /=; apply: inf_right => r; by apply: inf_left. Qed.
Instance esup_mono {R} `{Proset X, !DSupsOfShape R X}
  : Monotone (esup (X:=X) (R:=R)).
Proof. move=> A B D /=; apply: sup_left => r; by apply: sup_right. Qed.

Notation MeetSemilattice X
  := (forall `{H : EqDecision R}, @Finite R H -> DInfsOfShape R X).
Notation JoinSemilattice X
  := (forall `{H : EqDecision R}, @Finite R H -> DSupsOfShape R X).
Class Lattice (X : Type) `{Proset X, !MeetSemilattice X, !JoinSemilattice X}.
Hint Mode Lattice ! - - - - : typeclass_instances.
Instance lattice_def `{Proset X, !MeetSemilattice X, !JoinSemilattice X}
  : Lattice X := {}.
Notation InfLattice X := (forall R, DInfsOfShape R X).
Notation SupLattice X := (forall R, DSupsOfShape R X).
Class Complete (X : Type) `{Proset X, !InfLattice X, !SupLattice X}.
Hint Mode Complete ! - - - - : typeclass_instances.
Instance complete_def `{Proset X, !InfLattice X, !SupLattice X}
  : Complete X := {}.

Class Directed (X : Type) `{Proset X} :=
  direct `{Finite R} (J : R -> X) : exists A, upper_bound J A.
Instance join_semilattice_directed `{Proset X, !JoinSemilattice X} : Directed X.
Proof. move=> R ? ? J; exists (sup J); apply: sup_ub. Qed.
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
Instance: Params (@ub_diagram) 4 := {}.
Instance: Params (@lb_diagram) 4 := {}.
Lemma ub_diagram_spec `{Proset X} {R} {J : R -> X} {A}
  : glb (ub_diagram J) A <-> lub J A.
Proof.
  split=> [Glb | Lub].
  - pose Has := {| inf := A; is_inf := Glb |}; change A with (inf (ub_diagram J)); split.
    + move=> r; apply: inf_right => -[B UB] //=.
    + move=> B UB; by apply: (inf_left (B ↾ UB)).
  - pose Has := {| sup := A; is_sup := Lub |}; change A with (sup J); split.
    + move=> [B UB]; apply: sup_left => r //=.
    + move=> B LB; apply/(LB (sup J ↾ _)); apply: sup_ub.
Qed.
Lemma lb_diagram_spec `{Proset X} {R} {J : R -> X} {A}
  : lub (lb_diagram J) A <-> glb J A.
Proof.
  split=> [Lub | Glb].
  - pose Has := {| sup := A; is_sup := Lub |}; change A with (sup (lb_diagram J)); split.
    + move=> r; apply: sup_left => -[B LB] //=.
    + move=> B LB; by apply: (sup_right (B ↾ LB)).
  - pose Has := {| inf := A; is_inf := Glb |}; change A with (inf J); split.
    + move=> [B LB]; apply: inf_right => r //=.
    + move=> B UB; apply: (UB (inf J ↾ _)); apply: inf_lb.
Qed.
Definition infs_sufficient `{Proset X, !InfLattice X} : SupLattice X
  := fun R J => {| sup := inf (ub_diagram J); is_sup := proj1 ub_diagram_spec (is_inf _) |}.
Definition sups_sufficient `{Proset X, !SupLattice X} : InfLattice X
  := fun R J => {| inf := sup (lb_diagram J); is_inf := proj1 lb_diagram_spec (is_sup _) |}.

Lemma inf_binder_fwd `{Proset X} {R} {J J' : R -> X} `{!DInfsOfShape R X}
  : (forall r, J r ⊢ J' r) -> inf J ⊢ inf J'.
Proof. move=> D; apply: inf_right => r; apply: inf_left; by etransitivity. Qed.
Lemma inf_binder_bwd `{Proset X} {R} {J J' : R -> X} `{!DInfsOfShape R X}
  : (forall r, flip pro_le (J' r) (J r)) -> inf J ⊢ inf J'.
Proof. apply: inf_binder_fwd. Qed.
Lemma inf_binder `{Proset X} {R} {J J' : R -> X} `{!DInfsOfShape R X}
  : (forall r, J r ⟛ J' r) -> inf J ⟛ inf J'.
Proof. move=> D; split; apply: inf_binder_fwd; firstorder. Qed.
Lemma sup_binder_fwd `{Proset X} {R} {J J' : R -> X} `{!DSupsOfShape R X}
  : (forall r, J r ⊢ J' r) -> sup J ⊢ sup J'.
Proof. move=> D; apply: sup_left => r; apply: sup_right; by etransitivity. Qed.
Lemma sup_binder_bwd `{Proset X} {R} {J J' : R -> X} `{!DSupsOfShape R X}
  : (forall r, flip pro_le (J' r) (J r)) -> sup J ⊢ sup J'.
Proof. move=> /= D; apply: sup_left => r; apply: sup_right; by etransitivity. Qed.
Lemma sup_binder `{Proset X} {R} {J J' : R -> X} `{!DSupsOfShape R X}
  : (forall r, J r ⟛ J' r) -> sup J ⟛ sup J'.
Proof. move=> D; split; apply: sup_binder_fwd; firstorder. Qed.

Instance proset_rewrite' `{Proset X} : RewriteRelation (flip (pro_le (X:=X))) := {}.
Instance under_proper `{PreOrder A R} : Proper (R --> R ++> impl) (Under_rel A R).
Proof. rewrite Under_relE; firstorder. Qed.
(*
Instance under_proper' `{PreOrder A R} : Proper (R ++> R --> flip impl) (Under_rel A R).
Proof. rewrite Under_relE; firstorder. Qed.
*)

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
Lemma glb_alt `{Proset X} {R} {J : R -> X} {A}
  : glb J A <-> forall `{!Proper ((⟛) ==> iff) P}, P A <-> forall `{!HasInf J}, P (inf J).
Proof.
  split.
  - move=> Glb P ?; split.
    + move=> PA ?; rewrite (greatest_unique (is_inf _) Glb) //.
    + move=> /(_ {| inf := A; is_inf := Glb |}) //.
  - move=> E; apply/E => ?; apply: is_inf.
Qed.
Lemma lub_alt `{Proset X} {R} {J : R -> X} {A}
  : lub J A <-> forall `{!Proper ((⟛) ==> iff) P}, P A <-> forall `{!HasSup J}, P (sup J).
Proof.
  split.
  - move=> Lub P ?; split.
    + move=> PA ?; rewrite (least_unique (is_sup _) Lub) //.
    + move=> /(_ {| sup := A; is_sup := Lub |}) //.
  - move=> E; apply/E => ?; apply: is_sup.
Qed.
Lemma instantiate_inf `{Proset X, !Proper ((⟛) ==> iff) P} {R} {J : R -> X} `{!HasInf J}
  : (forall `{Has' : !HasInf J}, P (inf J (Has:=Has'))) <-> P (inf J).
Proof. symmetry; apply: (proj1 glb_alt (is_inf J)). Qed.
Lemma instantiate_sup `{Proset X, !Proper ((⟛) ==> iff) P} {R} {J : R -> X} `{!HasSup J}
  : (forall `{Has' : !HasSup J}, P (sup J (Has:=Has'))) <-> P (sup J).
Proof. symmetry; apply: (proj1 lub_alt (is_sup J)). Qed.

(*
Definition same_inf `{Proset X} {R} {J J' : R -> X} : HasInf J -> HasInf J' -> Prop
  := fun _ _ => inf J ⟛ inf J'.
Definition same_sup `{Proset X} {R} {J J' : R -> X} : HasSup J -> HasSup J' -> Prop
  := fun _ _ => sup J ⟛ sup J'.
Arguments same_inf {_ _ _ _ _ _} _ _ /.
Arguments same_sup {_ _ _ _ _ _} _ _ /.
Instance: Params (@same_inf) 6 := {}.
Instance: Params (@same_sup) 6 := {}.
Instance same_inf_equivalence `{Proset X} {R} {J : R -> X}
  : Equivalence (same_inf (J:=J) (J':=J)).
Proof. constructor=> ? //= *; by etransitivity. Qed.
Instance same_sup_equivalence `{Proset X} {R} {J : R -> X}
  : Equivalence (same_sup (J:=J) (J':=J)).
Proof. constructor=> ? //= *; by etransitivity. Qed.
Notation inf_proof_irrel := (Proper (same_inf ==> iff)).
Notation sup_proof_irrel := (Proper (same_sup ==> iff)).
Lemma same_inf_endo_total `{Proset X} {R} {J : R -> X} (Has Has' : HasInf J)
  : same_inf Has Has'.
Proof. apply: greatest_unique; apply: is_inf. Qed.
Lemma same_sup_endo_total `{Proset X} {R} {J : R -> X} (Has Has' : HasSup J)
  : same_sup Has Has'.
Proof. apply: least_unique; apply: is_sup. Qed.

Lemma ipi_alt `{Proset X} {R} {J : R -> X} (P : HasInf J -> Prop)
  : inf_proof_irrel P <-> (forall Has, all P <-> P Has).
Proof.
  split.
  - move=> IPI Has; split=> // P_Has Has'.
    rewrite (same_inf_endo_total Has' Has) //.
  - move=> E Has Has'.
    + done. move=> All.
Qed.

Lemma instantiate_inf' `{Proset X} {R} {J : R -> X} `{!HasInf J}
  : (forall `{Has' : !HasInf J}, P (inf J (Has:=Has'))) <-> P (inf J).
Proof. symmetry; apply: (proj1 glb_alt (is_inf J)). Qed.
*)

Program Instance pw_inf {X} `{Proset Y} {R} {J : R -> X -> Y} `{!forall x, HasInf (flip J x)}
  : HasInf J
  := {| inf x := inf (flip J x) |}.
Next Obligation.
  move=> X Y ? R J ?; split=> [r | F LB] A.
  - apply: inf_lb.
  - apply: inf_right; firstorder.
Qed.
Program Instance pw_sup {X} `{Proset Y} {R} {J : R -> X -> Y} `{!forall x, HasSup (flip J x)}
  : HasSup J
  := {| sup x := sup (flip J x) |}.
Next Obligation.
  move=> X Y ? R J ?; split=> [r | F UB] A.
  - apply: sup_ub.
  - apply: sup_left; firstorder.
Qed.
Program Instance op_inf `{Proset X} {R} {J : R -> op X} `{!HasSup (get_op ∘ J)}
  : HasInf J
  := {| inf := Op (sup (get_op ∘ J)) |}.
Next Obligation.
  move=> X ? R J ?; split=> [r | A LB] /=.
  (* TODO Work out better utilities for working with op. *)
  - rewrite op_def; by apply: (sup_right r).
  - apply: sup_left; firstorder.
Qed.
Program Instance op_sup `{Proset X} {R} {J : R -> op X} `{!HasInf (get_op ∘ J)}
  : HasSup J
  := {| sup := Op (inf (get_op ∘ J)) |}.
Next Obligation.
  move=> X ? R J ?; split=> [r | A UB] /=.
  - rewrite op_def; by apply: (inf_left r).
  - apply: inf_right; firstorder.
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
  move=> ? ? ? ? ? ? ? J ? ?.
  rewrite /glb /greatest /pred_upper_bound curry_dep.
  setoid_rewrite (prod_lb (J:=J)); simpl; setoid_rewrite inf_universal; firstorder.
Qed.
Program Instance prod_sup `{Proset X, Proset Y} {R} {J : R -> X * Y}
        `{!HasSup (fst ∘ J), !HasSup (snd ∘ J)}
  : HasSup J
  := {| sup := (sup (fst ∘ J), sup (snd ∘ J)) |}.
Next Obligation.
  move=> ? ? ? ? ? ? ? J ? ?.
  rewrite /lub /least /pred_lower_bound curry_dep.
  setoid_rewrite (prod_ub (J:=J)); simpl; setoid_rewrite sup_universal; firstorder.
Qed.
(*
Lemma op_lb_ub `{Proset X} {R}
*)

Notation Top X := (DInfsOfShape void X).
Notation Bot X := (DSupsOfShape void X).
Notation BinMeets X := (DInfsOfShape bool X).
Notation BinJoins X := (DSupsOfShape bool X).
Definition top (X : Type) `{Proset X, !Top X} : X :=
  inf (of_void _).
Definition bot (X : Type) `{Proset X, !Bot X} : X :=
  sup (of_void _).
Notation "⊤" := (top _) : proset_scope.
Notation "⊥" := (bot _) : proset_scope.
Notation bool_e A B := (fun b : bool => if b then A else B).
Definition meet `{Proset X, !BinMeets X} (A B : X) : X :=
  inf (bool_e A B).
Definition join `{Proset X, !BinJoins X} (A B : X) : X :=
  sup (bool_e A B).
Infix "⩕" := meet (at level 40, left associativity) : proset_scope.
Infix "⩖" := join (at level 40, left associativity) : proset_scope.
(* TODO This type could technically be less strict... *)
Definition embed_prop `{Proset X, !SupLattice X, !Top X} (P : Prop) : X := Sup H : P, ⊤.
Notation "⌜ P ⌝" := (embed_prop P) : proset_scope.
Arguments top : simpl never.
Arguments bot : simpl never.
Arguments meet : simpl never.
Arguments join : simpl never.
Arguments embed_prop : simpl never.
Instance: Params (@top) 4 := {}.
Instance: Params (@bot) 4 := {}.
Instance: Params (@meet) 4 := {}.
Instance: Params (@join) 4 := {}.
Instance: Params (@embed_prop) 5 := {}.

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
Lemma embed_prop_left `{Proset X, !SupLattice X, !Top X} {P : Prop} {Q : X}
  : (P -> ⊤ ⊢ Q) -> ⌜ P ⌝ ⊢ Q.
Proof. move=> D; by apply: sup_left. Qed.
Lemma embed_prop_right `{Proset X, !SupLattice X, !Top X} {P : X} {Q : Prop}
  : Q -> P ⊢ ⌜ Q ⌝.
Proof. move=> *; apply: sup_right; apply: top_right. Qed.
Instance meet_bi `{Proset X, !BinMeets X} : Bimonotone (meet (X:=X)).
Proof.
  move=> A A' B B' D1 D2; apply: meet_right.
  + by apply: meet_left1.
  + by apply: meet_left2.
Qed.
Instance join_bi `{Proset X, !BinJoins X} : Bimonotone (join (X:=X)).
Proof.
  move=> A A' B B' D1 D2; apply: join_left.
  + by apply: join_right1.
  + by apply: join_right2.
Qed.
Instance embed_prop_mono `{Proset X, !SupLattice X, !Top X} : Monotone (embed_prop (X:=X)).
Proof. move=> P Q D; apply: embed_prop_left => ?; by apply embed_prop_right, D. Qed.

Program Definition build_meet_semilattice (X : Type) `{Proset X, !Top X, !BinMeets X}
  : MeetSemilattice X
  := fun R _ _ J => {| inf := foldr meet ⊤ (map J (enum R)) |}.
Next Obligation.
  move=> X ? ? ? ? R ? ? J.
  rewrite /glb /greatest /pred_upper_bound /lower_bound; setoid_rewrite <- Forall_finite.
  elim: (enum R) => /= [| r rs [IH1 IH2]]; split.
  - done.
  - move=> *; apply: top_right.
  - constructor.
    + apply: meet_proj1.
    + apply: Forall_impl IH1 (fun _ => meet_left2).
  - move=> B /Forall_cons [? /IH2 ?]; by apply: meet_right.
Qed.
Program Definition build_join_semilattice (X : Type) `{Proset X, !Bot X, !BinJoins X}
  : JoinSemilattice X
  := fun R _ _ J => {| sup := foldr join ⊥ (map J (enum R)) |}.
Next Obligation.
  move=> X ? ? ? ? R ? ? J.
  rewrite /lub /least /pred_lower_bound /upper_bound; setoid_rewrite <- Forall_finite.
  elim: (enum R) => /= [| r rs [IH1 IH2]]; split.
  - done.
  - move=> *; apply: bot_left.
  - constructor.
    + apply: join_inj1.
    + apply: Forall_impl IH1 (fun _ => join_right2).
  - move=> B /Forall_cons [? /IH2 ?]; by apply: join_left.
Qed.

Program Instance nat_join_semilattice : JoinSemilattice nat
  := @build_join_semilattice nat _ _ (fun _ => {| sup := 0 |})
                             (fun J => {| sup := max (J true) (J false) |}).
Next Obligation. compute; dintuition. Qed.
Next Obligation.
  move=> J; split.
  - move=> []; [apply: Nat.le_max_l | apply: Nat.le_max_r].
  - move=> n UB; apply: Nat.max_lub; apply: UB.
Qed.
Program Instance bool_meet_semilattice : MeetSemilattice bool
  := @build_meet_semilattice bool _ _ (fun _ => {| inf := true |})
                             (fun J => {| inf := andb (J true) (J false) |}).
Next Obligation. compute; split; [dintuition | case; dintuition]. Qed.
Next Obligation.
  move=> J; split.
  - move=> []; apply/implyP => /andP [//].
  - move=> b LB; apply/implyP => H; apply/andP; split; by apply/(implyP (LB _)).
Qed.
Program Instance bool_join_semilattice : JoinSemilattice bool
  := @build_join_semilattice bool _ _ (fun _ => {| sup := false |})
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
Hint Mode PreservesInf ! - - ! - - ! ! ! : typeclass_instances.
Hint Mode PreservesSup ! - - ! - - ! ! ! : typeclass_instances.
Lemma distrib_inf `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesInf F J} `{!HasInf J, !HasInf (F ∘ J)}
  : F (Inf r, J r) ⟛ Inf r, F (J r).
Proof. apply/inf_unique/preserve_inf/is_inf. Qed.
Lemma distrib_sup `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesSup F J} `{!HasSup J, !HasSup (F ∘ J)}
  : F (Sup r, J r) ⟛ Sup r, F (J r).
Proof. apply/sup_unique/preserve_sup/is_sup. Qed.
Definition preserves_inf_img `{Proset X, Proset Y} (F : X -> Y)
           {R} (J : R -> X) `{!HasInf J, !PreservesInf F J}
  : HasInf (F ∘ J)
  := {| inf := F (inf J); is_inf := preserve_inf (inf J) (is_inf J) |}.
Definition preserves_sup_img `{Proset X, Proset Y} (F : X -> Y)
           {R} (J : R -> X) `{!HasSup J, !PreservesSup F J}
  : HasSup (F ∘ J)
  := {| sup := F (sup J); is_sup := preserve_sup (sup J) (is_sup J) |}.
Lemma distrib_inf' `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesInf F J} `{!HasInf J}
  : F (Inf r, J r) ⟛ @inf _ _ _ _ (fun r => F (J r)) (preserves_inf_img F J).
Proof. apply/inf_unique/preserve_inf/is_inf. Qed.
Lemma distrib_sup' `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!PreservesSup F J} `{!HasSup J}
  : F (Sup r, J r) ⟛ @sup _ _ _ _ (fun r => F (J r)) (preserves_sup_img F J).
Proof. apply/sup_unique/preserve_sup/is_sup. Qed.

Lemma preserves_inf_alt `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F}
  : PreservesInf F J <-> forall `{!HasInf J}, glb (F ∘ J) (F (inf J)).
Proof.
  split.
  - move=> ? ?; apply/preserve_inf/is_inf.
  - move=> GlbF A Glb; apply: (GlbF {| inf := A; is_inf := Glb |}).
Qed.
Lemma preserves_sup_alt `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F}
  : PreservesSup F J <-> forall `{!HasSup J}, lub (F ∘ J) (F (sup J)).
Proof.
  split.
  - move=> ? ?; apply/preserve_sup/is_sup.
  - move=> LubF A Lub; apply: (LubF {| sup := A; is_sup := Lub |}).
Qed.
Lemma preserves_inf_alt2 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J}
  : PreservesInf F J <-> glb (F ∘ J) (F (inf J)).
Proof.
  split.
  - move=> ?; apply/preserve_inf/is_inf.
  - move=> Glb A /inf_unique E.
      by apply/(greatest_proper _ _ proper_prf); first rewrite E.
Qed.
Lemma preserves_sup_alt2 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J}
  : PreservesSup F J <-> lub (F ∘ J) (F (sup J)).
Proof.
  split.
  - move=> ?; apply/preserve_sup/is_sup.
  - move=> Lub A /sup_unique E.
      by apply/(least_proper _ _ proper_prf); first rewrite E.
Qed.
Lemma preserves_inf_alt3 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J, !HasInf (F ∘ J)}
  : PreservesInf F J <-> F (Inf r, J r) ⟛ Inf r, F (J r).
Proof. rewrite preserves_inf_alt2; apply: inf_unique. Qed.
Lemma preserves_sup_alt3 `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J, !HasSup (F ∘ J)}
  : PreservesSup F J <-> F (Sup r, J r) ⟛ Sup r, F (J r).
Proof. rewrite preserves_sup_alt2; apply: sup_unique. Qed.

Notation PresInfsOfShape R F := (forall J, Monotone J -> PreservesInf (R:=R) F J).
Notation PresSupsOfShape R F := (forall J, Monotone J -> PreservesSup (R:=R) F J).
Notation PresDInfsOfShape R F := (forall J, PreservesInf (R:=R) F J).
Notation PresDSupsOfShape R F := (forall J, PreservesSup (R:=R) F J).
Notation Continuous F := (forall R, PresDInfsOfShape R F).
Notation Cocontinuous F := (forall R, PresDSupsOfShape R F).
Notation Lex F := (forall `{H : EqDecision R}, @Finite R H -> PresDInfsOfShape R F).
Notation Rex F := (forall `{H : EqDecision R}, @Finite R H -> PresDSupsOfShape R F).
Notation ScottContinuous F :=
  (forall `{H0 : Le R, H : @Proset R H0}, @Directed R H0 H -> PresSupsOfShape R F).

Lemma F_inf `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasInf J, !HasInf (F ∘ J)}
  : F (Inf r, J r) ⊢ Inf r, F (J r).
Proof. apply: inf_right => r; apply: mono; apply: inf_lb. Qed.
Lemma F_sup `{Proset X, Proset Y} {R} {F : X -> Y} {J : R -> X}
      `{!Monotone F, !HasSup J, !HasSup (F ∘ J)}
  : (Sup r, F (J r)) ⊢ F (Sup r, J r).
Proof. apply: sup_left => r; apply: mono; apply: sup_ub. Qed.
Lemma distrib_inf_sufficient `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!Monotone F, !HasInf J, !HasInf (F ∘ J)}
  : (Inf r, F (J r)) ⊢ F (Inf r, J r) -> PreservesInf F J.
Proof. move=> Distr; apply/preserves_inf_alt3; split; [apply: F_inf | apply: Distr]. Qed.
Lemma distrib_sup_sufficient `{Proset X, Proset Y} {R} (J : R -> X)
      {F : X -> Y} `{!Monotone F, !HasSup J, !HasSup (F ∘ J)}
  : F (Sup r, J r) ⊢ (Sup r, F (J r)) -> PreservesSup F J.
Proof. move=> Distr; apply/preserves_sup_alt3; split; [apply: Distr | apply: F_sup]. Qed.

Lemma bool_diagram_eta `{Proset X} (J : bool -> X)
  : J ⟛ bool_e (J true) (J false).
Proof. apply/pw_core' => -[] //. Qed.
Lemma bool_interval `{Proset X} (J : bool -> X)
  : Monotone J <-> J false ⊢ J true.
Proof.
  split.
  - move=> ?; by apply: mono.
  - move=> D [] [] //.
Qed.
Lemma bool_interval' `{Proset X} (A B : X)
  : A ⊢ B <-> Monotone (bool_e B A).
Proof. symmetry; apply: bool_interval. Qed.
Program Instance interval_inf `{Proset X} : InfsOfShape bool X
  := fun J _ => {| inf := J false |}.
Next Obligation. move=> X ? ? J /bool_interval D; split=> [[] | A] //. Qed.
Program Instance interval_sup `{Proset X} : SupsOfShape bool X
  := fun J _ => {| sup := J true |}.
Next Obligation. move=> X ? ? J /bool_interval D; split=> [[] | A] //. Qed.
Lemma mono_as_pres_infs `{Proset X, Proset Y} {F : X -> Y}
  : Monotone F <-> PresInfsOfShape bool F.
Proof.
  split.
  - move=> ? J ?; by apply: distrib_inf_sufficient.
  - move=> Pres A B /bool_interval'; set J := bool_e B A => ?.
    change A with (inf J); rewrite distrib_inf' (inf_lb true) //.
Qed.
Lemma mono_as_pres_sups `{Proset X, Proset Y} {F : X -> Y}
  : Monotone F <-> PresSupsOfShape bool F.
Proof.
  split.
  - move=> ? J ?; by apply: distrib_sup_sufficient.
  - move=> Pres A B /bool_interval'; set J := bool_e B A => ?.
    change B with (sup J); rewrite -(proj2 (distrib_sup' _)) -(sup_ub false) //.
Qed.

(* TODO Non-on-the-nose surjectivity *)
Lemma reindex_glb `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X} {A}
  : glb J A -> glb (J ∘ re) A.
Proof.
  move=> [LB Uni]; split.
  - firstorder.
  - move=> A' LB'; apply: Uni => r'.
    case: (surj re r') => r <-; apply: LB'.
Qed.
Lemma reindex_lub `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X} {A}
  : lub J A -> lub (J ∘ re) A.
Proof.
  move=> [UB Uni]; split.
  - firstorder.
  - move=> A' UB'; apply: Uni => r'.
    case: (surj re r') => r <-; apply: UB'.
Qed.
Lemma unreindex_glb `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X} {A}
  : glb (J ∘ re) A -> glb J A.
Proof.
  move=> [LB Uni]; split.
  - move=> r'.
    case: (surj re r') => r <-; apply: LB.
  - firstorder.
Qed.
Lemma unreindex_lub `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X} {A}
  : lub (J ∘ re) A -> lub J A.
Proof.
  move=> [UB Uni]; split.
  - move=> r'.
    case: (surj re r') => r <-; apply: UB.
  - firstorder.
Qed.
Lemma reindex_inf `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X}
      `{!HasInf J, !HasInf (J ∘ re)}
  : inf J ⟛ inf (J ∘ re).
Proof. apply/inf_unique/reindex_glb/is_inf. Qed.
Lemma reindex_sup `{Proset X} {R R'} (re : R -> R') `{!Surj (=) re} {J : R' -> X}
      `{!HasSup J, !HasSup (J ∘ re)}
  : sup J ⟛ sup (J ∘ re).
Proof. apply/sup_unique/reindex_lub/is_sup. Qed.

(* A number of continuity results are over in adjunction.v, because they drop out
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
Instance precomp_continuous {Y Y'} `{Complete X} {f : Y' -> Y}
  : Continuous (fun g : Y -> X => g ∘ f).
Proof. move=> ? ?; by apply/distrib_inf_sufficient. Qed.
Instance precomp_cocontinuous {Y Y'} `{Complete X} {f : Y' -> Y}
  : Cocontinuous (fun g : Y -> X => g ∘ f).
Proof. move=> ? ?; by apply/distrib_sup_sufficient. Qed.
Instance eval_at_continuous {X} `{Complete Y} {x : X} : Continuous (eval_at (Y:=Y) x).
Proof. move=> ? ?; by apply/distrib_inf_sufficient. Qed.
Instance eval_at_cocontinuous {X} `{Complete Y} {x : X}
  : Cocontinuous (eval_at (Y:=Y) x).
Proof. move=> ? ?; by apply/distrib_sup_sufficient. Qed.

Lemma distrib_top `{Proset X, Proset Y, !Top X, !Top Y} {F : X -> Y}
      `{!PresDInfsOfShape void F}
  : F ⊤ ⟛ ⊤.
Proof. rewrite distrib_inf; by apply: (mono_core einf); apply/pw_core'. Qed.
Lemma distrib_bot `{Proset X, Proset Y, !Bot X, !Bot Y} {F : X -> Y}
      `{!PresDSupsOfShape void F}
  : F ⊥ ⟛ ⊥.
Proof. rewrite distrib_sup; by apply: (mono_core esup); apply/pw_core'. Qed.
Lemma distrib_meet `{Proset X, Proset Y, !BinMeets X, !BinMeets Y}
      {F : X -> Y} `{!PresDInfsOfShape bool F} {A B}
  : F (A ⩕ B) ⟛ F A ⩕ F B.
Proof. rewrite distrib_inf; apply: (mono_core einf); apply/pw_core' => -[] //. Qed.
Lemma distrib_join `{Proset X, Proset Y, !BinJoins X, !BinJoins Y}
      {F : X -> Y} `{!PresDSupsOfShape bool F} {A B}
  : F (A ⩖ B) ⟛ F A ⩖ F B.
Proof. rewrite distrib_sup; apply: (mono_core esup); apply/pw_core' => -[] //. Qed.
Lemma distrib_embed_prop `{Proset X, !SupLattice X, !Top X,
                           Proset Y, !SupLattice Y, !Top Y} {F : X -> Y}
      {P : Prop} `{!PresDInfsOfShape void F, !PresDSupsOfShape P F} 
  : F (⌜ P ⌝) ⟛ ⌜ P ⌝.
Proof.
  rewrite distrib_sup; apply: (mono_core esup); apply/pw_core' => H_P /=.
  apply: distrib_top.
Qed.

Lemma F_top `{Proset X, Proset Y, !Top X, !Top Y} {F : X -> Y}
  : F ⊤ ⊢ ⊤.
Proof. apply: top_right. Qed.
Lemma F_bot `{Proset X, Proset Y, !Bot X, !Bot Y} {F : X -> Y}
  : ⊥ ⊢ F ⊥.
Proof. apply: bot_left. Qed.
Lemma F_meet `{Proset X, Proset Y, !BinMeets X, !BinMeets Y}
      {F : X -> Y} `{!Monotone F} {A B}
  : F (A ⩕ B) ⊢ F A ⩕ F B.
Proof. apply: meet_right; [rewrite meet_proj1 // | rewrite meet_proj2 //]. Qed.
Lemma F_join `{Proset X, Proset Y, !BinJoins X, !BinJoins Y}
      {F : X -> Y} `{!Monotone F} {A B}
  : F A ⩖ F B ⊢ F (A ⩖ B).
Proof. apply: join_left; [rewrite -join_inj1 // | rewrite -join_inj2 //]. Qed.
Lemma F_embed_prop `{Proset X, !SupLattice X, !Top X,
                     Proset Y, !SupLattice Y, !Top Y} {F : X -> Y}
      `{!Monotone F, !PresDInfsOfShape void F} {P}
  : ⌜ P ⌝ ⊢ F (⌜ P ⌝).
Proof.
  apply: embed_prop_left => H_P.
  rewrite /embed_prop -(sup_ub H_P) -(proj2 distrib_top) //.
Qed.


Lemma lex_alt `{Proset X, !MeetSemilattice X, Proset Y} (F : X -> Y) `{!Monotone F}
  : PresDInfsOfShape void F -> PresDInfsOfShape bool F -> Lex F.
Proof.
  move=> Base Step.
  enough (forall n, PresDInfsOfShape (fin n) F). {
    move=> R ? ? J A.
    have ? : Surj (=) (decode_fin (A:=R)) by apply/cancel_surj/decode_encode_fin.
    move=> /(reindex_glb decode_fin) /(preserve_inf (F:=F) A).
    apply: unreindex_glb.
  }
  elim=> [| n IH] J; apply/preserves_inf_alt2.
  - have ? : Surj (=) (of_void (fin 0)) by move=> x; case: (Fin.case0 (const False) x).
    rewrite reindex_inf distrib_inf'; apply/(unreindex_glb (of_void _))/is_inf.
  - split=> [? | B LB]; first by rewrite inf_lb /=.
    rewrite (_ : inf J ⟛ J Fin.F1 ⩕ inf (J ∘ FS)).
    + rewrite distrib_inf'; apply: inf_right => -[]; first by apply: LB.
      rewrite distrib_inf'; apply: inf_right => ?; apply: LB.
    + split; first apply: meet_right.
      * apply: inf_lb.
      * apply: inf_right => ?; apply: inf_lb.
      * apply: inf_right => r; elim/(Fin.caseS' (n:=n)): r => [| r].
        -- apply: meet_proj1.
        -- apply: meet_left2; apply: inf_lb.
Qed.
Lemma rex_alt `{Proset X, !JoinSemilattice X, Proset Y} (F : X -> Y) `{!Monotone F}
  : PresDSupsOfShape void F -> PresDSupsOfShape bool F -> Rex F.
Proof.
  move=> Base Step.
  enough (forall n, PresDSupsOfShape (fin n) F). {
    move=> R ? ? J A.
    have ? : Surj (=) (decode_fin (A:=R)) by apply/cancel_surj/decode_encode_fin.
    move=> /(reindex_lub decode_fin) /(preserve_sup (F:=F) A).
    apply: unreindex_lub.
  }
  elim=> [| n IH] J; apply/preserves_sup_alt2.
  - have ? : Surj (=) (of_void (fin 0)) by move=> x; case: (Fin.case0 (const False) x).
    rewrite reindex_sup distrib_sup'; apply/(unreindex_lub (of_void _))/is_sup.
  - split=> [? | B UB]; first by rewrite -sup_ub /=.
    rewrite (_ : sup J ⟛ J Fin.F1 ⩖ sup (J ∘ FS)).
    + rewrite distrib_sup'; apply: sup_left => -[]; first by apply: UB.
      rewrite distrib_sup'; apply: sup_left => ?; apply: UB.
    + split; last apply: join_left.
      * apply: sup_left => r; elim/(Fin.caseS' (n:=n)): r => [| r].
        -- apply: join_inj1.
        -- apply: join_right2; apply: sup_ub.
      * apply: sup_ub.
      * apply: sup_left => ?; apply: sup_ub.
Qed.

Program Instance Hom_inf `{Proset X, Proset Y} {R} {J : R -> Hom X Y}
        `{!forall x, HasInf (flip J x)}
  : HasInf J
  := {| inf := inf (ap_Hom ∘ J) ↾ _ |}.
Next Obligation.
  move=> X ? ? Y ? ? R J ? A B D /=.
  apply: inf_right => r; apply: (inf_left r) => /=; by apply: Hom_mono.
Qed.
Next Obligation.
  move=> X ? ? Y ? ? R J ? /=; split=> [r | A' LB] A /=.
  - apply: (inf_lb r).
  - apply: inf_right => r; apply: LB.
Qed.
Program Instance Hom_sup `{Proset X, Proset Y} {R} {J : R -> Hom X Y}
        `{!forall x, HasSup (flip J x)}
  : HasSup J
  := {| sup := sup (ap_Hom ∘ J) ↾ _ |}.
Next Obligation.
  move=> X ? ? Y ? ? R J ? A B D /=.
  apply: sup_left => r; apply: (sup_right r) => /=; by apply: Hom_mono.
Qed.
Next Obligation.
  move=> X ? ? Y ? ? R J ? /=; split=> [r | A' UB] A /=.
  - apply: (sup_ub r).
  - apply: sup_left => r; apply: UB.
Qed.
(* TODO Make some of the subsequent stuff more fine-grained. *)
Instance ap_Hom_complete_continuous `{Proset X, Complete Y}
  : Continuous (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> ? ?; by apply/distrib_inf_sufficient. Qed.
Instance ap_Hom_complete_cocontinuous `{Proset X, Complete Y}
  : Cocontinuous (ap_Hom (X:=X) (Y:=Y)).
Proof. move=> ? ?; by apply/distrib_sup_sufficient. Qed.
(* Hmm. *)
Instance flip_functoriality {R} `{Proset Y, Proset X}
         {F : R -> Y -> X} `{!forall r, Monotone (F r)}
  : Monotone (flip F).
Proof. firstorder. Qed.
Lemma Hom_inf_ `{Proset X, Complete Y} {R} (J : R -> Hom X Y)
  : inf J ⟛ in_Hom (einf ∘ flip J).
Proof. generalize dependent X; generalize dependent Y; by compute. Qed.
Lemma Hom_sup_ `{Proset X, Complete Y} {R} (J : R -> Hom X Y)
  : sup J ⟛ in_Hom (esup ∘ flip J).
Proof. generalize dependent X; generalize dependent Y; by compute. Qed.
Instance Hom_compose_continuous `{Proset X, Proset X', Complete Y} {F : Hom X' X}
  : Continuous (fun G : Hom X Y => G ○ F).
Proof.
  move=> R J; apply: distrib_inf_sufficient.
  - move=> G G'; apply: (bi_l Hom_compose).
  - move=> A /=; apply: (mono einf) => ? //=.
Qed.
Instance Hom_compose_cocontinuous `{Proset X, Proset X', Complete Y} {F : Hom X' X}
  : Cocontinuous (fun G : Hom X Y => G ○ F).
Proof.
  move=> R J; apply: distrib_sup_sufficient.
  - move=> G G'; apply: (bi_l Hom_compose).
  - move=> A /=; apply: (mono esup) => ? //=.
Qed.
Instance Hom_eval_at_continuous `{Proset X, Proset Y, !InfLattice Y} {x : X}
  : Continuous (Hom_eval_at (Y:=Y) x).
Proof. move=> ? ?; by apply: distrib_inf_sufficient. Qed.
Instance Hom_eval_at_cocontinuous `{Proset X, Proset Y, !SupLattice Y} {x : X}
  : Cocontinuous (Hom_eval_at (Y:=Y) x).
Proof. move=> ? ?; by apply: distrib_sup_sufficient. Qed.


(* Example *)
Definition fixed_point `{Proset X} (F : X -> X) (A : X) : Prop
  := F A ⟛ A.
Definition kleene_chain `{Proset X, !Bot X} (F : X -> X) : nat -> X
  := fun n => Nat.iter n F ⊥.
Instance: Params (@kleene_chain) 4 := {}.
Lemma kleene_chain_chain `{Proset X, !Bot X} {F : X -> X} `{!Monotone F}
  : chain (kleene_chain F).
Proof. elim=> /= [| n]; [apply: bot_left | apply: mono]. Qed.
Instance kleene_chain_mono `{Proset X, !Bot X} {F : X -> X} `{!Monotone F}
  : Monotone (kleene_chain F).
Proof. apply chain_mono, kleene_chain_chain. Qed.
Theorem kleene `{Proset X, !DirectedComplete X, !Bot X} {F : X -> X}
        `{!Monotone F, !ScottContinuous F}
  : least (fixed_point F) (sup (kleene_chain F)).
Proof.
  split.
  - rewrite /fixed_point distrib_sup; split; apply: sup_left => n.
    + by apply: (sup_right (S n)).
    + apply (sup_right n), kleene_chain_chain.
  - move=> A FP; apply: sup_left; elim=> /= [| n].
    + apply: bot_left.
    + move=> D; unfold fixed_point in FP.
      rewrite -(proj1 FP); by apply: mono.
Qed.


Class ReflectsInf `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  reflect_inf A : lower_bound J A -> glb (F ∘ J) (F A) -> glb J A.
Hint Mode ReflectsInf ! - - ! - - ! ! ! : typeclass_instances.
Arguments reflect_inf {_ _ _ _ _ _ _} F {_ _} A.

Class LiftsInf `{Proset X, Proset Y} {R} (F : X -> Y) (J : R -> X) :=
  lift_inf B : glb (F ∘ J) B -> {A | glb J A & F A ⟛ B}.
Hint Mode LiftsInf ! - - ! - - ! ! ! : typeclass_instances.
Arguments lift_inf {_ _ _ _ _ _ _} F {_ _} B.

(*
Lemma reflects_preserves `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F} {R} (J : R -> X) `{!HasInf (F ∘ J), !ReflectsInf F J}
  : image F (inf (F ∘ J)) -> PreservesInf F J.
Proof.
   move=> A Glb. apply/inf_unique.
Qed.

Lemma undistrib_inf `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F} {R} (J : R -> X) `{!HasInf J, !HasInf (F ∘ J), !ReflectsInf F J} A
  : F A ⟛ inf (F ∘ J) -> A ⟛ inf J.
Proof. move=> /inf_unique Glb. apply/inf_unique. apply: (reflect_inf A). ; apply: reflecting_reflects_inf. Qed.
Lemma reflecting_undistrib_sup `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) `{!HasSup (F ∘ J)} A
  : F A ⟛ sup (F ∘ J) -> lub J A.
Proof. move=> /sup_unique; apply: reflecting_reflects_sup. Qed.
*)

Lemma reflecting_reflects_inf `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) A
  : glb (F ∘ J) (F A) -> glb J A.
Proof.
  move=> Glb; split=> [r | A' LB].
  - apply: (reflect F); apply: (proj1 Glb).
  - apply: (reflect F); apply: (proj2 Glb) => r /=; by apply: mono.
Qed.
Lemma reflecting_reflects_sup `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) A
  : lub (F ∘ J) (F A) -> lub J A.
Proof.
  move=> Lub; split=> [r | A' UB].
  - apply: (reflect F); apply: (proj1 Lub).
  - apply: (reflect F); apply: (proj2 Lub) => r /=; by apply: mono.
Qed.
Lemma reflecting_undistrib_inf `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) `{!HasInf (F ∘ J)} A
  : F A ⟛ inf (F ∘ J) -> glb J A.
Proof. move=> /inf_unique; apply: reflecting_reflects_inf. Qed.
Lemma reflecting_undistrib_sup `{Proset X, Proset Y} {F : X -> Y}
      `{!Monotone F, !Reflecting F} {R} (J : R -> X) `{!HasSup (F ∘ J)} A
  : F A ⟛ sup (F ∘ J) -> lub J A.
Proof. move=> /sup_unique; apply: reflecting_reflects_sup. Qed.
