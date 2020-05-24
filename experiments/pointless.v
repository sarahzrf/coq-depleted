From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.adjunction.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Class Frame (X : Type)
      `{Proset X, !SupLattice X, !MeetSemilattice X, !Exponents X}.
Hint Mode Frame ! - - - - - : typeclass_instances.
Instance frame_def `{Proset X, !SupLattice X, !MeetSemilattice X, !Exponents X}
  : Frame X := {}.

Class FrameMorph `{Proset X, Proset Y} (F : X -> Y)
      `{!Monotone F, !Cocontinuous F, !Lex F}.
Hint Mode FrameMorph ! - - ! - - ! - - - : typeclass_instances.
Instance frame_morph_def `{Proset X, Proset Y} {F : X -> Y}
         `{!Monotone F, !Cocontinuous F, !Lex F}
  : FrameMorph F := {}.
Class FrameMorphPacked `{Proset X, Proset Y} (F : X -> Y) :=
  {frame_morph_mono :> Monotone F;
   frame_morph_cocont :> Cocontinuous F;
   frame_morph_lex :> Lex F}.
Hint Mode FrameMorphPacked ! - - ! - - ! : typeclass_instances.
(* This is not an instance in order to avoid loops in resolution. *)
Definition FMP `{FrameMorph X Y F} : FrameMorphPacked F.
Proof. constructor; typeclasses eauto. Defined.

(*
Class HasOpen (X : Type) := Open : Type.
Arguments Open X {_}.
Class Locale (X : Type) `{HasOpen X, Frame (Open X)}.
Hint Mode Locale ! - - - - - - - : typeclass_instances.
*)

Definition Map (X Y : Type) `{Proset X, Proset Y} : Type :=
  @sig (Y -> X) FrameMorphPacked.
Definition preimage (X Y : Type) `{Proset X, Proset Y} : Map X Y -> Y -> X
  := sval.
Arguments preimage {_ _ _ _ _ _} !_.
Instance: Params (@preimage) 6 := {}.
Notation "f ⁻¹" := (preimage f) (at level 1, format "f ⁻¹").
Instance preimage_bi `{Proset X, Proset Y} : Bimonotone (preimage (X:=X) (Y:=Y)).
Proof. move=> [F ?] [G ?] /= D ? ? -> //. Qed.
Instance Map_fmp `{Proset X, Proset Y} (F : Map X Y)
  : FrameMorphPacked (preimage F) := proj2_sig _.
Definition in_Map {X Y} `{FrameMorph Y X F} : Map X Y := F ↾ FMP.
Arguments in_Map {_ _ _ _ _ _} F {_ _ _ _} /.
Instance: Params (@in_Map) 6 := {}.
Lemma preimage_in_Map `{FrameMorph Y X F}
  : (in_Map F)⁻¹ = F.
Proof. done. Qed.
(* WARNING: This is brittle. It won't work in cases where the implicit arguments are filled
            differently from how Coq has inferred them here. *)
Lemma in_Map_preimage `{Proset X, Proset Y} {F : Map X Y} : in_Map F⁻¹ = F.
Proof. case: F => F [*] //=. Qed.
Lemma Map_core `{Proset X, Proset Y} {F G : Map X Y} : (forall A, F⁻¹ A ⟛ G⁻¹ A) <-> F ⟛ G.
Proof. compute; firstorder. Qed.
Definition Map_id `{Proset X} : Map X X := in_Map id.
Definition Map_compose `{Proset X, Proset Y, Proset Z'}
           (F : Map Y Z') (G : Map X Y) : Map X Z' := in_Map (G⁻¹ ∘ F⁻¹).
Infix "⊚" := Map_compose (at level 40) : proset_scope.
Notation "( f ⊚.)" := (Map_compose f) (only parsing) : proset_scope.
Notation "(.⊚ f )" := (flip Map_compose f) (only parsing) : proset_scope.
Instance: Params (@Map_id) 3 := {}.
Instance: Params (@Map_compose) 9 := {}.
Instance Map_compose_bi `{Proset X, Proset Y, Proset Z'}
  : Bimonotone (Map_compose (X:=X) (Y:=Y) (Z':=Z')).
Proof. move=> f g D f' g' D' x /=; rewrite D D' //. Qed.
Lemma Map_id_lident `{Proset X, Proset Y} {F : Map X Y}
  : Map_id ⊚ F ⟛ F.
Proof. compute; by fold (pro_le (X:=X)). Qed.
Lemma Map_id_rident `{Proset X, Proset Y} {F : Map X Y}
  : F ⊚ Map_id ⟛ F.
Proof. compute; by fold (pro_le (X:=X)). Qed.
Lemma Map_compose_assoc `{Proset X, Proset Y, Proset Z', Proset W}
      {F : Map Z' W} {G : Map Y Z'} {H' : Map X Y}
  : F ⊚ (G ⊚ H') ⟛ (F ⊚ G) ⊚ H'.
Proof. compute; by fold (pro_le (X:=X)). Qed.
Definition preimage_of `{Proset X, Proset Y} (y : Y) : Map X Y -> X := fun F => F⁻¹ y.
Arguments preimage_of {_ _ _ _ _ _} y _ /.
Instance: Params (@preimage_of) 6 := {}.
Instance preimage_of_mono `{Proset X, Proset Y}
  : Monotone (preimage_of (X:=X) (Y:=Y)).
Proof. solve_proper. Qed.
Instance preimage_of_bi `{Proset X, Proset Y}
  : Bimonotone (preimage_of (X:=X) (Y:=Y)).
Proof. solve_proper. Qed.
Instance preimage_of_cocontinuous `{Proset X, Proset Y, !SupLattice X}
  : Cocontinuous (preimage_of (X:=X) (Y:=Y)).
Proof.
  move=> R J.
  apply/preserves_sup_alt => ?; apply/sup_unique/pw_core' => f /=.
  rewrite distrib_sup //.
Qed.
Instance preimage_of_lex `{Proset X, Proset Y, !MeetSemilattice X}
  : Lex (preimage_of (X:=X) (Y:=Y)).
Proof.
  move=> R ? ? J.
  apply/preserves_inf_alt => ?; apply/inf_unique/pw_core' => f /=.
  rewrite distrib_inf //.
Qed.


(* The point as a locale. *)
Definition point : Type := Prop.

Instance embed_prop_lex `{Frame X} : Lex (embed_prop (X:=X)).
Proof.
  apply: lex_alt => J; apply: distrib_inf_sufficient.
  - apply: embed_prop_right => -[].
  - apply: prop_loop => [| ?] ; first apply: (inf_lb true).
    apply: prop_loop => [| ?] ; first apply: (inf_lb false).
    apply: embed_prop_right => -[] //.
Qed.
Definition to_point `{Frame X} : Map X point := in_Map embed_prop.
Instance: Params (@to_point) 7 := {}.
Lemma point_terminal `{Frame X} (F : Map X point) : F ⟛ to_point.
Proof.
  apply/Map_core => p.
  rewrite {1}(mono_core F⁻¹ (_ : p ⟛ (Sup H : p, ⊤))).
  - rewrite distrib_sup.
    apply: (mono_core esup); apply/pw_core' => ?; apply: distrib_top.
  - split; last by firstorder.
    move=> H_p; exists H_p => -[].
Qed.

(* TODO Put this in the right place. *)
Program Instance Hom_exponents `{Proset X, Proset Y, !InfLattice Y, !Exponents Y}
  : Exponents (Hom X Y)
  := {| exponential F G A := Inf B : {B0 | A ⊢ B0}, F (` B) ⟿ G (` B) |}.
Next Obligation.
  move=> * A B D.
  apply: inf_right => -[B' D'] /=.
  apply: (inf_left (_ ↾ _)); by etransitivity.
Qed.
Next Obligation.
  move=> X ? ? Y ? ? ? ? F G H; split.
  - move=> Uncurried A /=; apply: inf_right => -[B /= ->].
    rewrite -meet_exponential -(distrib_meet (F:=Hom_eval_at B)); apply/Uncurried.
  - move=> /= Curried A; specialize (Curried A); simpl in Curried.
    setoid_rewrite (inf_lb (A ↾ reflexivity _)) in Curried; simpl in Curried.
    etransitivity; first by apply: (F_meet (F:=Hom_eval_at A)).
    rewrite meet_exponential //.
Qed.

Definition sier : Type := Hom bool Prop.
Identity Coercion sier_to_Hom : sier >-> Hom.
Definition characteristic_f `{Frame X} (U : X) (S : sier) : X
  := (embed_prop (S true) ⩕ U) ⩖ embed_prop (S false).
Arguments characteristic_f {_ _ _ _ _ _ _} U S /.
Instance: Params (@characteristic_f) 7 := {}.
Lemma characteristic_f_uni `{Frame X} (U : X) (S : sier) (V : X)
  : characteristic_f U S ⊢ V <-> (S true -> U ⊢ V) /\ (S false -> ⊤ ⊢ V).
Proof.
  split.
  - move=> /= <-; split=> H_S.
    + apply: join_right1; apply: meet_right; [by apply: embed_prop_right | done].
    + apply: join_right2; by apply: embed_prop_right.
  - move=> [D1 D2]; apply: join_left.
    + apply: (prop_loop meet_proj1) => /D1 ->; apply: meet_proj2.
    + by apply: embed_prop_left.
Qed.
(*
Lemma characteristic_f_cases `{Frame X} (U : X) (S : sier)
  : characteristic_f U S ⊢ ⌜ (S false /\ ⊤ ⟛ characteristic_f U S) \/
                             (S true /\ U ⊢ characteristic_f U S) ⌝.
Proof.
  apply: join_left.
  - apply: sup_left => ?; apply: embed_prop_right.
    right; split; first by done.
    apply: join_right1; by apply: sup_ub.
  - apply: mono => ?.
    left; split; first by done.
    split; [apply: join_right2; by apply: embed_prop_right | apply: top_right].
Qed.
*)
Instance characteristic_f_bi `{Frame X} : Bimonotone (characteristic_f (X:=X)).
Proof. solve_proper. Qed.
Instance characteristic_f_cocontinuous `{Frame X} {U : X}
  : Cocontinuous (characteristic_f U).
Proof.
  move=> R J; apply: distrib_sup_sufficient.
  apply/characteristic_f_uni; split=> -[r /= ?]; apply: (sup_right r).
  + apply: join_right1; apply: meet_right; [by apply: embed_prop_right | done].
  + apply: join_right2; by apply: embed_prop_right.
Qed.
Instance characteristic_f_lex `{Frame X} {U : X}
  : Lex (characteristic_f U).
Proof.
  apply: lex_alt => J; apply: distrib_inf_sufficient.
  - apply: join_right2; apply: embed_prop_right => -[].
  - rewrite [L in L ⊢ _](meet_right (reflexivity _) (reflexivity _))
            {1}(inf_lb false) (inf_lb true) meet_exponential.
    apply/characteristic_f_uni; split => H_J1.
    all: rewrite -meet_exponential l_meet_exponential.
    all: apply/characteristic_f_uni; split => H_J2; rewrite -l_meet_exponential.
    + apply: join_right1; apply: meet_right.
      * apply: embed_prop_right; by case.
      * apply: meet_proj1.
    + apply: join_right1; apply: meet_right.
      * apply: embed_prop_right; case=> //=; by apply: (Hom_mono (J true)) H_J2.
      * apply: meet_proj1.
    + apply: join_right1; apply: meet_right.
      * apply: embed_prop_right; case=> //=; by apply: (Hom_mono (J false)) H_J1.
      * apply: meet_proj2.
    + apply: join_right2; apply: embed_prop_right; by case.
Qed.

(*
    apply: (prop_loop (R:=J true true)) => [| H_J1]. {
      apply: (inf_left true).
      apply: join_left; apply: sup_left => H_J; apply: embed_prop_right; first by done.
      move: H_J; by apply: (Hom_mono (J true)).
    }
    apply: (prop_loop (R:=J false true)) => [| H_J2]. {
      apply: (inf_left false).
      apply: join_left; apply: sup_left => H_J; apply: embed_prop_right; first by done.
      move: H_J; by apply: (Hom_mono (J false)).
    }
    apply: join_right1.  simpl. unfold flip. ; apply: embed_prop_right => -[] //=.
Qed.
*)
Definition characteristic `{Frame X} (U : X) : Map X sier
  := in_Map (characteristic_f U).
Arguments characteristic {_ _ _ _ _ _ _} U.
Instance: Params (@characteristic) 7 := {}.
Instance characteristic_mono `{Frame X} : Monotone (characteristic (X:=X)).
Proof. move=> U V D /= S; rewrite D //. Qed.
Definition universal_open : sier := in_Hom is_top.
Theorem sier_classifies_opens `{Frame X} (U : X) (F : Map X sier)
  : F ⟛ characteristic U <-> F⁻¹ universal_open ⟛ U.
Proof.
  split.
  - move=> -> /=; split; first apply: join_left.
    + apply: meet_proj2.
    + apply: embed_prop_left => ? //.
    + apply: join_right1; apply: meet_right => //; by apply: embed_prop_right.
  - move=> <- /=; apply/Map_core => S /=.
    rewrite (mono_core (F⁻¹) (_ : S ⟛ (characteristic universal_open)⁻¹ S)).
    + rewrite distrib_join distrib_meet distrib_embed_prop.
      apply: mono_core; apply: distrib_embed_prop.
    + apply/Hom_core => b.
      rewrite -[R in _ ⟛ R]/(Hom_eval_at b _)
        distrib_join distrib_meet [_ _ universal_open]/= /is_top.
      split.
      * case: b.
        -- apply join_right1, meet_right => // H_S; exists H_S => -[].
        -- apply join_right2 => H_S; exists H_S => -[].
      * apply join_left => [P | [H_S _]].
        -- move: (P true) (P false) => [? ?] <- //.
        -- case: b => //; by apply: (Hom_mono S) H_S.
Qed.

Definition point_of (X : Type) `{Proset X} : Type := Map point X.
Definition point_set (X : Type) `{Proset X} : Type := point_of X -> Prop.
Definition points_in `{Proset X} : X -> point_set X
  := preimage_of.
Arguments points_in {_ _ _} U !_ /.
Instance: Params (@points_in) 3 := {}.
Definition frame_interior `{Proset X, !SupLattice X} : point_set X -> X
  := universal_right_adjoint points_in.
Arguments frame_interior {_ _ _ _} U /.
Instance: Params (@frame_interior) 4 := {}.
Instance frame_interior_mono `{Proset X, !SupLattice X}
  : Monotone (frame_interior (X:=X)).
Proof. move=> U V D; rewrite /frame_interior D //. Qed.
Instance points_in_frame_interior_adj `{Proset X, !SupLattice X}
  : points_in (X:=X) ⊣ frame_interior
  := universal_adjunction2.
Definition interior `{Proset X, !SupLattice X} : point_set X -> point_set X
  := points_in ∘ frame_interior.
Arguments interior {_ _ _ _} U /.
Instance: Params (@interior) 4 := {}.

Definition open `{Proset X} (U : point_set X) : Prop
  := exists V, U ⟛ points_in V.
Lemma open_alt `{Frame X} (U : point_set X)
  : open U <-> forall p, U p -> exists V, points_in V p /\ points_in V ⊢ U.
Proof.
  split; first by firstorder.
  move=> Cov; exists (frame_interior U); split; last by apply: (adj_counit' _ _).
  move=> p /=; rewrite -[R in _ ⊢ R]F_sup => U_p /=.
  move: (U_p) => /Cov [V D] /=.
  unshelve eexists (V ↾ _) => /=; firstorder.
Qed.

(* TODO Move this
Definition choose `{Proset X, !SupLattice X} (P : X -> Prop) : X := Sup A : sig P, `A.
Lemma choose_spec `{Proset X, !SupLattice X} (P : X -> Prop) `{!Monotone P}
  : (exists A, P A) -> P (choose P).
Proof. move=> [A PA]; rewrite /choose -(sup_ub (A ↾ PA)) //=. Qed.
Theorem choice `{Proset X, !SupLattice X} {R} (P : R -> X -> Prop)
        `{!Proper ((=) ==> (⊢) ==> impl) P}
  : (forall r, exists A, P r A) -> exists f, forall r, P r (f r).
Proof. move=> AllEx; exists (fun r => choose (P r)) => r; by apply: choose_spec. Qed.
*)

Lemma open_union `{Frame X} {R} (J : R -> point_set X)
  : (forall r, open (J r)) -> open (sup J).
Proof.
  move=> AllOpen.
  apply/open_alt => p [r /= In].
  case: (AllOpen r) => U E; exists U; firstorder.
Qed.
Lemma open_intersection `{Frame X, Finite R} (J : R -> point_set X)
  : (forall r, open (J r)) -> open (inf J).
Proof.
  move=> /finite_choice [Neighs E_Neighs].
  apply/open_alt => p /= InAll.
  exists (inf Neighs); split; rewrite distrib_inf; firstorder.
Qed.

Definition soberification (X : Type) `{Proset X} : Type
  := @sig (point_set X) open.
Definition as_open `{Proset X, !SupLattice X} : soberification X -> X
  := frame_interior ∘ sval.
Arguments as_open {_ _ _ _} U /.
Instance: Params (@as_open) 4 := {}.
Instance as_open_mono `{Frame X} : Monotone (as_open (X:=X)).
Proof. unfold as_open; typeclasses eauto. Qed.
(*
Instance as_open_reflecting `{Frame X} : Reflecting (as_open (X:=X)).
*)

Program Instance soberification_suplattice `{Frame X} : SupLattice (soberification X)
  := fun R J => {| sup := sup (sval ∘ J) ↾ _ |}.
Next Obligation. move=> *; apply: open_union => r /=; apply: proj2_sig. Qed.
Next Obligation. move=> *; apply/(reflecting_reflects_sup (F:=sval))/is_sup. Qed.
Program Instance soberification_meet_semilattice `{Frame X}
  : MeetSemilattice (soberification X)
  := fun R _ _ J => {| inf := inf (sval ∘ J) ↾ _ |}.
Next Obligation. move=> *; apply: open_intersection => r /=; apply: proj2_sig. Qed.
Next Obligation. move=> *; apply/(reflecting_reflects_inf (F:=sval))/is_inf. Qed.
(*
Program Instance soberification_exponents `{Frame X} : Exponents (soberification X)
  := {| exponential U V := points_in (frame_interior U ⟿ frame_interior V) |}.
Next Obligation. firstorder. Qed.
*)


Record Presheaf `{Proset X} : Type :=
  {section_on (U : X) : Type;
   Section_Le (U : X) : Le (section_on U);
   Section_Proset (U : X) : Proset (section_on U);

   restrict {U V : X} : U ⊢ V -> section_on V -> section_on U;
   restrict_mono (U V : X) (H : U ⊢ V) : Monotone (restrict H);
   restrict_id (U : X) (H : U ⊢ U) : restrict H ⟛ id;
   restrict_compose (U V W : X) (H1 : U ⊢ V) (H2 : V ⊢ W) (H3 : U ⊢ W) :
     restrict H1 ∘ restrict H2 ⟛ restrict H3}.
Arguments Presheaf _ {_ _}.
(* Arguments as_open {_ _ _ _} U /. *)
Instance: Params (@section_on) 3 := {}.
Instance: Params (@restrict) 3 := {}.
Existing Instances Section_Le Section_Proset restrict_mono.

Lemma restrict_id'1 `{Proset X} (P : Presheaf X) (U : X) (s : P.(section_on) U)
  : P.(restrict) (reflexivity U) s ⟛ s.
Proof. apply: (pw_core (restrict_id _ _ _)). Qed.
Lemma restrict_id'2 `{Proset X} (P : Presheaf X) (U : X) (s : P.(section_on) U)
      (D : U ⊢ U)
  : P.(restrict) D s ⟛ s.
Proof. apply: (pw_core (restrict_id _ _ _)). Qed.
Lemma restrict_compose' `{Proset X} (P : Presheaf X) {U V W : X}
      (H1 : U ⊢ V) (H2 : V ⊢ W) (s : P.(section_on) W)
  : P.(restrict) H1 (P.(restrict) H2 s) ⟛ P.(restrict) (transitivity H1 H2) s.
Proof. apply: (pw_core (restrict_compose _ _ _ _ H1 H2 _)). Qed.

Lemma restrict_proof_irrel `{Proset X} (P : Presheaf X) {U V : X}
      (D D' : U ⊢ V) (s : P.(section_on) V)
  : P.(restrict) D s ⟛ P.(restrict) D' s.
Proof.
  rewrite -(pw_core (restrict_compose P _ _ _ D' (reflexivity _) D)) /=
    (mono_core _ (restrict_id'1 P V s)) //.
Qed.

Program Definition partial_monotone (X Y : Type) `{Proset X, Proset Y}
  : Presheaf (X -> Prop)
  := {| section_on U := Hom (sig U) Y;
        restrict U V H f x := f x |}.
Next Obligation. typeclasses eauto. Defined.
Next Obligation. typeclasses eauto. Defined.
Next Obligation. move=> ? ? ? ? ? ? ? ? H ? [? ?]; by apply: H. Qed.
Next Obligation. move=> /= * [? ?] [? ?] /= D; by apply: Hom_mono. Qed.
Next Obligation.
  move=> /= * [? ?] [? ?].
  rewrite /= /partial_monotone_obligation_1 /= => D [? ?] /=.
  rewrite D //.
Qed.
Next Obligation.
  move=> /= *.
  apply/pw_core' => ? /=; apply/Hom_core => -[? ?] /=.
  split; apply: Hom_mono; by simpl.
Qed.
Next Obligation.
  move=> /= *.
  apply/pw_core' => ? /=; apply/Hom_core => -[? ?] /=.
  split; apply: Hom_mono; by simpl.
Qed.

Program Definition sub_partial_monotone (X Y : Type) (O : (X -> Prop) -> Prop)
        `{Proset X, Proset Y}
  : Presheaf (sig O)
  := {| section_on U := Hom (sig U) Y;
        restrict U V H f x := f x |}.
Next Obligation. move=> /=; typeclasses eauto. Defined.
Next Obligation. move=> /=; typeclasses eauto. Defined.
Next Obligation. move=> ? ? ? ? ? ? ? ? ? H ? [? ?]; by apply: H. Qed.
Next Obligation. move=> /= * [? ?] [? ?] /= D; by apply: Hom_mono. Qed.
Next Obligation.
  move=> /= * [? ?] [? ?].
  rewrite /= /sub_partial_monotone_obligation_1 /= => D [? ?] /=.
  rewrite D //.
Qed.
Next Obligation.
  move=> /= *.
  apply/pw_core' => ? /=; apply/Hom_core => -[? ?] /=.
  split; apply: Hom_mono; by simpl.
Qed.
Next Obligation.
  move=> /= *.
  apply/pw_core' => ? /=; apply/Hom_core => -[? ?] /=.
  split; apply: Hom_mono; by simpl.
Qed.

(* restriction of [pre]sheaves *)
Program Definition direct_image `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F}
        (P : Presheaf Y) : Presheaf X
  := {| section_on U := P.(section_on) (F U);
        restrict U V H := P.(restrict) (mono F H) |}.
Next Obligation. move=> /= *; rewrite restrict_id //. Qed.
Next Obligation. move=> /= *; rewrite restrict_compose //. Qed.
Arguments direct_image {_ _ _ _ _ _} F {_} P.
Instance: Params (@direct_image) 6 := {}.


Definition is_filter `{Proset X} (P : Hom X Prop) : Prop
  := exists _ : Codirected (sig P), True.
Definition filter_in (X : Type) `{Proset X} : Type :=
  @sig (Hom X Prop) is_filter.
Definition ap_filter (X : Type) `{Proset X} : filter_in X -> Hom X Prop
  := sval.
Arguments ap_filter {_ _ _} !_.
Instance: Params (@ap_filter) 3 := {}.
Coercion ap_filter : filter_in >-> Hom.
Instance ap_filter_bi `{Proset X} : Bimonotone (ap_filter (X:=X)).
Proof. move=> [[F ?] ?] [[G ?] ?] /= D ? ? -> //. Qed.

Lemma filter_iff_lex `{Proset X, !MeetSemilattice X} (P : Hom X Prop)
  : is_filter P <-> Lex P.
Proof.
  split.
  - move=> [? _]; apply: lex_alt => J; apply: distrib_inf_sufficient.
    + (* case: (codirect_is_ub (of_void _)) => -[x P_x] _. *)
      rewrite -(_ : ` (codirect (of_void (sig P))) ⊢ inf J).
      * move=> _; case: (codirect _) => //.
      * apply: inf_right => -[].
    + move=> H_b; pose J' b := J b ↾ H_b b.
      rewrite -(_ : ` (codirect J') ⊢ inf J) //.
      * case: (codirect _) => //.
      * apply: inf_right => b; apply: (codirect_is_lb J').
  - move=> ?; (exists) => //.
    unshelve refine {| codirect R _ _ J := inf (sval ∘ J) ↾ _ |}; last first.
    + move=> R ? ? J r; apply: (reflect sval); rewrite /= inf_lb //=.
    + rewrite (distrib_inf (sval ∘ J)) => r' /=; case: (J r') => //.
Qed.

Lemma improper_is_filter `{Codirected X} : is_filter (top (Hom X Prop)).
Proof.
  exists => //; unshelve refine {| codirect R _ _ J := codirect (sval ∘ J) ↾ _ |}.
  - move=> [].
  - move=> * ?; apply: codirect_is_lb.
Qed.

Definition improper `{Codirected X} : filter_in X := ⊤ ↾ improper_is_filter.
Instance: Params (@improper) 4 := {}.

Definition principal {X} (x : X) : filter_in (X -> Prop)
  := in_Hom (eval_at x) ↾ proj2 (filter_iff_lex _) _.
Arguments principal {_} x /.
Instance: Params (@principal) 1 := {}.

(* TODO meets and joins of filters *)

Record stalk `{Proset X} {P : Presheaf X} {F : filter_in X} : Type :=
  {rep_domain : X; rep_domain_F : F rep_domain;
   rep_section : P.(section_on) rep_domain}.
Arguments stalk {_ _ _} P F.
Instance: Params (@rep_domain) 3 := {}.
Instance: Params (@rep_domain_F) 3 := {}.
Instance: Params (@rep_section) 3 := {}.

Instance stalk_le `{Proset X} {P : Presheaf X} {F : filter_in X} : Le (stalk P F)
  := fun f g => exists (U : X) (H1 : U ⊢ f.(rep_domain)) (H2 : U ⊢ g.(rep_domain)),
         F U /\ P.(restrict) H1 f.(rep_section) ⊢ P.(restrict) H2 g.(rep_section).
Arguments stalk_le {_ _ _ _ _} !_ !_ /.
Instance stalk_proset `{Proset X} {P : Presheaf X} {F : filter_in X}
  : Proset (stalk P F).
Proof.
  constructor. {
    move=> f; unshelve eexists f.(rep_domain), _, _; try done.
    split; [apply: f.(rep_domain_F) | done].
  }
  case: F => F [? ?].
  move=> f g h [U [H1 [H2 [F_U D]]]] [U' [H1' [H2' [F_U' D']]]].
  set V := codirect (bool_e (U ↾ F_U) (U' ↾ F_U')).
  set LB := codirect_is_lb _ : lower_bound _ V.
  case: V {LB} (LB true) (LB false) => /= V F_V LB1 LB2.
  eexists V, _, _; split; first by simpl.
  setoid_rewrite <- (restrict_compose' P LB1 H1 f.(rep_section)).
  setoid_rewrite <- (restrict_compose' P LB2 H2' h.(rep_section)).
  rewrite D -(mono _ D').
  rewrite !restrict_compose' restrict_proof_irrel //.
Qed.

Definition germ_at `{Proset X} {P : Presheaf X} {U : X} (F : filter_in X) (F_U : F U)
           (s : P.(section_on) U) : stalk P F
  := {| rep_domain := U; rep_domain_F := F_U; rep_section := s |}.
Arguments germ_at {_ _ _ _ _} F F_U s /.
Instance: Params (@germ_at) 5 := {}.
Instance germ_at_mono `{Proset X} {P : Presheaf X} {U : X}
         {F : filter_in X} {F_U : F U} : Monotone (germ_at (P:=P) F F_U).
Proof.
  move=> s s' D /=.
  (unshelve eexists U, _, _); try done.
  rewrite D //.
Qed.


(* ... germs of nets *)

Definition od_le `{Proset T} (i : op T) (j : discrete T) : Prop
  := get_op i ⊢ get_discrete j.
Arguments od_le {_ _ _} _ _ /.
Instance: Params (@od_le) 3 := {}.
Instance od_le_mono `{Proset T} : Monotone (od_le (T:=T)).
Proof. move=> i i' D j /=; rewrite D //. Qed.
Definition net (T X : Type) `{Directed T, Proset X} : Presheaf (op T)
  := direct_image od_le (partial_monotone (discrete T) X).

Definition hyper (T X : Type) `{Directed T, Proset X} := stalk (net T X) improper.
Program Definition formal_limit `{Directed T, Proset X} (n : T -> X)
  : hyper T X
  := germ_at (P:=net T X) (U:=codirect (of_void _)) improper _ n.
Next Obligation. move=> * []. Qed.
Next Obligation. move=> * ? ? /= -> //. Qed.
Arguments formal_limit {_ _ _ _ _ _ _} n /.
Instance: Params (@formal_limit) 7 := {}.

Definition const_germ `{Directed T, Proset X} (x : X) : hyper T X
  := formal_limit (const x).
Arguments const_germ {_ _ _ _ _ _ _} x /.
Instance: Params (@const_germ) 7 := {}.
Definition constant `{Directed T, Proset X} (h : hyper T X) : Prop
  := exists x, h ⟛ const_germ x.
Instance: Params (@constant) 7 := {}.
Instance constant_ext `{Directed T, Proset X} : Extensional (constant (T:=T) (X:=X)).
Proof. move=> h h' E; split=> -[x E']; exists x; [rewrite -E // | rewrite E //]. Qed.

(* special case? *)
Program Definition seq_tail (X : Type) `{Proset X} : Presheaf (op nat)
  := {| section_on _ := nat -> X;
        restrict n m H s i := s (i + (n - m)) |}.
Next Obligation.
  move=> /= ? ? ? ? ?; apply/pw_core' => a; apply/pw_core' => i.
    by replace (i + _) with i by lia.
Qed.
Next Obligation.
  move=> /= ? ? ? n m o H1 H2 H3; apply/pw_core' => a; apply/pw_core' => i /=.
  change (?n ⊢ ?m) with (m <= n) in *.
    by replace (i + _ + _) with (i + (n - o)) by lia.
Qed.
