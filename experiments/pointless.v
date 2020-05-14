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
