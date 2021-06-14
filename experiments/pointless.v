From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import QArith.
Require Import stdpp.finite.
Require Import stdpp.tactics.
Require Import Lqa.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.adjunction.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Class Frame (X : Type)
      `{MeetSemilattice X, !SupLattice X, !Exponents X}.
Hint Mode Frame ! - - - - - - - : typeclass_instances.
Instance frame_def `{MeetSemilattice X, !SupLattice X, !Exponents X}
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
Notation "f ⁻¹" := (preimage f) (at level 1, format "f ⁻¹") : proset_scope.
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
Instance preimage_of_lex `{MeetSemilattice X, MeetSemilattice Y}
  : Lex (preimage_of (X:=X) (Y:=Y)).
Proof.
  apply: lex_alt' => [| A B] f /=; rewrite -/(eval_at f _).
  - rewrite !distrib_top //.
  - rewrite !distrib_meet //.
Qed.


(* The point as a locale. *)
Definition point : Type := Prop.

(* TODO Put this in the right place. *)
Instance embed_prop_lex `{Frame X} : Lex (embed_prop (X:=X)).
Proof.
  apply: lex_alt' => [| A B].
  - by apply: embed_prop_right.
  - apply: prop_loop => [| ?]; first by apply: meet_proj1.
    apply: prop_loop => [| ?] ; first apply: (inf_lb false).
      by apply: embed_prop_right.
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
    move=> H_p; by exists H_p.
Qed.

Definition sier : Type := Hom bool Prop.
Identity Coercion sier_to_Hom : sier >-> Hom.
Definition characteristic_f `{Frame X} (U : X) (S : sier) : X
  := (embed_prop (S true) ⩕ U) ⩖ embed_prop (S false).
Arguments characteristic_f {_ _ _ _ _ _ _ _ _} U S /.
Instance: Params (@characteristic_f) 9 := {}.
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
  apply: lex_alt' => [| A B].
  - apply: join_right2; by apply: embed_prop_right.
  - apply/meet_exponential/characteristic_f_uni; split => H_A.
    all: rewrite -meet_exponential l_meet_exponential.
    all: apply/characteristic_f_uni; split => H_B; rewrite -l_meet_exponential.
    + apply: join_right1; apply: meet_right.
      * by apply: embed_prop_right.
      * apply: meet_proj1.
    + apply: join_right1; apply: meet_right.
      * apply: embed_prop_right; split=> //=; by apply: (Hom_mono B) H_B.
      * apply: meet_proj1.
    + apply: join_right1; apply: meet_right.
      * apply: embed_prop_right; split=> //=; by apply: (Hom_mono A) H_A.
      * apply: meet_proj2.
    + apply: join_right2; by apply: embed_prop_right.
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
Arguments characteristic {_ _ _ _ _ _ _ _ _} U.
Instance: Params (@characteristic) 9 := {}.
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
        -- apply join_right1, meet_right => // H_S; by (exists H_S).
        -- apply join_right2 => H_S; by (exists H_S).
      * apply join_left => [[[? ?] <-] | [H_S _]] //.
        case: b => //; by apply: (Hom_mono S) H_S.
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
  move=> Cov; exists (frame_interior U); split; last by apply: (adj_counit' _).
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
  set Has := @unbias_meets X.
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
Instance open_sup_closed `{Frame X} {R} {J : R -> soberification X} : SupClosed J
  := sup_closed_of_shape _ _ open_union _.
Instance open_inf_closed `{Frame X, Finite R} {J : R -> soberification X} : InfClosed J
  := inf_closed_of_shape _ _ open_intersection _.
Instance soberification_suplattice `{Frame X} : SupLattice (soberification X)
  := fun R J => sig_sup.
Program Instance soberification_meet_semilattice `{Frame X, Finite R}
  : DInfsOfShape R (soberification X)
  := fun J => sig_inf.
(*
Program Instance soberification_exponents `{Frame X} : Exponents (soberification X)
  := {| exponential U V := points_in (frame_interior U ⟿ frame_interior V) |}.
Next Obligation. firstorder. Qed.
*)


Definition subset (X : Type) `{Proset X} : Type := Hom (core X) Prop.
Identity Coercion subset_to_Hom : subset >-> Hom.
Program Definition sing `{Proset X} (x : X) : subset X := fun y : X => y ⟛ x.
Next Obligation. compute. firstorder. Qed.
Arguments sing {_ _ _} x.
Instance: Params (@sing) 3 := {}.
Definition refines `{Proset X} (U V : core X -> Prop) : Prop
  := forall u : X, U u -> exists v : X, u ⊢ v /\ V v.
Arguments refines {_ _ _} U V.
Instance: Params (@refines) 3 := {}.
Instance refines_di `{Proset X} : Dimonotone (refines (X:=X)).
Proof. move=> U U' /= D_U V V' D_V R u /D_U /R; firstorder. Qed.
Instance refines_preorder `{Proset X} : PreOrder (refines (X:=X)).
Proof.
  constructor; first by firstorder.
  move=> U V W R1 R2 u /R1 [v [D1 /R2]] [w [D2 ?]].
  exists w; rewrite D1 D2 //.
Qed.
Class Coverage `{Proset X} (Cov : X -> subset X -> Prop) :=
  {cov_le {u : X} {V} {v : X} : Cov u V -> V v -> v ⊢ u;
   shrink_cov {u u' : X} (H : u' ⊢ u) {V : subset X} (H' : Cov u V) : subset X;
   shrink_cov_spec1 {u u' : X} (H : u' ⊢ u) {V} (H' : Cov u V)
     : Cov u' (shrink_cov H H');
   shrink_cov_spec2 {u u' : X} (H : u' ⊢ u) {V} (H' : Cov u V)
     : refines (shrink_cov H H') V}.
Hint Mode Coverage ! - - ! : typeclass_instances.
Class Prosite (X : Type) `{Proset X} :=
  {covers : X -> subset X -> Prop;
   is_coverage : Coverage covers}.
Hint Mode Prosite ! - - : typeclass_instances.
Existing Instance is_coverage.

Local Arguments all _ /.
Definition sieve (X : Type) `{Proset X} : Type := Hom (op X) Prop.
Identity Coercion sieve_to_Hom : sieve >-> Hom.
Lemma sieve_map `{Proset X} {u v : X} (D : u ⊢ v) (U : sieve X) : U v ⊢ U u.
Proof. solve_proper. Qed.
Program Definition sieve_to_subset `{Proset X} (U : sieve X) : subset X
  := ` U ↾ _.
Next Obligation. move=> ? ? ? U A B [? ?]; by apply: (Hom_mono U). Qed.
Coercion sieve_to_subset : sieve >-> subset.
Instance sieve_to_subset_mono `{Proset X} : Monotone (sieve_to_subset (X:=X)).
Proof. firstorder. Qed.
Program Definition sieveify `{Proset X} (U : subset X) : sieve X
  := fun x : X => exists y : X, U y /\ x ⊢ y.
Next Obligation.
  move=> * ? ? D [y [? D']].
  exists y. by split; last etransitivity.
Qed.
Arguments sieveify {_ _ _} U.
Instance: Params (@sieveify) 3 := {}.
Instance sieveify_mono `{Proset X} : Monotone (sieveify (X:=X)).
Proof.
  move=> U V D u /= [v [? D']].
  eexists. split; last by etransitivity.
    by apply: D.
Qed.
Instance sieveify_reflection `{Proset X} : sieveify (X:=X) ⊣ sieve_to_subset.
Proof.
  constructor=> U v /=.
  - by (exists v).
  - move=> [u [? D]]. by apply: sieve_map.
Qed.
Program Definition princ `{Proset X} (x : X) : sieve X
  := fun y : X => y ⊢ x.
Next Obligation. firstorder. Qed.
Arguments princ {_ _ _} x.
Instance: Params (@princ) 3 := {}.
Definition saturated `{Prosite X} (U : sieve X) : Prop
  := forall (u : X) (V : subset X), covers u V -> (forall v, V v -> U v) -> U u.
Definition locale_of (X : Type) `{Prosite X} : Type
  := sig (saturated (X:=X)).
Instance saturated_infclosed `{Prosite X} : InfClosedAll (saturated (X:=X)).
Proof. move=> R; apply: inf_closed_of_shape; rewrite /saturated /=; firstorder. Qed.
Instance locale_of_inflattice `{Prosite X} : InfLattice (locale_of X)
  := fun _ _ => sig_inf.
Instance locale_of_suplattice `{Prosite X} : SupLattice (locale_of X)
  := infs_sufficient.
Definition saturate `{Prosite X} : sieve X -> locale_of X
  := universal_left_adjoint sval.
Arguments saturate {_ _ _ _} U /.
Instance: Params (@saturate) 4 := {}.
Instance saturate_mono `{Prosite X} : Monotone (saturate (X:=X)).
Proof. unfold saturate; typeclasses eauto. Qed.
Instance saturate_reflection `{Prosite X} : saturate (X:=X) ⊣ sval
  := universal_adjunction1.
Lemma sat_exp_ideal `{Prosite X} (U V : sieve X)
  : saturated V -> saturated (U ⟿ V).
Proof.
  move=> Sat u W Cov Sub [u' /op_def D] /= In_U.
  apply: Sat; first by apply: (shrink_cov_spec1 D Cov).
  move=> v' In_ShW.
  move: (shrink_cov_spec2 D Cov _ In_ShW) => [v [D' In_W]].
  apply: (Sub _ In_W (v' ↾ D')); simpl.
    by apply: (sieve_map (cov_le (X:=X) (shrink_cov_spec1 D Cov) In_ShW)).
Qed.
Definition sat_exp `{Prosite X} (U : sieve X) (V : locale_of X) : locale_of X
  := (U ⟿ ` V) ↾ sat_exp_ideal _ _ (proj2_sig V).
Arguments sat_exp {_ _ _ _} U V /.
Instance: Params (@sat_exp) 4 := {}.
Lemma sat_exp_inv `{Prosite X} (U : sieve X) (V : locale_of X)
  : U ⟿ ` V ⟛ ` (sat_exp U V).
Proof. done. Qed.
Program Instance locale_of_exponents `{Prosite X} : Exponents (locale_of X)
  := {| exponential U V := sat_exp (` U) V |}.
Next Obligation.
  move=> ? ? ? ? U V W.
  rewrite -[L in L <-> _](embed sval) -[R in _ <-> R](embed sval) -meet_exponential.
  split; rewrite distrib_meet //.
Qed.
(*
Lemma F_exp `{Exponents X, Exponents Y} (F : X -> Y) `{!Monotone F}
  : (forall A B, F (A ⟿ B) ⊢ F A ⟿ F B) -> forall A B, F A ⩕ F B ⊢ F (A ⩕ B).
Proof.
  move=> Distr A B.
  rewrite meet_exponential -Distr.
  apply: mono; by apply/meet_exponential.
Qed.
Proof. rewrite -meet_exponential -distrib_meet modus_ponens //. Qed. *)
Lemma saturate_meet `{Prosite X} (U V : sieve X)
  : saturate (U ⩕ V) ⟛ saturate U ⩕ saturate V.
Proof.
  split; first by apply: F_meet.
  apply/meet_exponential/transpose/meet_exponential.
  apply/l_meet_exponential; rewrite sat_exp_inv; apply: (mono sval).
  apply/transpose/l_meet_exponential/(adj_unit saturate_reflection).
Qed.
Instance saturate_lex `{Prosite X} : Lex (saturate (X:=X)).
Proof.
  apply: lex_alt' => [| U V].
  - move=> u /= _ [[[? ?] ?] /= /(_ u)]; by apply.
  - apply/meet_exponential/transpose/meet_exponential.
    apply/l_meet_exponential; rewrite sat_exp_inv; apply: (mono sval).
    apply/transpose/l_meet_exponential/(adj_unit saturate_reflection).
Qed.


Open Scope Q.
Instance Q_le : Le Q := Qle.
Instance Q_proset : Proset Q := Build_PreOrder _ Qle_refl Qle_trans.
Notation "(<)" := Qlt (only parsing) : Q_scope.
Definition Q_le_def q q' : q ⊢ q' = Qle q q' := erefl.
(* Definition Qc_strict : Qc -> Qc -> Prop := strict pro_le.
Notation "q < q'" := (strict (pro_le (X:=Qc)) q q').
Notation "(<)" := (strict (pro_le (X:=Qc))) (only parsing).
Lemma Qclt_alt' q q' : (q < q')%Qc <-> q < q'.
Proof.
  rewrite strict_spec_alt Qclt_alt [_ ⊢ _]Qcle_alt Qceq_alt.
  case: (q ?= q')%Qc; dintuition.
Qed.
*)
(*
Lemma Qcle_alt' q q' : q ⊢ q' <-> (q < q')%Qc \/ q = q'.
Proof.
  rewrite Qclt_alt [_ ⊢ _]Qcle_alt Qceq_alt.
  case: (q ?= q')%Qc; dintuition.
Qed.
Lemma Qclt_alt2 q q' : (q < q')%Qc <-> ~q' ⊢ q.
Proof.
  rewrite Qclt_alt'. split.
  - firstorder.
  - apply: total_not_strict.
Qed.
Lemma Qcle_alt2 q q' : q ⊢ q' <-> ~(q' < q)%Qc.
Proof. rewrite Qclt_alt2. firstorder. Qed.

Instance Qc_trichT : TrichotomyT (<).
Proof.
  move=> q q'. case E: (q ?= q')%Qc.
  - left. right. by apply/Qceq_alt.
  - left. left. by apply/Qclt_alt'/Qclt_alt.
  - right. by apply/Qclt_alt'/Qcgt_alt.
Defined.
*)
Instance Q_dec : RelDecision (pro_le (X:=Q)).
Proof.
  move=> q q'. unfold Decision.
  case E: (q ?= q') (Qle_alt q q'); dintuition.
Defined.
Instance Qlt_dec : RelDecision Qlt.
Proof.
  move=> q q'. unfold Decision.
  case E: (q ?= q') (Qlt_alt q q'); dintuition.
Defined.
Instance Qlt_di : Dimonotone (<)%Q.
Proof. compute -[Qle Qlt] => *. lra. Qed.
Instance Qlt_transitive : Transitive Qlt := Qlt_trans.
Definition Q_total (q q' : Q) : {q ⊢ q'} + {q' ⊢ q}.
  case: (Qlt_le_dec q q'); dintuition.
Defined.
  
Program Instance Q_binmeets : BinMeets Q
  := fun J => {| inf := if Q_total (J true) (J false) then J true else J false |}.
Next Obligation. move=> J; case: Q_total => Le /=; split=> [[] | ?] //. Qed.
Program Instance Q_binjoins : BinJoins Q
  := fun J => {| sup := if Q_total (J true) (J false) then J false else J true |}.
Next Obligation. move=> J; case: Q_total => Le /=; split=> [[] | ?] //. Qed.

Definition Q_ball : Type := {p : op Q * Q | p.1 < p.2}.
Notation lo_end B := (`B).1.
Notation hi_end B := (`B).2.
Lemma lo_lt_hi (B : Q_ball) : lo_end B < hi_end B.
Proof. case: B => //. Qed.
Hint Resolve lo_lt_hi.
Program Definition in_ball (B : Q_ball) : subset Q
  := fun q => lo_end B < q /\ q < hi_end B.
Next Obligation. compute -[Qle Qlt] => *. lra. Qed.
Arguments in_ball !B /.
Definition width (B : Q_ball) : Q := hi_end B - lo_end B.
Arguments width !B /.
Definition radius (B : Q_ball) : Q := width B / 2.
Arguments radius !B /.
Definition center (B : Q_ball) : Q := lo_end B + radius B.
Arguments center !B /.
Lemma width_pos B : 0 < width B.
Proof. case: B => [[B_l B_h]] /= L. lra. Qed.
Lemma radius_pos B : 0 < radius B.
Proof. apply: Qlt_shift_div_l; [lra | apply: width_pos]. Qed.
Lemma radius_lt_width B : radius B < width B.
Proof. move: (width_pos B) => ?. apply: Qlt_shift_div_r; lra. Qed.
Lemma center_in (B : Q_ball) : in_ball B (center B).
Proof.
  move: (radius_pos B) (radius_lt_width B).
  case: B => [[B_l B_h]] /= L.
  lra.
Qed.
Lemma Q_endless_down q : (q - 1 < q)%Q.
Proof. lra. Qed.
Lemma Q_endless_up q : (q < q + 1)%Q.
Proof. lra. Qed.
Hint Resolve Q_endless_down Q_endless_up.
Instance in_ball_mono : Monotone in_ball.
Proof. compute -[Qle Qlt] => *. lra. Qed.
Instance in_ball_reflect : Reflecting in_ball.
Proof.
  move=> B1 B2 D. move: (center B1) (center_in B1) (D _ (center_in B1)) => c In1 In2.
  move: B1 B2 D In1 In2 => [[B_in_l B_in_h] /= L_in] [[B_out_l B_out_h] /= L_out]
    D [L_in_l L_in_h] [L_out_l L_out_h].
  split; apply: Qnot_lt_le => L.
  - case: (D B_out_l); lra.
  - case: (D B_out_h); lra.
Qed.

Definition Q_cov (B : Q_ball) (V : subset Q_ball) : Prop
  := in_ball B ⟛ Sup B' : {B' | V B'}, in_ball (`B').
  (* := forall q, in_ball B q <-> exists B', V B' /\ in_ball B' q. *)
Program Instance Q_coverage : Coverage Q_cov
  := {| shrink_cov u u' D V Cov
        := princ u' ⩕ sieveify V |}.
Next Obligation.
  move=> u V v [Cov1 Cov2] In_V.
  apply: (reflect in_ball). rewrite -Cov2.
  apply: (sup_ub (v ↾ In_V)).
Qed.
Next Obligation.
  move=> u u' D V. rewrite /Q_cov => Cov.
  transitivity (in_ball u' ⩕ in_ball u);
    last transitivity (in_ball u' ⩕ Sup B' : {B' | V B'}, in_ball (`B')).
  - split.
    + rewrite -D. by apply meet_right.
    + apply: meet_proj1.
  - by apply: ext.
  - split.
    + rewrite l_meet_exponential. apply: sup_left => -[v In_V]. cbn [sval].
      rewrite -l_meet_exponential => q [[L1 L2] [L3 L4]].
      set l := get_op (lo_end u') ⩖ get_op (lo_end v).
      set h := hi_end u' ⩕ hi_end v.
      have L_lq : l < q by rewrite /l /join /=; case: is_left.
      have L_qh : q < h by rewrite /h /meet /=; case: is_left.
      have L_lh : l < h by transitivity q.
      (unshelve eexists (((l, h) ↾ L_lh) ↾ _)) => //=.
      split.
      * split; [apply: join_inj1 | apply: meet_proj1].
      * eexists. split; first done.
        split; [apply: join_inj2 | apply: meet_proj2].
    + apply: sup_left => -[v [D' [v' [In_V D'']]]]. cbn [sval].
      apply meet_right.
      * apply (mono in_ball D').
      * rewrite D''. apply: (sup_ub (v' ↾ In_V)).
Qed.
Next Obligation.
  move=> u u' D V Cov u'' /= [D' [v [In_V D'']]]. eauto.
Qed.
Instance Q_ball_prosite : Prosite Q_ball := {| covers := Q_cov |}.

Definition continuum : Type := locale_of Q_ball.


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

(*
Program Definition inverse_image `{Proset X, Proset Y} (F : X -> Y) `{!Monotone F}
        (P : Presheaf X) : Presheaf Y
  := {| section_on U := P.(section_on) (F U);
        restrict U V H := P.(restrict) (mono F H) |}.
*)


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

Lemma filter_iff_lex `{MeetSemilattice X} (P : Hom X Prop)
  : is_filter P <-> Lex P.
Proof.
  set Has := @unbias_meets X.
  split.
  - move=> [? _] R ? ? J.
    apply: distrib_inf_sufficient.
    move=> H_b; pose J' b := J b ↾ H_b b.
    rewrite -(_ : ` (codirect J') ⊢ inf J) //.
    * apply: proj2_sig.
    * apply: inf_right => b; apply: (codirect_is_lb J').
  - move=> ?; (exists) => //.
    unshelve refine {| codirect R _ _ J := inf (sval ∘ J) ↾ _ |}; last first.
    + move=> *; apply: inf_lb.
    + rewrite (distrib_inf (sval ∘ J)) => r' /=; case: (J r') => //.
Qed.

Lemma improper_is_filter `{Codirected X} : is_filter (top (Hom X Prop)).
Proof.
  exists => //; unshelve refine {| codirect R _ _ J := codirect (sval ∘ J) ↾ _ |}.
  - done.
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
Next Obligation. done. Qed.
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
        restrict n m H s i := s (i + (n - m))%nat |}.
Next Obligation.
  move=> /= ? ? ? ? ?; apply/pw_core' => a; apply/pw_core' => i.
    by replace (i + _)%nat with i by lia.
Qed.
Next Obligation.
  move=> /= ? ? ? n m o H1 H2 H3; apply/pw_core' => a; apply/pw_core' => i /=.
  change (?n ⊢ ?m) with (m <= n)%nat in *.
    by replace (i + _ + _)%nat with (i + (n - o))%nat by lia.
Qed.
