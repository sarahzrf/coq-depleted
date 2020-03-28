From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.

Require Import depleted.proset.
Require Import depleted.bounds.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


(* !!!
   IMPORTANT NOTE: Constraints for adjunctions should generally be placed BEFORE
   Monotone, etc constraints (as far as I can tell, so far) because resolving them
   can instantiate evars that would otherwise cause resolution of those other classes
   to fail! Hence, this ordering allows more powerful inference.
   !!! *)
Class Adjoint `{Proset X, Proset Y} (F : X -> Y) (G : Y -> X)
  : Prop := {adj_unit : id ⊢ G ∘ F; adj_counit : F ∘ G ⊢ id}.
(* TODO This is probably worth putting some more careful thought into! *)
Hint Mode Adjoint ! - - ! - - ! - : typeclass_instances.
Hint Mode Adjoint ! - - ! - - - ! : typeclass_instances.
Instance: Params (@Adjoint) 6 := {}.
Arguments adj_unit {_ _ _ _ _ _ _ _} Adj : rename.
Arguments adj_counit {_ _ _ _ _ _ _ _} Adj : rename.
Infix "⊣" := Adjoint (no associativity, at level 70) : proset_scope.
Definition adj_unit' `(Adj : Adjoint X Y F G) {A B} (D : A ⊢ B) : A ⊢ G (F B)
  := transitivity D (adj_unit Adj _).
Definition adj_counit' `(Adj : Adjoint X Y F G) {A B} (D : A ⊢ B) : F (G A) ⊢ B
  := transitivity (adj_counit Adj _) D.
Lemma transpose `(Adj : Adjoint X Y F G) `{!Monotone F, !Monotone G} (A : X) (B : Y)
  : F A ⊢ B <-> A ⊢ G B.
Proof.
  split=> D.
  - rewrite -D; by apply adj_unit'.
  - rewrite D; by apply adj_counit'.
Qed.
Lemma transpose_sufficient `{Proset X, Proset Y, !Monotone F, !Monotone G}
  : (forall (A : X) (B : Y), F A ⊢ B <-> A ⊢ G B) -> F ⊣ G.
Proof. move=> Transpose; constructor=> A /=; by apply/Transpose. Qed.
Instance adjoint_proper `{Proset X, Proset Y}
  : Proper ((⥊) ==> (⥊) ==> iff) (Adjoint (X:=X) (Y:=Y)).
Proof.
  apply: proper_sym_impl_iff_2.
  {firstorder. }
  {firstorder. }
  move=> F F' E_F G G' E_G Adj; constructor=> A /=.
  - rewrite -(proj1 (E_G _ _ (E_F _ _ _))) //; apply: (adj_unit Adj).
  - rewrite (proj2 (E_F _ _ (E_G _ _ _))) //; apply: (adj_counit Adj).
Qed.

Class OrderEquiv `{Proset X, Proset Y} (F : X -> Y) (G : Y -> X)
      `{!F ⊣ G, !G ⊣ F, !Monotone F, !Monotone G}.
Hint Mode OrderEquiv ! - - ! - - ! - - - - - : typeclass_instances.
Hint Mode OrderEquiv ! - - ! - - - ! - - - - : typeclass_instances.
Instance order_equiv_reflecting1 `{OrderEquiv X Y F G} : Reflecting F.
Proof. move=> A B /transpose D; apply: (transitivity D); apply: (adj_counit (F:=G)). Qed.
Instance order_equiv_reflecting2 `{OrderEquiv X Y F G} : Reflecting G.
Proof. move=> A B /transpose D; apply: (transitivity D); apply: (adj_counit (F:=F)). Qed.

Lemma reflecting_left_adjoint `(Adj : Adjoint X Y F G) `{!Reflecting F} : G ∘ F ⟛ id.
Proof.
  split=> A /=.
  - by apply (reflect F), adj_counit'.
  - by apply adj_unit'.
Qed.
Lemma reflecting_right_adjoint `(Adjoint X Y F G) `{!Reflecting G} : F ∘ G ⟛ id.
Proof.
  split=> A /=.
  - by apply adj_counit'.
  - by apply (reflect G), adj_unit'.
Qed.

Instance left_adjoint_cocontinuous `{Proset X, Proset Y} {F : X -> Y} {G : Y -> X}
         `{Adj : F ⊣ G, !Monotone F, !Monotone G}
  : Cocontinuous F | 2.
Proof.
  move=> R J A [UB Uni]; split=> [r | A' UB'] /=; first by apply: mono.
  apply/transpose/Uni => r; apply/(transpose Adj)/UB'.
Qed.
Instance right_adjoint_continuous `{Proset X, Proset Y} {F : X -> Y} {G : Y -> X}
         `{Adj : F ⊣ G, !Monotone F, !Monotone G}
  : Continuous G | 2.
Proof.
  move=> R J A [LB Uni]; split=> [r | A' LB'] /=; first by apply: mono.
  apply/(transpose (F:=F))/Uni => r; apply/transpose/LB'.
Qed.

Lemma reflecting_left_adjoint_glb
      `{Adj : Adjoint Y X F G, !Monotone F, !Monotone G, !Reflecting F}
      {R} {J : R -> Y} {A}
  : glb (F ∘ J) A -> glb J (G A).
Proof.
  move=> Glb.
  enough (G ∘ F ∘ J ⟛ J) as E by (rewrite -E; apply: preserve_inf Glb).
  apply/pw_core' => r /=; apply/(pw_core (reflecting_left_adjoint Adj)).
Qed.
Lemma reflecting_right_adjoint_lub
      `{Adj : Adjoint Y X F G, !Monotone F, !Monotone G, !Reflecting G}
      {R} {J : R -> X} {A}
  : lub (G ∘ J) A -> lub J (F A).
Proof.
  move=> Lub.
  enough (F ∘ G ∘ J ⟛ J) as E by (rewrite -E; apply: preserve_sup Lub).
  apply/pw_core' => r /=; apply/(pw_core (reflecting_right_adjoint Adj)).
Qed.
(* TODO be more fine-grained? *)
Definition reflective_dsups {R}
           `{Adjoint X Y F G, !Monotone F, !Monotone G, !Reflecting G,
             !DSupsOfShape R X}
  : DSupsOfShape R Y
  := fun J => {| sup := F (sup (G ∘ J));
              is_sup := reflecting_right_adjoint_lub (is_sup (G ∘ J)) |}.
(*
Definition reflective_inflattice
           `{Adjoint X Y F G, !Monotone F, !Montone G, !Reflecting G, !SupLattice X}
  : InfLattice Y
  := @sups_sufficient Y _ (reflective_suplattice (F:=F) (G:=G)).
*)
Definition coreflective_dinfs {R}
           `{Adjoint Y X F G, !Monotone F, !Monotone G, !Reflecting F,
             !DInfsOfShape R X}
  : DInfsOfShape R Y
  := fun J => {| inf := G (inf (F ∘ J));
              is_inf := reflecting_left_adjoint_glb (is_inf (F ∘ J)) |}.

(* TOO Comma prosets? *)
Definition universal_left_adjoint `{Proset X, Proset Y, !InfLattice Y}
           (G : Y -> X) (A : X) : Y
  := Inf B : {B0 | A ⊢ G B0}, `B.
Definition universal_right_adjoint `{Proset X, Proset Y, !SupLattice X}
           (F : X -> Y) (B : Y) : X
  := Sup A : {A0 | F A0 ⊢ B}, `A.
Arguments universal_left_adjoint {_ _ _ _ _ _ _} G A /.
Arguments universal_right_adjoint {_ _ _ _ _ _ _} F B /.
Instance: Params (@universal_left_adjoint) 7 := {}.
Instance: Params (@universal_right_adjoint) 7 := {}.
Instance ula_proper `{Proset X, Proset Y, !InfLattice Y}
  : Proper ((⊢) --> (⇀)) (universal_left_adjoint (X:=X) (Y:=Y)).
Proof.
  move=> F G D A B D' /=.
  apply: inf_right => -[B0 D''] /=; apply: (inf_lb (B0 ↾ _)).
  rewrite D' D'' //.
Qed.
Instance ura_proper `{Proset X, Proset Y, !SupLattice X}
  : Proper ((⊢) --> (⇀)) (universal_right_adjoint (X:=X) (Y:=Y)).
Proof.
  move=> F G D A B D' /=.
  apply: sup_left => -[A0 D''] /=; apply: (sup_ub (A0 ↾ _)).
  rewrite -D' -D'' //.
Qed.
(* These are not instances because we don't want them to conflict with other ones when we
   give more useful/explicit definitions. But they should be suitable for using to make
   instances very quickly! *)
Lemma universal_adjunction1 `{Proset X, Proset Y, !InfLattice Y}
      {G : Y -> X} `{!Monotone G, !Continuous G}
  : universal_left_adjoint G ⊣ G.
Proof.
  constructor=> [A | B] /=.
  - case: (proj1 (preserves_inf_alt2 (F:=G) (J:=fun B : {B0 | A ⊢ G B0} => `B))) => LB Uni.
    apply/Uni => -[B0 ?] //.
  - by apply: (inf_lb (B ↾ _)).
Qed.
Lemma universal_adjunction2 `{Proset X, Proset Y, !SupLattice X}
      {F : X -> Y} `{!Monotone F, !Cocontinuous F}
  : F ⊣ universal_right_adjoint F.
Proof.
  constructor=> [A | B] /=.
  - by apply: (sup_ub (A ↾ _)).
  - case: (proj1 (preserves_sup_alt2 (F:=F) (J:=fun A : {A0 | F A0 ⊢ B} => `A))) => UB Uni.
    apply/Uni => -[B0 ?] //.
Qed.

Instance id_id_adjoint `{Proset X} : (@id X) ⊣ id.
Proof. done. Qed.
Instance id_id_equiv `{Proset X} : OrderEquiv (@id X) id := {}.
Instance compose_adjoint `{Proset X, Proset Y, Proset Z'}
         {F : Y -> Z'} {G : Z' -> Y} {F' : X -> Y} {G' : Y -> X}
         `{!F ⊣ G, !F' ⊣ G', !Monotone F, !Monotone G, !Monotone F', !Monotone G'}
  : F ∘ F' ⊣ G' ∘ G.
Proof. apply/transpose_sufficient => * /=; rewrite 2!transpose //. Qed.
Instance compose_equiv `{Proset X, Proset Y, Proset Z'}
         {F : Y -> Z'} {G : Z' -> Y} {F' : X -> Y} {G' : Y -> X}
         `{!F ⊣ G, !G ⊣ F, !F' ⊣ G', !G' ⊣ F',
           !Monotone F, !Monotone G, !Monotone F', !Monotone G',
           !OrderEquiv F G, !OrderEquiv G F}
  : OrderEquiv (F ∘ F') (G' ∘ G) := {}.
Instance pair0_snd_adjoint `{Proset X, Proset Y, !Bot X}
  : pair ⊥ ⊣ (@snd X Y).
Proof. constructor=> [B | [A B]] //=; by split; first apply: bot_left. Qed.
Instance snd_pair1_adjoint `{Proset X, Proset Y, !Top X}
  : (@snd X Y) ⊣ pair ⊤.
Proof. constructor=> [[A B] | B] //=; by split; first apply: top_right. Qed.
Instance flip_pair0_fst_adjoint `{Proset X, Proset Y, !Bot Y}
  : flip pair ⊥ ⊣ (@fst X Y).
Proof. constructor=> [B | [A B]] //=; by split; last apply: bot_left. Qed.
Instance fst_flip_pair1_adjoint `{Proset X, Proset Y, !Top Y}
  : (@fst X Y) ⊣ flip pair ⊤.
Proof. constructor=> [[A B] | B] //=; by split; last apply: top_right. Qed.
Instance const_einf_adjoint {R} `{Proset X, !DInfsOfShape R X} : @const X R ⊣ einf.
Proof. apply/transpose_sufficient => A B; rewrite -inf_universal //. Qed.
Instance esup_const_adjoint {R} `{Proset X, !DSupsOfShape R X} : esup ⊣ @const X R.
Proof. apply/transpose_sufficient => A B; rewrite -sup_universal //. Qed.

Lemma left_adjoint_unique `{Proset X, Proset Y} {F F' : X -> Y} {G : Y -> X}
      `{!F ⊣ G, !Monotone F, !Monotone F', !Monotone G}
  : F' ⊣ G -> F' ⟛ F.
Proof.
  move=> Adj2.
  enough (Hy : forall (F F' : X -> Y) `{!Monotone F, !Monotone F'}, F ⊣ G -> F' ⊣ G -> F ⊢ F')
    by by split; apply Hy.
  move=> F_ F'_ ? ? Adj1_ Adj2_ A.
  apply/(transpose Adj1_)/(adj_unit Adj2_).
Qed.
Lemma right_adjoint_unique `{Proset X, Proset Y} {F : X -> Y} {G G' : Y -> X}
      `{!F ⊣ G, !Monotone F, !Monotone G, !Monotone G'}
  : F ⊣ G' -> G' ⟛ G.
Proof.
  move=> Adj2.
  enough (Hy : forall (G G' : Y -> X) `{!Monotone G, !Monotone G'}, F ⊣ G -> F ⊣ G' -> G ⊢ G')
    by by split; apply Hy.
  move=> F_ F'_ ? ? Adj1_ Adj2_ A.
  apply/(transpose Adj2_)/(adj_counit Adj1_).
Qed.

(*
Record Adjunction {X Y : Type} `{Proset X, Proset Y} : Type :=
  {LeftAdjoint : X -> Y; RightAdjoint : Y -> X;
   LAdj_Monotone : Monotone LeftAdjoint; RAdj_Monotone : Monotone RightAdjoint;
   Adjunction_adjoint : LeftAdjoint ⊣ RightAdjoint}.
Arguments Adjunction _ _ {_ _}.
Existing Instances LAdj_Monotone RAdj_Monotone Adjunction_adjoint | 10.
Definition adj_compose {Z} `{Proset X, Proset Y, Proset Z}
        (Adj1 : Adjunction Y Z) (Adj2 : Adjunction X Y) : Adjunction X Z
  := {| LeftAdjoint := LeftAdjoint Adj1 ∘ LeftAdjoint Adj2;
        RightAdjoint := RightAdjoint Adj2 ∘ RightAdjoint Adj1 |}.
*)


Definition local_lan `{Proset X, Proset X', Proset Y}
           (p : X -> X') (F : X -> Y) (F' : X' -> Y) : Prop
  := forall (G : X' -> Y), Monotone G -> F' ⊢ G <-> F ⊢ G ∘ p.
Definition local_ran `{Proset X, Proset X', Proset Y}
           (p : X -> X') (F : X -> Y) (F' : X' -> Y) : Prop
  := forall (G : X' -> Y), Monotone G -> G ⊢ F' <-> G ∘ p ⊢ F.
Definition global_lan `{Proset X, Proset X', Proset Y}
           (p : X -> X') `{!Monotone p} (lan_p : Hom X Y -> Hom X' Y) : Prop
  := lan_p ⊣ (.○ in_Hom p).
Definition global_ran `{Proset X, Proset X', Proset Y}
           (p : X -> X') `{!Monotone p} (ran_p : Hom X Y -> Hom X' Y) : Prop
  := (.○ in_Hom p) ⊣ ran_p.
Instance: Params (@local_lan) 9 := {}.
Instance: Params (@local_ran) 9 := {}.
Instance: Params (@global_lan) 9 := {}.
Instance: Params (@global_ran) 9 := {}.
Lemma local_global_lan `{Proset X, Proset X', Proset Y}
      {p : X -> X'} {lan_p : Hom X Y -> Hom X' Y} `{!Monotone p, !Monotone lan_p}
  : global_lan p lan_p <-> forall F : Hom X Y, local_lan p F (lan_p F).
Proof.
  split.
  - move=> Glob F G ?.
    change (ap_Hom (lan_p F) ⊢ _) with (lan_p F ⊢ in_Hom G).
    rewrite (transpose Glob) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (lan_p F ⊢ G) with (ap_Hom (lan_p F) ⊢ ap_Hom G).
    rewrite Loc //=.
Qed.
Lemma local_global_ran `{Proset X, Proset X', Proset Y}
      {p : X -> X'} {ran_p : Hom X Y -> Hom X' Y} `{!Monotone p, !Monotone ran_p}
  : global_ran p ran_p <-> forall F : Hom X Y, local_ran p F (ran_p F).
Proof.
  split.
  - move=> Glob F G ?.
    change (_ ⊢ ap_Hom (ran_p F)) with (in_Hom G ⊢ ran_p F).
    rewrite -(transpose Glob) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (F ⊢ ran_p G) with (ap_Hom F ⊢ ap_Hom (ran_p G)).
    rewrite Loc //=.
Qed.

Definition local_lift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) (F : X -> Y) (F' : X -> Y') : Prop
  := forall (G : X -> Y'), Monotone G -> F' ⊢ G <-> F ⊢ p ∘ G.
Definition local_rift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) (F : X -> Y) (F' : X -> Y') : Prop
  := forall (G : X -> Y'), Monotone G -> G ⊢ F' <-> p ∘ G ⊢ F.
Definition global_lift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) `{!Monotone p} (lift_p : Hom X Y -> Hom X Y') : Prop
  := lift_p ⊣ (in_Hom p ○.).
Definition global_rift `{Proset X, Proset Y, Proset Y'}
           (p : Y' -> Y) `{!Monotone p} (rift_p : Hom X Y -> Hom X Y') : Prop
  := (in_Hom p ○.) ⊣ rift_p.
Instance: Params (@local_lift) 9 := {}.
Instance: Params (@local_rift) 9 := {}.
Instance: Params (@global_lift) 9 := {}.
Instance: Params (@global_rift) 9 := {}.
Lemma local_global_lift `{Proset X, Proset Y, Proset Y'}
      {p : Y' -> Y} {lift_p : Hom X Y -> Hom X Y'} `{!Monotone p, !Monotone lift_p}
  : global_lift p lift_p <-> forall F : Hom X Y, local_lift p F (lift_p F).
Proof.
  split.
  - move=> Glob F G ?.
    change (ap_Hom (lift_p F) ⊢ _) with (lift_p F ⊢ in_Hom G).
    rewrite (transpose Glob) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (lift_p F ⊢ G) with (ap_Hom (lift_p F) ⊢ ap_Hom G).
    rewrite Loc //=.
Qed.
Lemma local_global_rift `{Proset X, Proset Y, Proset Y'}
      {p : Y' -> Y} {rift_p : Hom X Y -> Hom X Y'} `{!Monotone p, !Monotone rift_p}
  : global_rift p rift_p <-> forall F : Hom X Y, local_rift p F (rift_p F).
Proof.
  split.
  - move=> Glob F G ?.
    change (_ ⊢ ap_Hom (rift_p F)) with (in_Hom G ⊢ rift_p F).
    rewrite -(transpose Glob) //=.
  - move=> Loc; apply/transpose_sufficient => F G /=.
    change (F ⊢ rift_p G) with (ap_Hom F ⊢ ap_Hom (rift_p G)).
    rewrite Loc //=.
Qed.

Instance precomp_adjoint `{Proset X, Proset X', Proset Y}
         {p : Hom X X'} {p' : Hom X' X} `{!p ⊣ p'}
  : ((.○ p') : Hom X Y -> _) ⊣ (.○ p).
Proof.
  constructor=> f y /=.
  - apply: mono; apply: adj_unit.
  - apply: mono; apply: adj_counit.
Qed.
Instance postcomp_adjoint' `{Proset X, Proset Y', Proset Y}
         {p : Hom Y' Y} {p' : Hom Y Y'} `{!p ⊣ p'}
  : ((p ○.) : Hom X Y' -> _) ⊣ (p' ○.).
Proof.
  constructor=> f y /=.
  - apply: adj_unit.
  - apply: adj_counit.
Qed.

Program Definition universal_lan {X} `{Proset X', Proset Y, !SupLattice Y}
        (p : X -> X') (F : X -> Y) : Hom X' Y
  := fun x' => Sup y : {y0 | p y0 ⊢ x'}, F (`y).
Next Obligation.
  move=> X X' ? ? Y ? ? ? p F A B D.
  apply: sup_left => -[x D'] /=.
  apply: (sup_right (x ↾ _)); by etransitivity.
Qed.
Arguments universal_lan {_ _ _ _ _ _ _ _} p F /.
Instance: Params (@universal_lan) 8 := {}.
Program Definition universal_ran {X} `{Proset X', Proset Y, !InfLattice Y}
        (p : X -> X') (F : X -> Y) : Hom X' Y
  := fun x' => Inf y : {y0 | x' ⊢ p y0}, F (`y).
Next Obligation.
  move=> X X' ? ? Y ? ? ? p F A B D.
  apply: inf_right => -[x D'] /=.
  apply: (inf_left (x ↾ _)); by etransitivity.
Qed.
Arguments universal_ran {_ _ _ _ _ _ _ _} p F /.
Instance: Params (@universal_ran) 8 := {}.
Lemma universal_lan_global_lan `{Proset X, Proset X', Proset Y, !SupLattice Y}
      {p : X -> X'} `{!Monotone p}
  : global_lan (Y:=Y) p (universal_lan p).
Proof.
  constructor=> f x /=.
  - by apply: (sup_ub (x ↾ _)).
  - apply: sup_left => -[? D] /=; rewrite D //.
Qed.
Lemma universal_ran_global_ran `{Proset X, Proset X', Proset Y, !InfLattice Y}
      {p : X -> X'} `{!Monotone p}
  : global_ran (Y:=Y) p (universal_ran p).
Proof.
  constructor=> f x /=.
  - apply: inf_right => -[? D] /=; rewrite D //.
  - by apply: (inf_lb (x ↾ _)).
Qed.
