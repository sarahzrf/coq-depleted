From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.list.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.adjunction.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Class Monoidal `{Proset X} (T : X -> X -> X) `{!Bimonotone T} (U : X) :=
  {lunit A : T U A ⟛ A;
   runit A : T A U ⟛ A;
   massoc A B C : T A (T B C) ⟛ T (T A B) C}.
Hint Mode Monoidal ! - - ! - - : typeclass_instances.
Class Sym `{Proset X} (T : X -> X -> X) :=
  twist A B : T A B ⊢ T B A.
Hint Mode Sym ! - - ! : typeclass_instances.
Definition sym `{Sym X T} (A B : X) : T A B ⟛ T B A :=
  conj (twist A B) (twist B A).

Class MonSet (X : Type) `{Proset X} :=
  {memp : X;
   pro_tens : X -> X -> X;
   pro_tens_bi :> Bimonotone pro_tens;
   pro_monoidal :> Monoidal pro_tens memp}. (* ugh, unfortunate name *)
Hint Mode MonSet ! - - : typeclass_instances.
Arguments pro_tens {_ _ _ _} !_ !_ /.
Instance: Params (@memp) 4 := {}.
Instance: Params (@pro_tens) 4 := {}.
Infix "⊗" := pro_tens (at level 30) : proset_scope.
Notation "(⊗)" := pro_tens (only parsing) : proset_scope.
Definition pro_lunit `{MonSet X} (A : X) : memp ⊗ A ⟛ A := lunit A.
Definition pro_runit `{MonSet X} (A : X) : A ⊗ memp ⟛ A := runit A.
Definition pro_massoc `{MonSet X} (A B C : X) : A ⊗ (B ⊗ C) ⟛ (A ⊗ B) ⊗ C
  := massoc A B C.
Class SymMonSet (X : Type) `{MonSet X} :=
  {pro_twist :> Sym (X:=X) (⊗)}.
Hint Mode SymMonSet ! - - - : typeclass_instances.
Definition pro_sym `{SymMonSet X} (A B : X) : A ⊗ B ⟛ B ⊗ A := sym A B.

Class LaxMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {pres_memp : memp ⊢ F memp; pres_tens A B : F A ⊗ F B ⊢ F (A ⊗ B)}.
Hint Mode LaxMon ! - - - ! - - - ! : typeclass_instances.
Class OplaxMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {pres_memp_op : F memp ⊢ memp; pres_tens_op A B : F (A ⊗ B) ⊢ F A ⊗ F B}.
Hint Mode OplaxMon ! - - - ! - - - ! : typeclass_instances.
(* This definition is OK, since we are in prosets---I think??? *)
Class StrongMon `{MonSet X, MonSet Y} (F : X -> Y) :=
  {strong_lax :> LaxMon F; strong_oplax :> OplaxMon F}.
Hint Mode StrongMon ! - - - ! - - - ! : typeclass_instances.

Lemma oplax_adjoint_lax `{MonSet X, MonSet Y} (F : X -> Y) (G : Y -> X)
      `{Adj : !F ⊣ G, !Monotone F, !Monotone G}
  : OplaxMon F <-> LaxMon G.
Proof.
  split=> ?; constructor=> [| A B]; apply/(transpose Adj).
  - apply: pres_memp_op.
  - rewrite pres_tens_op !adj_counit' //.
  - apply: pres_memp.
  - rewrite -pres_tens -!adj_unit' //.
Qed.
Corollary adjoint_equivalence_strong `{MonSet X, MonSet Y} (F : X -> Y) (G : Y -> X)
          `{!F ⊣ G, !G ⊣ F, !Monotone F, !Monotone G}
  : StrongMon F <-> StrongMon G.
Proof. split; constructor; apply/oplax_adjoint_lax. Qed.
(* The next one may only work because we are in prosets---I should go check. *)
Corollary triple_strong `{MonSet X, MonSet Y} (F : X -> Y) (G : Y -> X) (H' : X -> Y)
          `{!F ⊣ G, !G ⊣ H', !Monotone F, !Monotone G, !Monotone H'}
  : TCAnd (OplaxMon F) (LaxMon H') <-> StrongMon G.
Proof. split=> [[Oplax Lax] | Strong]; split; apply/oplax_adjoint_lax. Qed.


Instance cartesian_monoidal `{Proset X, !MeetSemilattice X}
  : Monoidal (X:=X) meet ⊤.
Proof.
  constructor.
  - move=> A; split.
    + apply: meet_proj2.
    + apply: meet_right; [apply: top_right | done].
  - move=> A; split.
    + apply: meet_proj1.
    + apply: meet_right; [done | apply: top_right].
  - split; repeat apply: meet_right.
    + apply: meet_proj1.
    + apply: meet_left2; apply: meet_proj1.
    + apply: meet_left2; apply: meet_proj2.
    + apply: meet_left1; apply: meet_proj1.
    + apply: meet_left1; apply: meet_proj2.
    + apply: meet_proj2.
Qed.
Instance cocartesian_monoidal `{Proset X, !JoinSemilattice X}
  : Monoidal (X:=X) join ⊥.
Proof.
  constructor.
  - move=> A; split.
    + apply: join_left; [apply: bot_left | done].
    + apply: join_inj2.
  - move=> A; split.
    + apply: join_left; [done | apply: bot_left].
    + apply: join_inj1.
  - split; repeat apply: join_left.
    + apply: join_right1; apply: join_inj1.
    + apply: join_right1; apply: join_inj2.
    + apply: join_inj2.
    + apply: join_inj1.
    + apply: join_right2; apply: join_inj1.
    + apply: join_right2; apply: join_inj2.
Qed.
Instance cartesian_sym `{Proset X, !BinMeets X} : Sym (X:=X) meet.
Proof. move=> A B; apply: (meet_right meet_proj2 meet_proj1). Qed.
Instance cocartesian_sym `{Proset X, !BinJoins X} : Sym (X:=X) join.
Proof. move=> A B; apply: (join_left join_inj2 join_inj1). Qed.

Instance id_strongmon `{MonSet X} : StrongMon (@id X).
Proof. firstorder. Qed.
Instance compose_laxmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Monotone F, !Monotone G, !LaxMon F, !LaxMon G}
  : LaxMon (F ∘ G).
Proof.
  constructor=> [| A B] /=.
  - rewrite -!pres_memp //.
  - rewrite -!pres_tens //.
Qed.
Instance compose_oplaxmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Monotone F, !Monotone G, !OplaxMon F, !OplaxMon G}
  : OplaxMon (F ∘ G).
Proof.
  constructor=> [| A B] /=.
  - rewrite !pres_memp_op //.
  - rewrite !pres_tens_op //.
Qed.
Instance compose_strongmon `{MonSet X, MonSet Y, MonSet Z'}
         {F : Y -> Z'} {G : X -> Y} `{!Monotone F, !Monotone G, !StrongMon F, !StrongMon G}
  : StrongMon (F ∘ G).
Proof. constructor; typeclasses eauto. Qed.

Definition op_tens {X} (T : X -> X -> X) (a1 a2 : op X) : op X :=
  Op (T (get_op a1) (get_op a2)).
Arguments op_tens {X} T a1 a2 /.
Instance: Params (@op_tens) 2 := {}.
Instance op_tens_bi `{Proset X} {T : X -> X -> X} `{!Bimonotone T}
  : Bimonotone (op_tens T).
Proof.
  move=> A A' /op_def D_A B B' /op_def D_B /=.
  apply/op_def; by apply: bi.
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
Instance: Params (@pw_tens) 3 := {}.
Instance pw_tens_bi {X} `{Proset Y} {T : Y -> Y -> Y} `{!Bimonotone T}
  : Bimonotone (pw_tens X T).
Proof. move=> ? ? ? ? ? ? ? /=; firstorder. Qed.
Instance pw_tens_monoidal {X} `{Monoidal Y T U} : Monoidal (pw_tens X T) (const U).
Proof. firstorder. Qed.
Instance pw_tens_sym {X} `{Sym Y T} : Sym (pw_tens X T).
Proof. firstorder. Qed.
Instance pw_mset {X} `{MonSet Y} : MonSet (X -> Y) := {| pro_tens := pw_tens X (⊗) |}.
Instance pw_smset {X} `{SymMonSet Y} : SymMonSet (X -> Y) := {}.
Instance const_strongmon {X} `{MonSet Y} : StrongMon (@const Y X).
Proof. constructor; by constructor. Qed.
Instance precomp_strongmon {X X'} `{MonSet Y} {f : X' -> X} :
  StrongMon (X:=X -> Y) (.∘ f).
Proof. constructor; by constructor. Qed.
Instance postcomp_laxmon {X} `{MonSet Y, MonSet Y'}
         {f : Y -> Y'} `{!Monotone f, !LaxMon f} : LaxMon (X:=X -> Y) (f ∘.).
Proof. firstorder. Qed.
Instance postcomp_oplaxmon {X} `{MonSet Y, MonSet Y'}
         {f : Y -> Y'} `{!Monotone f, !OplaxMon f} : OplaxMon (X:=X -> Y) (f ∘.).
Proof. firstorder. Qed.
Instance postcomp_strongmon {X} `{MonSet Y, MonSet Y'}
         {f : Y -> Y'} `{!Monotone f, !StrongMon f} : StrongMon (X:=X -> Y) (f ∘.).
Proof. firstorder. Qed.
Instance eval_at_strongmon {X} `{MonSet Y} {x : X} : StrongMon (X:=X -> Y) (eval_at x).
Proof. constructor; by constructor. Qed.

Instance inf_laxmon {R} `{MonSet X, !DInfsOfShape R X} : LaxMon (X:=R -> X) einf.
Proof.
  constructor=> [| A B].
  - apply: inf_right => A //.
  - apply: inf_right => r; apply: bi; apply: inf_lb.
Qed.
Instance sup_oplaxmon {R} `{MonSet X, !DSupsOfShape R X} : OplaxMon (X:=R -> X) esup.
Proof.
  constructor=> [| A B].
  - apply: sup_left => A //.
  - apply: sup_left => r; apply: pro_tens_bi; apply: sup_ub.
Qed.

Definition prod_tens {X Y} (T : X -> X -> X) (T' : Y -> Y -> Y) (p1 p2 : X * Y) : X * Y :=
  (T p1.1 p2.1, T' p1.2 p2.2).
Arguments prod_tens {X Y} T T' !p1 !p2 /.
Instance: Params (@prod_tens) 4 := {}.
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
Instance fst_strongmon `{MonSet X, MonSet Y} : StrongMon (@fst X Y).
Proof. by compute. Qed.
Instance snd_strongmon `{MonSet X, MonSet Y} : StrongMon (@snd X Y).
Proof. by compute. Qed.
Instance memp_pair_strongmon `{MonSet X, MonSet Y} : StrongMon (@pair X Y memp).
Proof.
  constructor; constructor=> [| B B']; rewrite /= /prod_relation //=;
    (split; [apply (pro_lunit memp) | done]).
Qed.
Instance pair_memp_strongmon `{MonSet X, MonSet Y} : StrongMon (flip (@pair X Y) memp).
Proof.
  constructor; constructor=> [| A A']; rewrite /= /prod_relation //=;
    (split; [done | apply (pro_lunit memp)]).
Qed.
Instance prod_map_laxmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Monotone F, !Monotone G, !LaxMon F, !LaxMon G}
  : LaxMon (prod_map F G).
Proof. firstorder. Qed.
Instance prod_map_oplaxmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Monotone F, !Monotone G, !OplaxMon F, !OplaxMon G}
  : OplaxMon (prod_map F G).
Proof. firstorder. Qed.
Instance prod_map_strongmon `{MonSet X, MonSet X', MonSet Y, MonSet Y'}
         {F : X -> X'} {G : Y -> Y'} `{!Monotone F, !Monotone G, !StrongMon F, !StrongMon G}
  : StrongMon (prod_map F G).
Proof. firstorder. Qed.

Instance and_monoidal : Monoidal and True.
Proof. firstorder. Qed.
Instance or_monoidal : Monoidal or False.
Proof. firstorder. Qed.
Instance and_sym : Sym and.
Proof. firstorder. Qed.
Instance or_sym : Sym or.
Proof. firstorder. Qed.
Instance prop_mset : MonSet Prop
  := {| pro_tens := and |}.
Instance prop_smset : SymMonSet Prop := {}.

Instance plus_monoidal : Monoidal plus 0.
Proof. constructor=> *; compute -[plus] in *; lia. Qed.
Instance plus_sym : Sym plus.
Proof. compute -[plus] => *; lia. Qed.
Instance nat_mset : MonSet nat := {| pro_tens := plus |}.
Instance nat_smset : SymMonSet nat := {}.

Instance andb_monoidal : Monoidal andb true.
Proof. constructor=> [| [] | []] //=. Qed.
Instance orb_monoidal : Monoidal orb false.
Proof. constructor=> [| [] | []] //=. Qed.
Instance andb_sym : Sym andb.
Proof. move=> [] [] //=. Qed.
Instance orb_sym : Sym orb.
Proof. move=> [] [] //=. Qed.
Instance bool_mset : MonSet bool
  := {| pro_tens := andb |}.
Instance bool_smset : SymMonSet bool := {}.

(* TODO Finish fixing up this section. *)
Instance app_bi `{Proset X} : Bimonotone (@app X).
Proof. move=> ? ? ? ? ? ?; by apply: Forall2_app. Qed.
Instance app_monoidal `{Proset X} : Monoidal (@app X) nil.
Proof.
  constructor.
  - done.
  - move=> As; rewrite app_nil_r //.
  - move=> As Bs Cs; rewrite app_assoc //.
Qed.
Instance list_mset `{Proset X} : MonSet (list X)
  := {| pro_tens := app |}.
Instance list_map_strongmon `{Proset X, Proset Y} {F : X -> Y}
  : StrongMon (fmap (M:=list) F).
Proof. constructor; constructor=> // As Bs; rewrite fmap_app //. Qed.
Definition tens_all `{MonSet X} : list X -> X
  := foldr pro_tens memp.
Instance: Params (@tens_all) 4 := {}.
Instance tens_all_mono `{MonSet X} : Monotone (tens_all (X:=X)).
Proof. move=> ? ?; elim=> //= A B As Bs D _ IH; rewrite D IH //. Qed.
Instance tens_all_strongmon `{MonSet X} : StrongMon (tens_all (X:=X)).
Proof.
  constructor; constructor=> //; elim=> /= [| A As IH] Bs.
  - rewrite {2}/pro_tens /= pro_lunit //.
  - rewrite -pro_massoc IH //.
  - rewrite {1}/pro_tens /=; apply pro_lunit.
  - rewrite -(proj1 (pro_massoc _ _ _)); by apply: bi; last apply/IH.
Qed.
Fixpoint tens_all' `{MonSet X} (l : list X) : X :=
  match l with
  | [] => memp
  | [A] => A
  | A :: As => A ⊗ tens_all' As
  end.
Instance: Params (@tens_all') 4 := {}.
Lemma tens_all'_alt `{MonSet X}
  : forall {l : list X}, tens_all' l ⟛ tens_all l.
Proof.
  elim=> //= A [| A' As] /= IH.
  - rewrite pro_runit //.
  - split; apply: bi; firstorder.
Qed.
Instance tens_all'_mono `{MonSet X} : Monotone (tens_all' (X:=X)).
Proof. move=> *; rewrite !tens_all'_alt; by apply: mono. Qed.
Instance tens_all'_strongmon `{MonSet X} : StrongMon (tens_all' (X:=X)).
Proof.
  constructor; constructor=> // *.
  - rewrite 2!(proj1 tens_all'_alt) -(proj2 tens_all'_alt); apply: pres_tens.
  - rewrite tens_all'_alt -2!(proj2 tens_all'_alt); apply: pres_tens_op.
Qed.
Definition list_flat {X} `{MonSet Y} (F : X -> Y) : list X -> Y
  := tens_all' ∘ fmap F.
Definition list_sharp {X Y} (F : list X -> Y) : X -> Y
  := F ∘ mret.
Fact list_flat_signature `{Proset X, MonSet Y} {F : list X -> Y} `{!Monotone F}
  : TCAnd (Monotone (list_flat F)) (StrongMon (list_flat F)).
Proof. unfold list_flat; typeclasses eauto. Qed.
Fact list_sharp_signature `{Proset X, MonSet Y} {F : list X -> Y}
     `{!Monotone F, !StrongMon F}
  : Monotone (list_sharp F).
Proof. unfold list_sharp; typeclasses eauto. Qed.
Lemma list_free_monoid1 `{Proset X, MonSet Y} {F : list X -> Y} `{!StrongMon F}
  : list_flat (list_sharp F) ⟛ F.
Proof.
  apply/pw_core' => As.
  rewrite /list_flat /= tens_all'_alt.
  elim: As => /= [| A As IH].
  - rewrite /list_flat /list_sharp /=; split.
    + apply: (pres_memp (F:=F)).
    + apply: (pres_memp_op (F:=F)).
  - rewrite /list_flat /list_sharp /= -/fmap.
    change (A :: As) with (mret A ⊗ As).
    split.
    + rewrite -pres_tens (proj1 IH) //.
    + rewrite pres_tens_op (proj2 IH) //.
Qed.
Lemma list_free_monoid2 : forall {X} `{MonSet Y} {F : X -> Y},
    list_sharp (list_flat F) ⟛ F.
Proof. split=> ? //=; apply pro_runit. Qed.


Class MonClosed `{MonSet X} (P : X -> Prop) :=
  {memp_closed : P memp;
   tensor_closed : forall {A B : X}, P A -> P B -> P (A ⊗ B)}.
Hint Mode MonClosed ! - - - ! : typeclass_instances.
Definition sig_tens `{MonSet X} (P : X -> Prop) `{!MonClosed P}
           (s1 s2 : sig P) : sig P
  := match s1, s2 with a1 ↾ H1, a2 ↾ H2 => (a1 ⊗ a2) ↾ tensor_closed H1 H2 end.
Arguments sig_tens {_ _ _ _} P {_} !_ !_ /.
Instance: Params (@sig_tens) 6 := {}.
Instance sig_tens_bi `{MonClosed X P} : Bimonotone (sig_tens P).
Proof. move=> [? ?] [? ?] /= ? [? ?] [? ?] /= ?; by apply: bi. Qed.
Instance sig_tens_monoidal `{MonSet X} {P : X -> Prop} `{!MonClosed P} :
  Monoidal (sig_tens P) (memp ↾ memp_closed).
Proof.
  constructor=> [[? ?] | [? ?] | [? ?] [? ?] [? ?]] /=; apply: (reflect_core sval); simpl.
  - apply: lunit.
  - apply: runit.
  - apply: massoc.
Qed.
Instance sig_sym `{SymMonSet X} {P : X -> Prop} `{!MonClosed P} :
  Sym (sig_tens P).
Proof. move=> [A H_A] [B H_B] /=; apply: twist. Qed.
Instance sig_mset `{MonSet X} {P : X -> Prop} `{!MonClosed P} :
  MonSet (sig P) := {| pro_tens := sig_tens P |}.
Instance sig_smset  `{SymMonSet X} {P : X -> Prop} `{!MonClosed P} :
  SymMonSet (sig P) := {}.
Instance sval_strongmon `{MonSet X} {P : X -> Prop} `{!MonClosed P}
  : StrongMon (proj1_sig (P:=P)).
Proof. constructor; constructor=> // -[A H_A] [B H_B] //. Qed.
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


Class Closed `{Proset X} (T : X -> X -> X) (H : X -> X -> X) :=
  tensor_hom A B C : T A B ⊢ C <-> A ⊢ H B C.
Hint Mode Closed ! - - ! - : typeclass_instances.
Hint Mode Closed ! - - - ! : typeclass_instances.
Class LClosed `{Proset X} (T : X -> X -> X) (H : X -> X -> X) :=
  l_tensor_hom A B C : T B A ⊢ C <-> A ⊢ H B C.
Hint Mode LClosed ! - - ! - : typeclass_instances.
Hint Mode LClosed ! - - - ! : typeclass_instances.
Class ClosedMonSet (X : Type) `{MonSet X} :=
  {internal_hom : X -> X -> X;
   pro_tensor_hom :> Closed (⊗) internal_hom}.
Hint Mode ClosedMonSet ! - - - : typeclass_instances.
Instance: Params (@internal_hom) 5 := {}.
Infix "⊸" := internal_hom (at level 40) : proset_scope.
Notation "(⊸)" := internal_hom (only parsing) : proset_scope.
Class LClosedMonSet (X : Type) `{MonSet X} :=
  {l_internal_hom : X -> X -> X;
   pro_l_tensor_hom :> LClosed (⊗) l_internal_hom}.
Hint Mode LClosedMonSet ! - - - : typeclass_instances.
Instance: Params (@l_internal_hom) 5 := {}.
Infix "⊸̂" := l_internal_hom (at level 40) : proset_scope.
Notation "(⊸̂)" := l_internal_hom (only parsing) : proset_scope.
Class Exponents (X : Type) `{Proset X, !BinMeets X} :=
  {exponential : X -> X -> X;
   meet_exponential :> Closed meet exponential}.
Hint Mode Exponents ! - - - : typeclass_instances.
Instance: Params (@exponential) 5 := {}.
Infix "⟿" := exponential (at level 40) : proset_scope.
Notation "(⟿)" := exponential (only parsing) : proset_scope.
Instance sym_lclosed `{Sym X T, !Closed T H'} : LClosed T H' | 3.
Proof. move=> A B C; rewrite -tensor_hom; split=> ?; by rewrite sym. Qed.
Instance sym_lcmset `{SymMonSet X, !ClosedMonSet X} : LClosedMonSet X | 3
  := {| l_internal_hom := internal_hom |}.
Definition l_meet_exponential `{Exponents X} : LClosed (X:=X) meet exponential
  := _.

Instance internal_hom_di `{ClosedMonSet X} : Dimonotone (internal_hom (X:=X)).
Proof.
  move=> A A' /= D1 B B' D2.
  rewrite -tensor_hom D1 -D2 tensor_hom //.
Qed.
Instance l_internal_hom_di `{LClosedMonSet X} : Dimonotone (l_internal_hom (X:=X)).
Proof.
  move=> A A' /= D1 B B' D2.
  rewrite -l_tensor_hom D1 -D2 l_tensor_hom //.
Qed.
Instance exponential_di `{Exponents X} : Dimonotone (exponential (X:=X)).
Proof.
  move=> A A' /= D1 B B' D2.
  rewrite -tensor_hom D1 -D2 tensor_hom //.
Qed.

Program Instance prop_cmset : ClosedMonSet Prop
  := {| internal_hom (P Q : Prop) := P -> Q |}.
Next Obligation. firstorder. Qed.
Program Instance prop_exponents : Exponents Prop
  := {| exponential (P Q : Prop) := P -> Q |}.
Next Obligation.
  (* TODO Factor this into a lemma somewhere. *)
  move=> P Q R; enough (P ∧ Q <-> P ⩕ Q) by firstorder; split.
  - move=> [? ?] [] //.
  - move=> C; by move: (C true) (C false).
Qed.

Lemma mon_modus_ponens `{ClosedMonSet X} {A B : X}
  : (A ⊸ B) ⊗ A ⊢ B.
Proof. by rewrite tensor_hom. Qed.
Lemma mon_modus_ponens' `{ClosedMonSet X, !SymMonSet X} {A B : X}
  : A ⊗ (A ⊸ B) ⊢ B.
Proof. by rewrite sym tensor_hom. Qed.
Lemma l_mon_modus_ponens `{LClosedMonSet X} {A B : X}
  : A ⊗ (A ⊸̂ B) ⊢ B.
Proof. by rewrite l_tensor_hom. Qed.
Lemma modus_ponens `{Exponents X} {A B : X}
  : (A ⟿ B) ⩕ A ⊢ B.
Proof. by rewrite meet_exponential. Qed.
Lemma l_modus_ponens `{Exponents X} {A B : X}
  : A ⩕ (A ⟿ B) ⊢ B.
Proof. rewrite (cartesian_sym A) meet_exponential //. Qed.
Lemma prop_loop `{Proset X, !SupLattice X, !MeetSemilattice X, !Exponents X}
      {P Q : X} {R : Prop}
  : (P ⊢ embed_prop R) -> (R -> P ⊢ Q) -> P ⊢ Q.
Proof.
  move=> D1 D2.
  rewrite (meet_right D1 (reflexivity _)).
  apply/meet_exponential; apply: embed_prop_left => ?.
  apply/meet_exponential; rewrite meet_proj2; by apply: D2.
Qed.

Program Instance pw_exponents {X} `{Exponents Y} : Exponents (X -> Y)
  := {| exponential F G A := F A ⟿ G A |}.
Next Obligation.
  move=>>; apply: forall_proper => A.
  rewrite -meet_exponential -/(eval_at A (_ ⩕ _)).
  split; rewrite distrib_meet //.
Qed.

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


Class HeytingAlgebra (X : Type) `{Lattice X, !Exponents X}.
Hint Mode HeytingAlgebra ! - - - - - - : typeclass_instances.
Instance heytingalgebra_def `{Lattice X, !Exponents X} : HeytingAlgebra X := {}.


Class Quantale (X : Type)
      `{Complete X, !MonSet X, !ClosedMonSet X, !LClosedMonSet X}.
Hint Mode Quantale ! - - - - - - - - : typeclass_instances.
Instance quantale_def
         `{Complete X, !MonSet X, !ClosedMonSet X, !LClosedMonSet X}
  : Quantale X := {}.

Instance prop_quantale : Quantale Prop := {}.

Definition Endo (X : Type) `{Proset X} := Hom X X.
Identity Coercion endo_to_hom : Endo >-> Hom.
Instance compose_monoidal `{Proset X} : Monoidal (X:=Endo X) Hom_compose Hom_id.
Proof. constructor; compute; firstorder. Qed.
Instance endo_mset `{Proset X} : MonSet (Endo X)
  := {| pro_tens := Hom_compose |}.
Program Instance endo_cmset `{Complete X} : ClosedMonSet (Endo X)
  := {| internal_hom p F := universal_ran p F |}.
Next Obligation.
  move=>>; apply: (transpose universal_ran_global_ran).
  move=> F G D A /=; apply: (mono einf) => ?; apply: D.
Qed.
(*
Program Instance endo_cmset `{Complete X} : ClosedMonSet (Endo X)
  := r_tensor_internal_hom_adjoint_sufficient (fun (p F : Endo X) => universal_ran p F) _.
Next Obligation. move=> *; apply: universal_ran_global_ran. Qed.
*)
