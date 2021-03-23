From Coq Require Import ssreflect ssrfun ssrbool.
Require Import stdpp.tactics.
Require Import stdpp.finite.

Require Import depleted.proset.
Require Import depleted.bounds.
Require Import depleted.adjunction.
Require Import depleted.monoidal.
Local Open Scope proset_scope.
Local Open Scope proset_util_scope.


Notation LeDecision X := (RelDecision (pro_le (X:=X))).
Instance bool_ledec : LeDecision bool.
Proof. intros [] []; compute; auto. Defined.
Instance core_decision `{Proset X, !LeDecision X} : @RelDecision X X (⟛).
Proof.
  compute; intros A B.
  case (decide (A ⊢ B)); case (decide (B ⊢ A)); intuition.
Defined.

Definition DProp : Type := sigT Decision.
Coercion dprop := tag : DProp -> Prop.
Arguments dprop !_ /.
Instance dprop_decision {P : DProp} : Decision P := tagged P.
Definition in_DProp (P : Prop) `{H : !Decision P} : DProp := existT P H.
Instance dprop_le : Le DProp :=
  fun s1 s2 => dprop s1 ⊢ dprop s2.
Arguments dprop_le !_ !_ /.
(*
Instance: Params (@dprop_le) 6 := {}.
*)
Instance dprop_proset : @Proset DProp dprop_le.
Proof. firstorder. Qed.
Instance dprop_ledec : LeDecision DProp.
Proof. compute; intros (P, [? | ?]) (Q, [? | ?]); intuition. Defined.
Definition dprop_tens (s1 s2 : DProp) : DProp
  := in_DProp (dprop s1 ⊗ dprop s2).
Arguments dprop_tens !_ !_ /.
Instance dprop_tens_bi : Bimonotone dprop_tens.
Proof. compute; firstorder. Qed.
Instance dprop_tens_monoidal :
  Monoidal dprop_tens (in_DProp memp).
Proof. compute; firstorder. Qed.
Instance dprop_sym : Sym dprop_tens.
Proof. compute; firstorder. Qed.
Instance dprop_mset : MonSet DProp := {| pro_tens := dprop_tens |}.
Instance dprop_smset : SymMonSet DProp := {}.
Instance dprop_proper : Proper ((⟛) ==> iff) dprop.
Proof. firstorder. Qed.
Instance dprop_mono : Monotone dprop.
Proof. firstorder. Qed.
Instance dprop_reflecting : Reflecting dprop.
Proof. firstorder. Qed.
Instance dprop_strongmon : StrongMon dprop.
Proof. compute; firstorder. Qed.
Instance dprop_continuous : Continuous dprop.
Proof.
  move=> R J [P Dec] [LB Uni] /=; split=> [r | Q LB'] /=.
  - apply: LB.
  - move=> H_Q; by apply: (Uni (@in_DProp Q (left H_Q))).
Qed.

Program Instance dprop_reflect_inf {R} (J : R -> DProp) (Dec : Decision (forall r, J r))
  : HasInf J
  := {| inf := in_DProp (forall r, J r) |}.
Next Obligation. move=> *; by apply: (reflecting_undistrib_inf (F:=dprop)). Qed.
Program Instance dprop_reflect_sup {R} (J : R -> DProp) (Dec : Decision (exists r, J r))
  : HasSup J
  := {| sup := in_DProp (exists r, J r) |}.
Next Obligation. move=> *; by apply: (reflecting_undistrib_sup (F:=dprop)). Qed.

Program Instance dprop_top : Top DProp := mk_top (in_DProp ⊤) _.
Next Obligation. done. Qed.
Program Instance dprop_bot : Bot DProp := mk_bot (in_DProp ⊥) _.
Next Obligation. move=> ? []. Qed.
Program Instance dprop_binmeets : BinMeets DProp
  := mk_binmeets (fun P Q : DProp => in_DProp (P /\ Q)) _.
Next Obligation. move=> [? ?] [? ?] [? ?] /=. firstorder. Qed.
Program Instance dprop_binjoins : BinJoins DProp
  := mk_binjoins (fun P Q : DProp => in_DProp (P \/ Q)) _.
Next Obligation. move=> [? ?] [? ?] [? ?] /=. firstorder. Qed.

Program Instance dprop_exponents : Exponents DProp
  := {| exponential (P Q : DProp) := in_DProp (P -> Q) |}.
Next Obligation.
  move=> P Q R. rewrite -!(embed dprop).
  split; rewrite (distrib_meet (F:=dprop)) meet_exponential //.
Qed.
Instance dprop_boolean_alg : BooleanAlgebra DProp.
Proof. move=> []. compute. firstorder. Qed.

Lemma prop_negh (P : Prop) : ¬ₕP ⟛ ~P.
Proof. done. Qed.
Lemma prop_negh' (P : Prop) : ¬ₕP <-> ~P.
Proof. done. Qed.
Lemma dprop_negh (P : DProp) : ¬ₕP ⟛ in_DProp (~P).
Proof. firstorder. Qed.
Lemma dprop_negh' (P : DProp) : ¬ₕP <-> ~P.
Proof. apply: dprop_negh. Qed.

(* TODO "Algebras of the double negation monad" for an arbitrary Heyting algebra. *)
Class Regular (P : Prop) := dne : ~ ~ P -> P.
Hint Mode Regular ! : typeclass_instances.
Lemma dne' `{Regular P} : ~ ~ P <-> P.
Proof. firstorder. Qed.
Instance not_regular {P} : Regular (~P).
Proof. firstorder. Qed.
Instance dec_regular `{Decision P} : Regular P.
Proof. firstorder. Qed.
Instance forall_regular {R} {P : R -> Prop} `{!forall r, Regular (P r)} : Regular (forall r, P r).
Proof. firstorder. Qed.
Instance and_regular `{Regular P, Regular Q} : Regular (P /\ Q).
Proof. firstorder. Qed.
Instance impl_regular `{Regular P, Regular Q} : Regular (P -> Q).
Proof. firstorder. Qed.
Instance iff_regular `{Regular P, Regular Q} : Regular (P <-> Q).
Proof. firstorder. Qed.
Lemma regular_lem (P : Prop) `{Regular Q} : (Decision P -> Q) -> Q.
Proof. firstorder. Qed.
Lemma regular_lemT (P : Type) `{Regular Q} : (P + (P -> False) -> Q) -> Q.
Proof. firstorder. Qed.
Lemma regular_bind {P} `{Regular Q}
  : (P -> Q) -> ((P -> False) -> False) -> Q.
Proof. firstorder. Qed.

Definition RProp : Type := sig Regular.
Coercion rprop := sval : RProp -> Prop.
Arguments rprop !_ /.
Instance rprop_regular {P : RProp} : Regular (`P) := proj2_sig P.
Definition in_RProp (P : Prop) `{H : !Regular P} : RProp := P as_a RProp.
Instance regular_monclosed : MonClosed Regular.
Proof. firstorder. Qed.
Definition dn : Prop -> RProp := (not ∘ not) ↑.
Instance rprop_reflection : dn ⊣ rprop.
Proof. constructor; [firstorder | move=> [P ?] //=]. Qed.
Instance reg_closed {R} {J : R -> RProp} `{!HasInf (sval ∘ J)} : InfClosed J.
Proof. hnf. apply -> prop_unfold. apply inf_right => r. rewrite inf_lb dne' //. Qed.
Instance rprop_inflattice : InheritsDInfs Prop RProp
  := fun R _ J => sig_inf.
(*
Program Instance rprop_inflattice : InfLattice RProp
  := fun R J => {| inf := inf (rprop ∘ J) ↾ forall_regular |}.
Next Obligation. compute; firstorder. Qed.
*)
Instance rprop_suplattice : InheritsDSups Prop RProp
  := fun R _ J => reflective_dsup (F:=dn) J.

Definition d2r : DProp -> RProp := dprop ↑.

Program Instance rprop_exponents : Exponents RProp
  := {| exponential (P Q : RProp) := in_RProp (P -> Q) |}.
Next Obligation.
  move=> P Q R. rewrite -!(embed rprop).
  split; rewrite (distrib_meet (F:=rprop)) meet_exponential //.
Qed.
Lemma rprop_negh (P : RProp) : ¬ₕP ⟛ in_RProp (~P).
Proof. firstorder. Qed.
Lemma rprop_negh' (P : RProp) : ¬ₕP <-> ~P.
Proof. apply: rprop_negh. Qed.
Instance rprop_boolean_alg : BooleanAlgebra RProp.
Proof. move=> -[P]. compute. tauto. Qed.

Theorem rprop_monadic_completion `{Proset X} (i : X -> Prop) (L : Prop -> X)
        `{Adj : !L ⊣ i, !Monotone i, !Reflecting i, !Monotone L}
        (F : DProp -> X) `{!Monotone F} (E_F : i ∘ F ⟛ dprop)
  : let F' := L ∘ rprop in
    i ∘ F' ⟛ rprop /\ F ⟛ F' ∘ d2r /\
    forall (G : RProp -> X) `{!Monotone G}, i ∘ G ⟛ rprop /\ F ⟛ G ∘ d2r -> G ⟛ F'.
Proof.
  move=> F'.
  have E_F' : forall P, F P ⟛ F' (d2r P). {
    move=> P. apply: (reflect_core i).
    rewrite /F' /= -(pw_core E_F) /=
            [L _](pw_core (reflecting_right_adjoint Adj)) //.
  }
  split; last split=> [| G ? [E1 E2]]; apply/pw_core' => P //=.
  - split=> H_P; last by firstorder.
    apply: (regular_lem P) => Dec.
    rewrite -[_ P](pw_core E_F (in_DProp P)) /= E_F' //.
  - rewrite /F' /= -(pw_core E1) [L _](pw_core (reflecting_right_adjoint Adj)) //.
Qed.

Definition ran_dprop `{Proset X, !InfLattice X, !BinMeets X, !Bot X}
           (F : DProp -> X) (P : Prop) : X
  := (Inf _ : ~P, F ⊥) ⩕ F ⊤.
Lemma ran_dprop_correct `{Proset X, !InfLattice X, !BinMeets X, !Bot X}
      (F : Hom DProp X) (P : Prop)
  : universal_ran dprop F P ⟛ ran_dprop F P.
Proof.
  split.
  - apply: meet_right.
    + apply: inf_right => NP. by apply: (inf_left (⊥ ↾ _)).
    + by apply: (inf_left (⊤ ↾ _)); first apply: top_right.
  - apply: inf_right => -[[Q [Y | N]] /= D].
    + rewrite /ran_dprop meet_proj2. apply: mono. by compute.
    + rewrite /ran_dprop meet_proj1 (inf_lb (N ∘ D)) bot_left //.
Qed.
(*
Corollary dprop_codensity : local_ran dprop dprop dnegh.
Proof.
  (* ... *)
 *)

Corollary dprop_codensity : local_ran dprop dprop dnegh.
Proof.
  move=> G ?. split=> D P /=.
  - rewrite D. apply: dne.
  - move=> GP. apply: (regular_lem P) => ?.
    specialize (D (in_DProp P)). firstorder.
Qed.

Lemma dprop_nn_inf {R} (J : R -> DProp)
  : (HasInf J -> False) -> False.
Proof.
  apply: (regular_lem (forall r, J r)) => Dec.
  enough (HasInf J) by tauto.
  apply: dprop_reflect_inf.
Qed.
Lemma dprop_nn_sup {R} (J : R -> DProp)
  : (HasSup J -> False) -> False.
Proof.
  apply: (regular_lem (exists r, J r)) => Dec.
  enough (HasSup J) by tauto.
  apply: dprop_reflect_sup.
Qed.
Lemma dprop_inf {R} (J : R -> DProp) `{!HasInf J}
  : inf J <-> forall r, J r.
Proof. apply: (distrib_inf J (F:=dprop)). Qed.
Lemma dprop_inf' {R} (J : R -> DProp)
  : (forall `{!HasInf J}, dprop (inf J)) <-> forall r, J r.
Proof.
  apply: regular_bind (dprop_nn_inf J) => Has.
  rewrite instantiate_inf dprop_inf //.
Qed.
Instance d2r_cont : Continuous d2r.
Proof.
  move=> R J. apply/preserves_inf_alt4 => ?.
  change (dprop (inf J) <-> forall r, d2r (J r)). rewrite dprop_inf //.
Qed.
Definition must_exist {R} (J : R -> DProp) : Prop := ~ ~ exists r, J r.
Instance: Params (@must_exist) 1 := {}.
Instance d2r_cocont : Cocontinuous d2r.
Proof.
  move=> R J. apply/preserves_sup_alt4 => ?.
  split=> /= H.
  - apply: regular_lem => D.
    move: H. change (sup J ⊢ @in_DProp (must_exist J) D).
    apply: sup_left. compute. firstorder.
  - apply: regular_bind H => -[y].
    change (J y ⊢ sup J). apply: (sup_ub y).
Qed.
Lemma dprop_sup {R} (J : R -> DProp) `{!HasSup J}
  : sup J <-> must_exist J.
Proof. apply: (distrib_sup J (F:=d2r)). Qed.
Lemma dprop_sup' {R} (J : R -> DProp)
  : (forall `{!HasSup J}, sup J) <-> must_exist J.
Proof.
  apply: regular_bind (dprop_nn_sup J) => Has.
  rewrite instantiate_sup dprop_sup //.
Qed.

Instance decision_proper : CMorphisms.Proper
  (CMorphisms.respectful iff (CRelationClasses.flip CRelationClasses.arrow))
  Decision.
Proof. firstorder. Defined.
Lemma dprop_sup''1 {R} (J : R -> DProp)
  : HasSup J -> Decision (must_exist J).
Proof. move=> ?; rewrite -dprop_sup; apply: decide. Defined.
Lemma dprop_sup''2 {R} (J : R -> DProp)
  : Decision (must_exist J) -> HasSup J.
Proof.
  move=> Dec.
  refine {| sup := in_DProp (must_exist J) |}.
  case: (decide (must_exist J)); last by compute; firstorder.
  rewrite /must_exist /= => ME; have : ~ ~ exists r, J r by firstorder.
  apply: regular_bind => -[r J_r].
  split; first by firstorder.
  move=> A /(_ r J_r); firstorder.
Defined.

(* TODO Work with monotone stuff, not just extensional stuff! *)
Class Markovian (R : Type) `{Proset R} :=
  markov (P : R -> DProp) `{!Monotone P} : ~(forall r, P r) -> exists r, ~P r.
Class WeaklyOmniscient (R : Type) `{Proset R} :=
  weak_omniscience (P : R -> DProp) `{!Monotone P} : Decision (forall r, P r).
Class Omniscient (R : Type) `{Proset R} :=
  omniscience (P : R -> DProp) `{!Monotone P} : {forall r, P r} + {exists r, ~P r}.
  (* omniscience (P : R -> DProp) `{!Monotone P} : Decision (exists r, P r). *)
Hint Mode Markovian ! - - : typeclass_instances.
Hint Mode WeaklyOmniscient ! - - : typeclass_instances.
Hint Mode Omniscient ! - - : typeclass_instances.

Lemma WO_alt1 `{WeaklyOmniscient R} (J : R -> DProp) `{!Antitone J} : HasSup J.
Proof.
  apply/dprop_sup''2.
  case: (weak_omniscience (negh ∘ J)) => /=; [right | left]; firstorder.
Defined.
Lemma WO_alt2 `{Proset R} :
  (forall (J : R -> DProp) `{!Antitone J}, HasSup J) -> WeaklyOmniscient R.
Proof.
  move=> Has J ?.
  rewrite (_ : (forall r, J r) <-> ~ ~ ~ exists r, ~J r). 2: {
    setoid_rewrite <- (fun r => dne' (P:=J r)).
    firstorder.
  }
  apply: not_dec. apply/(dprop_sup''1 (negh ∘ J)).
Defined.
