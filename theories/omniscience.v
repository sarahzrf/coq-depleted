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
Instance dprop_decision {P : DProp} : Decision (tag P) := tagged P.
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

Definition negd (P : DProp) : DProp := in_DProp (~P).
Arguments negd !_ /.
Instance negd_anti : Antitone negd.
Proof. compute; firstorder. Qed.
Instance negd_antireflecting : Antireflecting negd.
Proof. move=> [P [? | ?]] [Q [? | ?]] /=; firstorder. Qed.
(* TODO yikes *)
Instance nn_adj : post_opped negd ⊣ pre_opped negd.
Proof. constructor=> -[P ?]; by compute. Qed.
Instance nn_adj' : pre_opped negd ⊣ post_opped negd.
Proof. constructor=> -[P ?]; compute; apply: dec_stable. Qed.
Instance nn_antiequiv1 : OrderEquiv (post_opped negd) (pre_opped negd) := {}.
Instance nn_antiequiv2 : OrderEquiv (pre_opped negd) (post_opped negd) := {}.

Lemma dcontra {P Q} : P ⊢ Q <-> negd Q ⊢ negd P.
Proof. move: P Q => [P [? | ?]] [Q [? | ?]] /=; firstorder. Qed.
Lemma ddne {P} : negd (negd P) ⟛ P.
Proof. move: P => [P [? | ?]]; by compute. Qed.
Lemma dcontra_l {P Q} : negd P ⊢ Q <-> negd Q ⊢ P.
Proof. rewrite dcontra; split=> ->; [rewrite ddne // | rewrite -(proj2 ddne) //]. Qed.
Lemma dcontra_r {P Q} : P ⊢ negd Q <-> Q ⊢ negd P.
Proof. rewrite dcontra; split=> <-; [rewrite -(proj2 ddne) // | rewrite ddne //]. Qed.

Program Instance negd_inf {R} {J : R -> DProp} `{!HasSup J}
  : HasInf (negd ∘ J)
  := {| inf := negd (sup J) |}.
Next Obligation.
  move=> R J ?.
  apply: (preserve_inf (J:=Op ∘ J) (F:=pre_opped negd)).
  apply: is_sup.
Qed.
Program Instance negd_sup {R} {J : R -> DProp} `{!HasInf J}
  : HasSup (negd ∘ J)
  := {| sup := negd (inf J) |}.
Next Obligation.
  move=> R J ?.
  apply: (preserve_sup (J:=Op ∘ J) (F:=pre_opped negd)).
  apply: is_inf.
Qed.

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

Program Instance dprop_reflect_inf {R} (J : R -> DProp) (Dec : Decision (forall r, J r))
  : HasInf J
  := {| inf := in_DProp (forall r, J r) |}.
Next Obligation. move=> *; by apply: (reflecting_undistrib_inf (F:=dprop)). Qed.
Program Instance dprop_reflect_sup {R} (J : R -> DProp) (Dec : Decision (exists r, J r))
  : HasSup J
  := {| sup := in_DProp (exists r, J r) |}.
Next Obligation. move=> *; by apply: (reflecting_undistrib_sup (F:=dprop)). Qed.

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
Definition must_exist {R} (J : R -> DProp) : Prop := ~forall r, negd (J r).
Instance: Params (@must_exist) 1 := {}.
Lemma dprop_sup {R} (J : R -> DProp) `{!HasSup J}
  : sup J <-> must_exist J.
Proof.
  rewrite -[dprop (sup J)]dne'; apply: not_iff_compat.
  change (dprop (inf (negd ∘ J)) ⟛ forall r, negd (J r)); apply: dprop_inf.
Qed.
Lemma dprop_sup' {R} (J : R -> DProp)
  : (forall `{!HasSup J}, dprop (sup J)) <-> must_exist J.
Proof.
  apply: regular_bind (dprop_nn_sup J) => Has.
  rewrite instantiate_sup dprop_sup //.
Qed.

Definition RProp : Type := sig Regular.
Coercion rprop := sval : RProp -> Prop.
Arguments rprop !_ /.
Instance rprop_regular {P : RProp} : Regular (`P) := proj2_sig P.
Definition in_RProp (P : Prop) `{H : !Regular P} : RProp := P as_a RProp.
Instance regular_monclosed : MonClosed Regular.
Proof. firstorder. Qed.
Definition dn : Prop -> RProp := (not ∘ not) ↑.
Instance RProp_reflection : dn ⊣ rprop.
Proof. constructor; [firstorder | move=> [P ?] //=]. Qed.
Program Instance rprop_inflattice : InfLattice RProp
  := fun R J => {| inf := inf (rprop ∘ J) ↾ forall_regular |}.
Next Obligation. compute; firstorder. Qed.
Instance rprop_suplattice : SupLattice RProp
  := fun R => reflective_dsups (F:=dn).

Definition negr (P : RProp) : RProp := in_RProp (~P).
Arguments negr !_ /.
Instance negr_anti : Antitone negr.
Proof. compute; firstorder. Qed.
Instance negr_antireflecting : Antireflecting negr.
Proof. move=> [P ?] [Q ?] /=; firstorder. Qed.
(* TODO yikes *)
Instance nnr_adj : post_opped negr ⊣ pre_opped negr.
Proof. constructor=> -[P ?]; by compute. Qed.
Instance nnr_adj' : pre_opped negr ⊣ post_opped negr.
Proof. constructor=> -[P ?]; by compute. Qed.
Instance nnr_antiequiv1 : OrderEquiv (post_opped negr) (pre_opped negr) := {}.
Instance nnr_antiequiv2 : OrderEquiv (pre_opped negr) (post_opped negr) := {}.

Lemma rcontra {P Q} : P ⊢ Q <-> negr Q ⊢ negr P.
Proof. move: P Q => [P ?] [Q ?] /=; firstorder. Qed.
Lemma rdne {P} : negr (negr P) ⟛ P.
Proof. move: P => [P ?]; by compute. Qed.
Lemma rcontra_l {P Q} : negr P ⊢ Q <-> negr Q ⊢ P.
Proof. move: P Q => [P ?] [Q ?] /=; firstorder. Qed.
Lemma rcontra_r {P Q} : P ⊢ negr Q <-> Q ⊢ negr P.
Proof. move: P Q => [P ?] [Q ?] /=; firstorder. Qed.

Definition d2r : DProp -> RProp := dprop ↑.


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
