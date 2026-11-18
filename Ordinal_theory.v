(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)
(*--------------------------------------------------------------------*)
(* Modified by Stephanie Weirich, 2026 (from                          *)
(* https://github.com/rocq-archive/zfc): Added [Set Universe          *)
(* Polymorphism]. [Vee] (formerly in [Omega.v]) defined here,         *)
(* returning [Vide] on atoms and pairs; [ex_rk] takes a new [pure]    *)
(* premise (hereditarily a set); added [Vee_is_set]; proofs           *)
(* rewritten.                                                         *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Export Plump.

(* Universe polymorphic, matching the [zfc] core (see [Sets.v]). *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* The cumulative hierarchy and the rank of a set, adapted to the sorted
   [Ens] of [Sets.v].

   [Vee] used to live in [Omega.v]; it is defined here now, with [Vee] of
   an atom or a pair being [Vide].  Every member of a [Vee L] is a set (a
   subset of some [Vee]), so atoms and pairs have no rank: [ex_rk] is
   stated for [pure] values, i.e. sets all of whose members are, in turn,
   [pure].  The other statements are as in the original. *)

Fixpoint Vee (E : Ens) : Ens :=
  match E with
  | sup A f => Union (sup A (fun a : A => Power (Vee (f a))))
  | _ => Vide
  end.

Fixpoint pure (E : Ens) : Prop :=
  match E with
  | sup A f => forall a : A, pure (f a)
  | _ => False
  end.

Lemma Vee_is_set : forall E : Ens, is_set (Vee E).
Proof. intro E; destruct E; exact I. Qed.

Lemma Vee_sound : forall E1 E2 : Ens, EQ E1 E2 -> EQ (Vee E1) (Vee E2).
Proof.
  induction E1 as [n | a IHa b IHb | A1 f1 HR1]; intros E2 e;
    destruct E2 as [m | c d | A2 f2]; simpl in e; try contradiction.
  - apply EQ_refl.
  - apply EQ_refl.
  - destruct e as [e1 e2].
    change (EQ (Union (sup A1 (fun a : A1 => Power (Vee (f1 a)))))
               (Union (sup A2 (fun a : A2 => Power (Vee (f2 a)))))).
    apply Union_sound; split.
    + intros a1; destruct (e1 a1) as [a2 h]; exists a2.
      apply Power_sound; apply HR1; exact h.
    + intros a2; destruct (e2 a2) as [a1 h]; exists a1.
      apply Power_sound; apply HR1; exact h.
Qed.



Lemma IN_Vee :
 forall V W : Ens, IN W V -> forall E : Ens, INC E (Vee W) -> IN E (Vee V).
Proof.
  intros V W i E inc. destruct V as [n | a b | A f]; simpl in i; try contradiction.
  destruct i as [a ea].
  change (IN E (Union (sup A (fun a : A => Power (Vee (f a)))))).
  apply IN_Union with (Power (Vee W)).
  - exists a; apply Power_sound; apply Vee_sound; exact ea.
  - apply INC_IN_Power; [ apply Vee_is_set | exact inc ].
Qed.

Lemma INC_IN_Vee_Succ :
 forall E L : Ens, Ord L -> INC E (Vee L) -> IN E (Vee (Succ L)).
Proof. intros E L o inc. apply IN_Vee with L; [ apply Succ_incr; exact o | exact inc ]. Qed.

Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) :=
  match c with
  | dep_i a p => a
  end.

Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) :=
  match c return (P (PI1 A P c)) with
  | dep_i a p => p
  end.



Lemma IN_Vee_EXType :
 forall E X : Ens,
 IN X (Vee E) -> EXType Ens (fun Y : Ens => IN Y E /\ INC X (Vee Y)).
Proof.
  intros E X i. destruct E as [n | a b | A f];
    [ destruct (Vide_est_vide X i) | destruct (Vide_est_vide X i) | ].
  change (IN X (Union (sup A (fun a : A => Power (Vee (f a)))))) in i.
  destruct (Union_IN _ _ i) as [T [i1 i2]].
  destruct i1 as [a e].
  exists (f a); split.
  - exists a; apply EQ_refl.
  - apply IN_Power_INC. apply IN_sound_right with T; assumption.
Qed.

Lemma mon_Vee : forall E1 E2 : Ens, INC E1 E2 -> INC (Vee E1) (Vee E2).
Proof.
  intros E1 E2 inc. apply INC_intro; [ apply Vee_is_set | ].
  intros X i. destruct (IN_Vee_EXType _ _ i) as [Y [i1 inc1]].
  apply IN_Vee with Y; [ apply INC_elim with E1; assumption | exact inc1 ].
Qed.

Hint Resolve IN_Power_INC: zfc.

Lemma IN_Succ_INC : forall E X : Ens, IN X (Succ E) -> INC X E.
Proof.
  unfold Succ; intros E X i. apply IN_Power_INC.
  apply INC_elim with (Comp (Power E) Ord); [ apply Comp_INC | exact i ].
Qed.


Hint Resolve Ord_Succ: zfc.

Lemma IN_Vee_Succ_EXType :
 forall E X : Ens,
 Ord E ->
 IN X (Vee (Succ E)) ->
 EXType _ (fun Y : Ens => INC Y E /\ Ord Y /\ INC X (Vee Y)).
Proof.
  intros E X o i. destruct (IN_Vee_EXType _ _ i) as [Y [i1 inc]].
  exists Y; split; [ apply IN_Succ_INC; exact i1 | split; [ | exact inc ] ].
  apply IN_Ord_Ord with (Succ E); [ apply Ord_Succ; exact o | exact i1 ].
Qed.

Lemma IN_Vee_Succ :
 forall E X : Ens,
 Ord E ->
 forall Y : Ens, Ord Y -> INC Y E -> INC X (Vee Y) -> IN X (Vee (Succ E)).
Proof.
  intros E X o Y o1 inc inc1. apply IN_Vee with Y; [ | exact inc1 ].
  unfold Succ; apply IN_P_Comp; [ exact Ord_ext | | exact o1 ].
  apply INC_IN_Power; [ apply Ord_is_set; exact o | exact inc ].
Qed.


Inductive depprod1 (A : Type) (P : A -> Type) : Type :=
    dep_i1 : forall x : A, P x -> depprod1 A P.

Definition PI11 (A : Type) (P : A -> Type) (c : depprod1 A P) :=
  match c with
  | dep_i1 a p => a
  end.

Definition PI21 (A : Type) (P : A -> Type) (c : depprod1 A P) :=
  match c return (P (PI11 A P c)) with
  | dep_i1 a p => p
  end.


Lemma ex_rk :
 forall E : Ens, pure E -> depprod1 _ (fun L : Ens => Ord L /\ IN E (Vee L)).
Proof.
  induction E as [n | a IHa b IHb | A f HR]; intros p; simpl in p; try contradiction.
  pose (R := fun a : A => PI11 _ _ (HR a (p a))).
  assert (HRa : forall a : A, Ord (R a) /\ IN (f a) (Vee (R a)))
    by (intro a; exact (PI21 _ _ (HR a (p a)))).
  pose (L := Union (sup A R)).
  assert (oL : Ord L).
  { apply Union_Ord. intros E' [a e].
    apply Ord_sound with (R a); [ apply EQ_sym; exact e | apply HRa ]. }
  exists (Succ L). split; [ apply Ord_Succ; exact oL | ].
  apply IN_Vee_Succ with L; [ exact oL | exact oL | apply INC_refl | ].
  apply INC_intro; [ exact I | ]. intros E' [a e].
  apply IN_sound_left with (f a); [ apply EQ_sym; exact e | ].
  apply INC_elim with (Vee (R a)); [ | apply HRa ].
  apply mon_Vee. apply IN_INC_Union; [ apply Ord_is_set; apply HRa | exists a; apply EQ_refl ].
Qed.
