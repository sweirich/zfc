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
(* Polymorphism]. Adapted to the sorted [Ens] of [Sets.v]: [ord] is a *)
(* Fixpoint that is [False] on atoms and pairs; [ord_tech] and        *)
(* [Ord_intro] take an [is_set] premise; added [ord_is_set],          *)
(* [Ord_is_set], [INC_is_set], [ord_is_set_sub], [Inter_is_set],      *)
(* [IN_Inter_inhabited] and [Ord_ext]; proofs rewritten.              *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
Require Export Sets.
Require Export Axioms.
Require Export Omega.

(* Universe polymorphic, matching the [zfc] core (see [Sets.v]). *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Plump ordinals, adapted to the sorted [Ens] of [Sets.v].

   An ordinal is a *set*: [ord] is [False] on an atom or a pair.  For a set
   [E = sup A f], [ord E E' _] says that every member of [E] lying in [E'] is
   an ordinal, and that [E'] contains every [ord]-subset of such a member.
   [Ord E] is [ord E E _].

   Changes from the original statements: [ord_tech] and [Ord_intro] take an
   [is_set] premise (a non-set has no members, so the other hypotheses hold
   vacuously for it), and [Ord_is_set] / [ord_is_set] are new. *)

Fixpoint ord (E : Ens) : forall E' : Ens, INC E' E -> Prop :=
  match E with
  | sup A f =>
      fun E' _ =>
        (forall a : A, IN (f a) E' -> ord (f a) (f a) (INC_refl (f a))) /\
        (forall (a : A) (e : Ens),
         IN (f a) E' -> forall p : INC e (f a), ord (f a) e p -> IN e E')
  | _ => fun _ _ => False
  end.

Definition Ord (E : Ens) := ord E E (INC_refl E).

Lemma ord_is_set : forall (E E' : Ens) (p : INC E' E), ord E E' p -> is_set E.
Proof. intros E; destruct E; simpl; tauto. Qed.

Lemma Ord_is_set : forall E : Ens, Ord E -> is_set E.
Proof. intros E; apply ord_is_set. Qed.

(* A subset (in the [INC] sense) of a set is a set. *)
Lemma INC_is_set : forall E E' : Ens, INC E' E -> is_set E -> is_set E'.
Proof.
  intros E E' inc s. destruct E' as [n | a b | A f]; simpl; trivial.
  - apply (EQ_is_set E (atom n)); [ apply EQ_sym; exact inc | exact s ].
  - apply (EQ_is_set E (pair a b)); [ apply EQ_sym; exact inc | exact s ].
Qed.

Lemma ord_is_set_sub :
 forall (E E' : Ens) (p : INC E' E), ord E E' p -> is_set E'.
Proof. intros E E' p o. apply INC_is_set with E; [ exact p | apply ord_is_set with E' p; exact o ]. Qed.

Lemma ord_ext :
 forall (E E' E'' : Ens) (p' : INC E' E) (p'' : INC E'' E),
 EQ E' E'' -> ord E E' p' -> ord E E'' p''.
Proof.
  intros E; destruct E as [n | a b | A f]; simpl; try tauto.
  intros E' E'' p' p'' e [o1 o2]; split.
  - intros a i; apply o1. apply IN_sound_right with E''; [ apply EQ_sym; exact e | exact i ].
  - intros a x i p o. apply IN_sound_right with E'; [ exact e | ].
    apply (o2 a x) with p; [ apply IN_sound_right with E''; [ apply EQ_sym; exact e | exact i ] | exact o ].
Qed.

Lemma ord_sound :
 forall E E' : Ens,
 EQ E E' ->
 forall (E'' : Ens) (p : INC E'' E) (p' : INC E'' E'),
 (ord E E'' p -> ord E' E'' p') /\ (ord E' E'' p' -> ord E E'' p).
Proof.
  induction E as [n | a IHa b IHb | A f HR]; intros E' e;
    destruct E' as [m | c d | B g]; simpl in e; try contradiction;
    intros E'' p p'; simpl; try tauto.
  destruct e as [e1 e2]. split.
  - intros [o1 o2]; split.
    + intros b i. destruct (e2 b) as [a ea].
      assert (inc : INC (g b) (f a)) by (apply EQ_INC; apply EQ_sym; exact ea).
      apply (proj1 (HR a (g b) ea (g b) inc (INC_refl (g b)))).
      apply ord_ext with (f a) (INC_refl (f a)); [ exact ea | ].
      apply o1. apply IN_sound_left with (g b); [ apply EQ_sym; exact ea | exact i ].
    + intros b x i p0 o. destruct (e2 b) as [a ea].
      assert (inc0 : INC x (f a)) by (apply INC_sound_right with (g b); [ apply EQ_sym; exact ea | exact p0 ]).
      apply (o2 a x) with inc0.
      * apply IN_sound_left with (g b); [ apply EQ_sym; exact ea | exact i ].
      * apply (proj2 (HR a (g b) ea x inc0 p0)); exact o.
  - intros [o1 o2]; split.
    + intros a i. destruct (e1 a) as [b eb].
      assert (inc : INC (f a) (g b)) by (apply EQ_INC; exact eb).
      apply (proj2 (HR a (g b) eb (f a) (INC_refl (f a)) inc)).
      apply ord_ext with (g b) (INC_refl (g b)); [ apply EQ_sym; exact eb | ].
      apply o1. apply IN_sound_left with (f a); [ exact eb | exact i ].
    + intros a x i p0 o. destruct (e1 a) as [b eb].
      assert (inc0 : INC x (g b)) by (apply INC_sound_right with (f a); [ exact eb | exact p0 ]).
      apply (o2 b x) with inc0.
      * apply IN_sound_left with (f a); [ exact eb | exact i ].
      * apply (proj1 (HR a (g b) eb x p0 inc0)); exact o.
Qed.

Lemma Ord_sound : forall E E' : Ens, EQ E E' -> Ord E -> Ord E'.
Proof.
  unfold Ord; intros E E' e o.
  assert (inc : INC E' E) by (apply EQ_INC; apply EQ_sym; exact e).
  apply (proj1 (ord_sound E E' e E' inc (INC_refl E'))).
  apply ord_ext with E (INC_refl E); [ exact e | exact o ].
Qed.

Lemma IN_Ord_Ord : forall E E' : Ens, Ord E -> IN E' E -> Ord E'.
Proof.
  intros E E' o i. destruct E as [n | a b | A f]; simpl in o, i; try contradiction.
  destruct o as [o1 _]. destruct i as [a ea].
  apply Ord_sound with (f a); [ apply EQ_sym; exact ea | ].
  apply o1. exists a; apply EQ_refl.
Qed.

Lemma ord_tech :
 forall (E1 E2 E : Ens) (p1 : INC E E1) (p2 : INC E E2),
 is_set E2 -> ord E1 E p1 -> ord E2 E p2.
Proof.
  intros E1 E2 E p1 p2 s2 o.
  destruct E1 as [n | a b | A1 f1]; simpl in o; try contradiction.
  destruct E2 as [m | c d | A2 f2]; simpl in s2; try contradiction.
  destruct o as [o1 o2]; simpl; split.
  - intros a2 i2.
    destruct (INC_elim E (sup A1 f1) p1 (f2 a2) i2) as [a1 e1].
    apply Ord_sound with (f1 a1); [ apply EQ_sym; exact e1 | ].
    apply o1. apply IN_sound_left with (f2 a2); [ exact e1 | exact i2 ].
  - intros a2 x i2 p o.
    destruct (INC_elim E (sup A1 f1) p1 (f2 a2) i2) as [a1 e1].
    assert (inc1 : INC x (f1 a1)) by (apply INC_sound_right with (f2 a2); [ exact e1 | exact p ]).
    apply (o2 a1 x) with inc1.
    + apply IN_sound_left with (f2 a2); [ exact e1 | exact i2 ].
    + apply (proj2 (ord_sound (f1 a1) (f2 a2) (EQ_sym _ _ e1) x inc1 p)); exact o.
Qed.

Lemma plump :
 forall E : Ens,
 Ord E ->
 forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E.
Proof.
  intros E o E1 E2 o1 o2 i inc.
  destruct E as [n | a b | A f]; simpl in i; try contradiction.
  destruct o as [h1 h2]. destruct i as [a ea].
  assert (inc0 : INC E2 (f a)) by (apply INC_sound_right with E1; [ exact ea | exact inc ]).
  apply (h2 a E2) with inc0; [ exists a; apply EQ_refl | ].
  apply ord_tech with E2 (INC_refl E2); [ | exact o2 ].
  apply Ord_is_set. apply h1. exists a; apply EQ_refl.
Qed.

Lemma Ord_intro :
 forall E : Ens,
 is_set E ->
 (forall E' : Ens, IN E' E -> Ord E') ->
 (forall E1 E2 : Ens, Ord E1 -> Ord E2 -> IN E1 E -> INC E2 E1 -> IN E2 E) ->
 Ord E.
Proof.
  intros E s h1 h2. destruct E as [n | a b | A f]; simpl in s; try contradiction.
  unfold Ord; simpl; split.
  - intros a i; apply h1; exact i.
  - intros a E1 i inc o. apply h2 with (f a); [ apply h1; exact i | | exact i | exact inc ].
    unfold Ord. apply ord_tech with (f a) inc; [ apply ord_is_set_sub with (f a) inc; exact o | exact o ].
Qed.

Lemma Ord_trans :
 forall E : Ens, Ord E -> forall E' : Ens, IN E' E -> INC E' E.
Proof.
  induction E as [n | a b IHa IHb | A f HR]; intros o E' i; simpl in i; try contradiction.
  assert (oE' : Ord E') by (apply IN_Ord_Ord with (sup A f); assumption).
  apply INC_intro; [ apply Ord_is_set; exact oE' | ].
  intros E'' i'.
  destruct i as [a ea].
  apply plump with E'; trivial.
  - apply IN_Ord_Ord with E'; assumption.
  - exists a; exact ea.
  - apply INC_sound_right with (f a); [ apply EQ_sym; exact ea | ].
    apply HR.
    + apply IN_Ord_Ord with (sup A f); [ exact o | exists a; apply EQ_refl ].
    + apply IN_sound_right with E'; assumption.
Qed.

Lemma Inter_is_set : forall E : Ens, is_set (Inter E).
Proof. intros E; destruct E; exact I. Qed.

(* A member of [Inter E] witnesses that [E] is inhabited. *)
Lemma IN_Inter_inhabited :
 forall E E' : Ens, IN E' (Inter E) -> EXType Ens (fun E'' => IN E'' E).
Proof.
  intros E E' i. destruct E as [n | b c | A f]; simpl in i.
  - destruct i as [x _]; destruct x.
  - destruct i as [x _]; destruct x.
  - destruct i as [[a _] _]. exists (f a); exists a; apply EQ_refl.
Qed.

Lemma Inter_Ord :
 forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Inter E).
Proof.
  intros E H. apply Ord_intro; [ apply Inter_is_set | | ].
  - intros E' i. destruct (IN_Inter_inhabited E E' i) as [E'' i''].
    apply IN_Ord_Ord with E''; [ apply H; exact i'' | apply IN_Inter_all with E; assumption ].
  - intros E1 E2 o1 o2 i inc. destruct (IN_Inter_inhabited E E1 i) as [E'' i''].
    apply all_IN_Inter with E''; [ exact i'' | ].
    intros X iX. apply plump with E1; trivial; [ apply H; exact iX | ].
    apply IN_Inter_all with E; assumption.
Qed.

Lemma inter_ord : forall E : Ens, Ord E -> Ord (Inter E).
Proof. intros E o; apply Inter_Ord; intros E' i; apply IN_Ord_Ord with E; assumption. Qed.

Lemma Union_Ord :
 forall E : Ens, (forall E' : Ens, IN E' E -> Ord E') -> Ord (Union E).
Proof.
  intros E H. apply Ord_intro; [ apply Union_is_set | | ].
  - intros E' i. destruct (Union_IN E E' i) as [E3 [i1 i2]].
    apply IN_Ord_Ord with E3; [ apply H; exact i1 | exact i2 ].
  - intros E1 E2 o1 o2 i inc. destruct (Union_IN E E1 i) as [E3 [i1 i2]].
    apply IN_Union with E3; [ exact i1 | ].
    apply plump with E1; trivial. apply H; exact i1.
Qed.

Lemma union_Ord : forall E : Ens, Ord E -> Ord (Union E).
Proof. intros E o; apply Union_Ord; intros E' i; apply IN_Ord_Ord with E; assumption. Qed.


Definition Succ (E : Ens) := Comp (Power E) Ord.

Lemma Ord_ext : forall w1 w2 : Ens, Ord w1 -> EQ w1 w2 -> Ord w2.
Proof. intros w1 w2 o e; apply Ord_sound with w1; assumption. Qed.

Lemma Ord_Succ : forall E : Ens, Ord E -> Ord (Succ E).
Proof.
  unfold Succ; intros E o. apply Ord_intro; [ apply Comp_is_set | | ].
  - intros E' i. apply IN_Comp_P with (Power E); [ exact Ord_ext | exact i ].
  - intros E1 E2 o1 o2 i inc. apply IN_P_Comp; [ exact Ord_ext | | exact o2 ].
    apply INC_IN_Power; [ apply Ord_is_set; exact o | ].
    apply INC_tran with E1; [ exact inc | ].
    apply IN_Power_INC. apply INC_elim with (Comp (Power E) Ord); [ apply Comp_INC | exact i ].
Qed.

Lemma Succ_incr : forall E : Ens, Ord E -> IN E (Succ E).
Proof.
  unfold Succ; intros E o. apply IN_P_Comp; [ exact Ord_ext | | exact o ].
  apply INC_IN_Power; [ apply Ord_is_set; exact o | apply INC_refl ].
Qed.

Definition PI1 (A : Type) (P : A -> Type) (c : depprod A P) : A :=
  match c with
  | dep_i a _ => a
  end.

Definition PI2 (A : Type) (P : A -> Type) (c : depprod A P) : P (PI1 A P c) :=
  match c return (P (PI1 A P c)) with
  | dep_i a p => p
  end.
