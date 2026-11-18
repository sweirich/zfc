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
(* https://github.com/rocq-archive/zfc): [Ens] extended with atoms    *)
(* ([atom n]) and primitive couples ([pair a b]) alongside sets       *)
(* ([sup]); [EQ], [IN] and [INC] made sort-aware; core definitions    *)
(* made universe polymorphic; added the sort predicates               *)
(* [is_atom]/[is_pair]/[is_set] and their lemmas; proofs rewritten in *)
(* modern tactic style.                                               *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* Sets with atoms and primitive couples.

   This file is Benjamin Werner's [Sets.v], with the universe [Ens]
   extended by two sorts of *non-set* values:

     - [atom n], a natural number.  Atoms have no members and two atoms are
       extensionally equal only when they are the same number.  This makes
       numerals disjoint from every set: in the pure encoding [Nat 0] was
       the empty set (hence the empty graph) and [Nat (S k)] contained it,
       so a numeral could be a function.
     - [pair a b], the ordered pair (the [Couple] of [Cartesian.v]).  Pairs
       have no members and are compared componentwise, so a graph is a set
       of pairs whose projections are definitional, and no set is a pair.

   Extensional equality [EQ] compares two values of the same sort and is
   [False] across sorts.  Membership [IN] is as before on a [sup] and [False]
   in a non-set.  Inclusion [INC] is *kind-aware*: a set is included in
   whatever contains all its members, while a non-set is included only in
   (something equal to) itself — so [INC] stays antisymmetric up to [EQ]
   without any sortedness premise ([INC_EQ]).  The set-formers of
   [Axioms.v] return the empty set when applied to a non-set.

   Proofs are written in modern tactic style; the statements and names of
   the original are preserved. *)

Global Set Asymmetric Patterns.

(* Only the handful of building blocks that the "small sets" construction
   in [Hierarchy.v] needs at a *second* universe level are made universe
   polymorphic ([Ens], [EXType], [depprod], [EQ], and [Power] in
   [Axioms.v]).  The theorems that follow are polymorphic too (see below). *)

(* The type of values (Ensemble = french for set).

   [Ens] is *cumulative*, so a lower-universe [Ens] is a subtype of a
   higher one.  Without this, monomorphic set-builders such as [Vide]
   (whose universe minimises to [Set]) could not be passed to operations
   whose [Ens] universe floats higher, e.g. [IN E Vide].  [EXType] /
   [depprod] stay non-cumulative: making them cumulative perturbs
   [simpl]/[auto] in the [Power] proofs of [Axioms.v]. *)
Polymorphic Cumulative Inductive Ens : Type :=
  | atom : nat -> Ens
  | pair : Ens -> Ens -> Ens
  | sup : forall A : Type, (A -> Ens) -> Ens.

(* Existential quantification.  Kept monomorphic on purpose: were it
   polymorphic, [EQ] (which is built from it) would acquire extra floating
   universes whose per-occurrence variance breaks [fold]/[rewrite] in the
   quotient proofs of [zf/quot/ZFSetCore.v].  [Hierarchy.v] uses plain
   [exists] instead of an [EXType] copy. *)
Inductive EXType (P : Type) (Q : P -> Prop) : Prop :=
    EXTypei : forall x : P, Q x -> EXType P Q.

(* Cartesian product in Type *)

Inductive prod_t (A B : Type) : Type :=
    pair_t : A -> B -> prod_t A B.


(* Existential on the Type level *)

Polymorphic Inductive depprod (A : Type) (P : A -> Type) : Type :=
    dep_i : forall x : A, P x -> depprod A P.


(* Recursive definition of the extensional equality.  Two atoms are equal
   when their numbers are; two pairs when their components are; two sets
   when every member of each is equal to a member of the other.  Values of
   different sorts are never equal. *)

Polymorphic Fixpoint EQ@{u} (E1 E2 : Ens@{u}) {struct E1} : Prop :=
  match E1, E2 with
  | atom n, atom m => n = m
  | pair a b, pair c d => EQ a c /\ EQ b d
  | sup A f, sup B g =>
      (forall x : A, EXType B (fun y : B => EQ (f x) (g y))) /\
      (forall y : B, EXType A (fun x : A => EQ (f x) (g y)))
  | _, _ => False
  end.

(* Membership on sets.

   From here on the file is universe polymorphic: [IN], [INC] and every
   equality/inclusion lemma get a floating [Ens] universe so they can be
   reused at more than one level (e.g. [Hierarchy.v] applies them to both
   [big] and [small] sets, while [lib] applies them at [ulib]).  Keeping
   these monomorphic pinned all those universes equal, which blocked the
   [small < big < huge] tower from lifting into the [ZFSet] quotient.
   [EXType]/[prod_t] above stay monomorphic on purpose (see their notes).

   [Unset Universe Minimization ToSet] is essential: without it the
   unconstrained [Ens] universe of each lemma is collapsed to [Set],
   pinning e.g. [Union_sound]'s arguments to [Ens@{Set}] so it can no
   longer be applied to [big]-level sets in [Hierarchy.v].  Unsetting it
   keeps that universe a genuine floating polymorphic parameter. *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* The three sorts. *)

Definition is_atom (E : Ens) : Prop := match E with atom _ => True | _ => False end.
Definition is_pair (E : Ens) : Prop := match E with pair _ _ => True | _ => False end.
Definition is_set  (E : Ens) : Prop := match E with sup _ _ => True | _ => False end.

(* Membership: the members of a set; a non-set has none. *)

Definition IN (E1 E2 : Ens) : Prop :=
  match E2 with
  | sup A f => EXType A (fun y : A => EQ E1 (f y))
  | _ => False
  end.


(* Inclusion, kind-aware: a set is included in anything that contains all
   its members; an atom or a pair is included only in something equal to
   itself.  (The member condition alone would make every non-set a subset
   of everything, and two distinct atoms mutually included.) *)

Definition INC (E1 E2 : Ens) : Prop :=
  match E1 with
  | sup _ _ => forall E : Ens, IN E E1 -> IN E E2
  | _ => EQ E1 E2
  end.


(* EQ is an equivalence relation  *)

Theorem EQ_refl : forall E : Ens, EQ E E.
Proof.
  induction E as [n | a IHa b IHb | A f IH]; simpl.
  - reflexivity.
  - split; assumption.
  - split; intro x; exists x; apply IH.
Qed.

Theorem EQ_tran : forall E1 E2 E3 : Ens, EQ E1 E2 -> EQ E2 E3 -> EQ E1 E3.
Proof.
  induction E1 as [n | a IHa b IHb | A f IH]; intros E2 E3;
    destruct E2 as [m | c d | B g]; destruct E3 as [k | e h | C j]; simpl;
    intros H1 H2; try contradiction.
  - rewrite H1; exact H2.
  - destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b].
    split; [ apply IHa with c | apply IHb with d ]; assumption.
  - destruct H1 as [H1 H1']; destruct H2 as [H2 H2']; split.
    + intro x. destruct (H1 x) as [y Hy]. destruct (H2 y) as [z Hz].
      exists z. apply IH with (g y); assumption.
    + intro z. destruct (H2' z) as [y Hy]. destruct (H1' y) as [x Hx].
      exists x. apply IH with (g y); assumption.
Qed.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
Proof.
  induction E1 as [n | a IHa b IHb | A f IH]; intros E2;
    destruct E2 as [m | c d | B g]; simpl; intros H; try contradiction.
  - symmetry; exact H.
  - destruct H as [Ha Hb]. split; [ apply IHa | apply IHb ]; assumption.
  - destruct H as [H1 H2]. split.
    + intro y. destruct (H2 y) as [x Hx]. exists x. apply IH; exact Hx.
    + intro x. destruct (H1 x) as [y Hy]. exists y. apply IH; exact Hy.
Qed.

(* Equality respects the sorts. *)

Theorem EQ_is_atom : forall E E' : Ens, EQ E E' -> is_atom E -> is_atom E'.
Proof. intros E E'; destruct E; destruct E'; simpl; intros; try contradiction; trivial. Qed.

Theorem EQ_is_pair : forall E E' : Ens, EQ E E' -> is_pair E -> is_pair E'.
Proof. intros E E'; destruct E; destruct E'; simpl; intros; try contradiction; trivial. Qed.

Theorem EQ_is_set : forall E E' : Ens, EQ E E' -> is_set E -> is_set E'.
Proof. intros E E'; destruct E; destruct E'; simpl; intros; try contradiction; trivial. Qed.

(* The atom and pair clauses of [EQ], as lemmas. *)

Theorem EQ_atom_atom : forall n m : nat, EQ (atom n) (atom m) -> n = m.
Proof. intros n m H; exact H. Qed.

Theorem atom_EQ : forall n : nat, EQ (atom n) (atom n).
Proof. intro n; simpl; reflexivity. Qed.

Theorem EQ_pair_pair :
 forall a b c d : Ens, EQ (pair a b) (pair c d) -> EQ a c /\ EQ b d.
Proof. intros a b c d H; exact H. Qed.

Theorem pair_sound :
 forall a a' b b' : Ens, EQ a a' -> EQ b b' -> EQ (pair a b) (pair a' b').
Proof. intros a a' b b' Ha Hb; simpl; split; assumption. Qed.

(* A non-set has no members. *)

Theorem IN_is_set : forall E E' : Ens, IN E E' -> is_set E'.
Proof. intros E E'; destruct E'; simpl; intros H; try contradiction; trivial. Qed.

Theorem IN_atom : forall (E : Ens) (n : nat), IN E (atom n) -> False.
Proof. intros E n H; exact H. Qed.

Theorem IN_pair : forall E a b : Ens, IN E (pair a b) -> False.
Proof. intros E a b H; exact H. Qed.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
Proof.
  intros E E' H. destruct E as [n | a b | A f]; simpl.
  - exact H.
  - exact H.
  - destruct E' as [m | c d | B g]; simpl in H; try contradiction.
    destruct H as [H1 H2].
    intros E0 HE0. destruct HE0 as [x Hx]. destruct (H1 x) as [y Hy].
    exists y. apply EQ_tran with (f x); assumption.
Qed.

Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.

(* Antisymmetry of inclusion — with no premise on the sorts, thanks to the
   kind-aware [INC]. *)

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
Proof.
  intros E E' H1 H2. destruct E as [n | a b | A f].
  - exact H1.
  - exact H1.
  - destruct E' as [m | c d | B g].
    + simpl in H2; contradiction.
    + simpl in H2; contradiction.
    + simpl. split.
      * intro x. destruct (H1 (f x)) as [y Hy]; [ exists x; apply EQ_refl | ].
        exists y; exact Hy.
      * intro y. destruct (H2 (g y)) as [x Hx]; [ exists y; apply EQ_refl | ].
        exists x; apply EQ_sym; exact Hx.
Qed.

Hint Resolve INC_EQ: zfc.


(* Membership is extentional (i.e. is stable w.r.t. EQ)   *)

Theorem IN_sound_left :
 forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
Proof.
  intros E E' E'' HE HIN. destruct E'' as [k | c d | A f]; simpl in *; try contradiction.
  destruct HIN as [a Ha]. exists a.
  apply EQ_tran with E; [ apply EQ_sym; exact HE | exact Ha ].
Qed.

Theorem IN_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
Proof.
  intros E E' E'' HE HIN.
  destruct E' as [k | c d | A f]; simpl in HIN; try contradiction.
  destruct E'' as [k' | c' d' | B g]; simpl in HE; try contradiction.
  destruct HE as [H1 H2]. destruct HIN as [a Ha].
  destruct (H1 a) as [b Hb]. exists b. apply EQ_tran with (f a); assumption.
Qed.

(* Inclusion is reflexive, transitive, extentional *)

Theorem INC_refl : forall E : Ens, INC E E.
Proof.
  intro E; destruct E as [n | a b | A f]; simpl.
  - reflexivity.
  - split; apply EQ_refl.
  - intros E H; exact H.
Qed.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
Proof.
  intros E E' E'' H1 H2. destruct E as [n | a b | A f].
  - (* an atom: [H1 : EQ (atom n) E'], so [E'] is that atom *)
    destruct E' as [m | c d | B g]; try (simpl in H1; contradiction).
    apply EQ_tran with (atom m); assumption.
  - destruct E' as [m | c d | B g]; try (simpl in H1; contradiction).
    apply EQ_tran with (pair c d); assumption.
  - intros E0 HE0. apply H1 in HE0.
    destruct E' as [m | c d | B g]; try (simpl in HE0; contradiction).
    apply H2; exact HE0.
Qed.


Theorem INC_sound_left :
 forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
Proof.
  intros E E' E'' HE HI. destruct E as [n | a b | A f].
  - destruct E' as [m | c d | B g]; try (simpl in HE; contradiction).
    apply EQ_tran with (atom n); [ apply EQ_sym; exact HE | exact HI ].
  - destruct E' as [m | c d | B g]; try (simpl in HE; contradiction).
    apply EQ_tran with (pair a b); [ apply EQ_sym; exact HE | exact HI ].
  - destruct E' as [m | c d | B g]; try (simpl in HE; contradiction).
    intros E0 HE0. apply HI. apply IN_sound_right with (sup B g); [ apply EQ_sym; exact HE | exact HE0 ].
Qed.

Theorem INC_sound_right :
 forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
Proof.
  intros E E' E'' HE HI. destruct E as [n | a b | A f].
  - apply EQ_tran with E'; assumption.
  - apply EQ_tran with E'; assumption.
  - intros E0 HE0. apply IN_sound_right with E'; [ exact HE | apply HI; exact HE0 ].
Qed.

(* Introduction and elimination of inclusion, and extensionality for sets. *)

Theorem INC_intro :
 forall E1 E2 : Ens, is_set E1 -> (forall E : Ens, IN E E1 -> IN E E2) -> INC E1 E2.
Proof. intros E1 E2 Hs H. destruct E1 as [n | a b | A f]; try contradiction. exact H. Qed.

Theorem INC_elim :
 forall E1 E2 : Ens, INC E1 E2 -> forall E : Ens, IN E E1 -> IN E E2.
Proof.
  intros E1 E2 H E HE. destruct E1 as [n | a b | A f]; simpl in HE; try contradiction.
  apply H; exact HE.
Qed.

Theorem EQ_ext :
 forall E E' : Ens, is_set E -> is_set E' ->
 (forall x : Ens, IN x E <-> IN x E') -> EQ E E'.
Proof.
  intros E E' Hs Hs' H. apply INC_EQ; apply INC_intro; try assumption;
    intros x Hx; apply H; exact Hx.
Qed.

(* A set included in a non-set has no members. *)

Theorem INC_not_set_empty :
 forall (A : Type) (f : A -> Ens) (E' : Ens),
 INC (sup A f) E' -> ~ is_set E' -> forall E : Ens, IN E (sup A f) -> False.
Proof.
  intros A f E' HI Hns E HE. apply HI in HE. apply Hns. apply IN_is_set with E. exact HE.
Qed.
