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
(* https://github.com/rocq-archive/zfc): [Couple] is now the          *)
(* primitive [pair] of [Sets.v] instead of the encoding [Paire (Sing  *)
(* E) (Paire Vide (Sing E'))]; proofs adapted; made universe          *)
(* polymorphic; added lemmas that couples have no members and that    *)
(* products contain only couples.                                     *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* The ordered pair and the cartesian product.

   The ordered pair [Couple] is now the primitive [pair] of [Sets.v] (the
   original encoded it as [Paire (Sing E) (Paire Vide (Sing E'))]), so its
   injectivity is the [pair] clause of [EQ] and it is disjoint from every
   set and every atom.  [Prod] is unchanged: the set of pairs of members. *)

Require Import Sets.
Require Import Axioms.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.


Definition Couple (E E' : Ens) : Ens := pair E E'.

Theorem Couple_is_pair : forall E E' : Ens, is_pair (Couple E E').
Proof. intros; exact I. Qed.

Theorem Couple_inj_left :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A B.
Proof. intros A A' B B' H. destruct H as [H1 _]. exact H1. Qed.

Theorem Couple_inj_right :
 forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A' B'.
Proof. intros A A' B B' H. destruct H as [_ H2]. exact H2. Qed.

Theorem Couple_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Couple A B) (Couple A' B).
Proof. intros A A' B H. simpl. split; [ exact H | apply EQ_refl ]. Qed.

Theorem Couple_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Couple A B) (Couple A B').
Proof. intros A B B' H. simpl. split; [ apply EQ_refl | exact H ]. Qed.

(* A couple has no members and is no set. *)

Theorem IN_Couple : forall E A B : Ens, IN E (Couple A B) -> False.
Proof. intros E A B H. exact H. Qed.

Theorem Couple_not_set : forall A B : Ens, is_set (Couple A B) -> False.
Proof. intros A B H. exact H. Qed.


(* Here we cheat. It is easier to define the cartesian product using    *)
(* the type theoretical product, i.e. we here use non set-theoretical   *)
(* constructions. We could however use the usual definitions.           *)


Definition Prod (E E' : Ens) : Ens :=
  match E, E' with
  | sup A f, sup A' f' =>
      sup _
        (fun c : prod_t A A' =>
         match c with
         | pair_t a a' => Couple (f a) (f' a')
         end)
  | _, _ => Vide
  end.

Theorem Prod_is_set : forall E E' : Ens, is_set (Prod E E').
Proof. intros E E'; destruct E; destruct E'; exact I. Qed.

Hint Resolve Paire_sound_left Paire_sound_right: zfc.

Theorem Couple_IN_Prod :
 forall E1 E2 E1' E2' : Ens,
 IN E1' E1 -> IN E2' E2 -> IN (Couple E1' E2') (Prod E1 E2).
Proof.
  intros E1 E2 E1' E2' i1 i2.
  destruct E1 as [n | a b | A1 f1]; simpl in i1; try contradiction.
  destruct E2 as [m | c d | A2 f2]; simpl in i2; try contradiction.
  destruct i1 as [x e1]. destruct i2 as [x0 e2].
  simpl. exists (pair_t _ _ x x0). simpl. split; assumption.
Qed.


Theorem Couple_Prod_IN :
 forall E1 E2 E1' E2' : Ens,
 IN (Couple E1' E2') (Prod E1 E2) -> IN E1' E1 /\ IN E2' E2.
Proof.
  intros E1 E2 E1' E2' i.
  destruct E1 as [n | a b | A1 f1]; destruct E2 as [m | c d | A2 f2]; simpl in i;
    try (solve [ destruct i as [x _]; destruct x ]).
  destruct i as [c e]. destruct c as [a1 a2]. simpl in e. destruct e as [e1 e2].
  split; [ exists a1; exact e1 | exists a2; exact e2 ].
Qed.



Theorem IN_Prod_EXType :
 forall E E' E'' : Ens,
 IN E'' (Prod E E') ->
 EXType _ (fun A : Ens => EXType _ (fun B : Ens => EQ (Couple A B) E'')).
Proof.
  intros E E' E'' i.
  destruct E as [n | a b | A f]; destruct E' as [m | c d | A' f']; simpl in i;
    try (solve [ destruct i as [x _]; destruct x ]).
  destruct i as [c e]. destruct c as [a a'].
  exists (f a). exists (f' a'). apply EQ_sym. exact e.
Qed.

(* Every member of a product is a couple. *)
Theorem IN_Prod_is_pair : forall E E' E'' : Ens, IN E'' (Prod E E') -> is_pair E''.
Proof.
  intros E E' E'' i. destruct (IN_Prod_EXType E E' E'' i) as [A [B e]].
  apply EQ_is_pair with (Couple A B); [ exact e | exact I ].
Qed.
