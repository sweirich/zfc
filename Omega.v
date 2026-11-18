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
(* https://github.com/rocq-archive/zfc): [Nat n] is now the primitive *)
(* [atom n] of [Sets.v] instead of a von Neumann numeral; proofs      *)
(* adapted; made universe polymorphic; added [Nat_inj],               *)
(* [Nat_not_set], [Omega_is_set] and related lemmas; removed          *)
(* [Omega_EQ_Union] (false once numerals are atoms) and [Vee] (now in *)
(* [Ordinal_theory.v]).                                               *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* The set of natural numbers.

   A numeral is now the atom [Nat n := atom n] of [Sets.v] rather than a
   von Neumann ordinal, and [Omega] is the set of all atoms.  Numerals are
   therefore memberless and disjoint from every set; [Nat] is injective by
   the atom clause of [EQ].  The ordinal successor [Class_succ] is kept as
   an operation on sets, no longer related to [Nat]. *)

Require Import Sets.
Require Import Axioms.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition Class_succ (E : Ens) := Union (Paire E (Sing E)).

Definition Nat (n : nat) : Ens := atom n.

Definition Omega : Ens := sup nat Nat.

Theorem IN_Class_succ : forall E : Ens, IN E (Class_succ E).
Proof.
  intro E. unfold Class_succ. apply IN_Union with (Sing E).
  - apply IN_Paire_right.
  - apply IN_Sing.
Qed.

(* A *set* is included in its successor. *)
Theorem INC_Class_succ : forall E : Ens, is_set E -> INC E (Class_succ E).
Proof.
  intros E Hs. unfold Class_succ. apply IN_INC_Union; [ exact Hs | apply IN_Paire_left ].
Qed.

Hint Resolve IN_Class_succ INC_Class_succ: zfc.


Theorem IN_Class_succ_or :
 forall E E' : Ens, IN E' (Class_succ E) -> EQ E E' \/ IN E' E.
Proof.
  intros E E' i. unfold Class_succ in i.
  destruct (Union_IN (Paire E (Sing E)) E' i) as [E1 [i1 i2]].
  destruct (Paire_IN E (Sing E) E1 i1) as [e | e].
  - right. apply IN_sound_right with E1; assumption.
  - left. apply EQ_sym. apply IN_Sing_EQ. apply IN_sound_right with E1; assumption.
Qed.


Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
Proof.
  induction E as [n | a IHa b IHb | A f IH]; intro i.
  - destruct i.
  - destruct i.
  - cut False; [ intro Hf; destruct Hf | ].
    destruct i as [a e].
    destruct (IH a (IN_sound_right _ _ _ e (EXTypei _ _ a (EQ_refl (f a))))).
Qed.


Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
Proof. intro n. unfold Omega, IN. exists n. apply EQ_refl. Qed.
Hint Resolve Nat_IN_Omega: zfc.


Theorem IN_Omega_EXType :
 forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
Proof.
  intros E H. destruct H as [n e]. exists n. apply EQ_sym. exact e.
Qed.

(* A numeral has no members. *)
Theorem IN_Nat : forall (n : nat) (E : Ens), IN E (Nat n) -> False.
Proof. intros n E H. exact H. Qed.

Theorem IN_Nat_EXType :
 forall (n : nat) (E : Ens),
 IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
Proof. intros n E H. destruct H. Qed.

(* Numerals are injective, and no numeral is a set. *)
Theorem Nat_inj : forall k1 k2 : nat, EQ (Nat k1) (Nat k2) -> k1 = k2.
Proof. intros k1 k2 H. exact H. Qed.

Theorem Nat_not_set : forall n : nat, is_set (Nat n) -> False.
Proof. intros n H. exact H. Qed.

Theorem Omega_is_set : is_set Omega.
Proof. exact I. Qed.
