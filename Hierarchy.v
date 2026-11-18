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
(* https://github.com/rocq-archive/zfc): Replaced the duplicated core *)
(* definitions ([Ens'], [EQ'], [Power'], ...) with the                *)
(* universe-polymorphic definitions of [Sets.v]/[Axioms.v]            *)
(* instantiated at a lower universe; [inj] extended to atoms and      *)
(* pairs; [Big] renamed [U0]; added closure lemmas for [U0] (pairs,   *)
(* atoms, [Vide], [Paire], [Sing], [Union], [Omega]); added the [U1]  *)
(* level.                                                             *)
(*--------------------------------------------------------------------*)
(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(* This is a step towards inaccessible cardinals.                       *)
(* We define the "small" sets and collect them into a single set [U0]. *)
(*                                                                       *)
(* The original development duplicated the core definitions here         *)
(* ([Ens'], [EXType'], [prod_t'], [depprod''], [EQ'], [Power']) because  *)
(* Coq did not support universe polymorphism.  It now does: [Ens], [EQ], *)
(* [Power] (and [depprod]) in [Sets.v]/[Axioms.v] are universe           *)
(* polymorphic, so the small sets are simply those same definitions      *)
(* instantiated at a strictly lower universe — no duplication required.  *)
(*                                                                       *)
(* With the sorted [Ens] (atoms, pairs, sets) the injection [inj] keeps   *)
(* atoms and rebuilds pairs componentwise; atoms and pairs of small       *)
(* values are small, and the closure facts get vacuous non-set cases.    *)
Require Import Sets.
Require Import Axioms.
Require Import Omega.
(* Two universe levels.  The [small] sets sit strictly below the [big]   *)
(* universe.  [small < big] is exactly what makes [U0] "inaccessible"    *)
(* from below: it is not itself a small set.  [big] is retained for the   *)
(* [U1] tower below ([U1] collects the [Ens@{big}] sets).                 *)
Universe small big.
Constraint small < big.
Set Universe Polymorphism.
Unset Universe Minimization ToSet.
(* The small sets: [Ens] at the lower universe. *)
Monomorphic Definition Ens' : Type := Ens@{small}.

(* Small sets inject into the target universe [j], rebuilding each node at *)
(* [j].  [inj] is polymorphic in [j]; every downstream lemma quantifies    *)
(* over the same [j] so that [inj@{j}] and [U0@{j}] share one instance.    *)
Fixpoint inj@{j +} (e : Ens') : Ens@{j} :=
  match e with
  | atom n => atom@{j} n
  | pair a b => pair@{j} (inj a) (inj b)
  | sup A f => sup@{j} A (fun a => inj (f a))
  end.

Theorem inj_sound@{j +} :
 forall E1 E2 : Ens', EQ E1 E2 -> EQ (inj@{j} E1) (inj@{j} E2).
Proof.
  induction E1 as [n | a IHa b IHb | A f IH]; intros E2;
    destruct E2 as [m | c d | B g]; simpl; intros H; try contradiction.
  - exact H.
  - destruct H as [Ha Hb]. split; [ apply IHa | apply IHb ]; assumption.
  - destruct H as [H1 H2]. split.
    + intro x. destruct (H1 x) as [y Hy]. exists y. apply IH. exact Hy.
    + intro y. destruct (H2 y) as [x Hx]. exists x. apply IH. exact Hx.
Qed.

(* [inj] of the small empty set is the empty set. *)
Theorem inj_Vide@{j +} : EQ (inj@{j} Vide) Vide.
Proof. simpl. split; intro x; destruct x. Qed.

(* The injection commutes with power sets.  Here the left [Power] is at   *)
(* the small universe and the right one at [j] — the same polymorphic     *)
(* [Power], replacing the former [Power'].                                 *)
Theorem Power_sound_inj@{j +} :
 forall E : Ens', EQ (inj@{j} (Power E)) (Power (inj@{j} E)).
Proof.
  intro E. destruct E as [n | a b | A f].
  - apply inj_Vide.
  - apply inj_Vide.
  - simpl. split.
    + intro P. exists P. split; intro c; destruct c as [a p];
        exists (dep_i A (fun a0 : A => P a0) a p); simpl; apply EQ_refl.
    + intro P. exists P. split; intro c; destruct c as [a p];
        exists (dep_i A (fun a0 : A => P a0) a p); simpl; apply EQ_refl.
Qed.


(* The set of small sets, at the target universe [j].            *)

Definition U0@{j +} : Ens@{j} := sup Ens' inj@{j}.

Theorem U0_is_big@{j +} : forall E : Ens', IN (inj@{j} E) U0@{j}.
Proof. intro E. unfold U0. simpl. exists E. apply EQ_refl. Qed.

Theorem IN_U0_small@{j +} :
 forall E : Ens@{j}, IN E U0@{j} -> exists E' : Ens', EQ E (inj@{j} E').
Proof. unfold U0. simpl. intros E H. destruct H as [E' HE']. exists E'. exact HE'. Qed.


Theorem IN_small_small@{j +} :
 forall (E : Ens@{j}) (E' : Ens'),
 IN E (inj@{j} E') -> exists E1 : Ens', EQ E (inj@{j} E1).
Proof.
  intros E E' H. destruct E' as [n | a b | A' f']; simpl in H; try contradiction.
  destruct H as [a' e']. exists (f' a'). exact e'.
Qed.



Theorem U0_closed_for_power@{j +} :
 forall E : Ens@{j}, IN E U0@{j} -> IN (Power E) U0@{j}.
Proof.
  intros E H. destruct (IN_U0_small E H) as [E' HE'].
  unfold U0. simpl. exists (Power E').
  apply EQ_tran with (Power (inj@{j} E')).
  - apply Power_sound; assumption.
  - apply EQ_sym; apply Power_sound_inj.
Qed.


(* ------------------------------------------------------------------- *)
(* Further closure properties of [U0]: it behaves like a Grothendieck *)
(* universe.  For each set-former we exhibit a "small" witness (built   *)
(* at the [small] universe from the polymorphic primitives [sup],       *)
(* [depprod], [pi1], [pi2]) and show that [inj] commutes with the       *)
(* operation, mirroring [Power_sound_inj].                              *)
(* ------------------------------------------------------------------- *)

(* Atoms are small, and pairs of small values are small. *)
Theorem U0_contains_atom@{j +} : forall n : nat, IN (atom n : Ens@{j}) U0@{j}.
Proof. intro n. unfold U0. simpl. exists (atom n). simpl. reflexivity. Qed.

Theorem U0_closed_pair@{j +} :
 forall E E' : Ens@{j}, IN E U0@{j} -> IN E' U0@{j} -> IN (pair E E') U0@{j}.
Proof.
  intros E E' HE HE'.
  destruct (IN_U0_small E HE) as [A' HA].
  destruct (IN_U0_small E' HE') as [B' HB].
  unfold U0. simpl. exists (pair A' B'). simpl. split; assumption.
Qed.

(* The components of a small pair are small. *)
Theorem IN_U0_pair_inv@{j +} :
 forall E E' : Ens@{j}, IN (pair E E') U0@{j} -> IN E U0@{j} /\ IN E' U0@{j}.
Proof.
  intros E E' H. destruct (IN_U0_small _ H) as [P HP].
  destruct P as [n | a b | A f]; simpl in HP; try contradiction.
  destruct HP as [Ha Hb]. split.
  - apply IN_sound_left with (inj@{j} a); [ apply EQ_sym; exact Ha | apply U0_is_big ].
  - apply IN_sound_left with (inj@{j} b); [ apply EQ_sym; exact Hb | apply U0_is_big ].
Qed.

(* The empty set is small. *)
Definition Vide_s : Ens' := sup F (fun f : F => match f return Ens@{small} with
                                                end).

Theorem inj_Vide_s@{j +} : EQ (inj@{j} Vide_s) Vide.
Proof. unfold Vide_s, Vide. simpl. split; intro x; destruct x. Qed.

Theorem U0_contains_Vide@{j +} : IN (Vide : Ens@{j}) U0@{j}.
Proof.
  apply IN_sound_left with (inj@{j} Vide_s).
  - apply inj_Vide_s.
  - apply U0_is_big.
Qed.

(* Small (unordered) pairing: [bool : Set] is below every universe. *)
Definition Paire_s (A B : Ens') : Ens' :=
  sup bool (fun b : bool => if b then A else B).

Theorem inj_Paire_s@{j +} :
 forall A B : Ens', EQ (inj@{j} (Paire_s A B)) (Paire (inj@{j} A) (inj@{j} B)).
Proof.
  intros A B. unfold Paire_s, Paire. simpl. split; intro b; exists b; destruct b; simpl; apply EQ_refl.
Qed.

Theorem U0_closed_Paire@{j +} :
 forall E E' : Ens@{j}, IN E U0@{j} -> IN E' U0@{j} -> IN (Paire E E') U0@{j}.
Proof.
  intros E E' HE HE'.
  destruct (IN_U0_small E HE) as [A' HA].
  destruct (IN_U0_small E' HE') as [B' HB].
  apply IN_sound_left with (inj@{j} (Paire_s A' B')).
  - apply EQ_tran with (Paire (inj@{j} A') (inj@{j} B')).
    + apply inj_Paire_s.
    + apply EQ_tran with (Paire E (inj@{j} B')).
      * apply Paire_sound_left; apply EQ_sym; assumption.
      * apply Paire_sound_right; apply EQ_sym; assumption.
  - apply U0_is_big.
Qed.

Theorem U0_closed_Sing@{j +} :
 forall E : Ens@{j}, IN E U0@{j} -> IN (Sing E) U0@{j}.
Proof. intros E HE. unfold Sing. apply U0_closed_Paire; assumption. Qed.

(* [inj] commutes with the base type and value function of each node:
   [pi1 (inj e) = pi1 e] (definitionally, once [e] is a [sup]) and
   [pi2 (inj e) b' = inj (pi2 e b)] at the matching index. *)
Lemma pi_inj_l@{j +} :
 forall (e : Ens') (b : pi1 e),
 EXType (pi1 (inj@{j} e)) (fun b' => EQ (inj@{j} (pi2 e b)) (pi2 (inj@{j} e) b')).
Proof.
  intros e b. destruct e as [n | a c | B g]; simpl in b; try (destruct b).
  simpl. exists b. apply EQ_refl.
Qed.

Lemma pi_inj_r@{j +} :
 forall (e : Ens') (b' : pi1 (inj@{j} e)),
 EXType (pi1 e) (fun b => EQ (inj@{j} (pi2 e b)) (pi2 (inj@{j} e) b')).
Proof.
  intros e b'. destruct e as [n | a c | B g]; simpl in b'; try (destruct b').
  simpl. exists b'. apply EQ_refl.
Qed.

(* Small union: the same construction as [Union], performed at the
   [small] universe with the polymorphic [pi1]/[pi2]/[depprod]. *)
Definition Union_s (E : Ens') : Ens' :=
  match E with
  | sup A f =>
      sup (depprod A (fun x : A => pi1 (f x)))
          (fun c : depprod A (fun x : A => pi1 (f x)) =>
           match c with
           | dep_i a b => pi2 (f a) b
           end)
  | _ => Vide_s
  end.

Theorem inj_Union_s@{j +} :
 forall E : Ens', EQ (inj@{j} (Union_s E)) (Union (inj@{j} E)).
Proof.
  intro E. destruct E as [n | a b | A f].
  - apply inj_Vide_s.
  - apply inj_Vide_s.
  - simpl. split.
    + intro c1. destruct c1 as [a b].
      destruct (pi_inj_l (f a) b) as [b' Hb'].
      exists (dep_i A (fun x : A => pi1 (inj@{j} (f x))) a b'). exact Hb'.
    + intro c2. destruct c2 as [a b'].
      destruct (pi_inj_r (f a) b') as [b Hb].
      exists (dep_i A (fun x : A => pi1 (f x)) a b). exact Hb.
Qed.

Theorem U0_closed_Union@{j +} :
 forall E : Ens@{j}, IN E U0@{j} -> IN (Union E) U0@{j}.
Proof.
  intros E HE. destruct (IN_U0_small E HE) as [E' HE'].
  apply IN_sound_left with (inj@{j} (Union_s E')).
  - apply EQ_tran with (Union (inj@{j} E')).
    + apply inj_Union_s.
    + apply Union_sound; apply EQ_sym; assumption.
  - apply U0_is_big.
Qed.


(* ------------------------------------------------------------------- *)
(* [Omega] is small: it is the image of the small type [nat] under the *)
(* atoms, so it is built at the [small] universe and [inj] commutes    *)
(* with it.  This is the closure-under-[ω] clause of inaccessibility.   *)
(* ------------------------------------------------------------------- *)

(* [Class_succ] respects extensional equality (its components do). *)
Theorem Class_succ_sound@{j +} :
 forall A B : Ens@{j}, EQ A B -> EQ (Class_succ A) (Class_succ B).
Proof.
  intros A B H. unfold Class_succ. apply Union_sound.
  apply EQ_tran with (Paire B (Sing A)).
  - apply Paire_sound_left; assumption.
  - apply Paire_sound_right; apply Sing_sound; assumption.
Qed.

(* Small singleton and successor, built from the small witnesses. *)
Definition Sing_s (E : Ens') : Ens' := Paire_s E E.

Theorem inj_Sing_s@{j +} :
 forall E : Ens', EQ (inj@{j} (Sing_s E)) (Sing (inj@{j} E)).
Proof. intro E. unfold Sing_s, Sing. apply inj_Paire_s. Qed.

Definition Class_succ_s (E : Ens') : Ens' := Union_s (Paire_s E (Sing_s E)).

Theorem inj_Class_succ_s@{j +} :
 forall E : Ens', EQ (inj@{j} (Class_succ_s E)) (Class_succ (inj@{j} E)).
Proof.
  intro E. unfold Class_succ_s, Class_succ.
  apply EQ_tran with (Union (inj@{j} (Paire_s E (Sing_s E)))).
  - apply inj_Union_s.
  - apply Union_sound.
    apply EQ_tran with (Paire (inj@{j} E) (inj@{j} (Sing_s E))).
    + apply inj_Paire_s.
    + apply Paire_sound_right; apply inj_Sing_s.
Qed.

(* The small numerals: the same atoms. *)
Definition Nat_s (n : nat) : Ens' := atom n.

Theorem inj_Nat_s@{j +} : forall n : nat, EQ (inj@{j} (Nat_s n)) (Nat n).
Proof. intro n. simpl. reflexivity. Qed.

(* The small [ω] and the proof it injects to [Omega]. *)
Definition Omega_s : Ens' := sup nat Nat_s.

Theorem inj_Omega_s@{j +} : EQ (inj@{j} Omega_s) Omega.
Proof.
  unfold Omega_s, Omega. simpl. split; intro n; exists n; apply inj_Nat_s.
Qed.

Theorem U0_contains_Omega@{j +} : IN (Omega : Ens@{j}) U0@{j}.
Proof.
  apply IN_sound_left with (inj@{j} Omega_s).
  - apply inj_Omega_s.
  - apply U0_is_big.
Qed.

(* ================================================================== *)
(** * A second Grothendieck universe [U1] above [U0], with [U0 ∈ U1] *)
(*                                                                     *)
(*  [huge] sits strictly above [big], so the [big] sets — [U0] among   *)
(*  them — can be collected into a single set [U1 : Ens@{huge}], the     *)
(*  next universe of the tower [small < big < huge].                     *)
(*                                                                     *)
(*  Membership is [Sets.IN] and transport uses [Sets.EQ_tran] /        *)
(*  [Sets.IN_sound_right]: [Sets.v] is universe polymorphic from [IN]  *)
(*  on, so they apply at every level of the tower.                     *)
(* ================================================================== *)

(* Back to monomorphic universes for the [U1] tower: [huge] and the
   [injp]/[Univ] machinery below manage their levels explicitly. *)
Unset Universe Polymorphism.

Universe huge.
Constraint big < huge.

(* The polymorphic injection and universe, exactly as [inj]/[U0] but at two
   floating levels [i < j].  [injp] rebuilds each node at level [j]. *)
Polymorphic Fixpoint injp@{i j} (e : Ens@{i}) : Ens@{j} :=
  match e with
  | atom n => atom@{j} n
  | pair a b => pair@{j} (injp a) (injp b)
  | sup A f => sup@{j} A (fun a => injp (f a))
  end.

Polymorphic Theorem injp_id@{i j +} : forall E : Ens@{i}, EQ E (injp@{i j} E).
Proof.
  induction E as [n | a IHa b IHb | A f IH]; simpl.
  - reflexivity.
  - split; assumption.
  - split; intro a; exists a; apply IH.
Qed.

(* Instance irrelevance for [inj]: rebuilding [inj@{j} E] one level up with
   [injp] yields (a set equal to) [inj@{k} E].  [inj]/[U0] are non-cumulative
   polymorphic definitions, so their instances are not convertible; this lemma
   bridges a [j]-level image to a [k]-level one, which is what lets the [ulib]
   quotient collect the [big]-level [U0]. *)
Polymorphic Theorem injp_inj@{j k +} :
 forall E : Ens', EQ (injp@{j k} (inj@{j} E)) (inj@{k} E).
Proof.
  induction E as [n | a IHa b IHb | A f IH]; simpl.
  - reflexivity.
  - split; assumption.
  - split; intro a; exists a; apply IH.
Qed.

(* Consequently [injp] carries [U0@{j}] to [U0@{k}]. *)
Polymorphic Theorem injp_U0@{j k +} : EQ (injp@{j k} U0@{j}) U0@{k}.
Proof. unfold U0. simpl. split; intro E'; exists E'; apply injp_inj. Qed.

(* The set of all [Ens@{i}] sets, one level up at [Ens@{j}]. *)
Polymorphic Definition Univ@{i j} : Ens@{j} := sup Ens@{i} injp@{i j}.

Polymorphic Theorem IN_Univ_small@{i j +} :
 forall E : Ens@{j}, IN E Univ@{i j} ->
 exists E' : Ens@{i}, EQ E (injp@{i j} E').
Proof. unfold Univ, IN. intros E H. destruct H as [E' HE']. exists E'. exact HE'. Qed.

Polymorphic Theorem IN_injp_small@{i j +} :
 forall (E : Ens@{j}) (E' : Ens@{i}),
 IN E (injp@{i j} E') -> exists E1 : Ens@{i}, EQ E (injp@{i j} E1).
Proof.
  intros E E' H. destruct E' as [n | a b | A' f']; simpl in H; try contradiction.
  destruct H as [a' e']. exists (f' a'). exact e'.
Qed.

(* Every [Ens@{i}] set is a member of [Univ@{i j}] ([injp_id] makes [E] its
   own witness).  In particular each stage of the tower contains the one
   below it. *)
Polymorphic Theorem Univ_contains@{i j +} : forall E : Ens@{i}, IN E Univ@{i j}.
Proof. intro E. unfold Univ, IN. exists E. apply injp_id. Qed.

(* [Univ] is transitive. *)
Polymorphic Theorem Univ_transitive@{i j +} :
 forall X Y : Ens@{j}, IN X Y -> IN Y Univ@{i j} -> IN X Univ@{i j}.
Proof.
  intros X Y HXY HYU.
  destruct (IN_Univ_small Y HYU) as [F' HF].
  destruct (IN_injp_small X F' (IN_sound_right _ _ _ HF HXY)) as [E1 HE1].
  unfold Univ, IN. exists E1. exact HE1.
Qed.

(* The set of big sets, and the key fact: [U0] is one of its members. *)
Definition U1 : Ens@{huge} := Univ@{big huge}.

Theorem U0_in_U1 : IN U0 U1.
Proof. exact (Univ_contains U0). Qed.

Theorem U1_transitive :
 forall X Y : Ens@{huge}, IN X Y -> IN Y U1 -> IN X U1.
Proof. exact Univ_transitive. Qed.

(* ------------------------------------------------------------------- *)
(* [injp] commutes with the set-formers, exactly as [inj] does one      *)
(* level down ([Power_sound_inj], [inj_Paire_s], [inj_Union_s]).  Since  *)
(* [injp] rebuilds each node at level [j] without changing its index     *)
(* type, [Power]/[Paire]/[pair] are near-definitional and [Union] needs  *)
(* the [pi]-helpers.  These are what make [Univ] — which contains every  *)
(* [Ens@{i}] set ([Univ_contains]) — closed under those formers, and     *)
(* hence what the [lib] [U1] Grothendieck toolkit lifts across the        *)
(* quotient.                                                              *)
(* ------------------------------------------------------------------- *)

Polymorphic Theorem injp_Vide@{i j +} : EQ (injp@{i j} Vide) Vide.
Proof. simpl. split; intro x; destruct x. Qed.

Polymorphic Theorem injp_pair@{i j +} :
 forall A B : Ens@{i},
 EQ (injp@{i j} (pair A B)) (pair (injp@{i j} A) (injp@{i j} B)).
Proof. intros A B. simpl. split; apply EQ_refl. Qed.

Polymorphic Theorem injp_Paire@{i j +} :
 forall A B : Ens@{i},
 EQ (injp@{i j} (Paire A B)) (Paire (injp@{i j} A) (injp@{i j} B)).
Proof.
  intros A B. unfold Paire. simpl. split; intro b; exists b; destruct b; simpl; apply EQ_refl.
Qed.

Polymorphic Theorem injp_Power@{i j +} :
 forall E : Ens@{i}, EQ (injp@{i j} (Power E)) (Power (injp@{i j} E)).
Proof.
  intro E. destruct E as [n | a b | A f].
  - apply injp_Vide.
  - apply injp_Vide.
  - simpl. split.
    + intro P. exists P. split; intro c; destruct c as [a p];
        exists (dep_i A (fun a0 : A => P a0) a p); simpl; apply EQ_refl.
    + intro P. exists P. split; intro c; destruct c as [a p];
        exists (dep_i A (fun a0 : A => P a0) a p); simpl; apply EQ_refl.
Qed.

Polymorphic Lemma injp_pi_l@{i j +} :
 forall (e : Ens@{i}) (b : pi1 e),
 EXType (pi1 (injp@{i j} e))
   (fun b' => EQ (injp@{i j} (pi2 e b)) (pi2 (injp@{i j} e) b')).
Proof.
  intros e b. destruct e as [n | a c | B g]; simpl in b; try (destruct b).
  simpl. exists b. apply EQ_refl.
Qed.

Polymorphic Lemma injp_pi_r@{i j +} :
 forall (e : Ens@{i}) (b' : pi1 (injp@{i j} e)),
 EXType (pi1 e)
   (fun b => EQ (injp@{i j} (pi2 e b)) (pi2 (injp@{i j} e) b')).
Proof.
  intros e b'. destruct e as [n | a c | B g]; simpl in b'; try (destruct b').
  simpl. exists b'. apply EQ_refl.
Qed.

Polymorphic Theorem injp_Union@{i j +} :
 forall E : Ens@{i}, EQ (injp@{i j} (Union E)) (Union (injp@{i j} E)).
Proof.
  intro E. destruct E as [n | a b | A f].
  - apply injp_Vide.
  - apply injp_Vide.
  - simpl. split.
    + intro c1. destruct c1 as [a b].
      destruct (injp_pi_l (f a) b) as [b' Hb'].
      exists (dep_i A (fun x : A => pi1 (injp@{i j} (f x))) a b'). exact Hb'.
    + intro c2. destruct c2 as [a b'].
      destruct (injp_pi_r (f a) b') as [b Hb].
      exists (dep_i A (fun x : A => pi1 (f x)) a b). exact Hb.
Qed.

(* [Univ] is closed under the set-formers.  Each proof shrinks the [j]-level
   argument to its [i]-level preimage ([IN_Univ_small]), applies the former
   at level [i], and re-injects with the [injp_*] commutation. *)

Polymorphic Theorem Univ_closed_Power@{i j +} :
 forall E : Ens@{j}, IN E Univ@{i j} -> IN (Power E) Univ@{i j}.
Proof.
  intros E HE. destruct (IN_Univ_small E HE) as [E' HE'].
  unfold Univ, IN. exists (Power E').
  apply EQ_tran with (Power (injp@{i j} E')).
  - apply Power_sound; exact HE'.
  - apply EQ_sym; apply injp_Power.
Qed.

Polymorphic Theorem Univ_closed_Union@{i j +} :
 forall E : Ens@{j}, IN E Univ@{i j} -> IN (Union E) Univ@{i j}.
Proof.
  intros E HE. destruct (IN_Univ_small E HE) as [E' HE'].
  unfold Univ, IN. exists (Union E').
  apply EQ_tran with (Union (injp@{i j} E')).
  - apply Union_sound; exact HE'.
  - apply EQ_sym; apply injp_Union.
Qed.

Polymorphic Theorem Univ_closed_Paire@{i j +} :
 forall E E' : Ens@{j},
 IN E Univ@{i j} -> IN E' Univ@{i j} -> IN (Paire E E') Univ@{i j}.
Proof.
  intros E E' HE HE'.
  destruct (IN_Univ_small E HE) as [A' HA].
  destruct (IN_Univ_small E' HE') as [B' HB].
  unfold Univ, IN. exists (Paire A' B').
  apply EQ_tran with (Paire (injp@{i j} A') (injp@{i j} B')).
  - apply EQ_tran with (Paire E (injp@{i j} B')).
    + apply Paire_sound_right; exact HB.
    + apply Paire_sound_left; exact HA.
  - apply EQ_sym; apply injp_Paire.
Qed.

Polymorphic Theorem Univ_closed_pair@{i j +} :
 forall E E' : Ens@{j},
 IN E Univ@{i j} -> IN E' Univ@{i j} -> IN (pair E E') Univ@{i j}.
Proof.
  intros E E' HE HE'.
  destruct (IN_Univ_small E HE) as [A' HA].
  destruct (IN_Univ_small E' HE') as [B' HB].
  unfold Univ, IN. exists (pair A' B'). simpl. split; assumption.
Qed.

Polymorphic Theorem Univ_contains_atom@{i j +} : forall n : nat, IN (atom n : Ens@{j}) Univ@{i j}.
Proof. intro n. unfold Univ, IN. exists (atom n). simpl. reflexivity. Qed.

Polymorphic Theorem IN_Univ_pair_inv@{i j +} :
 forall E E' : Ens@{j},
 IN (pair E E') Univ@{i j} -> IN E Univ@{i j} /\ IN E' Univ@{i j}.
Proof.
  intros E E' H. destruct (IN_Univ_small _ H) as [P HP].
  destruct P as [n | a b | A f]; simpl in HP; try contradiction.
  destruct HP as [Ha Hb]. split.
  - unfold Univ, IN. exists a. exact Ha.
  - unfold Univ, IN. exists b. exact Hb.
Qed.
