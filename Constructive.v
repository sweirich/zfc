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
(* Polymorphism]. Adapted to the sorted [Ens] of [Sets.v]: [EQC],     *)
(* [CIN] and [CINC] get atom and pair cases mirroring [EQ], [IN] and  *)
(* [INC]; [tout_vide_est_VideC] and [CIN_CINC_Union] take an [is_set] *)
(* premise; added [CINC_intro], [CINC_elim] and [pi2_CIN]; proofs     *)
(* rewritten.                                                         *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* Peter Aczel's Encoding of CZF *)

(* Using the same definition "Ens" of sets, we can developp Peter Aczel's   *)
(* encoding of "Constructive Type Theory" (CZF).                            *)
(* It is basically a simillar developement, but this time, the propositions *)
(* are objects of type "Type", i.e. are on the same level (resp. above) the *)
(* sets. The advantage is that we can extract the constructive witness of an*)
(* existential proof. The drawbacks are:                                    *)
(*  - no definition of the powerset                                         *)
(*  - complicated difference between bounded and unbounded quantification   *)
(*  - excluded middle is now much more "dangerous"                          *)


Require Import Sets.
Require Import Axioms.

(* Universe polymorphic, matching the [zfc] core (see [Sets.v]). *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Adapted to the sorted [Ens] of [Sets.v], following [EQ]/[IN]/[INC]
   there: [EQC] compares two atoms by their numbers and two pairs
   componentwise, and is empty ([F]) across sorts; a non-set has no [CIN]
   members; [CINC] is kind-aware (an atom or a pair is included only in
   something [EQC] to itself).  [tout_vide_est_VideC] and [CIN_CINC_Union]
   take an [is_set] premise, as their [Axioms.v] counterparts do. *)

Fixpoint EQC (E1 E2 : Ens) {struct E1} : Type :=
  match E1, E2 with
  | atom n, atom m => n = m
  | pair a b, pair c d => prod_t (EQC a c) (EQC b d)
  | sup A f, sup B g =>
      prod_t (forall x : A, depprod _ (fun y : B => EQC (f x) (g y)))
             (forall y : B, depprod _ (fun x : A => EQC (f x) (g y)))
  | _, _ => F
  end.



(* APPARTENANCE *)

Definition CIN (E1 E2 : Ens) : Type :=
  match E2 with
  | sup A f => depprod _ (fun y : A => EQC E1 (f y))
  | _ => F
  end.



(* INCLUSION *)

Definition CINC (E1 E2 : Ens) : Type :=
  match E1 with
  | sup _ _ => forall E : Ens, CIN E E1 -> CIN E E2
  | _ => EQC E1 E2
  end.



(* EQ EST UNE RELATION D'EQUIVALENCE *)

Theorem EQC_refl : forall E : Ens, EQC E E.
Proof.
  induction E as [n | a IHa b IHb | A f IH]; simpl.
  - reflexivity.
  - constructor; assumption.
  - constructor; intro x; exists x; apply IH.
Qed.

Theorem EQC_tran : forall E1 E2 E3 : Ens, EQC E1 E2 -> EQC E2 E3 -> EQC E1 E3.
Proof.
  induction E1 as [n | a IHa b IHb | A f IH]; intros E2 E3;
    destruct E2 as [m | c d | B g]; destruct E3 as [k | e h | C j]; simpl;
    intros H1 H2; try solve [ destruct H1 | destruct H2 ].
  - rewrite H1; exact H2.
  - destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b].
    constructor; [ apply IHa with c | apply IHb with d ]; assumption.
  - destruct H1 as [H1 H1']; destruct H2 as [H2 H2']; constructor.
    + intro x. destruct (H1 x) as [y Hy]. destruct (H2 y) as [z Hz].
      exists z. apply IH with (g y); assumption.
    + intro z. destruct (H2' z) as [y Hy]. destruct (H1' y) as [x Hx].
      exists x. apply IH with (g y); assumption.
Qed.

Theorem EQC_sym : forall E1 E2 : Ens, EQC E1 E2 -> EQC E2 E1.
Proof.
  induction E1 as [n | a IHa b IHb | A f IH]; intros E2;
    destruct E2 as [m | c d | B g]; simpl; intros H; try solve [ destruct H ].
  - symmetry; exact H.
  - destruct H as [Ha Hb]. constructor; [ apply IHa | apply IHb ]; assumption.
  - destruct H as [H1 H2]. constructor.
    + intro y. destruct (H2 y) as [x Hx]. exists x. apply IH; exact Hx.
    + intro x. destruct (H1 x) as [y Hy]. exists y. apply IH; exact Hy.
Qed.

Theorem EQC_INC : forall E E' : Ens, EQC E E' -> CINC E E'.
Proof.
  intros E E' H. destruct E as [n | a b | A f]; simpl.
  - exact H.
  - exact H.
  - destruct E' as [m | c d | B g]; simpl in H; try solve [ destruct H ].
    destruct H as [H1 H2].
    intros E0 [x Hx]. destruct (H1 x) as [y Hy].
    exists y. apply EQC_tran with (f x); assumption.
Qed.

Hint Resolve EQC_sym EQC_refl EQC_INC: zfc.

Theorem CINC_EQC : forall E E' : Ens, CINC E E' -> CINC E' E -> EQC E E'.
Proof.
  intros E E' H1 H2. destruct E as [n | a b | A f].
  - exact H1.
  - exact H1.
  - destruct E' as [m | c d | B g]; simpl in H2; try solve [ destruct H2 ].
    simpl. constructor.
    + intro x. destruct (H1 (f x)) as [y Hy]; [ exists x; apply EQC_refl | ].
      exists y; exact Hy.
    + intro y. destruct (H2 (g y)) as [x Hx]; [ exists y; apply EQC_refl | ].
      exists x; apply EQC_sym; exact Hx.
Qed.

Hint Resolve CINC_EQC: zfc.

Theorem CINC_intro :
 forall E1 E2 : Ens, is_set E1 -> (forall E : Ens, CIN E E1 -> CIN E E2) -> CINC E1 E2.
Proof. intros E1 E2 s H. destruct E1; simpl in s; try contradiction. exact H. Qed.

Theorem CINC_elim :
 forall E1 E2 : Ens, CINC E1 E2 -> forall E : Ens, CIN E E1 -> CIN E E2.
Proof.
  intros E1 E2 H E HE. destruct E1 as [n | a b | A f]; simpl in HE; try solve [ destruct HE ].
  apply H; exact HE.
Qed.


Theorem CIN_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CIN E E'' -> CIN E' E''.
Proof.
  intros E E' E'' HE HIN. destruct E'' as [k | c d | A f]; simpl in *; try solve [ destruct HIN ].
  destruct HIN as [a Ha]. exists a.
  apply EQC_tran with E; [ apply EQC_sym; exact HE | exact Ha ].
Qed.

Theorem CIN_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CIN E E' -> CIN E E''.
Proof.
  intros E E' E'' HE HIN.
  destruct E' as [k | c d | A f]; simpl in HIN; try solve [ destruct HIN ].
  destruct E'' as [k' | c' d' | B g]; simpl in HE; try solve [ destruct HE ].
  destruct HE as [H1 H2]. destruct HIN as [a Ha].
  destruct (H1 a) as [b Hb]. exists b. apply EQC_tran with (f a); assumption.
Qed.

Theorem CINC_refl : forall E : Ens, CINC E E.
Proof.
  intro E; destruct E as [n | a b | A f]; simpl.
  - reflexivity.
  - constructor; apply EQC_refl.
  - intros E H; exact H.
Qed.

Theorem CINC_tran :
 forall E E' E'' : Ens, CINC E E' -> CINC E' E'' -> CINC E E''.
Proof.
  intros E E' E'' H1 H2. destruct E as [n | a b | A f].
  - destruct E' as [m | c d | B g]; simpl in H1; try solve [ destruct H1 ].
    apply EQC_tran with (atom m); assumption.
  - destruct E' as [m | c d | B g]; simpl in H1; try solve [ destruct H1 ].
    apply EQC_tran with (pair c d); assumption.
  - intros E0 HE0. apply H1 in HE0.
    destruct E' as [m | c d | B g]; simpl in HE0; try solve [ destruct HE0 ].
    apply H2; exact HE0.
Qed.


Theorem CINC_sound_left :
 forall E E' E'' : Ens, EQC E E' -> CINC E E'' -> CINC E' E''.
Proof.
  intros E E' E'' HE HI. destruct E as [n | a b | A f].
  - destruct E' as [m | c d | B g]; simpl in HE; try solve [ destruct HE ].
    apply EQC_tran with (atom n); [ apply EQC_sym; exact HE | exact HI ].
  - destruct E' as [m | c d | B g]; simpl in HE; try solve [ destruct HE ].
    apply EQC_tran with (pair a b); [ apply EQC_sym; exact HE | exact HI ].
  - destruct E' as [m | c d | B g]; simpl in HE; try solve [ destruct HE ].
    intros E0 HE0. apply HI.
    apply CIN_sound_right with (sup B g); [ apply EQC_sym; exact HE | exact HE0 ].
Qed.

Theorem CINC_sound_right :
 forall E E' E'' : Ens, EQC E' E'' -> CINC E E' -> CINC E E''.
Proof.
  intros E E' E'' HE HI. destruct E as [n | a b | A f].
  - apply EQC_tran with E'; assumption.
  - apply EQC_tran with E'; assumption.
  - intros E0 HE0. apply CIN_sound_right with E'; [ exact HE | apply HI; exact HE0 ].
Qed.



Theorem tout_vide_est_VideC :
 forall E : Ens, is_set E -> (forall E' : Ens, CIN E' E -> F) -> EQC E Vide.
Proof.
  intros E s H. destruct E as [n | a b | A e]; simpl in s; try contradiction.
  unfold Vide; simpl; constructor.
  - intro x; destruct (H (e x)); exists x; apply EQC_refl.
  - intro y; destruct y.
Qed.


Theorem Paire_sound_leftC :
 forall A A' B : Ens, EQC A A' -> EQC (Paire A B) (Paire A' B).
Proof.
  intros A A' B e; unfold Paire; simpl; constructor.
  - intros [|]; [ exists true; exact e | exists false; apply EQC_refl ].
  - intros [|]; [ exists true; exact e | exists false; apply EQC_refl ].
Qed.

Theorem Paire_sound_rightC :
 forall A B B' : Ens, EQC B B' -> EQC (Paire A B) (Paire A B').
Proof.
  intros A B B' e; unfold Paire; simpl; constructor.
  - intros [|]; [ exists true; apply EQC_refl | exists false; exact e ].
  - intros [|]; [ exists true; apply EQC_refl | exists false; exact e ].
Qed.


Theorem CIN_Paire_left : forall E E' : Ens, CIN E (Paire E E').
Proof. intros E E'; unfold Paire; simpl; exists true; apply EQC_refl. Qed.

Theorem CIN_Paire_right : forall E E' : Ens, CIN E' (Paire E E').
Proof. intros E E'; unfold Paire; simpl; exists false; apply EQC_refl. Qed.

Inductive sum_t (A B : Type) : Type :=
  | inl_t : A -> sum_t A B
  | inr_t : B -> sum_t A B.
Hint Resolve inl_t inr_t: zfc.

Theorem Paire_CIN :
 forall E E' A : Ens, CIN A (Paire E E') -> sum_t (EQC A E) (EQC A E').
Proof.
  intros E E' A; unfold Paire; simpl; intros [b Hb].
  destruct b; [ left | right ]; exact Hb.
Qed.

Hint Resolve CIN_Paire_left CIN_Paire_right: zfc.

(* Singleton *)

Theorem CIN_Sing : forall E : Ens, CIN E (Sing E).
Proof. intro E; unfold Sing; apply CIN_Paire_left. Qed.

Theorem CIN_Sing_EQ : forall E E' : Ens, CIN E (Sing E') -> EQC E E'.
Proof. unfold Sing; intros E E' H; destruct (Paire_CIN E' E' E H); assumption. Qed.



Theorem EQC_EQ : forall E E' : Ens, EQC E E' -> EQ E E'.
Proof.
  induction E as [n | a IHa b IHb | A f IH]; intros E';
    destruct E' as [m | c d | B g]; simpl; intros H; try solve [ destruct H ].
  - exact H.
  - destruct H as [Ha Hb]; split; [ apply IHa | apply IHb ]; assumption.
  - destruct H as [H1 H2]; split.
    + intro a; destruct (H1 a) as [b Hb]; exists b; apply IH; exact Hb.
    + intro b; destruct (H2 b) as [a Ha]; exists a; apply IH; exact Ha.
Qed.


Theorem CIN_IN : forall E E' : Ens, CIN E E' -> IN E E'.
Proof.
  intros E E'; destruct E' as [m | c d | B g]; simpl; intro H; try solve [ destruct H ].
  destruct H as [b Hb]; exists b; apply EQC_EQ; exact Hb.
Qed.



Theorem EQC_EXType :
 forall E E' : Ens,
 EQC E E' ->
 forall a : pi1 E,
 depprod (pi1 E') (fun b : pi1 E' => EQC (pi2 E a) (pi2 E' b)).
Proof.
  intros E E' H a. destruct E as [n | b c | A f]; simpl in a; try solve [ destruct a ].
  destruct E' as [m | c d | B g]; simpl in H; try solve [ destruct H ].
  destruct H as [H1 _]; exact (H1 a).
Defined.

Theorem CIN_EXType :
 forall E E' : Ens,
 CIN E' E -> depprod (pi1 E) (fun a : pi1 E => EQC E' (pi2 E a)).
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H; try solve [ destruct H ].
  exact H.
Qed.

Theorem pi2_CIN : forall (E : Ens) (a : pi1 E), CIN (pi2 E a) E.
Proof.
  intros E a. destruct E as [n | b c | A f]; simpl in a; try solve [ destruct a ].
  simpl; exists a; apply EQC_refl.
Qed.

Theorem CIN_Union :
 forall E E' E'' : Ens, CIN E' E -> CIN E'' E' -> CIN E'' (Union E).
Proof.
  intros E E' E'' H1 H2. destruct E as [n | b c | A f]; simpl in H1; try solve [ destruct H1 ].
  destruct H1 as [a Ha].
  destruct (CIN_EXType (f a) E'') as [x e2]; [ apply CIN_sound_right with E'; assumption | ].
  simpl. exists (dep_i A (fun x : A => pi1 (f x)) a x). exact e2.
Qed.



Theorem CIN_CINC_Union :
 forall E E' : Ens, is_set E' -> CIN E' E -> CINC E' (Union E).
Proof.
  intros E E' s H. apply CINC_intro; [ exact s | ].
  intros E0 H0; apply CIN_Union with E'; assumption.
Qed.

(* idem depprod *)

Inductive depprod' (A : Type) (P : A -> Type) : Type :=
    dep_i' : forall x : A, P x -> depprod' A P.

Theorem Union_CIN :
 forall E E' : Ens,
 CIN E' (Union E) ->
 depprod' _ (fun E1 : Ens => prod_t (CIN E1 E) (CIN E' E1)).
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H.
  - destruct H as [x _]; destruct x.
  - destruct H as [x _]; destruct x.
  - destruct H as [[a b] e]. simpl in e.
    exists (f a). constructor.
    + exists a; apply EQC_refl.
    + apply CIN_sound_left with (pi2 (f a) b); [ apply EQC_sym; exact e | apply pi2_CIN ].
Qed.


Theorem Union_monC :
 forall E E' : Ens, CINC E E' -> CINC (Union E) (Union E').
Proof.
  intros E E' H. apply CINC_intro; [ apply Union_is_set | ].
  intros E0 H0. destruct (Union_CIN E E0 H0) as [E1 [h1 h2]].
  apply CIN_Union with E1; [ apply CINC_elim with E; assumption | exact h2 ].
Qed.

Theorem Union_soundC :
 forall E E' : Ens, EQC E E' -> EQC (Union E) (Union E').
Proof.
  intros E E' e. apply CINC_EQC; apply Union_monC; apply EQC_INC;
    [ exact e | apply EQC_sym; exact e ].
Qed.


(* surprinsingly, the predicative and impredicative definitions of the   *)
(* intersection do not seem equivalent.                                  *)
(* to be checked...                                                      *)
