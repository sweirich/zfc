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
(* https://github.com/rocq-archive/zfc): Adapted to the sorted [Ens]  *)
(* of [Sets.v]: every set-former returns a set, and [Comp], [Union],  *)
(* [Inter] and [Power] return the empty set when applied to a         *)
(* non-set; [INC_IN_Power], [Power_mon], [tout_vide_est_Vide] and     *)
(* [IN_INC_Union] take an [is_set] premise; definitions made universe *)
(* polymorphic ([pi1], [pi2] and [Power] explicitly); added the       *)
(* [*_is_set] lemmas.                                                 *)
(*--------------------------------------------------------------------*)


(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(* Definitions of the empty set, pair, union, intersection, comprehension  *)
(*  axiom and powerset, together with their properties.                    *)
(*                                                                         *)
(*  Adapted to the sorted [Ens] of [Sets.v] (atoms, pairs, sets): every    *)
(*  set-former is a set, and applied to a non-set it returns the empty     *)
(*  set.  The lemmas that read a set off its members ([INC_IN_Power],       *)
(*  [Power_mon], [tout_vide_est_Vide], [IN_INC_Union]) take an [is_set]     *)
(*  premise where a non-set would falsify them.                             *)


Require Import Sets.

(* Universe polymorphic, like [Sets.v]: the set-formers ([Paire], [Sing],
   [Comp], [Union], [Power]) and their soundness/membership lemmas float
   their [Ens] universe so [Hierarchy.v] can reuse them at the [small] and
   [big] levels while [lib] uses them at [ulib].  [EXType]/[prod_t] remain
   monomorphic (imported from [Sets.v]). *)
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

(* Useful types (actually top and bottom)   *)

Inductive Un : Set :=
    void : Un.

Inductive F : Set :=.

(* The empty set  (vide = french for empty)   *)

Definition Vide : Ens := sup F (fun f : F => match f return Ens with
                                             end).

Theorem Vide_is_set : is_set Vide.
Proof. exact I. Qed.

(* The axioms of the empty set *)

Theorem Vide_est_vide : forall E : Ens, IN E Vide -> F.
Proof. intros E H. exfalso. destruct H as [x _]. destruct x. Qed.

Theorem tout_vide_est_Vide :
 forall E : Ens, is_set E -> (forall E' : Ens, IN E' E -> F) -> EQ E Vide.
Proof.
  intros E Hs H0. destruct E as [n | a b | A e]; try contradiction.
  simpl. split.
  - intro x. destruct (H0 (e x) (EXTypei _ _ x (EQ_refl _))).
  - intro y. destruct y.
Qed.

(* Pair *)

Definition Paire (E E' : Ens) : Ens :=
  sup bool (fun b : bool => if b then E else E').

Theorem Paire_is_set : forall E E' : Ens, is_set (Paire E E').
Proof. intros; exact I. Qed.

(* The pair construction is extentional *)

Theorem Paire_sound_left :
 forall A A' B : Ens, EQ A A' -> EQ (Paire A B) (Paire A' B).
Proof.
  intros A A' B H. simpl. split; intro b; exists b; destruct b; simpl;
    [ exact H | apply EQ_refl | exact H | apply EQ_refl ].
Qed.

Theorem Paire_sound_right :
 forall A B B' : Ens, EQ B B' -> EQ (Paire A B) (Paire A B').
Proof.
  intros A B B' H. simpl. split; intro b; exists b; destruct b; simpl;
    [ apply EQ_refl | exact H | apply EQ_refl | exact H ].
Qed.

Hint Resolve Paire_sound_right Paire_sound_left: zfc.

(* The axioms of the pair *)

Theorem IN_Paire_left : forall E E' : Ens, IN E (Paire E E').
Proof. intros; simpl; exists true; apply EQ_refl. Qed.

Theorem IN_Paire_right : forall E E' : Ens, IN E' (Paire E E').
Proof. intros; simpl; exists false; apply EQ_refl. Qed.

Theorem Paire_IN :
 forall E E' A : Ens, IN A (Paire E E') -> EQ A E \/ EQ A E'.
Proof.
  intros E E' A H. destruct H as [b Hb]. destruct b; [ left | right ]; exact Hb.
Qed.

Hint Resolve IN_Paire_left IN_Paire_right Vide_est_vide: zfc.

(* The singleton set  *)

Definition Sing (E : Ens) := Paire E E.

Theorem Sing_is_set : forall E : Ens, is_set (Sing E).
Proof. intros; exact I. Qed.

(* The axioms  *)

Theorem IN_Sing : forall E : Ens, IN E (Sing E).
Proof. intro E; apply IN_Paire_left. Qed.

Theorem IN_Sing_EQ : forall E E' : Ens, IN E (Sing E') -> EQ E E'.
Proof. intros E E' H. destruct (Paire_IN E' E' E H); assumption. Qed.

Hint Resolve IN_Sing IN_Sing_EQ: zfc.

Theorem Sing_sound : forall A A' : Ens, EQ A A' -> EQ (Sing A) (Sing A').
Proof.
  intros A A' H. unfold Sing. apply EQ_tran with (Paire A A').
  - apply Paire_sound_right; exact H.
  - apply Paire_sound_left; exact H.
Qed.

Hint Resolve Sing_sound: zfc.

Theorem EQ_Sing_EQ : forall E1 E2 : Ens, EQ (Sing E1) (Sing E2) -> EQ E1 E2.
Proof.
  intros E1 E2 H. apply IN_Sing_EQ.
  apply IN_sound_right with (Sing E1); [ exact H | apply IN_Sing ].
Qed.

Hint Resolve EQ_Sing_EQ: zfc.



(* We here need sigma types -- i.e. computational existentials *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig A P.


(* The set obtained by the comprehension (or separation) axiom.  On a
   non-set it is the empty set. *)

Definition Comp (E : Ens) (P : Ens -> Prop) : Ens :=
  match E with
  | sup A f =>
      sup (sig A (fun x : A => P (f x)))
          (fun c : sig A (fun x : A => P (f x)) =>
             match c with exist x _ => f x end)
  | _ => Vide
  end.

Theorem Comp_is_set : forall (E : Ens) (P : Ens -> Prop), is_set (Comp E P).
Proof. intros E P; destruct E; exact I. Qed.

(* The comprehension/separation axioms *)

Theorem Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
Proof.
  intros E P. destruct E as [n | a b | A f]; simpl.
  - intros E0 H. destruct H as [x _]. destruct x.
  - intros E0 H. destruct H as [x _]. destruct x.
  - intros E0 H. destruct H as [c Hc]. destruct c as [x p]. simpl in Hc.
    exists x. exact Hc.
Qed.

Theorem IN_Comp_P :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A (Comp E P) -> P A.
Proof.
  intros E A P H i. destruct E as [n | a b | B f]; simpl in i.
  - destruct i as [x _]; destruct x.
  - destruct i as [x _]; destruct x.
  - destruct i as [c Hc]. destruct c as [x q]. simpl in Hc.
    apply H with (f x); [ exact q | apply EQ_sym; exact Hc ].
Qed.

Theorem IN_P_Comp :
 forall (E A : Ens) (P : Ens -> Prop),
 (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) ->
 IN A E -> P A -> IN A (Comp E P).
Proof.
  intros E A P H i p. destruct E as [n | a b | B f]; simpl in i; try contradiction.
  destruct i as [x Hx].
  assert (Pf : P (f x)) by (apply H with A; assumption).
  simpl. exists (exist B (fun x : B => P (f x)) x Pf). simpl. exact Hx.
Qed.


(* Projections of a set: *)
(*  1: its base type (empty for a non-set)    *)

Polymorphic Definition pi1 (E : Ens) : Type :=
  match E with
  | sup A _ => A
  | _ => F
  end.

(*  2: the function      *)

Polymorphic Definition pi2 (E : Ens) : pi1 E -> Ens :=
  match E return pi1 E -> Ens with
  | sup A f => f
  | atom _ => fun x => match x return Ens with end
  | pair _ _ => fun x => match x return Ens with end
  end.

Theorem pi2_IN : forall (E : Ens) (a : pi1 E), IN (pi2 E a) E.
Proof.
  intros E a. destruct E as [n | b c | A f]; simpl in a.
  - destruct a.
  - destruct a.
  - simpl. exists a. apply EQ_refl.
Qed.

(* The Union set   *)

Definition Union (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup (depprod A (fun x : A => pi1 (f x)))
          (fun c : depprod A (fun x : A => pi1 (f x)) =>
             match c with dep_i a b => pi2 (f a) b end)
  | _ => Vide
  end.

Theorem Union_is_set : forall E : Ens, is_set (Union E).
Proof. intro E; destruct E; exact I. Qed.

Theorem EQ_EXType :
 forall E E' : Ens,
 EQ E E' ->
 forall a : pi1 E,
 EXType (pi1 E') (fun b : pi1 E' => EQ (pi2 E a) (pi2 E' b)).
Proof.
  intros E E' H a. destruct E as [n | b c | A f]; simpl in a; try (destruct a).
  destruct E' as [m | d e | B g]; simpl in H; try contradiction.
  destruct H as [H1 _]. apply H1.
Qed.

Theorem IN_EXType :
 forall E E' : Ens,
 IN E' E -> EXType (pi1 E) (fun a : pi1 E => EQ E' (pi2 E a)).
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H; try contradiction.
  destruct H as [a Ha]. exists a. exact Ha.
Qed.

(* The union axioms *)
Theorem IN_Union :
 forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).
Proof.
  intros E E' E'' H1 H2. destruct E as [n | b c | A f]; simpl in H1; try contradiction.
  destruct H1 as [a Ha].
  assert (H2' : IN E'' (f a)) by (apply IN_sound_right with E'; assumption).
  destruct (IN_EXType (f a) E'' H2') as [b Hb].
  simpl. exists (dep_i A (fun x : A => pi1 (f x)) a b). simpl. exact Hb.
Qed.

(* A *set* member of [E] is included in [⋃E].  (An atom or pair member
   is not: it is included only in itself.) *)
Theorem IN_INC_Union : forall E E' : Ens, is_set E' -> IN E' E -> INC E' (Union E).
Proof.
  intros E E' Hs i. destruct E' as [m | c d | B g]; try contradiction.
  intros E'' i'. apply IN_Union with (sup B g); assumption.
Qed.

Theorem Union_IN :
 forall E E' : Ens,
 IN E' (Union E) -> EXType _ (fun E1 : Ens => IN E1 E /\ IN E' E1).
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H.
  - destruct H as [x _]; destruct x.
  - destruct H as [x _]; destruct x.
  - destruct H as [d Hd]. destruct d as [a b]. simpl in Hd.
    exists (f a). split.
    + exists a. apply EQ_refl.
    + apply IN_sound_left with (pi2 (f a) b); [ apply EQ_sym; exact Hd | apply pi2_IN ].
Qed.


(* extentionality of union  *)

Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
Proof.
  intros E E' H. destruct E as [n | b c | A f]; destruct E' as [m | d e | A' f'];
    simpl in H; try contradiction; try apply EQ_refl.
  destruct H as [e1 e2]. simpl. split.
  - intro x. destruct x as [a aa]. destruct (e1 a) as [a' ea].
    destruct (EQ_EXType (f a) (f' a') ea aa) as [aa' eaa].
    exists (dep_i A' (fun x : A' => pi1 (f' x)) a' aa'). simpl. exact eaa.
  - intro c'. destruct c' as [a' aa']. destruct (e2 a') as [a ea].
    assert (ea' : EQ (f' a') (f a)) by (apply EQ_sym; exact ea).
    destruct (EQ_EXType (f' a') (f a) ea' aa') as [aa eaa].
    exists (dep_i A (fun x : A => pi1 (f x)) a aa). simpl. apply EQ_sym. exact eaa.
Qed.



(* The union construction is monotone w.r.t. inclusion   *)

Theorem Union_mon : forall E E' : Ens, INC E E' -> INC (Union E) (Union E').
Proof.
  intros E E' H. destruct E as [n | b c | A f].
  - intros E0 HE0. destruct HE0 as [x _]. destruct x.
  - intros E0 HE0. destruct HE0 as [x _]. destruct x.
  - intros E0 HE0.
    destruct (Union_IN (sup A f) E0 HE0) as [E1 [I1 I2]].
    apply IN_Union with E1; [ apply H; exact I1 | exact I2 ].
Qed.



(* The  Intersection set   *)

Definition Inter (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun
           c : depprod _
                 (fun a : A =>
                  depprod _
                    (fun b : pi1 (f a) =>
                     forall x : A, IN (pi2 (f a) b) (f x))) =>
         match c with
         | dep_i a (dep_i b p) => pi2 (f a) b
         end)
  | _ => Vide
  end.

(* the axioms *)

Theorem IN_Inter_all :
 forall E E' : Ens,
 IN E' (Inter E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H.
  - destruct H as [x _]; destruct x.
  - destruct H as [x _]; destruct x.
  - destruct H as [d Hd]. destruct d as [a [aa paa]]. simpl in Hd.
    intros E'' HE''. destruct HE'' as [a1 ea1].
    apply IN_sound_right with (f a1); [ apply EQ_sym; exact ea1 | ].
    apply IN_sound_left with (pi2 (f a) aa); [ apply EQ_sym; exact Hd | apply paa ].
Qed.

Theorem all_IN_Inter :
 forall E E' E'' : Ens,
 IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter E).
Proof.
  intros E E' E'' i H. destruct E as [n | b c | A f]; simpl in i; try contradiction.
  destruct i as [a ea].
  assert (i0 : IN E' (f a)) by (apply H; exists a; apply EQ_refl).
  destruct (IN_EXType (f a) E' i0) as [bb e'].
  assert (H0 : forall x : A, IN (pi2 (f a) bb) (f x)).
  { intro x. apply IN_sound_left with E'; [ exact e' | apply H; exists x; apply EQ_refl ]. }
  simpl.
  exists (dep_i A
            (fun a0 : A => depprod (pi1 (f a0)) (fun b0 : pi1 (f a0) => forall x : A, IN (pi2 (f a0) b0) (f x)))
            a (dep_i (pi1 (f a)) (fun b0 : pi1 (f a) => forall x : A, IN (pi2 (f a) b0) (f x)) bb H0)).
  simpl. exact e'.
Qed.


Definition Inter' (E : Ens) : Ens :=
  Comp (Union E) (fun e : Ens => forall a : Ens, IN a E -> IN e a).

Theorem IN_Inter'_all :
 forall E E' : Ens,
 IN E' (Inter' E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
Proof.
  unfold Inter'. intros E E' i.
  change ((fun e : Ens => forall a : Ens, IN a E -> IN e a) E').
  apply (IN_Comp_P (Union E) E').
  - intros w1 w2 Hw Hw12 a Ha. apply IN_sound_left with w1; [ exact Hw12 | apply Hw; exact Ha ].
  - exact i.
Qed.

Theorem all_IN_Inter' :
 forall E E' E'' : Ens,
 IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter' E).
Proof.
  unfold Inter'. intros E E' E'' i H.
  apply IN_P_Comp.
  - intros w1 w2 Hw Hw12 a Ha. apply IN_sound_left with w1; [ exact Hw12 | apply Hw; exact Ha ].
  - apply IN_Union with (E' := E''); auto.
  - exact H.
Qed.

(*  The powerset and its axioms   *)

(* Polymorphic so [Hierarchy.v] can reuse it at the smaller universe of
   the "small sets" instead of duplicating it as [Power']. *)
Polymorphic Definition Power (E : Ens) : Ens :=
  match E with
  | sup A f =>
      sup _
        (fun P : A -> Prop =>
         sup _
           (fun c : depprod A (fun a : A => P a) =>
            match c with
            | dep_i a p => f a
            end))
  | _ => Vide
  end.

Theorem Power_is_set : forall E : Ens, is_set (Power E).
Proof. intro E; destruct E; exact I. Qed.

Theorem IN_Power_INC : forall E E' : Ens, IN E' (Power E) -> INC E' E.
Proof.
  intros E E' H. destruct E as [n | b c | A f]; simpl in H.
  - destruct H as [x _]; destruct x.
  - destruct H as [x _]; destruct x.
  - destruct H as [P HP].
    destruct E' as [m | d e | A' f']; simpl in HP; try contradiction.
    destruct HP as [HA HB].
    intros E'' HE''. destruct HE'' as [a' e'].
    destruct (HA a') as [d Hd]. destruct d as [a p]. simpl in Hd.
    exists a. apply EQ_tran with (f' a'); assumption.
Qed.

(* A subset of a *set* is in its power set.  (For a non-set [E] the only
   thing included in [E] is [E] itself, and [Power E] is empty.) *)
Theorem INC_IN_Power : forall E E' : Ens, is_set E -> INC E' E -> IN E' (Power E).
Proof.
  intros E E' Hs i. destruct E as [n | b c | A f]; try contradiction.
  destruct E' as [m | d e | A' f']; try (simpl in i; contradiction).
  simpl. exists (fun a : A => IN (f a) (sup A' f')). simpl. split.
  - intro x.
    assert (Hin : IN (f' x) (sup A' f')) by (exists x; apply EQ_refl).
    destruct (i (f' x) Hin) as [a e].
    exists (dep_i A (fun a0 : A => IN (f a0) (sup A' f')) a
              (IN_sound_left (f' x) (f a) (sup A' f') e Hin)).
    simpl. exact e.
  - intro d. destruct d as [a p]. destruct p as [x e].
    exists x. simpl. apply EQ_sym. exact e.
Qed.

Theorem Power_mon : forall E E' : Ens, is_set E' -> INC E E' -> INC (Power E) (Power E').
Proof.
  intros E E' Hs H. destruct E' as [m | d e | B g]; try contradiction.
  destruct E as [n | b c | A f]; try (simpl in H; contradiction).
  intros E0 HE0. apply INC_IN_Power; [ exact I | ].
  apply INC_tran with (sup A f); [ apply IN_Power_INC; exact HE0 | exact H ].
Qed.

Theorem Power_sound : forall E E' : Ens, EQ E E' -> EQ (Power E) (Power E').
Proof.
  intros E E' e. destruct E as [n | b c | A f]; destruct E' as [m | d e' | A' f'];
    simpl in e; try contradiction; try apply EQ_refl.
  apply INC_EQ.
  - intros X i. apply INC_IN_Power; [ exact I | ].
    apply INC_sound_right with (sup A f); [ exact e | apply IN_Power_INC; exact i ].
  - intros X i. apply INC_IN_Power; [ exact I | ].
    apply INC_sound_right with (sup A' f'); [ apply EQ_sym; exact e | apply IN_Power_INC; exact i ].
Qed.





(* small lemma *)

Theorem not_EQ_Sing_Vide : forall E : Ens, EQ (Sing E) Vide -> F.
Proof.
  intros E e.
  assert (H : IN E Vide) by (apply IN_sound_right with (Sing E); [ exact e | apply IN_Sing ]).
  exfalso. destruct H as [x _]. destruct x.
Qed.


Theorem not_EQ_Vide_Sing : forall E : Ens, EQ Vide (Sing E) -> F.
Proof. intros E e. apply (not_EQ_Sing_Vide E). apply EQ_sym. exact e. Qed.
