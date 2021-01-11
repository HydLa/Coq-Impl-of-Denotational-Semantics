Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.ROrderedType.
Require Import Lists.List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Open Scope R_scope.
Require Import Ascii String.

From HYDLA Require Export Trajectory.

(* closed formula based on Prop *)
(* I: injection, A: and, T: then, S: square *)
Inductive formula := I (p : Prop) | A (f g : formula) | T (p : Prop) (f : formula) | S (f : formula).

Lemma Feq_dec: forall x y : formula, {x = y} + {x <> y}.
Proof. Admitted.
Definition eq_f (f1 f2 : formula) : bool :=
  match Feq_dec f1 f2 with
  | left _ => true
  | right _ => false
  end.
Fixpoint eq_sf (s1 s2 : set formula) : bool :=
  match (s1, s2) with
  | (nil, nil) => true
  | (h1::t1, h2::t2) => (eq_f h1 h2) && (eq_sf t1 t2)
  | _ => false
  end.

(* low level means high priority*)
Notation "'$' p" := (I p) (at level 75).
Notation "f '&' g" := (A f g) (at level 80, right associativity).
Notation "p '~>' f" := (T p f) (at level 85, right associativity).
Notation "'[]' f" := (S f) (at level 100).
Check $True.
Check []$True.
Check [][]$True.
Check [](True /\ True ~> $True & []$True).
Variable x y : R.
Check $ x=0.
Check [] x=0 ~> []$ y=0.
Check [] [] $ x=0.

(* closure about a formula *)
Fixpoint cl (f : formula) : list formula :=
  match f with
  | S f' => f' :: cl f'
  | _ => nil
  end.
Example test_cl1: cl ($True) = nil.
Proof. reflexivity. Qed.
Example test_cl2: cl ([][]$True) = [[]$True; $True].
Proof. reflexivity. Qed.

(* closure about list formula i.e. formula in each phase*)
Definition fold_cl (l : list formula) : set formula := fold_left (fun x y => set_union Feq_dec x (cl y)) l nil.
Lemma TrueEqFalse: forall p : Prop, True = False -> p.
Proof.
  intros.
  assert (False -> p). { intros. inversion H0. }
  apply H0.
  rewrite <- H.
  trivial. Qed.
Example test_fold_cl1: fold_cl nil = nil.
Proof. reflexivity. Qed.
Example test_fold_cl2: fold_cl [$True] = nil.
Proof. reflexivity. Qed.
Example test_fold_cl3: fold_cl [[][]$True] = [$True; []$True].
Proof.
  unfold fold_cl. simpl.
  destruct (Feq_dec ([] $ True) ($ True)).
  - inversion e.
  - trivial. Qed.
Example test_fold_cl4: fold_cl [[][]$True; []$False] = [$True; []$True; $False].
Proof.
  unfold fold_cl. simpl.
  destruct (Feq_dec ([] $ True) ($ True)).
  - inversion e.
  - simpl.
    destruct (Feq_dec ($ False) ($ True)).
    + inversion e.
      generalize H0.
      apply TrueEqFalse.
      rewrite H0.
      trivial.
    + destruct (Feq_dec ($ False) ([] $ True)).
      * inversion e.
      * trivial. Qed.
Example test_fold_cr5: fold_cl [[][]$True; []$True] = [$True; []$True].
Proof.
  unfold fold_cl. simpl.
  destruct (Feq_dec ([] $ True) ($ True)).
  - inversion e.
  - simpl.
    destruct (Feq_dec ($ True) ($ True)).
    + trivial.
    + congruence. Qed.

Definition notsq (f : formula) : bool :=
  match f with
  | S f' => false
  | _ => true
  end.
Example test_notsq1: notsq ([]$True) = false.
Proof. reflexivity. Qed.
Example test_notsq2: notsq ($True) = true.
Proof. reflexivity. Qed.
Definition erasure (l : list formula) : list formula := filter notsq l.
Example test_erasure1: erasure nil = nil.
Proof. reflexivity. Qed.
Example test_erasure2: erasure [[]$True; $True] = [$True].
Proof. reflexivity. Qed.
(* in semantics, constraint is identified with function on time *)
(* and it is expressed by list in implementation like trajectory *)
Definition constraint := list (set formula).

(* is x subset of y? *)
Definition is_subset (x y : set formula) : bool :=
  fold_left (fun a b => a && (set_mem Feq_dec b y)) x true.
Definition sf_union := set_union Feq_dec.

(* closure2 isn't entrypoint *)
Fixpoint closure2 (c : constraint) (expanded : set formula) : constraint :=
  match c with
  | nil => nil
  | [h] =>
    let new_exp := sf_union h (fold_cl h) in
    match expanded with
    | nil => if eq_sf h new_exp then [h] else [new_exp; fold_cl h]
    | _ =>
      if is_subset expanded new_exp then [new_exp]
      else [sf_union expanded new_exp; (sf_union expanded (fold_cl h))]
    end
  | h::t => (sf_union h (sf_union expanded (fold_cl h))) :: closure2 t (sf_union expanded (fold_cl h))
  end.
Definition closure (c : constraint) : constraint := closure2 c nil.
Example test_closure1: closure nil = nil.
Proof. reflexivity. Qed.
Example test_closure2: closure [[$True]] = [[$True]].
Proof.
  unfold closure, closure2. simpl. unfold eq_f.
  destruct (Feq_dec ($ True) ($ True)).
  { reflexivity. }
  congruence. Qed.
Example test_closure3: closure [[[]$True]] = [[[]$True; $True]; [$True]].
Proof.
  unfold closure, closure2. simpl. unfold eq_f.
  destruct (Feq_dec ($ True) ([] $ True)).
  { congruence. }
  destruct (Feq_dec ([] $ True) ([] $ True)).
  { reflexivity. }
  congruence. Qed.
Example test_closure4:
  closure [[[]$True]; nil; [[]$False]]
  = [[[]$True; $True]; [$True]; [$True; $False; []$False]; [$True; $False]].
Proof.
  unfold closure, closure2. simpl.
  destruct (Feq_dec ($ True) ([] $ True)).
  { inversion e. }
  destruct (Feq_dec ($ False) ([] $ False)).
  { inversion e. }
  unfold is_subset. simpl.
  destruct (Feq_dec ($ True) ([] $ False)).
  { inversion e. }
  destruct (Feq_dec ($ True) ($ False)).
  { inversion e. generalize H0. apply TrueEqFalse. }
  destruct (Feq_dec ($ False) ($ True)).
  { inversion e. generalize H0. apply TrueEqFalse. rewrite H0. trivial. }
  simpl.
  destruct (Feq_dec ([] $ False) ($ True)).
  { inversion e. }
  destruct (Feq_dec ([] $ False) ($ False)).
  { inversion e. }
  trivial. Qed.
Example test_closure5:
  closure [[[]$True]; [$True]] = [[[]$True; $True]; [$True]].
Proof.
  unfold closure, closure2. simpl.
  destruct (Feq_dec ($ True) ([] $ True)).
  { inversion e. }
  unfold is_subset. simpl.
  destruct (Feq_dec ($ True) ($ True)).
  { trivial. }
  congruence. Qed.

(* history of constraint *)
Definition history : Type := string -> option constraint.
Definition emph : history := (fun _ => None).
Definition update_history (h : history) (s : string) (c : constraint) : history :=
  fun t => if eqb s t then Some c else h t.

Notation "s '~~>' c ';' h" := (update_history h s c)
  (at level 100, c at next level, right associativity).
Notation "s '~~>' c" := (update_history emph s c)
  (at level 100).
Variable x' x'' prevx prevx': R.
Check "INIT" ~~> [[$x = 10; $x' = 0]].
Check "BOUNCE" ~~> [[[]prevx = 0 ~> $ x' = -prevx']].
Check "INIT" ~~> [[$x = 10; $x' = 0]]; "FALL" ~~> [[[]$x'' = -10]].

(* is c1 subset of c2? *)
Fixpoint c_subset (c1 c2 : constraint) :=
  match (c1, c2) with
  | (h1::t1, h2::t2) => (is_subset h1 h2) && (c_subset t1 t2)
  | (nil, _) => true
  | _ => false
  end.
Example test_c_subset1:
  c_subset nil nil = true.
Proof.
  reflexivity. Qed.
Example test_c_subset2:
  c_subset [[$x'' = -10]] [[$x'' = -10]] = true.
Proof.
  simpl. unfold is_subset. simpl.
  destruct (Feq_dec ($ x'' = -10) ($ x'' = -10)).
  - reflexivity.
  - congruence. Qed.
Example test_c_subset3:
  c_subset [[[]$x'' = -10]] [[[]$x'' = -10; $x'' = -10]; [$x'' = -10]] = true.
Proof.
  simpl.
  unfold is_subset. simpl.
  destruct (Feq_dec ([] $ x'' = -10) ([] $ x'' = -10)).
  - reflexivity.
  - congruence. Qed.
Example test_c_subset4:
  c_subset [[[]$x'' = -10; $x'' = -10]] [[[]$x'' = -10]] = false.
Proof.
  simpl. unfold is_subset. simpl.
  destruct (Feq_dec ([] $ x'' = -10) ([] $ x'' = -10)).
  - destruct (Feq_dec ($ x'' = -10) ([] $ x'' = -10)).
    + congruence.
    + reflexivity.
  - congruence. Qed.
Example test_c_subset5:
  c_subset [[$x'' = -10]; [$x'' = -10]] [[$x'' = -10]] = false.
Proof.
  simpl.
  rewrite -> andb_false_r.
  trivial. Qed.

(* c1 == c2? *)
Definition c_eq (c1 c2 : constraint) := c_subset c1 c2 && c_subset c2 c1.
Example test_c_eq1: c_eq nil nil = true.
Proof. reflexivity. Qed.
Example test_c_eq:
  c_eq [[$x'' = -10]] [[$x'' = -10]] = true.
Proof.
  unfold c_eq. simpl. unfold is_subset. simpl.
  destruct (Feq_dec ($ x'' = -10) ($ x'' = -10)).
  - reflexivity.
  - congruence. Qed.

Variable z z' z'': partial.
Variable t: R.

Definition unfold_some (c : option constraint) : constraint :=
  match c with
  | Some c' => c'
  | None => nil
  end.
Example test_unfold_some1: unfold_some (Some [[$ z(t) = Some 10; $ z'(t) = Some 0]]) = [[$ z(t) = Some 10; $ z'(t) = Some 0]].
Proof. reflexivity. Qed.
Example test_unfold_some2: unfold_some None = nil.
Proof. reflexivity. Qed.


(* unwrap formula to prop *)
(* []f can't be unwraped, so return True *)
Fixpoint f2p (f : formula) : Prop :=
  match f with
  | $ p => p
  | f & g => f2p(f) /\ f2p(g)
  | p ~> f => p -> f2p(f)
  | _ => True
  end.
Example test_f2p1 : f2p($ True).
Proof. simpl. trivial. Qed.
Example test_f2p2 : f2p(False ~> $ True).
Proof. simpl. trivial. Qed.
Example test_f2p3 : f2p([]$False).
Proof. simpl. trivial. Qed.

Lemma reqb00false: Reqb 0 0 = false -> False.
Proof.
  unfold Reqb.
  destruct (Req_dec 0 0).
  - intro.
    discriminate H.
  - apply Rdichotomy in n.
    generalize n.
    intros [A|B].
    + apply Rlt_irrefl in A.
      inversion A.
    + apply Rgt_irrefl in B.
      inversion B. Qed.

Definition andl (l : list Prop) : Prop :=
  fold_left and l True.
Example test_andl1: andl([True; True]).
Proof.
  unfold andl. simpl. auto. Qed.


Definition ssubset (x y : set string) : bool :=
  fold_left (fun a b => a && (set_mem string_dec b y)) x true.