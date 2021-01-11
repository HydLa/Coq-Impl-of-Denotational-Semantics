Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.ROrderedType.
Require Import Lists.List.
Import ListNotations.
Open Scope R_scope.

From HYDLA Require Export Partial.

Definition Inf := None : option R.

(* see https://coq.inria.fr/library/Coq.Reals.ROrderedType.html#Reqb *)
Definition Rleb r1 r2 := if Rle_dec r1 r2 then true else false.
Definition Rltb r1 r2 := if Rlt_dec r1 r2 then true else false.
Definition Rgeb r1 r2 := if Rge_dec r1 r2 then true else false.
Definition Rgtb r1 r2 := if Rgt_dec r1 r2 then true else false.
Example test_Rleb1: forall r1 r2 : R, r1 <= r2 <-> Rleb r1 r2 = true.
Proof.
  intros.
  split.
  - intros.
    unfold Rleb.
    destruct (Rle_dec r1 r2).
    + trivial.
    + apply Rnot_le_gt in n.
      apply Rgt_lt in n.
      apply Rle_lt_trans with (r3:=r1) in H.
      * apply Rlt_irrefl in H.
        inversion H.
      * trivial.
  - unfold Rleb.
    destruct (Rle_dec r1 r2).
    + trivial.
    + intros.
      discriminate H. Qed.
Example test_Rleb2: forall r1 r2 : R, r1 > r2 <-> Rleb r1 r2 = false.
Proof.
  intros.
  split.
  - intros.
    unfold Rleb.
    destruct (Rle_dec r1 r2).
    + apply Rgt_lt in H.
      apply Rle_lt_trans with (r3:=r1) in r.
      * apply Rlt_irrefl in r.
        inversion r.
      * trivial.
    + trivial.
  - unfold Rleb.
    destruct (Rle_dec r1 r2).
    + intros.
      discriminate H.
    + intros.
      apply Rnot_le_lt in n.
      trivial. Qed.
Example test_Rltb1: forall r1 r2 : R, r1 < r2 <-> Rltb r1 r2 = true.
Proof.
  intros.
  split.
  - intros.
    unfold Rltb.
    destruct (Rlt_dec r1 r2).
    + trivial.
    + apply Rnot_lt_ge in n.
      apply Rge_le in n.
      apply Rlt_le_trans with (r3:=r1) in H.
      * apply Rlt_irrefl in H.
        inversion H.
      * trivial.
  - unfold Rltb.
    destruct (Rlt_dec r1 r2).
    + intros.
      trivial.
    + intros.
      discriminate H. Qed.
Example test_Rltb2: forall r1 r2 : R, r1 >= r2 <-> Rltb r1 r2 = false.
Proof.
  intros.
  split.
  - intros.
    unfold Rltb.
    destruct (Rlt_dec r1 r2).
    + apply Rge_le in H.
      apply Rlt_le_trans with(r3:=r1) in r.
      * apply Rlt_irrefl in r.
        inversion r.
      * trivial.
    + trivial.
  - intros.
    unfold Rltb in H.
    destruct (Rlt_dec r1 r2).
    + inversion H.
    + apply Rnot_lt_ge in n.
      trivial. Qed.
Example test_Reqb1: forall r1 r2 : R, r1 = r2 <-> Reqb r1 r2 = true.
Proof.
  intros.
  split.
  - intros.
    unfold Reqb.
    destruct (Req_dec r1 r2).
    + trivial.
    + rewrite H in n.
      apply Rdichotomy in n.
      generalize n.
      intros [A|B].
      * apply Rlt_irrefl in A.
        inversion A.
      * apply Rgt_irrefl in B.
        inversion B.
  - unfold Reqb.
    destruct (Req_dec r1 r2).
    + trivial.
    + intros.
      discriminate H. Qed.
Example test_Reqb2: forall r1 r2 : R, r1 <> r2 <-> Reqb r1 r2 = false.
Proof.
  intros.
  split.
  - intros.
    apply Rdichotomy in H.
    generalize H.
    intros [A|B].
    + unfold Reqb.
      destruct (Req_dec r1 r2).
      * rewrite e in A.
        apply Rlt_irrefl in A.
        inversion A.
      * trivial.
    + unfold Reqb.
      destruct (Req_dec r1 r2).
      * rewrite e in B.
        apply Rgt_irrefl in B.
        inversion B.
      * trivial.
  - unfold Reqb.
    destruct (Req_dec r1 r2).
    + intros.
      discriminate H.
    + trivial. Qed.

(* update value of m at x with v, i.e. m(x):=v *)
Definition update_pt (m : partial) (x : option R) (v : option R) :=
  fun y =>
    match x with
    | Some x' => if Reqb x' y then v else m y
    | None => m y
    end.
Notation "x '|-->' v ';' m" := (update_pt m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|-->' v" := (update_pt empty x v)
  (at level 100).
Example test_update_pt1: (Some 0 |--> Some 10) 0 = Some 10.
Proof.
  simpl.
  destruct (Reqb 0 0) eqn:E.
  - trivial.
  - unfold Reqb in E.
    destruct (Req_dec 0 0).
    + discriminate E.
    + apply Rdichotomy in n.
      generalize n.
      intros [A|B].
      * apply Rlt_irrefl in A.
        inversion A.
      * apply Rgt_irrefl in B.
        inversion B. Qed.
Example test_update_pt2: (Some 0 |--> Some 10) 1 = None.
Proof.
  simpl.
  destruct (Reqb 0 1) eqn:E.
  - apply test_Reqb1 in E.
    apply eq01_False in E.
    destruct E.
  - unfold empty.
    trivial. Qed.

(* update m in open interval (begt, endt) by m' *)
Definition update_in (m : partial) (m' : partial) (begt : option R) (endt : option R) : partial :=
  fun x' =>
    match (begt, endt) with
    | (Some begt', Some endt') => if andb (Rltb begt' x') (Rltb x' endt') then m' x' else m x'
    | (Some begt', Inf) => if Rltb begt' x' then m' x' else m x'
    | (_, _) => m x'
    end.
Notation "n '|_(' begt ',' endt ')' ';' m" := (update_in m n begt endt)
  (at level 100, right associativity).
Notation "n '|_(' begt ',' endt ')'" := (update_in empty n begt endt)
  (at level 100).
Example test_update_in1: (fun x => Some x)|_(Some 0, Some 2) 1 = Some 1.
Proof.
  unfold update_in.
  simpl.
  destruct (Rltb 0 1) eqn:E1.
  - simpl.
    destruct (Rltb 1 2) eqn:E2.
    + trivial.
    + unfold Rltb in E2.
      destruct (Rlt_dec 1 2).
      * inversion E2.
      * apply Rnot_lt_le in n.
        apply le21_False in n.
        destruct n.
  - simpl.
    unfold Rltb in E1.
    destruct (Rlt_dec 0 1).
    + discriminate E1.
    + apply Rnot_lt_ge in n.
      apply Rge_le in n.
      apply le10_False in n.
      destruct n. Qed.
Example test_update_in2: (fun x => Some x)|_(Some 0, Some 2) 2 = None.
Proof.
  unfold update_in.
  unfold Rltb.
  destruct (Rlt_dec 2 2).
  - apply Rlt_irrefl in r.
    destruct r.
  - destruct (Rlt_dec 0 2).
    + unfold empty. reflexivity.
    + unfold empty. reflexivity. Qed.

Inductive phase : Type := pp (v : option R) | ip (m : partial) (begt : option R) (endt : option R).
Definition trajectory : Type := list phase.
(* the def of trajectory dosen't request alternation of PP and IP, *)
(* so validation might be needed *)

(* entry point is valid, not valid2 *)
Require Import Coq.funind.Recdef.
(* TODO: check continuity on ip *)
Function valid2 (tr : trajectory) {measure length tr} : Prop :=
  match tr with
  | [pp _; ip _ begt endt] => lt begt endt \/ endt = Inf
  | pp _ :: ip _ begt1 endt1 :: pp v2 :: ip m2 begt2 endt2 :: tr'
      => (lt begt1 endt1 \/ endt1 = Inf) /\ endt1 = begt2 /\ valid2 (pp v2 :: ip m2 begt2 endt2 :: tr')
  | _ => False
  end.
Proof.
  intros.
  simpl.
  repeat apply lt_n_S.
  apply lt_n_SSn. Qed.
Definition valid (tr : trajectory) : Prop :=
  match tr with
  | (pp v) :: (ip m (Some t) endt) :: tr' => t = 0 /\ valid2 tr
  | _ => False
  end.
Example test_valid1: valid [pp (Some 0) ; ip (fun x => Some x) (Some 0) Inf].
Proof.
  unfold valid.
  split.
  - trivial.
  - rewrite valid2_equation.
    right.
    trivial. Qed.
Example test_valid2:
  valid [pp (Some 0) ; ip (fun x => Some(2*x)) (Some 0) (Some 1) ; pp (Some 2) ; ip (fun x => Some x) (Some 1) Inf].
Proof.
  unfold valid.
  split.
  - trivial.
  - rewrite valid2_equation.
    split.
    + unfold lt.
      left.
      apply Rlt_0_1.
    + split.
      * trivial.
      * rewrite valid2_equation.
        right.
        trivial. Qed.
Example test_not_valid1: ~ valid [pp (Some 0) ; pp (Some 0)].
Proof.
  unfold valid.
  intro.
  destruct H. Qed.
Example test_not_valid2: ~ valid [pp (Some 0) ; ip (fun x => Some x) (Some 1) Inf].
Proof.
  unfold valid.
  intros [A B].
  symmetry in A.
  apply eq01_False in A.
  destruct A. Qed.
Example test_not_valid3: ~ valid [pp (Some 0) ; ip (fun x => Some x) (Some 0) (Some (-1))].
Proof.
  unfold valid.
  rewrite valid2_equation.
  unfold lt.
  intros [A B].
  destruct B.
  - apply Rlt_le_trans with (r3:=0) in H.
    + apply Rlt_irrefl in H.
      destruct H.
    + left.
      apply Rplus_lt_reg_l with (r:=1).
      rewrite Rplus_opp_r.
      rewrite Rplus_0_r.
      apply Rlt_0_1.
  - inversion H. Qed.
Example test_not_valid4: ~ valid [pp (Some 0) ; ip (fun x => Some x) (Some 0) (Some 1); pp (Some 0) ; ip (fun x => Some x) (Some 0) (Some 1)].
Proof.
  unfold valid.
  rewrite valid2_equation.
  intros [A [B [C D]]].
  - inversion C.
    symmetry in H0.
    apply eq01_False in H0.
    destruct H0. Qed.

(* convert trajectory to partial *)
Fixpoint tr2partial (tr : trajectory) : partial :=
  match tr with
  | [] => empty
  | (pp v) :: (ip m begt endt) :: tr' => (begt |--> v ; m|_(begt, endt) ; (tr2partial tr'))
  | _ => empty
  end.
Example test_tr2partial1: tr2partial [pp (Some 0) ; ip (fun x => Some x) (Some 0) Inf] 1 = Some 1.
Proof.
  unfold tr2partial.
  unfold update_pt.
  unfold update_in.
  unfold Inf.
  unfold Reqb.
  destruct (Req_dec 0 1).
  - apply eq01_False in e.
    destruct e.
  - unfold Rltb.
    destruct (Rlt_dec 0 1).
    + trivial.
    + apply Rnot_lt_le in n0.
      apply le10_False in n0.
      destruct n0. Qed.
Example test_tr2partial2: tr2partial [pp (Some 0) ; ip (fun x => Some x) (Some 0) Inf] (-1) = None.
Proof.
  unfold tr2partial.
  unfold update_pt.
  unfold update_in.
  unfold Inf.
  unfold Reqb.
  destruct (Req_dec 0 (-1)).
  - apply eq0m1_False in e.
    destruct e.
  - unfold Rltb.
    destruct (Rlt_dec 0 (-1)).
    + apply Rplus_lt_compat_r with (r:=1) in r.
      assert (0 + 1 = 1). { ring. } rewrite H in r.
      assert (-1 + 1 = 0). { ring. } rewrite H0 in r.
      apply Rlt_le in r.
      apply le10_False in r.
      destruct r.
    + unfold empty.
      trivial. Qed.