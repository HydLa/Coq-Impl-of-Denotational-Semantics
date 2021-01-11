Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.ROrderedType.
Open Scope R_scope.

Lemma Rge_3_0: 3 >= 0.
Proof.
  unfold IZR. unfold IPR. unfold IPR_2.
  assert (R0 = R0 + R0). { ring. } rewrite H.
  apply Rplus_ge_compat.
  - apply Rle_ge. apply Rle_0_1.
  - rewrite H.
    apply Rplus_ge_compat.
    apply Rle_ge. apply Rle_0_1.
    apply Rle_ge. apply Rle_0_1. Qed.

Lemma Rle_0_2: 0 <= 2.
  unfold IZR. unfold IPR. unfold IPR_2.
  assert (R0 = R0 + R0). { ring. } rewrite H.
  apply Rplus_le_compat.
  - apply Rle_0_1.
  - apply Rle_0_1. Qed.

Lemma Rle_0_4: 0 <= 4.
Proof.
  unfold IZR. unfold IPR. unfold IPR_2.
  assert (R0 = R0 * R0). { ring. } rewrite H.
  apply Rmult_le_compat.
  - right. ring.
  - right. ring.
  - apply Rle_0_2.
  - apply Rle_0_2. Qed.

Lemma lt_n_SSn: forall n : nat, (n < S (S n))%nat.
Proof.
  intros.
  induction n.
  - auto.
  - apply le_n_S.
    trivial. Qed.

Lemma eq01_False: 0 = 1 -> False.
Proof.
  unfold IZR. unfold IPR.
  intros.
  symmetry in H.
  apply Req_le in H.
  apply Rle_lt_trans with (r3:=R1) in H.
  - apply Rlt_irrefl in H.
    destruct H.
  - apply Rlt_0_1. Qed.

Tactic Notation "toR01" :=
  unfold IZR;
  unfold IPR;
  unfold IPR_2.

Lemma le21_False: 2 <= 1 -> False.
Proof.
  intros.
  apply Rle_lt_trans with (r3:=2) in H.
  + apply Rlt_irrefl in H.
    destruct H.
  + apply Rplus_lt_reg_l with (r:=-1).
    assert (-1 + 1 = 0). { apply Rplus_opp_l. } rewrite H0.
    assert (-1 + 2 = 1). { ring. } rewrite H1.
    apply Rlt_0_1.
    Qed.

Lemma le10_False: 1 <= 0 -> False.
Proof.
  intros.
  apply Rle_lt_trans with (r3:=1) in H.
  - apply Rlt_irrefl in H.
    destruct H.
  - apply Rlt_0_1. Qed.

Lemma eq0m1_False: 0 = -1 -> False.
Proof.
  intros.
  apply Req_le in H.
  apply Rle_lt_trans with (r3:=0) in H.
  - apply Rlt_irrefl in H.
    destruct H.
  - apply Rplus_lt_reg_r with (r:=1).
    assert (-1 + 1 = 0). { apply Rplus_opp_l. } rewrite H0.
    assert (0 + 1 = 1). { ring. } rewrite H1.
    apply Rlt_0_1. Qed.

Lemma forall_iff_expand: forall (X : Type) (P Q : X -> Prop),
  (forall x : X, P x <-> Q x) -> ((forall x : X, P x) <-> (forall x : X, Q x)).
Proof.
  intros.
  split.
  - intros.
    apply H.
    apply H0.
  - intros.
    apply H.
    apply H0. Qed.
Lemma imp_expand: forall (P Q R : Prop), (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)).
Proof.
  intros.
  apply H.
  - trivial.
  - apply H0.
    apply H1. Qed.
Lemma forall_and_expand: forall (X : Type) (P Q : X -> Prop),
  (forall x : X, P x /\ Q x) <-> ((forall x : X, P x) /\ (forall x : X, Q x)).
Proof.
  split.
  - split.
    + apply H.
    + apply H.
  - split.
    + apply H.
    + apply H. Qed.