Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.ROrderedType.
Require Import Coq.Logic.Classical.
Require Import Omega.
Open Scope R_scope.

From HYDLA Require Export Util.

(* option R means R with bottom *)
(* partial mean partial function on R *)
Definition partial := R -> option R.

(* empty maps nothing *)
Definition empty : partial := (fun _ => None).
Example test_empty1: empty 0 = None.
Proof. reflexivity. Qed.
Example test_empty2: empty 1 = None.
Proof. reflexivity. Qed.
Example test_empty3: empty (-1) = None.
Proof. reflexivity. Qed.

(* result of any arithmetic operation with None is None *)
Definition minus (x : option R) (y : option R) : option R :=
  match (x, y) with
  | (Some x', Some y') => Some (x' - y')
  | (_, _) => None
  end.
Example test_minus1: minus (Some 1) (Some 1) = Some 0.
Proof.
  unfold minus.
  assert (1 - 1 = 0). { ring. } rewrite H.
  trivial. Qed.
Example test_minus2: minus (Some 1) None = None.
Proof. reflexivity. Qed.
Example test_minus3: minus None None = None.
Proof. reflexivity. Qed.
Example test_minus4: minus (Some 2) (Some 1) = Some 1.
Proof.
  unfold minus.
  assert (2 - 1 = 1). { ring. } rewrite H.
  trivial. Qed.

Definition mul (x : option R) (y : option R) : option R :=
  match (x, y) with
  | (Some x', Some y') => Some (x' * y')
  | (_, _) => None
  end.

Definition abs (x : option R) : option R :=
  match x with
  | Some x => Some (Rabs x)
  | None => None
  end.
Example test_abs1: abs (Some 3) = Some 3.
Proof.
  simpl.
  rewrite Rabs_right.
  - trivial.
  - apply Rge_3_0. Qed.
Example test_abs2: abs (Some (-3)) = Some 3.
Proof.
  simpl.
  assert (Rabs (-3) = Rabs 3). { apply Rabs_Ropp. } rewrite H.
  rewrite Rabs_right.
  - trivial.
  - apply Rge_3_0. Qed.
Example test_abs3: abs None = None.
Proof. reflexivity. Qed.

(* result of comparison operation with None is None *)
Definition lt (r1 r2 : option R) : Prop :=
  match (r1, r2) with
  | (Some x', Some y') => x' < y'
  | (_, _) => False
  end.
Example test_lt1: lt (Some 1) (Some 2).
Proof.
  unfold lt.
  unfold IZR. unfold IPR. unfold IPR_2.
  assert ((R1 < R1 + R1) = (R0 + R1 < R1 + R1)). { rewrite Rplus_0_l. trivial. } rewrite H.
  apply Rplus_lt_compat_r.
  apply Rlt_0_1. Qed.
Example test_lt2: lt (Some 100) None <-> False.
Proof. reflexivity. Qed.
Example test_lt3: lt None None <-> False.
Proof. reflexivity. Qed.

(* left limit about partial *)
(* "leftLim f a l" mean left limit of f at a is l *)
Definition leftLim (f : partial) (a : R) (l : option R) : Prop :=
  forall eps : R, eps > 0 ->
    exists del : R, del > 0 /\
      forall x : R, 0 < a - x < del -> lt (abs (minus (f x) l)) (Some eps).
Example test_leftLim1: leftLim (fun x => Some x) 2 (Some 2).
Proof.
  unfold leftLim.
  intros eps H1.
  exists eps. (* take delta as eps *)
  split.
  - trivial.
  - intros.
    simpl.
    unfold lt.
    rewrite Rabs_minus_sym.
    rewrite Rabs_right.
    + apply H.
    + unfold Rge.
      left.
      apply H. Qed.
Example test_leftLim2: leftLim (fun x => Some (x^2)) 2 (Some 4).
Proof.
  unfold leftLim.
  intros eps H1.
  exists (sqrt(4+eps)-2).
  split.
  - apply Rplus_gt_reg_l with (r:=2).
    assert (2 + 0 = 2). { rewrite Rplus_comm. apply Rplus_0_l. } rewrite H.
    assert (2 + (sqrt (4 + eps) - 2) = sqrt (4 + eps)). {
      assert (sqrt (4 + eps) - 2 = -2 + sqrt (4 + eps)). { apply Rplus_comm. }
      rewrite H0.
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_l.
      trivial.
    } rewrite H0.
    rewrite <- sqrt_square.
    + assert (2 * 2 = 4). { ring. } rewrite H2.
      apply Rlt_gt.
      apply sqrt_lt_1.
      * apply Rle_0_4.
      * assert (0 = 0 + 0). { ring. } rewrite H3.
        apply Rplus_le_compat.
        -- apply Rle_0_4.
        -- left. apply H1.
      * assert ((4 < 4 + eps) = (4 + 0 < 4 + eps)). {
          assert (4 + 0 = 0 + 4). { apply Rplus_comm. } rewrite H3.
          rewrite Rplus_0_l. trivial.
        } rewrite H3.
        apply Rgt_lt.
        apply Rplus_gt_compat_l.
        apply H1.
    + unfold IZR. unfold IPR. unfold IPR_2. apply Rle_0_2.
  - intros x [HL HR].
    simpl.
    unfold lt.
    assert (x*1 = 1*x). { apply Rmult_comm. } rewrite H.
    rewrite Rmult_1_l.
    assert (Rabs (x * x - 4) = 4 - x * x). {
      assert (forall x : R, 0 < 2 - x -> x < 2). {
        intros.
        apply Rplus_lt_reg_l with (r:=-x0).
        rewrite Rplus_comm.
        rewrite Rplus_opp_r.
        rewrite Rplus_comm.
        apply H0.
      }
      apply H0 in HL.
      apply Rmult_gt_0_lt_compat with (r1:=x) (r2:=2) in HL.
      + assert (2*2=4). { ring. }
        rewrite H2 in HL.
        apply Rplus_lt_compat_r with (r:=-4) in HL.
        rewrite Rplus_opp_r in HL.
        assert (4 - x * x = -(x * x - 4)). { ring. } rewrite H3.
        apply Rabs_left.
        apply HL.
      + admit.
      + admit.
      + trivial.
    } rewrite H0.
    Admitted.

Definition rightLim (f : partial) (a : R) (l : option R) : Prop :=
  forall eps : R, eps > 0 ->
    exists del : R, del > 0 /\
      forall x : R, 0 < x - a < del -> lt (abs (minus (f x) l)) (Some eps).
Example test_rightLim1: rightLim (fun x => Some x) 2 (Some 2).
Proof.
  unfold rightLim.
  intros eps H1.
  exists eps.
  split.
  - trivial.
  - intros.
    simpl.
    unfold lt.
    rewrite Rabs_right.
    + apply H.
    + unfold Rge.
      left.
      apply H. Qed.
Example test_rightLim2: rightLim (fun x => Some (x^2)) 2 (Some 4).
Proof. Admitted.

Lemma forall_and_distribute:
  forall (X : Type) (P Q : X -> Prop),
    (forall x : X, P x -> Q x) -> ((forall x : X, P x) -> (forall x : X, Q x)).
Proof.
  intros.
  apply H.
  apply H0. Qed.

(* define limit by eps-del, not using leftLim and rightLim *)
Definition lim (f : partial) (a : R) (l : option R) : Prop :=
  forall eps : R, eps > 0 ->
    exists del : R, del > 0 /\
      forall x : R, 0 < Rabs(x - a) < del -> lt (abs (minus (f x) l)) (Some eps).
Lemma Rabs_preserve_pos: forall (x : R), 0 < x -> x = Rabs x.
Proof.
  intros.
  symmetry.
  apply Rabs_right.
  left.
  apply H. Qed.
Lemma tmp:
  forall (X : Type) (P Q : X -> Prop),
    ((forall x : X, P x) /\ (forall x : X, Q x)) -> (forall x : X, P x /\ Q x).
Proof.
  intros.
  split.
  + apply H.
  + apply H. Qed.

(* proof of equality *)
Theorem lim_iff_leftLim_and_rightLim:
  forall (f : partial) (a : R) (l : option R), lim f a l <-> leftLim f a l /\ rightLim f a l.
Proof.
  intros.
  unfold lim, leftLim, rightLim.
  split.
  - intros.
    apply forall_and_expand.
    generalize H.
    apply forall_and_distribute.
    intros.
    split.
    + intros.
      destruct H0 as [x0 [xa A]]. { trivial. }
      exists x0.
      split.
      * trivial.
      * intros.
        apply A.
        assert (Rabs (x1 - a) = Rabs (a - x1)). { apply Rabs_minus_sym. } rewrite H2.
        assert (a - x1 = Rabs (a - x1)). { apply Rabs_preserve_pos. apply H0. }
        rewrite <- H3.
        apply H0.
    + intros.
      destruct H0 as [x0 [xa A]]. { trivial. }
      exists x0.
      split.
      * trivial.
      * intros.
        apply A.
        assert (x1 - a = Rabs (x1 - a)). { apply Rabs_preserve_pos. apply H0. }
        rewrite <- H2.
        apply H0.
  - intros.
    apply tmp with (x:=eps) in H.
    destruct H.
    assert (eps > 0). { trivial. } (* add assumption *)
    apply H in H0.
    apply H1 in H2.
    destruct H0 as [x0 [xa A]].
    destruct H2 as [x1 [xb B]].
    exists (Rmin x0 x1). (* take min to converge both. *)
    split.
    + unfold Rmin.
      destruct (Rle_dec x0 x1).
      * trivial.
      * trivial.
    + intros x.
      unfold Rabs.
      destruct (Rcase_abs (x - a)).
      * intros.
        apply A. (* A *)
        assert (- (x - a) = a - x). { ring. } rewrite -> H2 in H0.
        split.
        -- apply H0.
        -- generalize H0. intros [C D].
           apply Rlt_le_trans with (r3 := x0) in D.
           ++ trivial.
           ++ apply Rmin_l.
      * intros.
        apply B. (* B *)
        generalize H0. intros [C D].
        split.
        -- trivial.
        -- apply Rlt_le_trans with (r3 := x1) in D.
           ++ trivial.
           ++ apply Rmin_r. Qed.

Lemma Rabs_pos_iff_neq: forall (a b : R), 0 < Rabs (a - b) <-> b <> a.
  split.
  - intros.
    unfold Rabs in H.
    destruct (Rcase_abs (a - b)).
    + apply Rplus_lt_compat_r with (r:=b) in r.
      assert (a - b + b = a). { ring. } rewrite H0 in r.
      rewrite Rplus_0_l in r.
      apply Rlt_not_eq in r.
      apply not_eq_sym.
      apply r.
    + apply Rplus_lt_compat_r with (r:=b) in H.
      assert (a - b + b = a). { ring. } rewrite H0 in H.
       rewrite Rplus_0_l in H.
      apply Rlt_not_eq in H.
      apply H.
  - intros.
    rewrite Rabs_minus_sym.
    apply Rabs_pos_lt.
    apply Rminus_eq_contra.
    apply H. Qed.
(* for any total function, the limit is equal to a limit when considered as partial function *)
Theorem preserve_limit:
  forall (f : R -> R) (a l : R), limit1_in f (D_x no_cond a) l a <-> lim (fun x => Some (f x)) a (Some l).
Proof.
  intros.
  unfold limit1_in, limit_in, lim, D_x, no_cond.
  apply forall_iff_expand.
  intros x.
  split.
  - apply imp_expand.
    intros.
    destruct H0 as [x0 [xp H0]].
    simpl in H0.
    simpl.
    exists x0.
    unfold R_dist in H0.
    unfold abs, lt.
    split.
    + apply xp.
    + intros x1.
      intros.
      apply H0.
      split.
      * split.
        -- apply I.
        -- apply Rabs_pos_iff_neq.
           apply H1.
      * apply H1.
  - apply imp_expand.
    intros.
    destruct H0 as [x0 [xp H0]].
    exists x0.
    simpl.
    simpl in H0.
    unfold R_dist.
    unfold lt, abs in H0.
    split.
    + apply xp.
    + intros.
      apply H0.
      split.
      * apply Rabs_pos_iff_neq.
        apply H1.
      * apply H1. Qed.

(* define continuity using limit *)
Definition leftCont (f : partial) (x : R) : Prop := leftLim f x (f x).
Definition rightCont (f : partial) (x : R) : Prop := rightLim f x (f x).
Definition cont (f : partial) (x : R) : Prop := leftCont f x /\ rightCont f x.
Example test_leftCont1: leftCont (fun x => Some x) 2.
Proof.
  unfold leftCont.
  apply test_leftLim1. Qed.
Example test_leftCont2: leftCont (fun x => Some (x^2)) 2.
Proof.
  unfold leftCont.
  assert (2^2=4). { ring. } rewrite H.
  apply test_leftLim2. Qed.
Example test_rightCont1: rightCont (fun x => Some x) 2.
Proof.
  unfold rightCont.
  apply test_rightLim1. Qed.
Example test_rightCont2: rightCont (fun x => Some (x^2)) 2.
Proof.
  unfold rightCont.
  assert (2^2=4). { ring. } rewrite H.
  apply test_rightLim2. Qed.
Example test_cont1: cont (fun x => Some x) 2.
Proof.
  unfold cont.
  split.
  - apply test_leftCont1.
  - apply test_rightCont1. Qed.
(* for any total function, the continuity is equal to a continuity when considered as partial function *)
Theorem preserve_continuity:
  forall (f : R -> R) (a l : R), continue_in f no_cond a <-> cont (fun x => Some (f x)) a.
Proof.
  intros.
  unfold continue_in, cont, leftCont, rightCont.
  split.
  - intros.
    apply lim_iff_leftLim_and_rightLim.
    apply preserve_limit.
    trivial.
  - intros.
    apply preserve_limit.
    apply lim_iff_leftLim_and_rightLim.
    trivial. Qed.

(* "sim f g x" mean f and g have same continuity at x *)
Definition sim (f g : partial) (x : R)
  := (leftCont f x <-> leftCont g x) /\ (rightCont f x <-> rightCont g x).
Example test_sim1: sim (fun x => Some x) (fun x => Some (x^2)) 2.
Proof.
  unfold sim.
  split.
  - split.
    + intros. apply test_leftCont2.
    + intros. apply test_leftCont1.
  - split.
    + intros. apply test_rightCont2.
    + intros. apply test_rightCont1. Qed.

Definition div (x : option R) (y : R) : option R :=
  match x with
  | Some x' => Some (x' / y)
  | _ => None
  end.
Example test_div1: div (Some 4) 2 = Some 2.
Proof.
  unfold div.
  assert (4 / 2 = 2). {
    apply Rmult_eq_reg_r with (r := 2).
    - assert (2 * 2 = 4). { ring. } rewrite H.
      unfold Rdiv.
      rewrite Rmult_assoc.
      assert (/ 2 * 2 = 1). { apply Rinv_l. auto. } rewrite H0.
      ring.
    - auto.
  }
  rewrite H.
  trivial. Qed.
Example test_div2: div None 2 = None.
Proof. reflexivity. Qed.

(* secant of f at a*)
Definition sec (f : partial) (a : R) := fun x => div (minus (f x) (f a)) (x - a).
(* "D f d a" means d is a derivative of f at a *)
Definition D (f d : partial) (a : R) : Prop :=
  lim (sec f a) a (d a)                                   (* usual differentiation *)
  \/ (~ lim (sec f a) a (d a) /\ cont f a /\ d a <> None) (* When it isn't differentiable, but it is continuous *)
  \/ (~ cont f a /\ d a = None).                          (* When it isn't continuous *)
(* Differentiation in partial is weak, so -> only *)
Theorem preserve_deriv:
  forall (f d: R -> R) (a : R), D_in f d no_cond a -> D (fun x => Some (f x)) (fun x => Some (d x)) a.
Proof.
  unfold D_in, D, sec.
  simpl.
  intros.
  left.
  apply preserve_limit.
  trivial. Qed.

Lemma dist_not_lt_at_bottom:
  forall (f : partial) (a x eps : R), f a = None -> not (lt (abs (minus (f x) (f a))) (Some eps)).
Proof.
  unfold not.
  intros.
  rewrite H in H0.
  unfold minus, abs, lt in H0.
  case_eq (f x).
  - intros.
    rewrite H1 in H0.
    case H0.
  - intros.
    rewrite H1 in H0.
    case H0.
  Qed.
Lemma half_in_interval:
  forall (x : R), x > 0 -> 0 < x / 2 < x.
Proof.
  intros.
  assert (0 < / 2).
  {
    apply pos_half_prf.
  }
  assert (0 = 0 / 2).
  {
    unfold Rdiv.
    rewrite Rmult_0_l.
    trivial.
  }
  rewrite H1.
  assert (0 / 2 < x / 2).
  {
    apply Rmult_lt_compat_r.
    - apply H0.
    - apply H.
  }
  split.
  - apply H2.
  - rewrite double_var.
    assert (x / 2 + 0 < x / 2 + x / 2 -> x / 2 < x / 2 + x / 2).
    {
      rewrite Rplus_0_r.
      trivial.
    }
    apply H3.
    apply Rgt_lt.
    apply Rplus_gt_compat_l.
    rewrite H1.
    apply H2.
  Qed.
Theorem not_left_cont_at_bottom:
  forall (f : partial) (a : R), f a = None -> not (leftCont f a).
Proof.
  unfold not, leftCont, leftLim.
  intros.
  specialize (H0 1).
  simpl in H0.
  assert (1 > 0).
  {
    apply Rlt_gt.
    apply Rlt_0_1.
  }
  apply H0 in H1.
  clear H0.
  destruct H1 as [A [B C]].
  specialize (C (a-A/2)).
  assert (a - (a - A / 2) = A / 2). { ring. }
  rewrite H0 in C.
  clear H0.
  apply half_in_interval in B.
  apply C in B.
  apply dist_not_lt_at_bottom in B.
  - case B.
  - apply H.
  Qed.
Theorem not_right_cont_at_bottom:
  forall (f : partial) (a : R), f a = None -> not (rightCont f a).
Proof.
  unfold not, rightCont, rightLim.
  intros.
  specialize (H0 1).
  assert (1 > 0).
  {
    apply Rlt_gt.
    apply Rlt_0_1.
  }
  apply H0 in H1.
  clear H0.
  destruct H1 as [A [B C]].
  specialize (C (a+A/2)).
  assert ((a + A / 2) - a = A / 2). { ring. }
  rewrite H0 in C.
  clear H0.
  apply half_in_interval in B.
  apply C in B.
  apply dist_not_lt_at_bottom in B.
  - case B.
  - apply H.
  Qed.
Theorem not_cont_at_bottom:
  forall (f : partial) (a : R), f a = None -> not (cont f a).
Proof.
  unfold not, cont.
  intros.
  destruct H0 as [H1 H2].
  apply not_left_cont_at_bottom in H.
  unfold not in H.
  apply H in H1.
  case H1.
  Qed.

Theorem deriv_bottom_at_bottom:
  forall (f d : partial) (a : R),
    D f d a /\ f a = None -> d a = None.
Proof.
  intros.
  destruct H as [A B].
  unfold D in A.
  destruct A as [HA | [HB | HC]].
  - unfold lim, sec in HA.
    specialize (HA 1).
    assert (1 > 0).
    { apply Rlt_gt. apply Rlt_0_1. }
    apply HA in H.
    clear HA.
    destruct H. destruct H.
    specialize (H0 (a+x/2)).
    assert (a + x / 2 - a = x / 2). { ring. }
    rewrite H1 in H0.
    clear H1.
    assert (Rabs(x/2) = x/2).
    {
      apply Rabs_pos_eq.
      apply Rlt_le.
      apply half_in_interval.
      apply H.
    }
    rewrite H1 in H0.
    clear H1.
    apply half_in_interval in H.
    apply H0 in H.
    clear H0.
    rewrite B in H.
    unfold lt, abs, minus, div in H.
    destruct (f (a + x / 2)).
    + case H.
    + case H.
  - destruct HB as [H1 [H2 H3]].
    apply not_cont_at_bottom in B.
    apply B in H2.
    case H2.
  - apply HC.
  Qed.
