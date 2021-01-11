Require Import Coq.Bool.Bool.
Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Reals.ROrderedType.
Require Import Lists.List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Open Scope R_scope.
Require Import Ascii String.

From HYDLA Require Export PropFormula.

Variable x x' x'' prevx prevx': partial.
Variable t: R.
Definition INIT := [[$ x(t) = Some 10; $ x'(t) = Some 0]].
Definition FALL := [[[]$ x''(t) = Some(-10)]].
Definition BOUNCE := [[[]prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))]].
(* add history about continuity for implementation *)
Definition Q : history :=
  "INIT" ~~> [[$ x(t) = Some 10; $ x'(t) = Some 0]; nil; nil; nil];
  "FALL" ~~> [[[]$ x''(t) = Some(-10); $ x''(t) = Some(-10)];
              [$ x''(t) = Some(-10)]; [$ x''(t) = Some(-10)]; [$ x''(t) = Some(-10)]];
  "BOUNCE" ~~> [[[]prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))];
                [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))];
                [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t))];
                [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))]];
  "continuity" ~~> [[$rightCont x t; $rightCont x' t; $rightCont x'' t]; [$cont x t; $cont x' t; $cont x'' t];
                    [$cont x t; $rightCont x' t]; [$cont x t; $cont x' t; $cont x'' t]].
Definition MS : set string := ["INIT"%string; "FALL"%string; "BOUNCE"%string].

Theorem semantics_i :
  let init := unfold_some (Q "INIT"%string) in
  let bounce := unfold_some (Q "BOUNCE"%string) in
  let fall := unfold_some (Q "FALL"%string) in
    Is_true (c_eq init (closure init)) /\
    Is_true (c_eq fall (closure fall)) /\
    Is_true (c_eq bounce (closure bounce)).
Proof.
  intros. split.
  - unfold Is_true, c_eq, c_subset, is_subset. simpl.
    destruct (Feq_dec ($ x t = Some 10) ($ x t = Some 10)).
    + destruct (Feq_dec ($ x' t = Some 0) ($ x t = Some 10)).
      { reflexivity. }
      destruct (Feq_dec ($ x' t = Some 0) ($ x' t = Some 0)).
      { reflexivity. }
      { congruence. }
    + congruence.
  - split.
    + unfold Is_true, c_eq, c_subset, is_subset. simpl.
      destruct (Feq_dec ($ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
      { congruence. }
      destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
      { simpl. destruct (Feq_dec ([] $ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
        { destruct (Feq_dec ($ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
          { congruence. }
          simpl. destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
          { unfold set_mem, is_subset. simpl. destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
            { destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
              { simpl. destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
                { reflexivity. }
                congruence.
              }
              congruence.
            }
            congruence.
          }
          congruence.
        }
        congruence.
      }
      congruence.
    + unfold Is_true, c_eq, c_subset, is_subset. simpl.
      destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
      { congruence. }
      destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
      { simpl. destruct (Feq_dec ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
        { destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
          { congruence. }
          destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
          { destruct (Feq_dec ($ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
            { congruence. }
            destruct (Feq_dec ($ x' t = mul (Some (-1)) (prevx' t)) ($ x' t = mul (Some (-1)) (prevx' t))).
            { unfold is_subset. simpl. destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
              { unfold set_mem. simpl. destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
                { reflexivity. }
                congruence.
              }
              congruence.
            }
            congruence.
          }
          congruence.
        }
        congruence.
      }
      congruence. Qed.

Lemma cl_INIT: closure INIT = INIT.
Proof.
  unfold closure, INIT, closure2. simpl.
  unfold eq_f.
  destruct (Feq_dec ($ x t = Some 10) ($ x t = Some 10)).
  { destruct (Feq_dec ($ x' t = Some 0) ($ x' t = Some 0)).
    { reflexivity. }
    congruence.
  }
  congruence. Qed.
Lemma cl_FALL:
  closure FALL = [[[]$ x''(t) = Some(-10); $ x''(t) = Some(-10)]; [$ x''(t) = Some(-10)]].
Proof.
  unfold closure, FALL, closure2. simpl.
  destruct (Feq_dec ($ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
  { congruence. }
  unfold eq_f.
  destruct (Feq_dec ([] $ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
  { reflexivity. }
  congruence. Qed.
Lemma cl_BOUNCE:
  closure BOUNCE
    = [[[]prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))];
       [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t))]].
Proof.
  unfold closure, BOUNCE, closure2. simpl.
  destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
  { congruence. }
  unfold eq_f. destruct (Feq_dec ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
  { reflexivity. }
  congruence. Qed.
Theorem semantics_ii :
  let init := unfold_some (Q "INIT"%string) in
  let bounce := unfold_some (Q "BOUNCE"%string) in
  let fall := unfold_some (Q "FALL"%string) in
    Is_true (c_subset (closure INIT) init) /\
    Is_true (c_subset (closure FALL) fall) /\
    Is_true (c_subset (closure BOUNCE) bounce).
Proof.
  intros.
  rewrite -> cl_INIT.
  rewrite -> cl_FALL.
  rewrite -> cl_BOUNCE.
 unfold Is_true, c_subset, is_subset. simpl. split.
  - destruct (Feq_dec ($ x t = Some 10) ($ x t = Some 10)).
    { destruct (Feq_dec ($ x' t = Some 0) ($ x t = Some 10)).
      { reflexivity. }
      destruct (Feq_dec ($ x' t = Some 0) ($ x' t = Some 0)).
      { reflexivity. }
      congruence.
    }
    congruence.
  - split.
    + destruct (Feq_dec ([] $ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
      { destruct (Feq_dec ($ x'' t = Some (-10)) ([] $ x'' t = Some (-10))).
        { congruence. }
        destruct (Feq_dec ($ x'' t = Some (-10)) ($ x'' t = Some (-10))).
        { reflexivity. }
        congruence.
      }
      congruence.
    + destruct (Feq_dec ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
      { destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) ([] prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
        { congruence. }
        destruct (Feq_dec (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t)) (prevx t = Some 0 ~> $ x' t = mul (Some (-1)) (prevx' t))).
        { reflexivity. }
        congruence.
      }
      congruence. Qed.

Definition y := Some 0 |--> Some 10; (fun t => Some(10-5*t^2))|_(Some 0, Some(sqrt 2));
                Some(sqrt 2) |--> Some 0; (fun t => Some(20*sqrt(2)*t-5*t^2-30))|_(Some(sqrt 2), Some(3*sqrt(2))).
Definition y' := Some 0 |--> Some 0; (fun t => Some(-10*t))|_(Some 0, Some(sqrt 2));
                 Some(sqrt 2) |--> Some(10*sqrt(2)); (fun t => Some(20*sqrt(2)-10*t))|_(Some(sqrt 2), Some(3*sqrt(2))).
Definition y'' := Some 0 |--> Some(-10); (fun t => Some(-10))|_(Some 0, Some(sqrt 2));
                  (fun t => Some(-10))|_(Some(sqrt 2), Some(3*sqrt(2))).
Definition prevy := (fun t => Some(10-5*t^2))|_(Some 0, Some(sqrt 2));
                    Some(sqrt 2) |--> Some 0; (fun t => Some(20*sqrt(2)*t-5*t^2-30))|_(Some(sqrt 2), Some(3*sqrt(2))).
Definition prevy' := (fun t => Some(-10*t))|_(Some 0, Some(sqrt 2));
                     Some(sqrt 2) |--> Some(-10*sqrt(2)); (fun t => Some(20*sqrt(2)-10*t))|_(Some(sqrt 2), Some(3*sqrt(2))).
Definition prevy'' := (fun t => Some(-10))|_(Some 0, Some(3*sqrt(2))).

Theorem semantics_iii_s1_pp1 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let t := 0 in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x(t) = Some 10; $ x'(t) = Some 0;
              []$ x''(t) = Some(-10); $ x''(t) = Some(-10);
              []prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $rightCont x t; $rightCont x' t; $rightCont x'' t] in
  andl (map f2p QEt).
Proof.
  unfold map, f2p, andl, y, y', y'', prevy. simpl.
  repeat split.
  - destruct (Reqb 0 0) eqn:E.
    + trivial.
    + apply reqb00false in E.
      case E.
  - destruct (Reqb 0 0) eqn:E.
    + trivial.
    + apply reqb00false in E.
      case E.
  - destruct (Reqb 0 0) eqn:E.
    + trivial.
    + apply reqb00false in E.
      case E.
  - unfold update_pt, update_in.
    destruct (Rltb 0 0) eqn:E1.
    + simpl.
      destruct (Rltb 0 (sqrt 2)) eqn:E2.
      * destruct (Reqb 0 0) eqn:E3.
        -- rewrite Rmult_0_l.
           rewrite Rmult_0_r.
           rewrite Rminus_0_r.
           intros.
           inversion H.
           assert (H2: 10 = 0 -> False). { admit. }
           apply H2 in H1.
           case H1.
        -- apply reqb00false in E3.
           case E3.
      * assert (H: Rltb 0 (sqrt 2) = false -> False). { admit. }
        apply H in E2.
        case E2.
    + simpl.
      destruct (Reqb (sqrt 2) 0) eqn:E2.
      * assert (H: Reqb (sqrt 2) 0 = true -> False). { admit. }
        apply H in E2.
        case E2.
      * assert (H: Rltb (sqrt 2) 0 = false). { admit. }
        rewrite H. simpl.
        unfold empty.
        intros.
        inversion H0.
  - admit.
  - admit.
  - admit.
  Admitted.

Theorem semantics_iii_s1_ip2 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  0 < t < sqrt(2) -> andl (map f2p QEt).
Proof.
  unfold map, f2p, andl, y'', prevy. simpl.
  intros.
  repeat split.
  - destruct (Reqb 0 t) eqn:E.
    + trivial.
    + unfold update_in, Rltb. simpl.
      destruct (Rlt_dec 0 t). simpl.
      * destruct (Rlt_dec t (sqrt 2)).
        -- trivial.
        -- inversion H.
           contradiction.
      * inversion H.
        contradiction.
  - unfold update_in, Rltb. simpl.
    destruct (Rlt_dec 0 t). simpl.
    + destruct (Rlt_dec t (sqrt 2)).
      * admit.
      * inversion H.
        contradiction.
    + inversion H.
      contradiction.
  - Admitted.

Theorem semantics_iii_s1_pp3 :
  let E := ["INIT"%string; "BOUNCE"%string] in
  let t := sqrt(2) in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $rightCont x' t] in
  andl (map f2p QEt).
Proof.
  unfold map, f2p, andl. simpl.
  repeat split.
  - intros.
    unfold y', prevy', update_pt.
    destruct (Reqb 0 (sqrt 2)) eqn:E1.
    + apply Reqb_eq in E1.
      rewrite <- sqrt_0 in E1.
      apply sqrt_inj in E1.
      * assert (H2: 0 = 2 -> False). { admit. }
        apply H2 in E1. case E1.
      * apply Rle_refl.
      * apply Rle_0_2.
    + unfold update_in, update_pt, Rltb.
      destruct (Rlt_dec (sqrt 2) (sqrt 2)).
      * apply Rlt_irrefl in r. case r.
      * rewrite andb_false_r. simpl.
        destruct (Reqb (sqrt 2) (sqrt 2)) eqn:E2.
        -- unfold mul. admit.
        -- apply test_Reqb2 in E2.
           apply Rdichotomy in E2.
           generalize E2. intros [E3|E4].
           { contradiction. }
           { contradiction. }
  - unfold y', mul, prevy'. simpl.
    destruct (Reqb 0 (sqrt 2)) eqn:E1.
    + apply Reqb_eq in E1.
      assert (H: 0 = sqrt 2 -> False). { admit. }
      apply H in E1. case E1.
    + unfold update_in, update_pt, Rltb.
      destruct (Rlt_dec (sqrt 2) (sqrt 2)).
      * apply Rlt_irrefl in r. case r.
      * rewrite andb_false_r. simpl.
        destruct (Reqb (sqrt 2) (sqrt 2)) eqn:E2.
        -- assert (H: -1 * (-10 * sqrt 2) = 10 * sqrt 2). { admit. }
           rewrite H. trivial.
        -- apply test_Reqb2 in E2.
           apply Rdichotomy in E2.
           generalize E2. intros [E3|E4].
           { contradiction. } { contradiction. }
  Admitted.

Theorem semantics_iii_s1_ip4 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  sqrt(2) < t < 3*sqrt(2) -> andl (map f2p QEt).
Proof.
  unfold map, f2p, andl. simpl.
  repeat split.
  - unfold y'', update_pt, update_in.
    destruct (Reqb 0 t) eqn:E1.
    + trivial.
    + unfold Rltb.
      destruct (Rlt_dec t (sqrt 2)).
      * inversion H.
        apply Rgt_asym in r.
        contradiction.
      * rewrite andb_false_r.
        -- destruct (Rlt_dec (sqrt 2) t).
           ++ destruct (Rlt_dec t (3*sqrt 2)).
              { reflexivity. }
              { inversion H. contradiction. }
           ++ inversion H. contradiction.
  - unfold prevy, update_in, update_pt. simpl.
    unfold Rltb.
    destruct (Rlt_dec t (sqrt 2)) eqn:E1.
    + inversion H.
      apply Rgt_asym in H0.
      contradiction.
    + rewrite andb_false_r.
      destruct (Reqb (sqrt 2) t) eqn:E2.
      * apply Reqb_eq in E2.
        inversion H.
        assert (H2: sqrt 2 = t -> sqrt 2 < t -> False). { admit. }
        apply H2 in E2.
        { case E2. } { apply H0. }
      * destruct (Rlt_dec (sqrt 2) t) eqn:E3.
        -- destruct (Rlt_dec t (3*sqrt 2)) eqn:E4.
           ++ simpl. intros.
              assert (H1: Some (20 * sqrt 2 * t - 5 * (t * (t * 1)) - 30) = Some 0 -> False). { admit. }
              apply H1 in H0. case H0.
           ++ unfold empty. simpl.
              intros.
              discriminate H0.
        -- unfold empty. simpl.
           intros. discriminate H0.
  Admitted.

Theorem semantics_iii_s2_1_pp1 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let t := 0 in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x(t) = Some 10; $ x'(t) = Some 0;
              []$ x''(t) = Some(-10); $ x''(t) = Some(-10);
              []prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $rightCont x t; $rightCont x' t; $rightCont x'' t] in
  ~ exists E', ssubset E' MS = true /\ ssubset E E' = true /\ E <> E' /\ andl (map f2p QEt).
Proof.
  unfold not.
  intros.
  destruct H.
  generalize H.
  unfold MS.
  intros [A [B [C D]]].
  assert (H1: x0 = ["INIT"%string; "FALL"%string; "BOUNCE"%string]). { admit. }
  rewrite <- H1 in C. clear H.
  assert (H: x0 = x0). { trivial. }
  apply C in H. case H.
  Admitted.

Theorem semantics_iii_s2_1_ip2 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  0 < t < sqrt(2) -> ~ exists E', ssubset E' MS = true /\ ssubset E E' = true /\ E <> E' /\ andl (map f2p QEt).
Proof.
  unfold not.
  intros.
  destruct H0. destruct H0. destruct H1. destruct H2.
  assert (H4: x0 = ["INIT"%string; "FALL"%string; "BOUNCE"%string]). { admit. }
  rewrite <- H4 in H2.
  assert (H5: x0 = x0). { trivial. }
  apply H2 in H5. case H5.
  Admitted.

Theorem semantics_iii_s2_1_pp3 :
  let E := ["INIT"%string; "BOUNCE"%string] in
  let t := sqrt 2 in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QE't := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $rightCont x' t] in
  ~ exists E', ssubset E' MS = true /\ ssubset E E' = true /\ E <> E' /\ andl (map f2p QE't).
Proof.
  unfold not.
  intros.
  destruct H. destruct H. destruct H0. destruct H1.
  assert (H3: x0 = ["INIT"%string; "FALL"%string; "BOUNCE"%string]). { admit. }
  unfold andl, map, f2p in H2.
  simpl in H2.
  repeat destruct H2.
  assert (H9: y'' (sqrt 2) = None). { admit. }
  rewrite H9 in H8.
  inversion H8.
  Admitted.

Theorem semantics_iii_s2_1_ip4 :
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  sqrt(2) < t < 3*sqrt(2) -> ~ exists E', ssubset E' MS = true /\ ssubset E E' = true /\ E <> E' /\ andl (map f2p QEt).
Proof.
  unfold not.
  intros.
  destruct H0. destruct H0. destruct H1. destruct H2.
  unfold MS in H0.
  assert (H4: x0 = ["INIT"%string; "FALL"%string; "BOUNCE"%string]). { admit. }
  rewrite <- H4 in H2.
  assert (H5: x0 = x0). { trivial. }
  apply H2 in H5. case H5.
  Admitted.

(* z : rival trajectory *)
(* set z to x, for "andl (map f2p QEt)" *)
Theorem semantics_iii_s2_2_pp1:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let t := 0 in
  let QEt := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [$ x(t) = Some 10; $ x'(t) = Some 0;
              []$ x''(t) = Some(-10); $ x''(t) = Some(-10);
              []prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $rightCont x t; $rightCont x' t; $rightCont x'' t] in
  ~ exists (z z' z'' prevz prevz' prevz'' : partial), exists E',
  let x := z in let x' := z' in let x'' := z'' in
  let prevx := prevz in let prevx' := prevz' in let prevx'' := prevz'' in
    ssubset E' MS = true
    /\ (forall t', t' < t /\ z(t') = y(t') /\ z'(t') = y'(t') /\ z''(t') = y''(t'))
    /\ (~ sim y z t \/ ~ sim y' z' t \/ ~ sim y'' z'' t)
    /\ ssubset E E' = true
    /\ andl (map f2p (QEt x x' x'' prevx prevx' prevx'')).
Proof.
  unfold not.
  intros. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
  destruct H. destruct H0. destruct H1. destruct H2.
  case H1.
  - intros.
    assert (H5: ~ rightCont x0 0). { admit. }
    unfold not in H5.
    unfold andl, map, f2p in H3. simpl in H3.
    destruct H3. destruct H3. destruct H3.
    apply H5 in H8.
    case H8.
  - intros. case H4.
    Admitted.

Theorem semantics_iii_s2_2_ip2:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let QEt := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [$ x''(t) = Some(-10); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
               $cont x t; $cont x' t; $cont x'' t] in
  0 < t < sqrt(2) -> ~ exists (z z' z'' prevz prevz' prevz'' : partial), exists E',
  let x := z in let x' := z' in let x'' := z'' in
  let prevx := prevz in let prevx' := prevz' in let prevx'' := prevz'' in
    ssubset E' MS = true
    /\ (forall t', t' < t /\ z(t') = y(t') /\ z'(t') = y'(t') /\ z''(t') = y''(t'))
    /\ (~ sim y z t \/ ~ sim y' z' t \/ ~ sim y'' z'' t)
    /\ ssubset E E' = true
    /\ andl (map f2p (QEt x x' x'' prevx prevx' prevx'')).
Proof.
  unfold not.
  intros.
  destruct H. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
  destruct H0. destruct H2. destruct H3. destruct H4.
  clear H0. clear H4.
  unfold andl, map, f2p in H5. simpl in H5.
  destruct H5. destruct H0. destruct H0.
  case H3.
  - intros.
    assert (H8: ~ leftCont x0 t \/ ~ leftCont x0 t). { admit. }
    case H8.
    + intros.
      unfold cont in H6.
      destruct H6.
      unfold not in H9.
      apply H9 in H6.
      case H6.
    + Admitted.

Theorem semantics_iii_s2_2_pp3_case1:
  let E := ["INIT"%string; "BOUNCE"%string] in
  let t := sqrt 2 in
  let QEt := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
               $cont x t; $rightCont x' t] in
  ~ exists (z z' z'' prevz prevz' prevz'' : partial), exists E',
  let x := z in let x' := z' in let x'' := z'' in
  let prevx := prevz in let prevx' := prevz' in let prevx'' := prevz'' in
  let QE't := QEt in E = E' /\
    ssubset E' MS = true
    /\ (forall t', t' < t /\ z(t') = y(t') /\ z'(t') = y'(t') /\ z''(t') = y''(t'))
    /\ (~ sim y z t \/ ~ sim y' z' t \/ ~ sim y'' z'' t)
    /\ ssubset E E' = true
    /\ andl (map f2p (QE't x x' x'' prevx prevx' prevx'')).
Proof.
  unfold not.
  intros.
  destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
  destruct H. destruct H0. destruct H1. destruct H2. destruct H3.
  clear H0. clear H3.
  unfold andl in H4. simpl in H4.
  destruct H4. repeat destruct H0.
  destruct H2.
  - clear H. clear H1. clear H5. clear H6. clear H3.
    assert (G: cont y (sqrt 2)). { admit. } unfold cont in G. destruct G.
    unfold sim in H0.
    unfold cont in H4. destruct H4.
    destruct H0.
    split.
    + split.
      * intros. trivial.
      * intros. trivial.
    + split.
      * intros. trivial.
      * intros. trivial.
  - destruct H0.
    + clear H. clear H1. clear H6. clear H4.
      assert (H: ~ leftCont x1 (sqrt 2)). { admit. } (* by H5 *)
      assert (G: rightCont y' (sqrt 2) /\ ~ leftCont y' (sqrt 2)). { admit. }
      unfold sim in H0. destruct H0.
      destruct G.
      split.
      * split.
        -- intros.
           unfold not in H1.
           apply H1 in H2.
           case H2.
        -- intros.
           unfold not in H.
           apply H in H2.
           case H2.
      * split.
        -- intros. trivial.
        -- intros. trivial.
    + clear H. clear H1. clear H6. clear H4. clear H3.
      assert (H: ~ leftCont x2 (sqrt 2) /\ ~ rightCont x2 (sqrt 2)). { admit. } (* by H0 and def of derivative *)
      assert (G: ~ leftCont y'' (sqrt 2) /\ ~ rightCont y'' (sqrt 2)). { admit. }
      unfold not in H. destruct H.
      unfold not in G. destruct G.
      unfold sim in H0. destruct H0.
      split.
      * split.
        -- intros.
           apply H2 in H0.
           case H0.
        -- intros.
           apply H in H0.
           case H0.
      * split.
        -- intros.
           apply H3 in H0.
           case H0.
        -- intros.
           apply H1 in H0.
           case H0.
  Admitted.

Theorem semantics_iii_s2_2_pp3_case2:
  let E := ["INIT"%string; "BOUNCE"%string] in
  let t := sqrt 2 in
  let QEt := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
               $cont x t; $rightCont x' t] in
  ~ exists (z z' z'' prevz prevz' prevz'' : partial), exists E',
  let x := z in let x' := z' in let x'' := z'' in
  let prevx := prevz in let prevx' := prevz' in let prevx'' := prevz'' in
  let QE't := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [$ x''(t) = Some(-10);
               prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
               $cont x t; $rightCont x' t] in
  E' = ["INIT"%string; "FALL"%string; "BOUNCE"%string] /\
    ssubset E' MS = true
    /\ (forall t', t' < t /\ z(t') = y(t') /\ z'(t') = y'(t') /\ z''(t') = y''(t'))
    /\ (~ sim y z t \/ ~ sim y' z' t \/ ~ sim y'' z'' t)
    /\ ssubset E E' = true
    /\ andl (map f2p (QE't x x' x'' prevx prevx' prevx'')).
Proof.
  unfold not.
  intros.
  destruct H. destruct H. destruct H. destruct H. destruct H. destruct H. destruct H.
  destruct H. destruct H0. destruct H1. destruct H2. destruct H3.
  clear H0. clear H2. clear H3. clear H. clear H1.
  unfold andl in H4. simpl in H4.
  destruct H4. repeat destruct H.
  clear H3. clear H1. clear H0.
  assert (H: x2 (sqrt 2) = None). { admit. } (* by H2 and def of derivative *)
  rewrite H in H4.
  discriminate.
  Admitted.

Theorem semantics_iii_s2_2_ip4:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let QEt := fun (x x' x'' prevx prevx' prevx'' : partial) =>
              [$ x''(t) = Some(-10); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
               $cont x t; $cont x' t; $cont x'' t] in
  sqrt(2) < t < 3*sqrt(2) -> ~ exists (z z' z'' prevz prevz' prevz'' : partial), exists E',
  let x := z in let x' := z' in let x'' := z'' in
  let prevx := prevz in let prevx' := prevz' in let prevx'' := prevz'' in
    ssubset E' MS = true
    /\ (forall t', t' < t /\ z(t') = y(t') /\ z'(t') = y'(t') /\ z''(t') = y''(t'))
    /\ (~ sim y z t \/ ~ sim y' z' t \/ ~ sim y'' z'' t)
    /\ ssubset E E' = true
    /\ andl (map f2p (QEt x x' x'' prevx prevx' prevx'')).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0. destruct H0.
  destruct H0. destruct H1. destruct H2. destruct H3.
  clear H0. clear H3.
  simpl in H4.
  unfold andl in H4. simpl in H4.
  destruct H4. destruct H0. destruct H0.
  case H2.
  - intros.
    assert (H8: ~ leftCont x0 t \/ ~ leftCont x0 t). { admit. }
    case H8.
    + intros.
      unfold cont in H5.
      destruct H5.
      unfold not in H7.
      apply H7 in H5.
      case H5.
    + Admitted.

Theorem semantics_iii_s3_pp1:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let t := 0 in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x(t) = Some 10; $ x'(t) = Some 0;
              []$ x''(t) = Some(-10); $ x''(t) = Some(-10);
              []prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $rightCont x t; $rightCont x' t; $rightCont x'' t] in
  prevx(t) = Some 0 -> set_mem Feq_dec ($ x'(t) = mul (Some(-1)) (prevx'(t))) QEt = true.
Proof.
  simpl.
  intros.
  unfold prevy, update_in, update_pt, Rltb in H.
  destruct (Rlt_dec 0 0) in H.
  - apply Rlt_irrefl in r. case r.
  - simpl in H.
    destruct (Reqb (sqrt 2) 0) eqn:E1.
    + assert (H2: Reqb (sqrt 2) 0 = true -> False). { admit. }
      apply H2 in E1. case E1.
    + destruct (Rlt_dec (sqrt 2) 0).
      * assert (H2: sqrt 2 < 0 -> False). { admit. }
        apply H2 in r. case r.
      * simpl in H.
        inversion H.
  Admitted.

Theorem semantics_iii_s3_ip2:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  0 < t < sqrt(2) -> prevx(t) = Some 0 -> set_mem Feq_dec ($ x'(t) = mul (Some(-1)) (prevx'(t))) QEt = true.
Proof.
  intros.
  assert (H1: prevx0 t = Some 0 -> False). { admit. }
  apply H1 in H0. case H0.
  Admitted.

Theorem semantics_iii_s3_pp3:
  let E := ["INIT"%string; "BOUNCE"%string] in
  let t := sqrt 2 in 
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $rightCont x' t] in
  prevx(t) = Some 0 -> set_mem Feq_dec ($ x'(t) = mul (Some(-1)) (prevx'(t))) QEt = true.
Proof.
  intros.
  unfold QEt. simpl.
  destruct (Feq_dec ($ x'0 t0 = mul (Some (-1)) (prevx'0 t0)) (prevx0 t0 = Some 0 ~> $ x'0 t0 = mul (Some (-1)) (prevx'0 t0))).
  - trivial.
  - destruct (Feq_dec ($ x'0 t0 = mul (Some (-1)) (prevx'0 t0)) ($ x'0 t0 = mul (Some (-1)) (prevx'0 t0))).
    + trivial.
    + contradiction.
  Qed.

Theorem semantics_iii_s3_ip4:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x''(t) = Some(-10);
              prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $cont x t; $cont x' t; $cont x'' t] in
  sqrt(2) < t < 3*sqrt(2) -> prevx(t) = Some 0 -> set_mem Feq_dec ($ x'(t) = mul (Some(-1)) (prevx'(t))) QEt = true.
Proof.
  intros.
  assert (H1: prevx0 t = Some 0 -> False). { admit. }
  apply H1 in H0. case H0.
  Admitted.

Theorem semantics_iii_s4_pp1:
  let E := ["INIT"%string; "FALL"%string; "BOUNCE"%string] in
  let t := 0 in
  let x := y in let x' := y' in let x'' := y'' in
  let prevx := prevy in let prevx' := prevy' in let prevx'' := prevy'' in
  let QEt := [$ x(t) = Some 10; $ x'(t) = Some 0;
              []$ x''(t) = Some(-10); $ x''(t) = Some(-10);
              []prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t)); prevx(t) = Some 0 ~> $ x'(t) = mul (Some(-1)) (prevx'(t));
              $rightCont x t; $rightCont x' t; $rightCont x'' t] in
  leftCont x t -> set_mem Feq_dec ($leftCont x t) QEt = true
  /\ leftCont x' t -> set_mem Feq_dec ($leftCont x' t) QEt = true
  /\ leftCont x'' t -> set_mem Feq_dec ($leftCont x'' t) QEt = true
  /\ rightCont x t -> set_mem Feq_dec ($rightCont x t) QEt = true
  /\ rightCont x' t -> set_mem Feq_dec ($rightCont x' t) QEt = true
  /\ rightCont x'' t -> set_mem Feq_dec ($rightCont x'' t) QEt = true.
Proof.
  Admitted.