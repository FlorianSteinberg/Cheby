From mathcomp Require Import all_ssreflect all_algebra.
From Stdlib Require Import Reals Psatz.
Require Import Coquelicot.Coquelicot Interval.Tactic CPoly.
Require Import Rstruct filter_Rlt generalities atan_asin_acos.

Import GRing.Theory.

Section Cheby_rec.

Definition Cheby n x := cos (INR n * acos x).

Lemma Cheby_0 x : -1 <= x <= 1 -> Cheby 0 x = 1.
Proof. by rewrite /Cheby Rmult_0_l cos_0. Qed.

Lemma Cheby_1 x : -1 <= x <= 1 -> Cheby 1 x = x.
Proof. by rewrite /Cheby Rmult_1_l; exact: cos_acos. Qed.

Lemma Cheby_rec x n : 
  -1 <= x <= 1 ->  Cheby n.+2 x = 2 * x * Cheby n.+1 x - Cheby n x.
Proof.
move=> H.
suff : Cheby n.+2 x + Cheby n x = 2 * x * Cheby n.+1 x.
  move=> <-; ring.
rewrite form1.
have-> : (INR n.+2 * acos x - INR n * acos x) / 2 = acos x.
  rewrite !S_INR; field.
have-> : (INR n.+2 * acos x + INR n * acos x) / 2 = INR n.+1 * acos x.
  rewrite !S_INR; field.
by rewrite cos_acos.
Qed.

Local Open Scope ring_scope.

Lemma pT_Cheby n (x: R):
	(-1 <= x <= 1)%R -> Cheby n x = ('T_n).[x].
Proof.
move => ineq.
elim/ltn_ind : n => [] [|[|n]] IH.
- by rewrite Cheby_0; try lra; rewrite pT0 hornerC.
- by	rewrite Cheby_1; try lra; rewrite pT1 hornerX.
rewrite pTSS Cheby_rec; try lra.
rewrite hornerD hornerM mulr2n hornerD hornerX hornerN.
by rewrite -!IH; toR; try lra; rewrite E.
Qed.
End Cheby_rec.

Lemma Cheby_cos n a : 0 <= a <= PI -> Cheby n (cos a) = cos ((INR n) * a).
Proof. move=> *; rewrite /Cheby acos_cos //. Qed.

Lemma cos_add_INR a n :
  cos (a + INR n * PI) = if Nat.even n then cos a else -cos a.
Proof.
elim: n => [|n IH]; first by rewrite /= Rmult_0_l Rplus_0_r.
rewrite S_INR Rmult_plus_distr_r Rmult_1_l -Rplus_assoc.
rewrite neg_cos IH Nat.even_succ -Nat.negb_even.
by case: Nat.even => /=; lra.
Qed.

Lemma Cheby_compi m n a : -1 <= a <= 1 -> Cheby n (Cheby m a) = Cheby (n * m) a.
Proof.
move=> Ha.
have U := acos_bound a.
rewrite /Cheby mult_INR Rmult_assoc.
set v := _ * acos a.
have HP := PI2_1;
have [k [r [-> Hr]]] : exists k, exists r, v = r + INR k * PI /\ (0 <= r <= PI).
  pose k := Z.to_nat (up (v / PI) - 1).
  exists k; exists (v - INR k * PI); split; try lra.
  rewrite INR_IZR_INZ Znat.Z2Nat.id; last first.
    suff : (0 < up (v / PI))%Z by lia.
    apply: lt_0_IZR.
    suff : 0 <= v / PI by case: (archimed (v / PI)); lra.
    apply: Rmult_le_pos.
      apply: Rmult_le_pos; try lra.
      by apply: pos_INR.
    by apply/Rlt_le/Rinv_0_lt_compat; lra.
  rewrite minus_IZR. 
  rewrite {1 3}(_ : v = (v / PI) * PI); last by field; lra.
  case: (archimed (v / PI)); nra.
rewrite Rmult_plus_distr_l -Rmult_assoc -mult_INR [RHS]cos_add_INR.
rewrite Nat.even_mul orbC.
rewrite cos_add_INR.
have [kE|kO] := boolP (Nat.even k).
  by rewrite acos_cos.
rewrite /= acos_opp acos_cos //.
rewrite (_ : INR n * (PI - r) = - (INR n * r) + INR n * PI); try ring.
by rewrite cos_add_INR cos_neg.
Qed.

Lemma RInt_cos_0_PI (m : nat) : 
  m <> 0%nat ->
   is_RInt (fun y : R => cos (INR m * y)) 0 PI 0.
Proof.
move=> mNZ.
apply: (is_RInt_ext  (fun y : R => /(INR m) * (INR m * cos (INR m * y + 0)))) => [x _|].
  by rewrite Rplus_0_r /=; field; apply: not_0_INR.
rewrite {3}(_ : 0 = /(INR m) * 0); try lra.
apply: is_RInt_scal.
apply: is_RInt_comp_lin.
rewrite Rmult_0_r !Rplus_0_r.
rewrite {2}(_ : 0 = sin (INR m * PI) - sin 0); last first.
  rewrite sin_0.
  elim: (m) => [|n IH]; first by rewrite Rmult_0_l sin_0; lra.
  rewrite S_INR Rmult_plus_distr_r Rmult_1_l.
  by rewrite neg_sin; lra.
apply: is_RInt_derive => [x _|x _].
  by apply/is_derive_Reals/derivable_pt_lim_sin.
apply: ex_derive_continuous.
apply: ex_derive_Reals_1.
exists (- sin x).
by apply/derivable_pt_lim_cos.
Qed.

Lemma RInt_cos_cos_0_PI (n m : nat) :
  RInt (fun y => cos (INR n * y) * cos (INR m * y)) 0 PI = 
           if (n == m) then if (n == 0%nat) then PI else PI/2 else 0.
Proof.
apply is_RInt_unique.
case: eqP=> [->|/= nDm].
  case: eqP => [->|/= mZ].
    apply: (is_RInt_ext (fun y => 1)) => [x _|].
      by rewrite !Rmult_0_l cos_0; lra.
    rewrite {2}(_ : PI = ((PI - 0) * 1)); try lra.
    by apply: is_RInt_const.
  pose f y := (/2) * (cos (INR (m + m) * y) + cos (INR (m - m) * y)).
  apply: (is_RInt_ext f) => [x _|].
    rewrite /f form1 -Rmult_minus_distr_r -minus_INR; last first.
      by rewrite -plusE -minusE; lia.
    rewrite -Rmult_plus_distr_r -plus_INR.
    rewrite (_ : (m + m - (m - m) = 2 * m)%coq_nat); last first.
      by rewrite -plusE -minusE; lia.
    rewrite (_ : (m + m + (m - m) = 2 * m)%coq_nat); last first.
      by rewrite -plusE -minusE; lia.
    rewrite !mult_INR (_ : INR 2 = 2); last by rewrite /=; lra.
    rewrite  [_ * _ * x]Rmult_assoc [_/2]Rinv_r_simpl_m /=; last by lra.
    by field.
  rewrite (_ : PI/2 = /2 * PI); try lra.
  apply: is_RInt_scal.
  rewrite {2}(_ : PI = 0 + PI); try lra.
  apply: is_RInt_plus.
    by apply: RInt_cos_0_PI; rewrite -!plusE; lia.
  apply: (is_RInt_ext (fun y => 1)) => [x _|].
    by rewrite subnn Rmult_0_l cos_0.
  rewrite {2}(_ : PI = (PI - 0) * 1); try lra.
  by apply: is_RInt_const.
wlog /leP nLm : m n nDm / (n <= m)%nat => [H|].
  case: (leqP n m) => [/H//|/ltnW/H H1]; first by apply.
  apply: (is_RInt_ext (fun y =>  cos (INR m * y) * cos (INR n * y))) => [x _|].
    by lra.
  by apply: H1; lia.
pose f y := (/2) * (cos (INR (m + n) * y) + cos (INR (m - n) * y)).
apply: (is_RInt_ext f) => [x Hx|].
  rewrite /f form1 -Rmult_minus_distr_r -minus_INR; last first.
    by rewrite -plusE -minusE; lia.
  rewrite (_ : (m + n - (m - n) = 2 * n)%coq_nat); last first.
    by rewrite -plusE -minusE; lia.
  rewrite -Rmult_plus_distr_r -plus_INR.
  rewrite (_ : (m + n + (m - n) = 2 * m)%coq_nat); last first.
    by rewrite -plusE -minusE; lia.
  rewrite !mult_INR (_ : INR 2 = 2); last by rewrite /=; lra.
  rewrite  [_ * _ * x]Rmult_assoc [_/2]Rinv_r_simpl_m; last by lra.
  rewrite  [_ * _ * x]Rmult_assoc [_/2]Rinv_r_simpl_m /=; last by lra.
  by field.
rewrite {2}(_ : 0 = /2 * 0); try lra.
apply: is_RInt_scal.
rewrite {2}(_ : 0 = 0 + 0); try lra.
apply: is_RInt_plus; apply: RInt_cos_0_PI; first by rewrite -plusE; lia.
rewrite -minusE; lia.
Qed.

Lemma RInt_cosm_cosn_diff (m n : nat) : n != m ->
   RInt (fun x => cos (INR m * x) * cos (INR n * x)) 0 PI = 0.
Proof.
intros H.
rewrite RInt_cos_cos_0_PI.
by rewrite eq_sym (negPf H).
Qed.

Lemma cosn_is_ortho (n m : nat) l :
  is_RInt_gen (fun x => cos (INR n * x) * cos (INR m * x))
       (at_right 0) (at_left PI) l ->
  is_RInt_gen (fun y => -cos (INR n * acos y) * cos (INR m * acos y) /
                   (sqrt (1 - y ^ 2)))
              (at_left 1) (at_right (-1)) l.
Proof.
move=> lprop.
pose dg x := -/sqrt (1 - x ^ 2).
set g := acos.
pose f x := cos (INR n * x) * cos (INR m * x).
have rgt1 : at_right (-1) (ball 0 (mkposreal _ Rlt_0_1)).
  exists (mkposreal _ Rlt_0_1).
  rewrite /ball /= /AbsRing_ball /minus /opp /plus /abs /=
    => y /Rabs_def2 [y1 y2] y3.
  by apply: Rabs_def1; lra.
have llt1 : at_left 1 (ball 0 (mkposreal _ Rlt_0_1)).
  exists (mkposreal _ Rlt_0_1).
  rewrite /ball /= /AbsRing_ball /minus /opp /plus /abs /=
    => y /Rabs_def2 [y1 y2] y3.
  by apply: Rabs_def1; lra.
suff : is_RInt_gen
          (fun x => scal (dg x) (f (g x)))
          (at_left 1) (at_right (-1)) l.
  apply: is_RInt_gen_ext.
  exists (ball 0 (mkposreal _ Rlt_0_1))(ball 0 (mkposreal _ Rlt_0_1)) => // x y.
  rewrite !ball_Rabs /= => /Rabs_def2 [Hx1 Hx2] /Rabs_def2 => [] [Hy1 Hy2] z zint.
  rewrite /scal /= /mult /= /dg /f /Rdiv /=.
  by rewrite -!Ropp_mult_distr_l Rmult_comm  -!Rmult_assoc.
apply: is_RInt_gen_comp.
  exists (ball 0 (mkposreal _ Rlt_0_1))(ball 0 (mkposreal _ Rlt_0_1)) => // x y.
  rewrite !ball_Rabs => /= /Rabs_def2 [Hx1 Hx2] /Rabs_def2 [Hy1 Hy2] z zint.
  split; last split.
  - by apply: (ex_derive_continuous f); rewrite /f; auto_derive.
  - apply: acos_derivative; split.
      apply: Rlt_le_trans (Rmin_glb_lt _ _ _ _ _) (proj1 zint); lra.
    by apply: Rle_lt_trans (proj2 zint) (Rmax_lub_lt _ _ _ _ _); lra.
  apply: (ex_derive_continuous dg); rewrite /dg; auto_derive.
  rewrite (_ : 1 + - (z * (z * 1)) = (1 - z) * (1 + z)); last by ring.
  have pP : 0 < (1 - z) * (1 + z).
    apply: Rmult_lt_0_compat.
      apply: Rlt_le_trans (_ : 1 - Rmax x y <= _); try lra.
      rewrite -Rminus_lt_0; apply: Rmax_lub_lt; lra.
    apply: Rlt_le_trans (_ : 1 + Rmin x y <= _); try lra.
    have mH : -1 < Rmin x y by apply: Rmin_glb_lt; lra.
    by lra.
  by repeat split=> //; apply/Rgt_not_eq/sqrt_lt_R0.
move: lprop; apply: is_RInt_gen_filter_le; try
    solve [apply: at_right_proper_filter |
      apply: at_left_proper_filter |
    apply/filtermap_proper_filter/at_left_proper_filter |
    apply/filtermap_proper_filter/at_right_proper_filter].
  by apply: lim_acos_1.
by apply: lim_acos_m1.
Qed.

Lemma Cheby_is_ortho n m :
  is_RInt_gen (fun y => Cheby n y * Cheby m y /
                   (sqrt (1 - y ^ 2)))
              (at_right (-1)) (at_left 1)
    (if n =? m then if n =? 0 then PI else PI/2 else 0).
Proof.
rewrite -RInt_cos_cos_0_PI -[RInt _ _ _]Ropp_involutive.
apply: is_RInt_gen_swap.
pose f x := - (- cos (INR n * acos x) * cos (INR m * acos x)
                / sqrt (1 - x ^ 2)).
apply: (is_RInt_gen_ext f); rewrite {}/f /=.
  exists (ball 0 (mkposreal _ Rlt_0_1)) (ball 0 (mkposreal _ Rlt_0_1))
       => [||x y Hx Hy z].
  - exists (mkposreal _ Rlt_0_1).
    rewrite /ball /= /AbsRing_ball /minus /opp /plus /abs /=
      => y /Rabs_def2 [y1 y2] y3.
    by apply: Rabs_def1; lra.
  - exists (mkposreal _ Rlt_0_1).
    rewrite /ball /= /AbsRing_ball /minus /opp /plus /abs /=
      => y /Rabs_def2 [y1 y2] y3.
    by apply: Rabs_def1; lra.
  - by rewrite /f -Ropp_mult_distr_l -[_/_]Ropp_mult_distr_l Ropp_involutive.
apply: is_RInt_gen_opp.
pose f x := cos (INR n * x) * cos (INR m * x).
apply: cosn_is_ortho.
have cmp0PI1 : filter_Rlt (at_point 0) (at_left PI).
  exists 1.
  exists (Rgt 1) (Rlt 1) => [||/= *]; first by rewrite /at_point; lra.
    rewrite /at_left; exists (mkposreal _ Rlt_0_1) => /= y.
    rewrite ball_Rabs => /Rabs_def2 *.
    interval_intro PI; lra.
  by lra.
have cmp0PI2 : filter_Rlt (at_point (- PI)) (at_point 0).
  apply: filter_Rlt_at_point.
  by interval_intro PI; lra.
apply: is_RInt_gen_at_point_at_right => //.
  apply: filter_forall => x.
  apply: (ex_derive_continuous f).
  by rewrite /f; auto_derive.
apply: is_RInt_gen_at_point_at_left => //.
- apply: filter_forall => x.
  by apply: (ex_derive_continuous f); rewrite /f; auto_derive.
- rewrite is_RInt_gen_at_point.
  apply/(RInt_correct f)/ex_RInt_continuous => *.
  by apply: (ex_derive_continuous f); rewrite /f; auto_derive.
by apply: filter_Rlt_at_point; interval_intro PI; lra.
Qed.
Lemma Cheby_ortho n m :
  RInt_gen (fun y => Cheby n y * Cheby m y /
                   (sqrt (1 - y ^ 2)))
              (at_right (-1)) (at_left 1) =
    if n =? m then if n =? 0 then PI else PI/2 else 0.
Proof. by apply/is_RInt_gen_unique/Cheby_is_ortho. Qed.

Lemma pT_ortho n m :
  RInt_gen (fun y => (('T_n).[y])%RR * (('T_m).[y])%RR /
                   (sqrt (1 - y ^ 2)))
              (at_right (-1)) (at_left 1) =
    if n =? m then if n =? 0 then PI else PI/2 else 0.
Proof.
apply: is_RInt_gen_unique.
apply: is_RInt_gen_ext (Cheby_is_ortho _ _).
have oP : 0 < 1 by lra.
apply: Filter_prod.
- exists (mkposreal _ oP) => y /ball_Rabs /= H1 H2.
    have Hy : -1 < y < 1 by split_Rabs; lra.
    by exact: Hy.
- exists (mkposreal _ oP) => y /ball_Rabs /= H1 H2.
    have Hy : -1 < y < 1 by split_Rabs; lra.
    by exact: Hy.
move=> x y /= Hx Hy x0 H1.
by rewrite !pT_Cheby //;
   move: H1; rewrite /Rmin /Rmax; case: Rle_dec; lra.
Qed.
