From mathcomp Require Import all_ssreflect all_algebra.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz CPoly Rstruct.
Require Import filter_Rlt generalities.

Import GRing.Theory.

Set Bullet Behavior "None". 

Open Scope R_scope.

Definition Rgt0_bool x := (if total_order_T x 0 is inright _ then true else false).

Inductive Rgt0_bool_spec (x : R) : bool -> Type := 
   Rgt0_bool_spec1 :  x > 0 -> Rgt0_bool_spec x true
  |Rgt0_bool_spec2 :  x <= 0 -> Rgt0_bool_spec x false.

Lemma Rgt_boolP x : Rgt0_bool_spec x (Rgt0_bool x).
Proof.
by rewrite /Rgt0_bool; case: total_order_T => [[H|H]|H];
  ((apply: Rgt0_bool_spec1 ; lra) || (apply: Rgt0_bool_spec2 ; lra)).
Qed.

Definition Req_bool x y := (if total_order_T x y is inleft (right _) then true else false).

Lemma Req_bool_id x : Req_bool x x = true.
Proof.
by rewrite /Req_bool; case: total_order_T => [[|//]|]; lra.
Qed.

Inductive Req_bool_spec (x y : R) : bool -> Type := 
   Req_bool_spec1 :  x = y -> Req_bool_spec x y true
  |Req_bool_spec2 :  x <> y -> Req_bool_spec x y false.

Lemma Req_boolP x y : Req_bool_spec x y (Req_bool x y).
Proof.
rewrite /Req_bool; case: total_order_T => [[H|H]|H]; 
  ((apply: Req_bool_spec1 ; lra) || (apply: Req_bool_spec2 ; lra)).
Qed.

Definition acos x := 
  match total_order_T x 0 with
  | inleft (left _) => PI + atan (sqrt (1 - x * x) / x)
  | inleft (right _) => PI / 2
  | inright _  => atan (sqrt (1 - x * x) / x)
  end.

Lemma acos_0 : acos 0 = PI/2.
Proof. by rewrite /acos; case: total_order_T => [[]|]; lra. Qed.

Lemma acos_1 : acos 1 = 0.
Proof. 
rewrite /acos; case: total_order_T => [[]|]; try lra.
by rewrite Rminus_diag_eq ?sqrt_0 ?[_/_]Rmult_0_l ?atan_0; lra.
Qed.

Lemma acos_opp x : acos (- x) = PI - acos x.
Proof.
(rewrite /acos; do 2 case: total_order_T => [[]|]; try lra) => 
     H _; rewrite Rmult_opp_opp.
  by rewrite /Rminus -atan_opp [-(_/x)]Ropp_mult_distr_r Ropp_inv_permute; lra.
rewrite /Rdiv -Ropp_inv_permute; try lra.
by rewrite -Ropp_mult_distr_r atan_opp; lra.
Qed.

Lemma acos_atan x : 0 < x -> acos x = atan (sqrt (1 - x * x) / x).
Proof. by rewrite /acos; case: total_order_T => [[]|]; lra. Qed.

Lemma acos_bound x : -1 <= x <= 1 -> 0 <= acos x <= PI.
Proof.
move=> xB.
suff F y : 0 <= y <= 1 -> 0 <= acos y <= PI => [|Hy].
  have [H|H] : 0 <= x \/ x <= 0 by lra.
    by apply: F; lra.
  have : 0 <= acos (-x)  <= PI by apply: F; lra.
  by rewrite acos_opp; lra.
have PIP := PI_RGT_0.
have [->|yP] : y = 0 \/ 0 < y by lra.
  by rewrite acos_0; lra.
rewrite acos_atan; try lra.
have [->|yO] : y = 1 \/ y < 1 by lra.
  by rewrite Rmult_1_l Rminus_diag_eq // sqrt_0 [_/_]Rmult_0_l atan_0; lra.
set a := _ / _.
have Ha := atan_bound a.
suff : 0 < atan a by lra.
rewrite -atan_0; apply: atan_increasing.
apply: Rdiv_lt_0_compat => //.
by apply: sqrt_lt_R0; nra.
Qed.

Lemma atan_eq0 x : atan x = 0 -> x = 0.
Proof.
have := atan_increasing 0 x.
have := atan_increasing x 0.
rewrite atan_0.
lra.
Qed.

Lemma IZR_case k : [\/ IZR k <= -1, IZR k = 0 | IZR k >= 1].
Proof.
have [H1|[->|H1]] : (k <= - 1 \/ k = 0 \/ k >= 1)%Z by lia.
- by apply: Or31; apply: IZR_le (-1)%Z _.
- by apply: Or32.
by apply: Or33; apply: IZR_ge 1%Z _.
Qed.

Lemma atan_left_inv x : - PI / 2 < x < PI / 2 -> atan (tan x) = x.
Proof.
move=> xB.
apply: tan_is_inj; try lra.
  apply: atan_bound.
apply: atan_right_inv.
Qed.

Lemma cos_is_inj x y : 0 <= x <= PI -> 0 <= y <= PI -> cos x = cos y -> x = y.
Proof.
move=> xP yP Hcos.
have [H | [->//|H]] : (x < y) \/ (x = y) \/ (y < x) by lra.
  suff: cos y < cos x by lra.
  by apply: cos_decreasing_1; lra.
suff: cos x < cos y by lra.
by apply: cos_decreasing_1; lra.
Qed.

Lemma acos_right_inv x : -1 <= x <= 1 -> cos (acos x) = x.
Proof.
move=> HB.
suff HP y : 0 < y <= 1 -> cos (acos y) = y => [|[H1 H2]].
  have [->|[H|H]] : x = 0 \/ -1 <= x < 0 \/ 0 < x <= 1 by lra.
  - by rewrite acos_0 cos_PI2.
  - have : cos (acos (-x)) = -x by apply: HP; lra.
    by rewrite acos_opp [_ - _]Rplus_comm neg_cos -cos_sym; lra.
  by apply: HP.
rewrite acos_atan; try lra.
set A := atan _.
have AB : - PI / 2 < A < PI / 2 by apply: atan_bound.
have [|yNz] : y = 1 \/ y < 1 by lra.
  rewrite /A => ->.
  rewrite Rmult_1_l Rminus_diag_eq // sqrt_0 [0/_]Rmult_0_l.
  by rewrite atan_0 cos_0.
have ANZ : A <> 0.
  move=> /atan_eq0/Rmult_integral[H3|].
    have [] : 1 - y * y <> 0 by nra.
    by apply: sqrt_eq_0; nra.
  by apply: Rinv_neq_0_compat; lra.
have cosANZ : cos A <> 0.
  move/cos_eq_0_0=> [k Hk].
  by case: (IZR_case k) => H; nra.
have sinANZ : sin A <> 0.
  move/sin_eq_0_0=> [k Hk].
  case: (IZR_case k) => H; try nra.
have H3 := sin2_cos2 A.
rewrite /Rsqr in H3.
have := (Logic.eq_refl ((tan A)^2)).
rewrite {1}atan_right_inv /tan !Rpow_mult_distr -!Rinv_pow; try lra.
move=> H4.
have : sqrt (1 - y * y) ^ 2 * cos A ^ 2 - y ^ 2 * sin A ^ 2 = 0.
  have F a b : b <> 0 -> a = (a */ b) * b by move=> *; field.
  rewrite [sqrt _ ^ 2](F _ (y^2)) ?H4 ; try nra.
  by field.
rewrite (_ : (sin A)^2 = 1 - (cos A)^2); try lra.
rewrite -Rsqr_pow2 [Rsqr _]sqrt_sqrt; try nra.
move=> H5; ring_simplify in H5.
have /Rmult_integral[] : (y - cos A) * (y + cos A) = 0 by nra.
  by lra.
have sP : 0 < sqrt (1 - y * y) by apply: sqrt_lt_R0; nra.
have AP : 0 < A.
  rewrite -atan_0; apply: atan_increasing.
suff :  0 / y < sqrt (1 - y * y) / y by lra.
apply: Rmult_lt_compat_r; last by lra.
by apply: Rinv_0_lt_compat; lra.
suff : 0 < cos A by lra.
by apply: cos_gt_0; lra.
Qed.

Lemma acos_left_inv x : 0 <= x <= PI -> acos (cos x) = x.
Proof.
move=> HB.
apply: cos_is_inj => //.
  apply: acos_bound.
  apply: COS_bound.
apply/acos_right_inv/COS_bound.
Qed.

Section Cheby_rec.
Definition Cheby n x := cos (INR n * acos x).

Lemma Cheby_0 x : -1 <= x <= 1 -> Cheby 0 x = 1.
Proof. by rewrite /Cheby Rmult_0_l cos_0. Qed.

Lemma Cheby_1 x : -1 <= x <= 1 -> Cheby 1 x = x.
Proof. by rewrite /Cheby Rmult_1_l; exact: acos_right_inv. Qed.

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
by rewrite acos_right_inv.
Qed.
Local Open Scope ring_scope.

Lemma pT_Cheby n (x: R):
	(Rle (IZR (-1)) x) /\ (Rle x (IZR 1)) -> Cheby n x = ('T_n).[x].
Proof.
move => ineq.
elim: n {-2}(n) (leqnn n) => [n ass | n ih k ineqk].
	have/eqP-> : n == 0%nat by rewrite -leqn0.
	by rewrite Cheby_0; try lra; rewrite pT0 hornerC.
rewrite leq_eqVlt in ineqk; case/orP: ineqk => [/eqP eqn | ineqk]; last by rewrite ih.
case E: n => [ | m]; first by	rewrite eqn E Cheby_1; try lra; first by rewrite pT1 hornerX.
rewrite eqn E pTSS Cheby_rec; try lra.
rewrite hornerD hornerM mulr2n hornerD hornerX hornerN.
by rewrite -!ih; toR; try lra; rewrite E.
Qed.
End Cheby_rec.

Lemma Cheby_cos n a : 0 <= a <= PI -> Cheby n (cos a) = cos ((INR n) * a).
Proof. move=> *; rewrite /Cheby acos_left_inv //. Qed.

Lemma cos_add_INR a n : cos (a + INR n * PI) = if Nat.even n then cos a else -cos a.
Proof.
elim: n => [|n IH]; first by rewrite /= Rmult_0_l Rplus_0_r.
rewrite S_INR Rmult_plus_distr_r Rmult_1_l -Rplus_assoc.
rewrite neg_cos IH Nat.even_succ -Nat.negb_even.
by case: Nat.even => /=; lra.
Qed.

Lemma Cheby_compi m n a : -1 <= a <= 1 -> Cheby n (Cheby m a) = Cheby (n * m) a.
Proof.
move=> Ha.
have U := acos_bound _ Ha.
rewrite /Cheby mult_INR Rmult_assoc.
set v := _ * acos a.
have HP := PI2_1;
have [k [r [-> Hr]]] : exists k, exists r, v = r + INR k * PI /\ (0 <= r <= PI).
  pose k := Z.to_nat (up (v / PI) - 1).
  exists k; exists (v - INR k * PI); split; try lra.
  rewrite INR_IZR_INZ Z2Nat.id; last first.
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
  by rewrite acos_left_inv.
rewrite /= acos_opp acos_left_inv //.
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
           if (n == m) then if (n == 0%N) then PI else PI/2 else 0.
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

Definition asin x  := atan (x / sqrt (1 - x ^ 2)).

Lemma asin_derivative x : -1 < x < 1 ->
  is_derive asin x (/sqrt (1 - x ^ 2)).
Proof.
move=> intx.
have H1 : 0 < (1 + x) * (1 - x) by nra.
have H2 : sqrt ((1 + x) * (1 - x)) <> 0.
   by apply/Rgt_not_eq/sqrt_lt_R0; lra.
have H3 : 0 <= sqrt ((1 + x) * (1 - x)) by apply: sqrt_pos.
have H4 : 0 <= sqrt ((1 + x) * (1 - x)) * x ^ 2 by apply: Rmult_le_pos; nra.
rewrite /asin; auto_derive;
  rewrite (_ :  1 + - (x * (x * 1)) = (1 + x) * (1 - x)) //; try ring.
rewrite (_ : 1 - x ^ 2 = (1 + x) * (1 - x)); last by ring.
field_simplify; try nra.
rewrite arcsinh.pow2_sqrt; try nra.
rewrite -(tech_pow_Rmult (sqrt _)) arcsinh.pow2_sqrt; try nra.
field; repeat split; auto; nra.
Qed.

Lemma asin_0 : asin 0 = 0.
Proof. by rewrite /asin [_/_]Rmult_0_l atan_0. Qed.

Lemma asin_opp x : asin (- x) = -asin x.
Proof.
rewrite /asin  -![_^ 2]Rmult_assoc !Rmult_1_r.
by rewrite Rmult_opp_opp -atan_opp [-(x/_)]Ropp_mult_distr_l.
Qed.

Lemma sin_asin x : -1 < x < 1 -> sin (asin x) = x.
Proof.
intros xB.
suff HP y : 0 < y < 1 -> sin (asin y) = y => [|[H1 H2]].
  have [->|[H|H]] : x = 0 \/ -1 < x < 0 \/ 0 < x < 1 by lra.
  - by rewrite asin_0 sin_0.
  - have : sin (asin (-x)) = -x by apply: HP; lra.
    by rewrite asin_opp sin_neg; lra.
  by apply: HP.
have SH : sqrt (1 - y ^ 2) <> 0.
    intro H.
    have [] : 1 - y ^ 2 <> 0 by nra.
    by apply: sqrt_eq_0; nra.
rewrite /asin.
set A := atan _.
have AB : - PI / 2 < A < PI / 2 by apply: atan_bound.
have ANZ : A <> 0.
  move=> /atan_eq0/Rmult_integral[H3|]; try lra.
  by apply: Rinv_neq_0_compat.
have cosANZ : cos A <> 0.
  move/cos_eq_0_0=> [k Hk].
  by case: (IZR_case k) => H; nra.
have sinANZ : sin A <> 0.
  move/sin_eq_0_0=> [k Hk].
  case: (IZR_case k) => H; try nra.
have H3 := sin2_cos2 A.
rewrite /Rsqr in H3.
have := (Logic.eq_refl ((tan A)^2)).
rewrite {1}atan_right_inv /tan !Rpow_mult_distr -!Rinv_pow; try lra.
move=> H4.
have : sqrt (1 - y ^ 2) ^ 2 * sin A ^ 2 - y ^ 2 * cos A ^ 2 = 0.
  have F a b : b <> 0 -> a = (a */ b) * b by move=> *; field.
  rewrite {2}[y^2](F _ (sqrt (1 - y ^ 2)^2)) ?H4; try nra.
  by field.
rewrite (_ : (sin A)^2 = 1 - (cos A)^2); try lra.
rewrite -Rsqr_pow2 [Rsqr _]sqrt_sqrt; try nra.
move=> H5; ring_simplify in H5.
have /Rmult_integral[] : (y - sin A) * (y + sin A) = 0 by nra.
  by lra.
have sP : 0 < sqrt (1 - y ^ 2) by apply: sqrt_lt_R0; nra.
have AP : 0 < A.
  rewrite -atan_0; apply: atan_increasing.
  suff :  0 / sqrt (1 - y ^ 2) < y / sqrt (1 - y ^ 2) by lra.
  apply: Rmult_lt_compat_r; last by lra.
  by apply: Rinv_0_lt_compat; lra.
suff : 0 < sin A by lra.
by apply: sin_gt_0; lra.
Qed.

Lemma asin_Vsqrt2 : asin (/sqrt 2) = PI/4.
Proof.
have SH := sqrt2_neq_0.
rewrite /asin -Rinv_pow // sqrt_pow_2; try lra.
rewrite (_ : 1 - /2 = /2); try lra.
rewrite -inv_sqrt; try lra.
by rewrite (_ : _ / _ = 1) ?atan_1 //; field.
Qed.

Lemma acosE x : -1 < x < 1 -> acos x = PI/2 - asin x.
Proof.
move=> xB.
wlog : x xB / 0 < x => [H|xP].
  have [xN|[->|xP]] : (x < 0 \/ x = 0 \/ x > 0) by lra.
  - by rewrite -{1}[x]Ropp_involutive acos_opp H ?asin_opp; lra.
  - by rewrite acos_0 asin_0; lra.
  by apply: H; lra.
rewrite /acos; case: total_order_T => [[|]|_]; try lra.
rewrite -Interval_missing.atan_inv; last first.
  apply: RIneq.Rdiv_lt_0_compat => //.
  by apply: sqrt_lt_R0; nra.
rewrite Rinv_Rdiv; try lra.
  by rewrite (_ : x * x = x ^ 2); lra.
by move/sqrt_eq_0; nra.
Qed.

Lemma lim_asin_1 : filterlim asin (at_left 1) (at_left (PI/2)).
Proof.
rewrite /asin.
apply: filterlim_comp; last first.
  by apply: atan_derivative_improper_integral.lim_atan_p_infty.
apply: (filterlim_ext
   (fun x => (fun p => fst p * snd p) (x, /sqrt (1 - x ^ 2)))) => //.
apply: (filterlim_comp _ _ _ (fun x => (x, /sqrt (1 - x ^ 2)))
          (fun p => fst p * snd p)
          _ (filter_prod (at_left 1) (Rbar_locally p_infty)))
     => [|P [M PM]].
  apply: filterlim_pair (filterlim_id _ _) _.
  apply: (filterlim_comp _ _ _ _ Rinv _ (at_right 0)); last first.
    by apply: filterlim_Rinv_0_right.
  apply: (filterlim_comp _ _ _ _ sqrt _ (at_right 0))
        => [P [eps b]|]; last by  apply: filterlim_sqrt_0.
  have e20 : 0 < Rmin (pos_div_2 eps) 1.
    by apply: Rmin_glb_lt; try apply: cond_pos; lra.
  exists (mkposreal _ e20) => /= y yc ylt1.
  move: yc; rewrite ball_Rabs Rabs_left1 => [yc|]; last by lra.
  have ygt0 : 0 < y.
    apply/Ropp_lt_cancel/(Rplus_lt_reg_r 1).
    rewrite Ropp_0 Rplus_0_l.
    by apply: Rlt_le_trans (Rmin_r (eps / 2) 1); lra.
  have yc1 : 1 - y < eps / 2.
    by apply: Rlt_le_trans (Rmin_l (eps / 2) 1); lra.
  apply: b; try nra.
  by rewrite ball_Rabs Rminus_0_r Rabs_right; nra.
exists (ball 1 pos_half) (Rlt (2 * (Rmax 1 M))) => [||x y].
- by exists pos_half.
- by exists (2 * Rmax 1 M).
rewrite ball_Rabs => /Rabs_def2 /= => [] [cx1 cx2] cy.
apply: PM.
have xL2 : / 2 < x  by lra.
apply: Rle_lt_trans  (_ : /2 * (2 * Rmax 1 M) < _).
  rewrite -Rmult_assoc Rinv_l // Rmult_1_l; try lra.
  by  apply: Rmax_r.
apply: Rmult_gt_0_lt_compat; try lra.
apply: Rmult_lt_0_compat; try lra; apply: Rlt_le_trans (Rmax_l _ _).
lra.
Qed.

Lemma acos_derivative x : -1 < x < 1 ->
  is_derive acos x (-/sqrt (1 - x ^ 2)).
Proof.
intros intx.
pose dx := Rmin (1 - x) (x + 1).
have dxP : 0 < dx.
  rewrite /dx /Rmin; case: Rle_dec; try lra.
have dxM : dx <= 1 - x /\ dx <= x + 1.
  by rewrite /dx /Rmin; case: Rle_dec; lra.
have Hl : locally x (fun x =>  PI/2 - asin x = acos x).
  exists (mkposreal _ dxP) => y /ball_Rabs /= H.
  rewrite acosE //; split_Rabs; lra.
apply: is_derive_ext_loc Hl _.
auto_derive.
  exists (/sqrt (1 - x ^ 2)).
  by apply:  asin_derivative.
have dq : Derive asin x = /sqrt (1 - x ^ 2).
  by apply/is_derive_unique/asin_derivative.
by rewrite Rmult_1_l dq.
Qed.

Lemma lim_acos_1 : filterlim acos (at_left 1) (at_right 0).
Proof.
suff F : filterlim (fun x : R => PI / 2 - asin x) (at_left 1) (at_right 0).
  move => P U.
  have [x Hx] := F P U.
  have xP : 0 < x by apply: cond_pos.
  pose y := Rmin x (/2).
  have yP : 0 < y.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have yB : y <= x /\ y <= /2.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  exists (mkposreal _ yP) => /= z Hz zL1.
  rewrite acosE.
    apply: Hx => //.
    apply: ball_le Hz.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have /ball_Rabs HH := Hz.
  by split_Rabs; lra.
apply: filterlim_comp => [|P [eps b]]; first by apply: lim_asin_1.
exists eps => y cy ylt1.
apply: b; last by lra.
rewrite ball_Rabs Rminus_0_r Rabs_right; try lra.
move: cy.
by rewrite ball_Rabs Rabs_left1; lra.
Qed.

Lemma lim_asin_m1 : filterlim asin (at_right (-1)) (at_right (-PI/2)).
Proof.
rewrite /asin.
apply: filterlim_comp; last first.
  apply: atan_derivative_improper_integral.lim_atan_m_infty.
apply: (filterlim_ext
   (fun x => (fun p => fst p * snd p) (x, /sqrt (1 - x ^ 2)))) => //.
apply: (filterlim_comp _ _ _ (fun x => (x, /sqrt (1 - x ^ 2)))
          (fun p => fst p * snd p)
          _ (filter_prod (at_right (-1)) (Rbar_locally p_infty)))
   => [|P [M PM]].
  apply: filterlim_pair; first apply: filterlim_id.
  apply: (filterlim_comp _ _ _ _ Rinv _ (at_right 0)); last first.
    by apply: filterlim_Rinv_0_right.
  apply: (filterlim_comp _ _ _ _ sqrt _ (at_right 0))
         => [P [eps b]|]; last first.
    by apply: filterlim_sqrt_0.
  have e20 : 0 < Rmin (pos_div_2 eps) 1.
    by apply: Rmin_glb_lt; try apply: cond_pos; lra.
  exists (mkposreal _ e20) => /= y yc ylt1.
  move: yc.
  (rewrite ball_Rabs Rabs_right; try lra) => yc.
  have ygt0 : y < 0.
    apply: (Rplus_lt_reg_r 1).
    rewrite Rplus_0_l.
    by apply: Rlt_le_trans (Rmin_r (eps / 2) 1); lra.
  have yc1 : y + 1 < eps / 2.
    by apply: Rlt_le_trans (Rmin_l (eps / 2) 1); lra.
  apply: b; try nra.
  by rewrite ball_Rabs Rminus_0_r Rabs_right; nra.
exists (ball (-1) pos_half) (Rlt (2 * (Rmax 1 (-M)))) => [||x y].
- by exists pos_half.
- by exists (2 * Rmax 1 (-M)).
rewrite ball_Rabs => /Rabs_def2 /= [cx1 cx2] cy.
apply: PM.
have xL2 : x < -/ 2 by lra.
apply: Ropp_lt_cancel; rewrite Ropp_mult_distr_l.
apply: Rle_lt_trans (_ : /2 * (2 * Rmax 1 (-M)) < _).
  rewrite -Rmult_assoc Rinv_l ?Rmult_1_l; try lra.
  by apply: Rmax_r.
apply: Rmult_gt_0_lt_compat; try lra.
apply: Rmult_lt_0_compat; try lra; apply: Rlt_le_trans (Rmax_l _ _).
lra.
Qed.

Lemma lim_acos_m1 : filterlim acos (at_right (-1)) (at_left PI).
Proof.
suff F : filterlim (fun x : R => PI / 2 - asin x) (at_right (-1)) (at_left PI).
  move => P U.
  have [x Hx] := F P U.
  have xP : 0 < x by apply: cond_pos.
  pose y := Rmin x (/2).
  have yP : 0 < y.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have yB : y <= x /\ y <= /2.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  exists (mkposreal _ yP) => /= z Hz zL1.
  rewrite acosE.
    apply: Hx => //.
    apply: ball_le Hz.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have /ball_Rabs HH := Hz.
  by split_Rabs; lra.
rewrite /acos; apply: filterlim_comp => [|P [eps b]].
  by apply: lim_asin_m1.
exists eps => y cy ylt1; apply: b; last by lra.
rewrite ball_Rabs Rabs_left1; try lra.
by move: cy; rewrite ball_Rabs Rabs_right; lra.
Qed.
Lemma ortho1 (n m : nat) l :
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

Lemma is_RInt_gen_at_point_at_left (f : R -> R) (a : R) F {FF : ProperFilter F}
  v : locally a (continuous f) -> is_RInt_gen f F (at_point a) v ->
  filter_Rlt F (at_point a) ->  is_RInt_gen f F (at_left a) v.
Proof.
move=> [delta1 pd1] intf [m [P Q FP FQ /= cmp]] P2 PP2.
have [delta2 Pd2] :=
   (pd1 a (ball_center a delta1)
          (ball (f a) (mkposreal _ Rlt_0_1)) (locally_ball _ _)).
have qa : Q a by (apply: FQ => *; apply: ball_center).
have intf2 := intf P2 PP2.
have [eps P2eps] := PP2.
pose M := Rabs (f a) + 1.
have M0 : 0 < eps / M.
  apply: Rmult_lt_0_compat; first by apply: cond_pos.
  apply: Rinv_0_lt_compat.
  have RH : 0 <= Rabs (f a) by apply: Rabs_pos.
  by rewrite /M; lra.
have close y : y <> a -> ball a delta2 y -> Rabs (f y) < M.
  move=> ay b_y; rewrite /M (_: f y = f a + (f y - f a)); last by lra.
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  by apply/Rplus_lt_compat_l/Pd2.
have exrint_close a' : ball a delta1 a' -> ex_RInt f a' a.
  move=> baa'.
  apply: (ex_RInt_continuous f)=> z pz; apply: pd1.
  have [aa' | a'a] := Rle_dec a a'.
    move: pz; rewrite Rmin_right // Rmax_left // => pz.
    change (Rabs (z - a) < delta1).
    rewrite Rabs_right; try lra.
    apply: Rle_lt_trans (_ : a' - a < _); try lra.
    rewrite -(Rabs_right (a' - a)); try lra.
    tauto.
  change (Rabs (z - a) < delta1).
  have [az | za] := Rle_dec a z.
    have a'aW :=  Rnot_le_lt _ _ a'a.
    move: pz; rewrite Rmin_left; try lra.
    rewrite Rmax_right => [pz|]; try lra.
    have za' : z = a by apply: Rle_antisym; lra.
    by rewrite za' Rminus_eq_0 Rabs_R0; case delta1.
  have a'a1 :=  Rnot_le_lt _ _ a'a; have za1 :=  Rnot_le_lt _ _ za.
  move: pz; rewrite Rmin_left; try lra.
  rewrite Rmax_right => [pz|]; try lra.
  apply: Rle_lt_trans (_ : a - a' < _); try (split_Rabs; lra).
  rewrite -(Rabs_right (a - a')); try (split_Rabs; lra).
  by change (ball a' delta1 a); apply: ball_sym.
have pre_ep2 : 0 < eps / 2 * /M.
  repeat apply: Rmult_lt_0_compat; try lra.
    by destruct eps; tauto.
  by apply: Rinv_0_lt_compat; rewrite /M; assert (t := Rabs_pos (f a)); lra.
pose ep2 := mkposreal _ pre_ep2.
have aH : (at_left a (fun x => ball a delta1 x /\ ball a ep2 x /\
                             ball a delta2 x /\ m < x /\ x < a)).
  repeat apply: filter_and; try (by apply/filter_le_within/locally_ball).
    have  [y' Py'] := filter_ex _ FP.
    have ma0 : 0 < a - m by case:  (cmp y' a) => //; lra.
    exists (mkposreal _ ma0) => /= y.
    rewrite ball_Rabs=> bay ay; rewrite Rabs_left in bay; lra.
  by exists ep2.
have [Pl Ql FPl FQl closerint] := intf _ (locally_ball v (pos_div_2 eps)).
have pla : Ql a by apply: FQl => *; apply: ball_center.
have HF : F (fun y => P y /\ Pl y) by apply: filter_and.
exists (fun y => P y /\ Pl y)
       (fun x => ball a delta1 x /\ ball a ep2 x /\
                 ball a delta2 x /\ m < x /\ x < a) => // x y bx Ry.
exists (RInt f x y).
have [||fxa [close_fxa]] // := closerint x a; first by tauto.
split => /=.
  apply: (RInt_correct f x y).
  apply: (ex_RInt_Chasles_1 f _ _ a); last by exists fxa; tauto.
  split; apply: Rlt_le; last by tauto.
  apply: Rlt_trans (_ : m < _); last by tauto.
  by assert (t := cmp x a (proj1 bx) qa); tauto.
apply: P2eps.
have RH :  Rabs (RInt f y a) < pos_div_2 eps.
  apply: Rle_lt_trans (_ : (a - y) * M < _).
    apply: abs_RInt_le_const => [||t yta]; first by apply: Rlt_le; tauto.
      by apply: exrint_close; tauto.
    rewrite (_ : f t =f a + (f t - f a)); last by lra.
    apply: Rle_trans (Rabs_triang _ _) _.
    apply: Rplus_le_compat (Rle_refl _) _.
    apply/Rlt_le/(Pd2 t).
    change (Rabs (t - a) < delta2); rewrite Rabs_left1; try lra.
    apply: Rle_lt_trans (_ : a - y < _); try lra.
    rewrite -(Rabs_right (a - y)); try lra.
    by rewrite -Rabs_Ropp Ropp_minus_distr; tauto.
  rewrite (_ : pos (pos_div_2 eps) = ep2 * M) /=.
    rewrite -(Rabs_right (a - y)); try lra.
    apply: Rmult_lt_compat_r.
      by assert (t := Rabs_pos (f a)); rewrite /M; lra.
    by rewrite -Rabs_Ropp Ropp_minus_distr; tauto.
  by field; rewrite /M; apply: Rgt_not_eq; assert (t := Rabs_pos (f a)); lra.
rewrite (_ : pos eps = pos_div_2 eps + pos_div_2 eps) /=; last by field.
apply: ball_triangle (_ : ball v (eps / 2) (RInt f x a)) _; last first.
  change (Rabs (RInt f x y - RInt f x a) < pos_div_2 eps).
  rewrite (_ : RInt f x a = RInt f x y + RInt f y a); last first.
    apply/sym_equal/(RInt_Chasles f); last by apply: exrint_close; tauto.
    apply: (ex_RInt_Chasles_1 f _ _ a); last by exists fxa.
    split.
      by apply/Rlt_le/(Rlt_trans _ _ _ _ (_ : m < _)); case: (cmp x a); tauto.
    by apply: Rlt_le; tauto.
  by split_Rabs; lra.
by rewrite (is_RInt_unique f x a fxa).
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
apply: ortho1.
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

