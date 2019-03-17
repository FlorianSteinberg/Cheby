(******************************************************************************)
(* This file contains material that should be included into                   *)
(* Coquelicot                                                                 *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.
Require Import filter_Rlt generalities.

Set Bullet Behavior "None". 

Open Scope R_scope.

(* case theorem for IZR               *)

Lemma IZR_case k : [\/ IZR k <= -1, IZR k = 0 | IZR k >= 1].
Proof.
have [H1|[->|H1]] : (k <= - 1 \/ k = 0 \/ k >= 1)%Z by lia.
- by apply: Or31; apply: IZR_le (-1)%Z _.
- by apply: Or32.
by apply: Or33; apply: IZR_ge 1%Z _.
Qed.

(* Some extra properties of cos *)

Lemma cos_is_inj x y : 0 <= x <= PI -> 0 <= y <= PI -> cos x = cos y -> x = y.
Proof.
move=> xP yP Hcos.
have [H | [->//|H]] : (x < y) \/ (x = y) \/ (y < x) by lra.
  suff: cos y < cos x by lra.
  by apply: cos_decreasing_1; lra.
suff: cos x < cos y by lra.
by apply: cos_decreasing_1; lra.
Qed.

(* Some extra properties of sin *)

Lemma sin_is_inj x y : -(PI/2)  <= x <= PI/2 -> -(PI/2) <= y <= PI/2 -> sin x = sin y -> x = y.
Proof.
move=> xP yP Hsin.
have [H | [->//|H]] : (x < y) \/ (x = y) \/ (y < x) by lra.
  suff: sin x < sin y by lra.
  by apply: sin_increasing_1; lra.
suff: sin y < sin x by lra.
by apply: sin_increasing_1; lra.
Qed.

(* Some extra properties of atan      *)

Lemma atan_eq0 x : atan x = 0 -> x = 0.
Proof.
have := atan_increasing 0 x.
have := atan_increasing x 0.
rewrite atan_0.
lra.
Qed.

Lemma atan_left_inv x : - PI / 2 < x < PI / 2 -> atan (tan x) = x.
Proof.
move=> xB.
apply: tan_is_inj; try lra.
  apply: atan_bound.
apply: atan_right_inv.
Qed.

Lemma lim_atan_p_infty :
  filterlim atan (Rbar_locally p_infty) (at_left (PI/2)).
Proof.
assert (0 < PI) by (assert (t := PI2_RGT_0); psatzl R).
intros S [ep Pep].
set (e' := Rmin (PI/2) ep).
assert (0 < e') by now apply Rmin_glb_lt; destruct ep; auto; psatzl R.
assert (e' <= PI/2) by apply Rmin_l.
exists (tan (PI/2 - e')); intros x Px.
assert (atan x < PI/2) by (destruct (atan_bound x); psatzl R).
apply Pep;[|psatzl R].
change (Rabs (atan x - PI/2) < ep).
rewrite Rabs_left ?Ropp_minus_distr;[| psatzl R].
apply Rlt_le_trans with (PI / 2 - atan (tan (PI / 2 - e'))).
  now apply Rplus_lt_compat_l, Ropp_lt_contravar, atan_increasing.
replace (atan (tan (PI / 2 - e'))) with (PI / 2 - e').
  now ring_simplify; apply Rmin_r.
apply tan_is_inj;[psatzl R | apply atan_bound | now rewrite atan_right_inv].
Qed.

Lemma lim_atan_m_infty :
  filterlim atan (Rbar_locally m_infty) (at_right (-PI/2)).
Proof.
apply filterlim_ext with (fun x => - (atan (- x))).
  now intros; rewrite atan_opp ?Ropp_involutive.
apply (filterlim_comp _ _ _ (fun x => atan (- x)) Ropp _ (at_left (PI/2))).
  apply (filterlim_comp _ _ _ Ropp atan _ (Rbar_locally p_infty)).
    now apply filterlim_Rbar_opp.
  now apply lim_atan_p_infty.
replace (- PI / 2) with (- (PI / 2)) by field.
apply filterlim_Ropp_left.
Qed.

Lemma atan_lim_pinfty : Lim atan p_infty = PI/2.
Proof. 
assert (t := PI2_RGT_0).
apply is_lim_unique; intros P [eps Peps].
assert (ep2 : 0 < Rmin eps (PI/4)).
  apply Rmin_glb_lt;[apply cond_pos | lra].
set (eps' := mkposreal _ ep2).
assert (eps' < PI / 2).
  unfold eps'; simpl.
  apply Rle_lt_trans with (PI/4).
    now apply Rmin_r.
  lra.
assert (eps' <= eps).
  now unfold eps'; simpl; apply Rmin_l.
assert (0 < eps') by apply cond_pos.
exists (tan (PI / 2 - eps')); intros x cx.
apply Peps. change (Rabs (atan x -PI/2) < eps).
  rewrite Rabs_left; cycle 1.
  destruct (atan_bound x); lra.
enough (PI / 2 - eps' < atan x) by lra.
rewrite <- (atan_left_inv (PI/2 - eps')); cycle 1.
  now split; psatzl R.
now apply atan_increasing.
Qed.

Lemma atan_lim_minfty : Lim atan m_infty = -PI/2.
Proof. 
assert (t := PI2_RGT_0).
apply is_lim_unique; intros P [eps Peps].
assert (ep2 : 0 < Rmin eps (PI/4)).
  apply Rmin_glb_lt;[apply cond_pos | lra].
set (eps' := mkposreal _ ep2).
assert (eps' < PI / 2).
  unfold eps'; simpl.
  apply Rle_lt_trans with (PI/4).
    now apply Rmin_r.
  lra.
assert (eps' <= eps).
  now unfold eps'; simpl; apply Rmin_l.
assert (0 < eps') by apply cond_pos.
exists (tan (-PI / 2 + eps')); intros x cx.
apply Peps; change (Rabs (atan x - -PI/2) < eps).
  rewrite Rabs_right; cycle 1.
  destruct (atan_bound x); lra.
enough (atan x < -PI / 2 + eps') by lra.
rewrite <- (atan_left_inv (-PI/2 + eps')); cycle 1.
  now split; psatzl R.
now apply atan_increasing.
Qed.

Lemma integral_atan_comp_scal m : 0 < m ->
   is_RInt_gen (fun x => /m * /((x / m) ^ 2 + 1)) 
       (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
Proof.
(* assert (tmp := PI2_RGT_0). *)
intros m0.
assert (is_derive_atan_scal : forall x,  
           is_derive (fun x => atan (x / m)) x (/ m * /((x/m)^2 + 1))).
  intros x; auto_derive; auto; field.
  split; apply Rgt_not_eq; auto; apply Rplus_le_lt_0_compat.
    now apply pow2_ge_0.
  now apply pow2_gt_0, Rgt_not_eq.
intros P [eps Peps].
(* assert (ep2 : 0 < Rmin eps (PI/2)).
  apply Rmin_glb_lt;[apply cond_pos | psatzl R].
assert (eps' := mkposreal _ ep2).
*)
assert (atle : at_left (PI/2) (ball (PI/2) (pos_div_2 eps))).
  now exists (pos_div_2 eps); intros; tauto.
assert (atri : at_right (-PI/2) (ball (-PI/2) (pos_div_2 eps))).
  now exists (pos_div_2 eps); intros; tauto.
assert (H0 := lim_atan_p_infty _ atle).
assert (H0' := lim_atan_m_infty _ atri).
assert (abs' : 0 < / m) by now apply Rinv_0_lt_compat.
assert (H1 : filterlim (fun x => x / m) (Rbar_locally p_infty)
                (Rbar_locally p_infty)).
  replace (Rbar_locally p_infty) with (Rbar_locally (Rbar_mult p_infty (/ m))) at 2.
    now apply filterlim_Rbar_mult_r.
  apply f_equal; simpl; case (Rle_dec 0 (/ m)).
    intros r; case (Rle_lt_or_eq_dec 0 (/ m) r); auto.
    now intros abs; rewrite <- abs in abs'; case (Rlt_irrefl 0).
  now intros abs; case abs; apply Rlt_le.
assert (H2 : filterlim (fun x => x / m) (Rbar_locally m_infty)
                (Rbar_locally m_infty)).
  replace (Rbar_locally m_infty) with (Rbar_locally (Rbar_mult m_infty (/ m))) at 2.
    now apply filterlim_Rbar_mult_r.
  apply f_equal; simpl; case (Rle_dec 0 (/ m)).
    intros r; case (Rle_lt_or_eq_dec 0 (/ m) r); auto.
    now intros abs; rewrite <- abs in abs'; case (Rlt_irrefl 0).
  now intros abs; case abs; apply Rlt_le.
assert (t := filterlim_comp R R R (fun x => x / m) atan (Rbar_locally p_infty)
              (Rbar_locally p_infty) (at_left (PI/2)) H1 lim_atan_p_infty).
assert (t' := filterlim_comp R R R (fun x => x / m) atan (Rbar_locally m_infty)
              (Rbar_locally m_infty) (at_right (-PI/2)) H2 lim_atan_m_infty ).
specialize (t _ atle).
specialize (t' _ atri).
unfold filtermapi, filtermap in t, t' |- *.
apply (Filter_prod _ _ _ _ _ t' t).
intros x y; exists (atan (y/m) - atan (x/m)); split.
  apply (is_RInt_derive (fun x => atan (x / m))).
    intros z _; exact (is_derive_atan_scal z).
  intros z _; apply (ex_derive_continuous (fun x1 => /m * / ((x1 / m) ^ 2 + 1))).
  auto_derive; change ((z / m) ^ 2 + 1 <> 0).
  now apply Rgt_not_eq, Rplus_le_lt_0_compat;
           [apply pow2_ge_0 | apply Rlt_0_1].
apply Peps.
change (Rabs ((atan (y / m) - atan (x / m)) - PI) < eps).
replace ((atan (y / m) - atan (x / m)) - PI) with
    ((atan (y / m) - PI / 2) - (atan (x / m) + PI / 2)) by field.
apply Rle_lt_trans with (1 := Rabs_triang _ _).
replace (pos eps) with (pos_div_2 eps + pos_div_2 eps) by (simpl; field).
apply Rplus_lt_compat.
  exact H3.
rewrite <- Rabs_Ropp, !Ropp_plus_distr, Ropp_involutive, <- Ropp_div.
exact H.
Qed.

Lemma atan_derivative_improper_integral :
  is_RInt_gen (fun x => /(x ^ 2 + 1))
     (Rbar_locally m_infty) (Rbar_locally p_infty) PI.
Proof.
apply is_RInt_gen_ext with (fun x =>  /1 * /((x/1)^2 + 1)).
  exists (Rgt 0) (Rlt 0); try (exists 0; intros; psatzl R).
  intros x y _ _ z _; rewrite Rdiv_1 ?Rinv_1 ?Rmult_1_l; reflexivity.
apply integral_atan_comp_scal; psatzl R.
Qed.

(* A twisted definition of asin in term of atan so it is defined for -1 and 1 *)
Definition asin x := 
  match total_order_T x 0 with
  | inleft (left _) => - PI/2 - atan (sqrt (1 - x * x) / x)
  | inleft (right _) => 0
  | inright _  => PI/2 - atan (sqrt (1 - x * x) / x)
  end.

Lemma asin_0 : asin 0 = 0.
Proof. by rewrite /asin; case: total_order_T => [[]|]; lra. Qed.

Lemma asin_1 : asin 1 = PI / 2.
Proof. 
rewrite /asin; case: total_order_T => [[]|_]; try lra.
replace (1 - 1 * 1) with 0 by lra.
rewrite sqrt_0 [0 / _]Rmult_0_l atan_0; lra.
Qed.

Lemma asin_m1 : asin (-1) = - PI / 2.
Proof. 
rewrite /asin; case: total_order_T => [[_|]|]; try lra.
replace (1 - -1 * -1) with 0 by lra.
rewrite sqrt_0 [0 / _]Rmult_0_l atan_0; lra.
Qed.

Lemma asin_opp x : asin (- x) = - asin x.
Proof.
have F y : - y * - y = y * y by lra. 
have G y z : z <> 0 -> y / - z = - (y / z).
  by move=> yNZ; rewrite /Rdiv -Ropp_inv_permute; lra.
rewrite /asin; do 2 case: total_order_T => [[]|]; 
   try lra; move=> Px Py; rewrite F G ?atan_opp; try lra.
Qed.

(* We recover the "natural" definition *)
Lemma asin_atan x : -1 < x < 1 ->
     asin x = atan (x / sqrt (1 - x ^ 2)).
Proof.
move=> xB.
wlog : x xB / 0 < x => [H|xP].
  have [xN|[->|xP]] : (x < 0 \/ x = 0 \/ x > 0) by lra.
  - rewrite -{1}[x]Ropp_involutive asin_opp H; try lra.
    replace ((- x) ^ 2) with (x ^ 2) by lra.
    by rewrite -[_ / _]Ropp_mult_distr_l atan_opp; lra.
  - by rewrite [0 / _]Rmult_0_l atan_0 asin_0; lra.
  by apply: H; lra.
rewrite /asin; case: total_order_T => [[|]|_]; try lra.
rewrite -[_ / x]Rinv_Rdiv => [||H]; try lra; last first.
  by have /sqrt_eq_0 /(_ H) : 0 <= 1 - x * x; nra.
rewrite Interval_missing.atan_inv.
  by rewrite (_ : x * x = x ^ 2); lra.
apply: RIneq.Rdiv_lt_0_compat => //.
by apply: sqrt_lt_R0; nra.
Qed.

Lemma asin_derivative x : -1 < x < 1 ->
  is_derive asin x (/sqrt (1 - x ^ 2)).
Proof.
move=> intx.
pose dx := Rmin (1 - x) (x + 1).
have dxP : 0 < dx.
  rewrite /dx /Rmin; case: Rle_dec; try lra.
have dxM : dx <= 1 - x /\ dx <= x + 1.
  by rewrite /dx /Rmin; case: Rle_dec; lra.
have Hl : locally x (fun x =>  atan (x / sqrt (1 - x ^ 2)) = asin x).
  exists (mkposreal _ dxP) => y /ball_Rabs /= H.
  by rewrite asin_atan //; split_Rabs; lra.
apply: is_derive_ext_loc Hl _.
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

Lemma asin_right_inv x : -1 <= x <= 1 -> sin (asin x) = x.
Proof.
intros xB.
suff HP y : 0 < y <= 1 -> sin (asin y) = y => [|[H1 H2]].
  have [->|[H|H]] : x = 0 \/ -1 <= x < 0 \/ 0 < x <= 1 by lra.
  - by rewrite asin_0 sin_0.
  - have: sin (asin (- x)) = -x by apply: HP; lra.
    by rewrite asin_opp sin_neg; lra.
  by apply: HP.
have [->|yL1] : y = 1 \/ y < 1 by lra.
  by rewrite asin_1 sin_PI2.
rewrite asin_atan; last by lra.
have SH : sqrt (1 - y ^ 2) <> 0.
    intro H.
    have [] : 1 - y ^ 2 <> 0 by nra.
    by apply: sqrt_eq_0; nra.
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

Lemma asin_bound x : -1 <= x <= 1 -> - (PI/2) <= asin x <= PI/2.
Proof.
move=> xB.
suff F y : 0 <= y <= 1 -> -(PI/2) <= asin y <= PI/2 => [|Hy].
  have [H|H] : 0 <= x \/ x <= 0 by lra.
    by apply: F; lra.
  have : -(PI/2) <= asin (-x)  <= PI/2 by apply: F; lra.
  by rewrite asin_opp; lra.
have PIP := PI_RGT_0.
have [->|yP] : y = 0 \/ 0 < y by lra.
  by rewrite asin_0; lra.
rewrite /asin; case: total_order_T => [[]|_]; try lra.
have [->|yO] : y = 1 \/ y < 1 by lra.
  replace (1 - 1 * 1) with 0 by lra.
  rewrite sqrt_0 [0 /_]Rmult_0_l atan_0; lra.
set a := _ / y.
have Ha := atan_bound a.
suff : 0 < atan a by lra.
rewrite -atan_0; apply: atan_increasing.
apply: Rdiv_lt_0_compat => //.
by apply: sqrt_lt_R0; nra.
Qed.

Lemma asin_left_inv x : -(PI/2) <= x <= PI/2 -> asin (sin x) = x.
Proof.
move=> HB.
apply: sin_is_inj => //.
  apply: asin_bound.
  apply: SIN_bound.
apply/asin_right_inv/SIN_bound.
Qed.

Lemma asin_Vsqrt2 : asin (/sqrt 2) = PI/4.
Proof.
rewrite asin_atan; last first.
  split; last first.
    replace 1 with (/1) by lra.
    apply: Raux.Rinv_lt; try lra.
    by rewrite -sqrt_1; apply: sqrt_lt_1_alt; lra.
  apply: Rlt_trans (_ : 0 < _); try lra.
  by apply/Rinv_0_lt_compat/sqrt_lt_R0; lra.
have SH := sqrt2_neq_0.
rewrite -Rinv_pow // sqrt_pow_2; try lra.
rewrite (_ : 1 - /2 = /2); try lra.
rewrite -inv_sqrt; try lra.
by rewrite (_ : _ / _ = 1) ?atan_1 //; field.
Qed.

Lemma lim_asin_1 : filterlim asin (at_left 1) (at_left (PI/2)).
Proof.
suff F : filterlim (fun x => atan (x / sqrt (1 - x ^ 2))) (at_left 1) (at_left (PI/2)).
  move => P U.
  have [x Hx] := F P U.
  have xP : 0 < x by apply: cond_pos.
  pose y := Rmin x (/2).
  have yP : 0 < y.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have yB : y <= x /\ y <= /2.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  exists (mkposreal _ yP) => /= z Hz zL1.
  rewrite asin_atan.
    apply: Hx => //.
    apply: ball_le Hz.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have /ball_Rabs HH := Hz.
  by split_Rabs; lra.
apply: filterlim_comp; last first.
  by apply: lim_atan_p_infty.
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

Lemma lim_asin_m1 : filterlim asin (at_right (-1)) (at_right (-PI/2)).
Proof.
apply: filterlim_ext.
  move=> x.
  by rewrite -{2}[x](Ropp_involutive) asin_opp.
apply: filterlim_comp; last first.
  by rewrite RIneq.Ropp_div; apply: filterlim_Ropp_left.
apply: filterlim_comp; last by exact: lim_asin_1.
rewrite -[1](Ropp_involutive).
exact: filterlim_Ropp_right.
Qed.

(* A twisted definition of acos so it is defined for -1 and 1 *)
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

(* We recover the "natural" definition *)
Lemma acos_sin x : -1 < x < 1 -> acos x = PI/2 - asin x.
Proof.
move=> xB.
wlog : x xB / 0 < x => [H|xP].
  have [xN|[->|xP]] : (x < 0 \/ x = 0 \/ x > 0) by lra.
  - by rewrite -{1}[x]Ropp_involutive acos_opp H ?asin_opp; lra.
  - by rewrite acos_0 asin_0; lra.
  by apply: H; lra.
rewrite /acos; case: total_order_T => [[|]|_]; try lra.
rewrite asin_atan // -Interval_missing.atan_inv; last first.
  apply: RIneq.Rdiv_lt_0_compat => //.
  by apply: sqrt_lt_R0; nra.
rewrite Rinv_Rdiv; try lra.
  by rewrite (_ : x * x = x ^ 2); lra.
by move/sqrt_eq_0; nra.
Qed.

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
  rewrite acos_sin //; split_Rabs; lra.
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
  rewrite acos_sin.
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

Lemma lim_acos_m1 : filterlim acos (at_right (-1)) (at_left PI).
Proof.
apply: filterlim_ext.
  move=> x.
  by rewrite -{2}[x](Ropp_involutive) acos_opp.
apply: filterlim_comp.
  apply: filterlim_comp.
    exact: filterlim_Ropp_right.
  rewrite Ropp_involutive.
  exact: lim_acos_1.
move => P [d /= Hd].
exists d => y /= Hy Hy'.
apply Hd; last by lra.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
replace (Rabs (PI - y + - PI)) with (Rabs (y - 0)).
  by apply Hy.
split_Rabs; lra.
Qed.
