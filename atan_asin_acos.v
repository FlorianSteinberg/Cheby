(******************************************************************************)
(* This file contains material that should be included into                   *)
(* Coquelicot                                                                 *)
(******************************************************************************)

From mathcomp Require Import all_boot.
From Stdlib Require Import Reals Psatz.
Require Import Coquelicot.Coquelicot Interval.Missing.Stdlib.
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
rewrite <- (atan_tan (PI/2 - eps')); cycle 1.
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
rewrite <- (atan_tan (-PI/2 + eps')); cycle 1.
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
  replace (Rbar_locally p_infty) with 
    (Rbar_locally (Rbar_mult p_infty (/ m))) at 2.
    now apply filterlim_Rbar_mult_r.
  apply f_equal; simpl; case (Rle_dec 0 (/ m)).
    intros r; case (Rle_lt_or_eq_dec 0 (/ m) r); auto.
    now intros abs; rewrite <- abs in abs'; case (Rlt_irrefl 0).
  now intros abs; case abs; apply Rlt_le.
assert (H2 : filterlim (fun x => x / m) (Rbar_locally m_infty)
                (Rbar_locally m_infty)).
  replace (Rbar_locally m_infty) with
    (Rbar_locally (Rbar_mult m_infty (/ m))) at 2.
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
  intros z _; apply (ex_derive_continuous 
                      (fun x1 => /m * / ((x1 / m) ^ 2 + 1))).
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
rewrite <- Rabs_Ropp, !Ropp_plus_distr, Ropp_involutive, <- Rdiv_opp_l.
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
  rewrite asin_atan ?Rsqr_pow2 //; split_Rabs; lra.
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

Lemma lim_asin_1 : filterlim asin (at_left 1) (at_left (PI/2)).
Proof.
suff F : filterlim (fun x => atan (x / sqrt (1 - x ^ 2))) 
                   (at_left 1) (at_left (PI/2)).
  move => P U.
  have [x Hx] := F P U.
  have xP : 0 < x by apply: cond_pos.
  pose y := Rmin x (/2).
  have yP : 0 < y.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  have yB : y <= x /\ y <= /2.
    by rewrite /y /Rmin; case: Rle_dec; lra.
  exists (mkposreal _ yP) => /= z Hz zL1.
  rewrite asin_atan ?Rsqr_pow2.
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
exists (ball 1 posreal_half) (Rlt (2 * (Rmax 1 M))) => [||x y].
- by exists posreal_half.
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
  by rewrite Rdiv_opp_l; apply: filterlim_Ropp_left.
apply: filterlim_comp; last by exact: lim_asin_1.
rewrite -[1](Ropp_involutive).
exact: filterlim_Ropp_right.
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
  rewrite acos_asin //; split_Rabs; lra.
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
  rewrite acos_asin.
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
