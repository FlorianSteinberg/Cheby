From mathcomp Require Import all_ssreflect  all_algebra.
Require Import Rstruct CPoly CPoly_trigo CPoly_interpolation.
Import Rtrigo_def Rtrigo1.
Require Import Reals Coquelicot.Coquelicot Interval.Tactic Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for cos                                         *)
(*                                                                           *)
(*****************************************************************************)

Section Cos.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let cinter := interpolation cos ls.
Let cerror := ierror cos ls.

Definition cos_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) cos (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma cos_cheby_eq :
   cinter = \sum_(i < n.+1) cos_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_cos k x : 
  Derive_n cos k x = 
    (if odd k then (-1) ^ k./2 * - sin x else (-1) ^ k./2 * cos x).
Proof.
by apply/is_derive_n_unique/Coquelicot.is_derive_n_cos.
Qed.

Lemma ierror_cos x z :
  a <= x <= b ->
  (forall y, a <= y <= b -> 
    if odd n then Rabs (cos y) <= z else Rabs (sin y) <= z) ->
  Rabs (cerror x) <= (b - a)^+ n.+1 / ((expn 2 n.+1.*2.-1 * n.+1 `!) %:R) * z.
Proof.
move=> xB HD.
apply: ierror_scheby => //.
- have H : a - 1 < a by lra.
  by exact H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> y k yB kLn.
  apply: Coquelicot.ex_derive_n_is_derive_n.
  by apply: Coquelicot.is_derive_n_cos.
- move=> y k kLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_cos.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    apply: continuous_opp.
    by apply: continuous_sin.
  by apply: continuous_cos.
move=> y yB.
rewrite Derive_n_cos /=.
have := HD _ yB; case: odd => /=.
  by rewrite Rabs_mult pow_1_abs; lra.
by rewrite Rabs_mult pow_1_abs; split_Rabs; lra.
Qed.

Lemma cos_scheby_ge x :
  a <= x <= b ->
  (   (forall x, a <= x <= b -> (if odd n then sin x else cos x) <= 0) 
    \/
      (forall x, a <= x <= b -> (if odd n then sin x else cos x) >= 0)) ->
  Rabs (cerror x) <= Rmax (Rabs (cerror a)) (Rabs (cerror b)).
Proof.
move=> xB HD.
have oddE k : (-1) ^ k = if odd k then -1 else 1.
  by elim: k => //= k ->; case: odd => /=; lra.
apply: interpolation_scheby_ge => //.
- have H : a - 1 < a by lra.
  by exact: H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> m y mLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_cos.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    apply: continuous_opp.
    by apply: continuous_sin.
  by apply: continuous_cos.
- move: HD. 
  have [On|En] := boolP (odd n) => [] [HD|HD];
    have [On1|En1] := boolP (odd n./2).
  - right => y yB; rewrite Derive_n_cos /= On oddE On1 /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_cos /= On oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_cos /= On oddE On1 /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_cos /= On oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_cos /= (negPf En) oddE On1 /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_cos /= (negPf En) oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_cos /= (negPf En) oddE On1 /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_cos /= (negPf En) oddE (negPf En1) /=.
    by have := HD _ yB; lra.
move=> m y mLn yB.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Coquelicot.is_derive_n_cos.
Qed.

End Cos.


(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for exp                                         *)
(*                                                                           *)
(*****************************************************************************)

Section Exp.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let einter := interpolation exp ls.
Let eerror := ierror exp ls.

Definition exp_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) exp (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma exp_cheby_eq :
   einter = \sum_(i < n.+1) exp_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_exp k x : Derive_n exp k x =  exp x. 
Proof.
by apply/is_derive_n_unique/is_derive_n_exp.
Qed.

Lemma exp_scheby_ge x :
  a <= x <= b -> True ->
  Rabs (eerror x) <= Rmax (Rabs (eerror a)) (Rabs (eerror b)).
Proof.
move=> xB HD.
apply: interpolation_scheby_ge => //.
- have H : a - 1 < a by lra.
  by exact: H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> m y mLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_exp.
  by apply: continuous_exp.
- right => y yD.
  rewrite Derive_n_exp.
  by have := exp_pos y; lra.
move=> m y mLn yB.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: is_derive_n_exp.
Qed.

End Exp.


(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for 1/x                                         *)
(*                                                                           *)
(*****************************************************************************)


Section Inv.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let iinter := interpolation Rinv ls.
Let ierror := ierror Rinv ls.

Definition inv_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) /(((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma inv_cheby_eq :
   iinter = \sum_(i < n.+1) inv_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_inv k x : 
  x <> 0 ->
  Derive_n Rinv k x =  (-1) ^ k * INR (k`!) * / x ^ k.+1.
Proof.
move=> xD0.
rewrite -add1n.
suff -> : (-1) ^ k * INR k`! = \big[Rmult/1]_(i < k)  - INR (1 + i).
  by apply/is_derive_n_unique/(Coquelicot.is_derive_n_inv _).
elim: k => [|k IH].
  by rewrite big_ord0 fact0 Rmult_1_r.
rewrite factS mult_INR big_ord_recr -IH.
by toR; lra.
Qed.

Lemma continuous_pow m x : continuous (pow^~ m) x.
Proof.
elim: m => [|m IH] //=.
  by apply: continuous_const.
apply: continuous_mult IH.
apply: continuous_id.
Qed.

Lemma inv_scheby_ge x :
  a <= x <= b -> ~ (a <= 0 <= b) ->
  Rabs (ierror x) <= Rmax (Rabs (ierror a)) (Rabs (ierror b)).
Proof.
move=> xB zB.
have FPos : 0 < INR (n.+2)`! by apply/lt_0_INR/ltP/fact_gt0.
have F z : z * z = z ^ 2 by lra.
have [aN|aP] : (a < 0 \/ a > 0) by lra.
  have bN : b < 0 by lra.
  have Ha : a - 1 < a by lra.
  have Hb : b < b - b / 2 by lra.
  apply: interpolation_scheby_ge Ha Hb _ _ _ _ => //.
  - move=> m y mLn yB.
    apply: continuous_ext_loc.
      pose z := Rmin (y - 2 * a) (b / 2 - y).
      have Pz : 0 < z by apply: Rmin_pos; lra.
      exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
      apply/sym_equal/Derive_n_inv.
      rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
      by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
    apply: continuous_scal; first apply: continuous_const.
    apply: continuous_Rinv_comp.
      by apply: continuous_pow.
    by apply: pow_nonzero; lra.
  - have [On|En] := boolP (odd n).
      left => x1 Hx1.
      rewrite Derive_n_inv; try lra.
      rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= On GRing.expr1.
      apply/Rlt_le.
      suff : 0 < / x1 ^ n.+3 by toR; nra.
      apply: Rinv_0_lt_compat.
      rewrite -[_.+3]odd_double_half /= On add0n -addnn.
      rewrite Rdef_pow_add F.
      apply: pow2_gt_0.
      by apply: pow_nonzero; lra.
    left => x1 Hx1.
    rewrite Derive_n_inv; try lra.
    rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= (negPf En) GRing.expr0.
    apply/Rlt_le.
    suff : / x1 ^ n.+3 < 0 by toR; nra.
    apply: Rinv_lt_0_compat.
    rewrite -[_.+3]odd_double_half /= En.
    rewrite -addnn !pow_add F pow_1.
    suff : 0 < (x1 ^ (uphalf n).+1) ^ 2 by nra.
    apply: pow2_gt_0.
    by apply: pow_nonzero; lra.
  move=> m y Hm Hl.
  apply: Coquelicot.ex_derive_n_is_derive_n.
  by apply: Coquelicot.is_derive_n_inv; lra.
have bN : 0 < b by lra.
have Ha : a - a / 2 < a by lra.
have Hb : b < b + 1 by lra.
apply: interpolation_scheby_ge Ha Hb _ _ _ _ => //.
- move=> m y mLn yB.
  apply: continuous_ext_loc.
  pose z := Rmin (y - a / 2) (b + 1 - y).
    have Pz : 0 < z by apply: Rmin_pos; lra.
    exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
    apply/sym_equal/Derive_n_inv.
    rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
    by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
  apply: continuous_scal; first apply: continuous_const.
  apply: continuous_Rinv_comp.
    by apply: continuous_pow.
  by apply: pow_nonzero; lra.
- have [On|En] := boolP (odd n).
    left => x1 Hx1.
    rewrite Derive_n_inv; try lra.
    rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= On GRing.expr1.
    apply/Rlt_le.
    suff : 0 < / x1 ^ n.+3 by toR; nra.
    apply: Rinv_0_lt_compat.
    rewrite -[_.+3]odd_double_half /= On add0n -addnn.
    rewrite Rdef_pow_add F.
    apply: pow2_gt_0.
    by apply: pow_nonzero; lra.
  right => x1 Hx1.
  rewrite Derive_n_inv; try lra.
  rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= (negPf En) GRing.expr0.
  apply/Rgt_ge/Rlt_gt.
  suff : 0 < / x1 ^ n.+3 by toR; nra.
  apply: Rinv_0_lt_compat.
  rewrite -[_.+3]odd_double_half /= En.
  rewrite -addnn !pow_add F pow_1.
  suff : 0 < (x1 ^ (uphalf n).+1) ^ 2 by nra.
  apply: pow2_gt_0.
  by apply: pow_nonzero; lra.
move=> m y Hm Hl.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Coquelicot.is_derive_n_inv; lra.
Qed.

End Inv.

(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for ln                                          *)
(*                                                                           *)
(*****************************************************************************)

Section Ln.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let linter := interpolation ln ls.
Let lerror := ierror ln ls.

Definition ln_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) ln (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma ln_cheby_eq :
   linter = \sum_(i < n.+1) ln_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_ln k x : 
  0 < x ->
  Derive_n ln k.+1 x =  (-1) ^ k * INR (k`!) * / x ^ k.+1.
Proof.
move=> xP.
rewrite -add1n.
suff -> : (-1) ^ k * INR k`! = \big[Rmult/1]_(i < k)  - INR (1 + i).
  by apply/is_derive_n_unique/(Coquelicot.is_derive_n_ln _).
elim: k => [|k IH].
  by rewrite big_ord0 fact0 Rmult_1_r.
rewrite factS mult_INR big_ord_recr -IH.
by toR; lra.
Qed.

Lemma ln_scheby_ge x :
  a <= x <= b -> 0 < a ->
  Rabs (lerror x) <= Rmax (Rabs (lerror a)) (Rabs (lerror b)).
Proof.
move=> xB zB.
have FPos : 0 < INR (n.+1)`! by apply/lt_0_INR/ltP/fact_gt0.
have F z : z * z = z ^ 2 by lra.
have bN : 0 < b by lra.
have Ha : a - a / 2 < a by lra.
have Hb : b < b + 1 by lra.
apply: interpolation_scheby_ge Ha Hb _ _ _ _ => //.
- move=> m y mLn yB.
  case: m mLn => [_|m mLn].
    by apply: continuous_ln; lra.
  apply: continuous_ext_loc.
  pose z := Rmin (y - a / 2) (b + 1 - y).
    have Pz : 0 < z by apply: Rmin_pos; lra.
    exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
    apply/sym_equal/Derive_n_ln.
    rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
    by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
  apply: continuous_scal; first apply: continuous_const.
  apply: continuous_Rinv_comp.
    by apply: continuous_pow.
  by apply: pow_nonzero; lra.
- have [On|En] := boolP (odd n).
    right => x1 Hx1.
    rewrite Derive_n_ln; try lra.
    rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= On Rmult_1_l.
    apply/Rgt_ge/Rlt_gt.
    suff : 0 < / x1 ^ n.+2 by toR; nra.
    by apply/Rinv_0_lt_compat/pow_lt; lra.
  left => x1 Hx1.
  rewrite Derive_n_ln; try lra.
  rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= (negPf En).
  rewrite  GRing.expr1.
  apply: Rlt_le.
  suff : 0 < / x1 ^ n.+2 by toR; nra.
  by apply/Rinv_0_lt_compat/pow_lt; lra.
move=> m y Hm Hl.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Coquelicot.is_derive_n_ln; lra.
Qed.

End Ln.

(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for sin                                         *)
(*                                                                           *)
(*****************************************************************************)


Section Sin.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let sinter := interpolation sin ls.
Let serror := ierror sin ls.

Definition sin_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) sin (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma sin_cheby_eq :
   sinter = \sum_(i < n.+1) sin_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_sin k x : 
  Derive_n sin k x = 
    (if odd k then (-1) ^ k./2 * cos x else (-1) ^ k./2 * sin x).
Proof.
by apply/is_derive_n_unique/Coquelicot.is_derive_n_sin.
Qed.

Lemma ierror_sin x z :
  a <= x <= b ->
  (forall y, a <= y <= b -> 
    if odd n then Rabs (sin y) <= z else Rabs (cos y) <= z) ->
  Rabs (serror x) <= (b - a)^+ n.+1 / ((expn 2 n.+1.*2.-1 * n.+1 `!) %:R) * z.
Proof.
move=> xB HD.
apply: ierror_scheby => //.
- have H : a - 1 < a by lra.
  by exact H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> y k yB kLn.
  apply: Coquelicot.ex_derive_n_is_derive_n.
  by apply: Coquelicot.is_derive_n_sin.
- move=> y k kLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_sin.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    by apply: continuous_cos.
  by apply: continuous_sin.
move=> y yB.
rewrite Derive_n_sin /=.
have := HD _ yB; case: odd => /=.
  by rewrite Rabs_mult pow_1_abs; lra.
by rewrite Rabs_mult pow_1_abs; lra.
Qed.

Lemma sin_scheby_ge x :
  a <= x <= b ->
  (   (forall x, a <= x <= b -> (if odd n then cos x else sin x) <= 0) 
    \/
      (forall x, a <= x <= b -> (if odd n then cos x else sin x) >= 0)) ->
  Rabs (serror x) <= Rmax (Rabs (serror a)) (Rabs (serror b)).
Proof.
move=> xB HD.
have oddE k : (-1) ^ k = if odd k then -1 else 1.
  by elim: k => //= k ->; case: odd => /=; lra.
apply: interpolation_scheby_ge => //.
- have H : a - 1 < a by lra.
  by exact: H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> m y mLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_sin.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    by apply: continuous_cos.
  by apply: continuous_sin.
- move: HD. 
  have [On|En] := boolP (odd n) => [] [HD|HD];
    have [On1|En1] := boolP (odd n./2).
  - left => y yB; rewrite Derive_n_sin /= On oddE On1 /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_sin /= On oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_sin /= On oddE On1 /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_sin /= On oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_sin /= (negPf En) oddE On1 /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_sin /= (negPf En) oddE (negPf En1) /=.
    by have := HD _ yB; lra.
  - right => y yB; rewrite Derive_n_sin /= (negPf En) oddE On1 /=.
    by have := HD _ yB; lra.
  - left => y yB; rewrite Derive_n_sin /= (negPf En) oddE (negPf En1) /=.
    by have := HD _ yB; lra.
move=> m y mLn yB.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Coquelicot.is_derive_n_sin.
Qed.

End Sin.

(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for atan                                         *)
(*                                                                           *)
(*****************************************************************************)


Section Atan.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let atinter := interpolation atan ls.
Let aterror := ierror atan ls.

Definition atan_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) atan (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma atan_cheby_eq :
   atinter = \sum_(i < n.+1) atan_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Definition coef_poly_atan (m i : nat) (k2 := (m - i)%nat) (k := k2./2) := 
  if odd k2 then 0 else
  (-1)^+ k * 'C(m.+1, k2.+1) %:R.

Definition poly_atan m : {poly R} := \poly_(i < m.+1) coef_poly_atan m i.

Import GRing.Theory.

Fixpoint eval_atan_rec m (bv : bool) i j x res := 
  if m is m1.+2 then
  let i1 := i.+2 in 
  let j1 := ((j * m  %/ i1) * m.-1 %/ i1.+1)%nat in
  let res1 := res * x * x + (-1) ^+ bv * j1%:R in
  eval_atan_rec m1 (~~ bv) i1 j1 x res1
  else if m is 1%nat then x * res else res.

Lemma eval_atan_rec_cor m m1 bv i j x res :
  ~~ odd i ->
  (m1 <= m)%nat ->
  (m = m1 + i)%nat ->
  (j = 'C(m.+1, i.+1))%nat ->
  (bv = odd i./2.+1)%nat ->
  res = (\poly_(u < (m - m1).+1) coef_poly_atan m (u + m1)).[x] ->
  eval_atan_rec m1 bv i j x res = (\poly_(i < m.+1) coef_poly_atan m i).[x].
Proof.
have [v VV] := ubnP (m1.+1).
elim: v m1 VV bv i j res => 
   // v IH [|[|m1]] /= mLv bv i j res iE m1Lm mE jE bvE resE.
- rewrite resE subn0; congr (_.[_]).
  by apply: eq_poly => i1; rewrite addn0.
- rewrite resE subn1 prednK //.
  rewrite (_ : forall x y, x * y = (x * y)%RR) //.
  rewrite -{1}[x]hornerX -hornerM; congr (_.[_]).
  apply/polyP => /= w.
  rewrite coefXM !coef_poly addn1.
  case: w => //=.
  rewrite /coef_poly_atan ifT //.
  rewrite subn0 -[odd _]negbK -[~~ (odd _)]/(odd (S m)).
  by rewrite mE /= iE.
rewrite IH //=.
- by rewrite ltnS in mLv; apply: leq_trans mLv.
- by rewrite iE.
- by rewrite (leq_trans _ m1Lm) // ltnW.
- by rewrite 2!addnS.
- rewrite jE (_ : m1.+2 = m.+1 - i.+1)%nat; last by rewrite subSS mE addnK.
  rewrite [(_ * (_ - _))%nat]mulnC -mul_bin_left //.
  rewrite [(_ * 'C(_, _))%nat]mulnC mulnK //.
  rewrite (_ : m1.+1 = m.+1 - i.+2)%nat; last first.
    by rewrite mE -addSn 2!addSnnS addnK.
  rewrite [(_ * (_ - _))%nat]mulnC -mul_bin_left //.
  by rewrite [(_ * 'C(_, _))%nat]mulnC mulnK //.
- by rewrite bvE.
rewrite resE jE.
rewrite !(_ : forall x y, x * y = (x * y)%RR) //.
rewrite -{2 3}[x]hornerX -!hornerM -(hornerC (_ * _%:R) x).
rewrite !(_ : forall x y, x + y = (x + y)%RR) //.
rewrite -hornerD; congr (_.[_]).
apply/polyP => /= w.
rewrite coefD coefC !coefMX !coef_poly.
case: w => [|[|w]] /=.
- rewrite add0r add0n /= /coef_poly_atan.
  have ->/=: (m - m1 = i.+2)%nat.
    rewrite mE 2!addSn 2?subSn ?leq_addr //.
      by rewrite addnC addnK.
    by rewrite -addnS leq_addr.
  rewrite iE /= bvE -[in RHS]signr_odd; congr (_ * _)%RR.
  rewrite (_ : m1.+2 = m.+1 - i.+1)%nat; last by rewrite subSS mE addnK.
  rewrite [(_ * (_ - _))%nat]mulnC -mul_bin_left //.
  rewrite [(_ * 'C(_, _))%nat]mulnC mulnK //.
  rewrite (_ : m1.+1 = m.+1 - i.+2)%nat; last first.
    by rewrite mE -addSn 2!addSnnS addnK.
  rewrite [(_ * (_ - _))%nat]mulnC -mul_bin_left //.
  by rewrite [(_ * 'C(_, _))%nat]mulnC mulnK.
- rewrite ltnS subn_gt0 -ltnS (leq_trans m1Lm) //=.
  by rewrite add0r /coef_poly_atan mE addSnnS addnC addnK /= iE.
rewrite addr0 !ltnS -2!ltnS -2?subSn ?subSS ?addnS //=.
by rewrite (leq_trans m1Lm).
Qed.

Definition eval_atan m x := eval_atan_rec m true 0 m.+1 x m.+1%:R.

Lemma eval_atan_cor m x :
  eval_atan m x = (\poly_(i < m.+1) coef_poly_atan m i).[x].
Proof.
apply: eval_atan_rec_cor => //.
- by rewrite addn0.
- by rewrite bin1.
rewrite subnn /coef_poly_atan.
rewrite horner_poly big_ord1 subnn /= expr0 mulr1 bin1.
by rewrite Rmult_1_l.
Qed.

Lemma size_poly_atan m : size (poly_atan m) = m.+1.
Proof.
apply: size_poly_eq.
rewrite /coef_poly_atan /=.
rewrite subnn /= bin1.
apply: GRing.mulf_neq0.
  apply: GRing.expf_neq0.
  by rewrite GRing.oppr_eq0 GRing.oner_neq0.
by rewrite Num.Theory.pnatr_eq0.
Qed.

Lemma poly_atan_0 : poly_atan 0%nat = 1%:P.
Proof.
apply/polyP => i; rewrite coefC coef_poly /coef_poly_atan /=.
by case: i; rewrite //= binn !Rmult_1_l.
Qed.

Import GRing.Theory.

Lemma poly_atan_deriv m : 
 ((m.+1)%:R%:P * poly_atan m.+1 =
   (2%:R * m.+1%:R)%:P * 'X * (poly_atan m)-
        ('X^2 + 1%:P) * (poly_atan m)^`())%RR.
Proof.
apply/polyP => i.
rewrite [(('X^2 + _) * _)%RR]mulrDl mul1r coefCM coefB coefD.
rewrite -mulrA coefCM coefXnM coefXM.
rewrite coef_deriv /coef_poly_atan !coef_poly.
rewrite /coef_poly_atan size_poly_atan !ltnS.
case: m => [|[|m]]; rewrite /= ?rm0.
- by case: i => [|[|i]]; rewrite /= ?rm0 //; toR; lra.
- case: i => [|[|[|i]]]; rewrite //= ?rm0; try (toR; lra).
  rewrite -['C(3, _)]/1%nat -['C(2, _)]/2%nat ?rm1.
  by toR; lra.
case: i => [|[|i]]; rewrite ?rm0 !subSS !subn0 /=.
- rewrite negbK binn binSn.
  case: odd; rewrite /= ?rm0 //.
  rewrite !exprS Rmult_1_r -[in RHS]mulr_natl.
  by toR; lra.
- case: odd; rewrite /= ?rm0 //.
  rewrite !exprS.
  rewrite binSn binn.
  set v := _ ^+ _.
  rewrite !rm1 Rmult_1_r -!mulrnAr !natrS.
  rewrite (_ : _ *+2 = m.+3%:R * m.+2%:R)%RR.
    rewrite -[in RHS]mulr_natl !natrS; toR; lra.
  rewrite -bin_sub 1?ltnW // subSS subSn // subSn // subnn.
  by rewrite mulr2n -natrD addnn -muln2 bin_ffact ffactnS ffactn1 natrM.
rewrite !ltnS.
case: (leqP i m.+1) => [|H]; last first.
  rewrite !rm0.
  by rewrite ifN ?rm0 // ltnNge (leq_trans _ H) // ltnW.
rewrite leq_eqVlt => /orP[/eqP->|].
  rewrite subnn /= ifN ?ltnNge 1?ltnW //.
  rewrite !rm0 !bin1 /=.
  rewrite -[_ *+ m.+2]mulr_natl !natrS.
  by toR; lra.
rewrite ltnS leq_eqVlt => /orP[/eqP<-|H1].
  by rewrite subSn // subnn ltnn !rm0.
rewrite H1 /=.
rewrite subSn 1?ltnW // subnS.
set u := (_ - _)%nat.
rewrite -(subnKC (ltnW H1)) {}/u. 
move: H1; rewrite -subn_gt0; case: subn => [|k]; rewrite //= ?negbK !addnS => Hk.
have [H2|H2] := boolP (odd _).
  by rewrite !rm0.
rewrite [LHS]mulrCA -2!natrM.
have->: ((i + k).+4 * 'C((i + k).+1.+4, k.+3) =
  'C((i + k).+4, k.+1) *i.+3 +
  (i.+1 + k.+1.*2).+4 * 'C((i + k).+4, k.+3))%nat.
  rewrite binS mulnDr.
  suff-> : ((i + k).+4 * 'C((i + k).+4, k.+2) =
         'C((i + k).+4, k.+1) * i.+3 +
           k.+3 * 'C((i + k).+4, k.+3))%nat.
    by rewrite addnCA -mulnDl -addnn !addSn !addnS addnA.
  rewrite [(_ * i.+3)%nat]mulnC (_ : i.+3 = (i + k).+4 - k.+1)%nat; last first. 
    by rewrite subSS !subSn ?addnK ?leq_addl // ltnW // ltnS // ?leq_addl // ltnW // ltnS // leq_addl.
  rewrite -mul_bin_left.
  rewrite [X in (_ = _ + X)%nat]mul_bin_left.
  rewrite -mulnDl; congr (_ * _)%nat.
  by rewrite [RHS]addnC subnK // ltnS ltnW // !ltnS ltnW // ltnS leq_addl.
rewrite exprS.
move: (_^+ _) 'C(_,_) 'C(_,_) => u1 v1 v2.
rewrite -[_ *+ i.+3]mulr_natl.
rewrite -[_ *+ i.+1]mulr_natl.
rewrite -addnn !(natrM, natrD, natrS).
toR; lra.
Qed.

Lemma Derive_n_atan k x : 
  Derive_n atan k.+1 x = (-1)^+ k * k`!%:R * (poly_atan k).[x] / (1 + x ^ 2)^k.+1.
Proof.
elim: k x => [x|k IH x].
  rewrite /= poly_atan_0 !hornerE /=.
  apply: is_derive_unique.
  rewrite !Rmult_1_r /Rdiv Rmult_1_l.
  by exact: is_derive_atan.
apply: etrans.
  apply: Derive_ext => y.
  by exact: IH.
rewrite Derive_div; last 3 first.
  - apply: ex_derive_mult.
      by apply: ex_derive_const.
    by exact: ex_derive_horner.
  - apply: ex_derive_pow.
    apply: ex_derive_plus.
      by apply: ex_derive_const.
    apply: ex_derive_pow.
    by apply: ex_derive_id.
 - by apply: pow_nonzero; nra.
rewrite factS mulnC natrM ![in RHS]Rmult_assoc.
rewrite (_ : k.+1%:R = k.+1%:R%:P.[x]); last by rewrite hornerE.
rewrite -[_.[x] * _.[x]](@hornerM (GRing.ComPzRing.clone _ R)).
rewrite poly_atan_deriv.
rewrite ![in RHS]hornerE !Derive_scal !Derive_horner .
rewrite Derive_pow; last first.
  apply: ex_derive_plus.
    by apply: ex_derive_const.
  apply: ex_derive_pow.
  by apply: ex_derive_id.
rewrite Derive_plus; last 2 first.
- by apply: ex_derive_const.
- by apply/ex_derive_pow/ex_derive_id.
rewrite Derive_const Derive_pow; last first.
  by exact: ex_derive_id.
rewrite Derive_id.
rewrite -natr_INR !natrS /= exprS.
rewrite !(Rmult_1_l, Rmult_1_r, Rplus_0_l).
rewrite (_ : x * x + 1 = 1 + x * x)%RR; last by toR; lra.
toR.
set u1 := _.[_].
set u2 := _.[_].
set v1 := 1 + _.
set v2 := _ ^ _.
field; split.
  by rewrite /v2 /v1; apply: pow_nonzero; nra.
by rewrite /v1; nra.
Qed.

Lemma ierror_atan x z :
  a <= x <= b ->
  (forall y, a <= y <= b -> 
      Rabs (poly_atan n).[y] / (1 + y ^ 2)^n.+1 <= z) ->
  Rabs (aterror x) <= (b - a)^+ n.+1 / ((expn 2 n.+1.*2.-1 * n.+1) %:R) * z.
Proof.
move=> xB HD.
have-> : (b - a)^+ n.+1 / ((expn 2 n.+1.*2.-1 * n.+1) %:R) * z =
         (b - a)^+ n.+1 / ((expn 2 n.+1.*2.-1 * n.+1`!) %:R) * (n`!%:R * z).
  rewrite factS !natrM !natrS; toR; field; repeat split.
  - apply: (not_INR _ 0%nat) => //.
    by case: _`! (fact_gt0 n).
  - have : 0 <= INR n by apply: pos_INR.
    by lra.
  apply: (not_INR _ 0%nat) => //.
  by case: expn (expn_gt0 2 n.*2.+1).
apply: ierror_scheby => //.
- have H : a - 1 < a by lra.
  by exact H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> y k yB kLn.
  apply: Coquelicot.ex_derive_n_is_derive_n.
  by apply: Private.IT1.IT.TM.TMI.is_derive_n_atan.
- move=> y [/=|k] kLn yB.
    by apply: continuous_atan.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_atan.
  apply: continuous_mult.
    apply: ex_derive_continuous.
    apply: ex_derive_mult.
      by apply: ex_derive_const.
    by apply: ex_derive_horner.
  apply: continuous_Rinv_comp; last first.
    by apply: pow_nonzero; nra.
  apply: ex_derive_continuous.
  apply: ex_derive_pow.
  apply: ex_derive_plus.
    by apply: ex_derive_const.
  apply: ex_derive_pow.
  by apply: ex_derive_id.
move=> y yB.
rewrite Derive_n_atan Rabs_mult.
rewrite [X in _ * X <= _]Rabs_pos_eq.
  rewrite !Rabs_mult Rabs_exprN1 Rmult_1_l.
  rewrite Rabs_pos_eq; last first.
    by rewrite natr_INR; apply: pos_INR.
  rewrite Rmult_assoc.
  apply: Rmult_le_compat_l.
    by rewrite natr_INR; apply: pos_INR.
  by exact: HD.
apply/Rlt_le/Rinv_0_lt_compat.
by apply: pow_lt; nra.
Qed.

Lemma atan_scheby_ge x :
  a <= x <= b ->
  (   (forall x, a <= x <= b -> (poly_atan n.+1).[x] <= 0) 
    \/
      (forall x, a <= x <= b -> (poly_atan n.+1).[x] >= 0)) ->
  Rabs (aterror x) <= Rmax (Rabs (aterror a)) (Rabs (aterror b)).
Proof.
move=> xB HD.
apply: interpolation_scheby_ge => //.
- have H : a - 1 < a by lra.
  by exact: H.
- have H : b < b + 1 by lra.
  by exact: H.
- move=> [|m] y mLn yB.
    by apply: continuous_atan.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_atan.
  apply: continuous_mult.
    apply: ex_derive_continuous.
    apply: ex_derive_mult.
      by apply: ex_derive_const.
    by apply: ex_derive_horner.
  apply: continuous_Rinv_comp; last first.
    by apply: pow_nonzero; nra.
  apply: ex_derive_continuous.
  apply: ex_derive_pow.
  apply: ex_derive_plus.
    by apply: ex_derive_const.
  apply: ex_derive_pow.
  by apply: ex_derive_id.
- case: HD => HD.
    case : (boolP (odd n)) => E.
      left => y Hy.
      rewrite Derive_n_atan.
      apply: Rmult_le_0_r; last first.
        apply/Rlt_le/Rinv_0_lt_compat.
        by apply: pow_lt; nra.
      apply: Rmult_le_0_l; last by apply: HD.
      apply: Rmult_le_pos.
        by rewrite -signr_odd /= E expr0; toR; lra.
      by rewrite natr_INR; apply: pos_INR.
    right => y Hy.
    rewrite Derive_n_atan.
    rewrite -signr_odd [odd _]/= E expr1.
    apply/Rle_ge/Rmult_le_pos.
      apply: Stdlib.Rmult_le_neg_neg.
        by rewrite natr_INR; have := pos_INR n.+1`!; toR; lra.
      by apply: HD.
    apply/Rlt_le/Rinv_0_lt_compat.
    by apply: pow_lt; nra.
  case : (boolP (odd n)) => E.
    right => y Hy.
    rewrite Derive_n_atan.
    rewrite -signr_odd [odd _]/= E expr0 Rmult_1_l.
    apply/Rle_ge/Rmult_le_pos.
      apply: Rmult_le_pos.
        by rewrite natr_INR; apply: pos_INR.
      by apply/Rge_le/HD.
    apply/Rlt_le/Rinv_0_lt_compat.
    by apply: pow_lt; nra.
  left => y Hy.
  rewrite Derive_n_atan.
  rewrite -signr_odd [odd _]/= E expr1.
  apply: Rmult_le_0_r.
    apply: Rmult_le_0_r.
      apply: Rmult_le_0_r; first by toR; lra.
      by rewrite natr_INR; apply: pos_INR.
    by apply/Rge_le/HD.
  apply/Rlt_le/Rinv_0_lt_compat.
  by apply: pow_lt; nra.
move=> m y mLn yB.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Private.IT1.IT.TM.TMI.is_derive_n_atan.
Qed.

End Atan.

(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for sqrt                                        *)
(*                                                                           *)
(*****************************************************************************)

Section DoubleFact.

Fixpoint dfact_rec (n : nat) :=
  if n is n1.+2 then muln n (dfact_rec n1) else 1%nat.

Definition dfact := dfact_rec.

Arguments dfact : simpl never.

Lemma dfact0 : dfact 0 = 1%nat.
Proof. by []. Qed.

Lemma dfact1 : dfact 1 = 1%nat.
Proof. by []. Qed.

Lemma dfactSS (n : nat) : dfact n.+2 = muln n.+2 (dfact n).
Proof. by []. Qed.

Lemma dfact_evenE (n : nat) : dfact (n.*2) = muln (expn 2 n) (factorial n).
Proof.
elim: n => // n IH.
rewrite doubleS dfactSS IH factS !mulnA.
congr (_ * _)%nat.
by rewrite expnS [RHS]mulnAC mulnS add2n mul2n.
Qed.

End DoubleFact.

Section Sqrt.

Variable n : nat.
Variable a b : R.
Hypothesis aLb : a < b.

Let l := cheby_nodes n.+1.
Let ls := scheby_nodes a b n.+1.
Let sinter := interpolation sqrt ls.
Let serror := ierror sqrt ls.

Definition sqrt_coef i := 
  (if i == 0%nat then 1 else 2) / INR (n.+1) *
   \sum_(j < n.+1) sqrt (((b - a) * (l`_j) + a + b) / 2)%R * ('T_i).[l`_j].

Lemma sqrt_cheby_eq :
   sinter = \sum_(i < n.+1) sqrt_coef i *: 'T^(a, b)_i.
Proof.
have aDb : a != b by apply/eqP; lra.
rewrite [LHS](@sdsprod_cheby_eq a b n) //.
- apply: eq_bigr => i _.
  congr (_ *: _).
  by apply: sdsprod_coef_interpolation_pT.
apply: leq_trans (interpolation_size _ _) _.
by rewrite size_scheby_nodes.
Qed.

Lemma Derive_n_sqrt k x : 
  0 < x ->
  Derive_n sqrt k x =  (-1) ^ k.-1 *  (/INR (expn 2 k)) * INR (dfact (k.*2 - 3)) *  sqrt x / x ^ k.
Proof.
move=> xP.
suff -> : (-1) ^ k.-1 *  (/INR (expn 2 k)) * INR (dfact (k.*2 - 3))  = 
          \big[Rmult/1]_(i < k) (/ 2 - INR i).
  rewrite [_ / _]Rmult_assoc.
  suff -> : sqrt x * / x ^ k = Rpower x (/ 2 - INR k).
    by apply/is_derive_n_unique/Coquelicot.is_derive_n_sqrt.
  by rewrite Rpower_plus Rpower_Ropp Rpower_sqrt // Rpower_pow.
elim: k => [|[|[|k]] IH].
- by rewrite big_ord0 /=; field.
- by rewrite big_ord1 /=; field.
- by rewrite big_ord_recl big_ord1 /=; field.
rewrite big_ord_recr -IH [nat_of_ord _]/=.
rewrite doubleS -[_.*2.+2]add2n -addnBA // add2n dfactSS.
rewrite [RHS]Rmult_assoc [_ * (_ - _)]Rmult_comm.
rewrite [INR (_ * _)]mult_INR -!Rmult_assoc; congr (_ * _).
rewrite (_ : _ ^ _ = (-1) ^ k.+2.-1  * (-1)); last by rewrite /=; ring.
rewrite 2![LHS]Rmult_assoc [RHS]Rmult_assoc; congr (_ * _).
rewrite expnS mult_INR (_ : (_ - _).+2 = k.*2.+3); last by [].
set u := INR (expn _ _).
rewrite -!mul2n !S_INR !mult_INR /=.
field.
apply/not_0_INR.
by apply/eqP; rewrite expn_eq0.
Qed.

Lemma sqrt_scheby_ge x :
  a <= x <= b -> 0 < a ->
  Rabs (serror x) <= Rmax (Rabs (serror a)) (Rabs (serror b)).
Proof.
move=> xB zB.
have FPos : 0 < INR (n.+1)`! by apply/lt_0_INR/ltP/fact_gt0.
have F z : z * z = z ^ 2 by lra.
have bN : 0 < b by lra.
have Ha : a - a / 2 < a by lra.
have Hb : b < b + 1 by lra.
apply: interpolation_scheby_ge Ha Hb _ _ _ _ => //.
- move=> m y mLn yB.
  case: m mLn => [_|m mLn].
    by apply: continuous_sqrt; lra.
  apply: continuous_ext_loc.
  pose z := Rmin (y - a / 2) (b + 1 - y).
    have Pz : 0 < z by apply: Rmin_pos; lra.
    exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
    apply/sym_equal/Derive_n_sqrt.
    rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
    by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
  apply: continuous_scal; last first.
    apply: continuous_Rinv_comp.
      by apply: continuous_pow.
    by apply: pow_nonzero; lra.
  apply: continuous_scal; last first.
    by apply: continuous_sqrt.
  by apply: continuous_const.
- have [On|En] := boolP (odd n).
    right => x1 Hx1.
    rewrite Derive_n_sqrt; try lra.
    apply/Rle_ge/Rmult_le_pos; last first.
      by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    apply: Rmult_le_pos; last by apply: sqrt_pos.
    apply: Rmult_le_pos; last by apply: pos_INR.
    apply: Rmult_le_pos; last first.
      apply/Rlt_le/Rinv_0_lt_compat/lt_0_INR.
      by apply/ltP; rewrite expn_gt0.
    rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= On /= GRing.expr0.
    by toR; lra.
  left => x1 Hx1.
  rewrite Derive_n_sqrt; try lra.
  apply: Rmult_le_0_r; last first.
    by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
  apply: Rmult_le_0_r; last by apply: sqrt_pos.
  apply: Rmult_le_0_r; last by apply: pos_INR.
  apply: Rmult_le_0_r; last first.
    apply/Rlt_le/Rinv_0_lt_compat/lt_0_INR.
    by apply/ltP; rewrite expn_gt0.
  rewrite -expr_Rexp -GRing.signr_odd [_ ^+ _]/= En /= GRing.expr1.
  by toR; lra.
move=> m y Hm Hl.
apply: Coquelicot.ex_derive_n_is_derive_n.
by apply: Coquelicot.is_derive_n_sqrt; lra.
Qed.

End Sqrt.