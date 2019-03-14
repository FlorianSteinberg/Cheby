From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_trigo CPoly_interpolation.
Import Rtrigo_def Rtrigo1.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

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
by apply/is_derive_n_unique/coquelicot_compl.is_derive_n_cos.
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
  apply: coquelicot_compl.ex_derive_n_is_derive_n.
  by apply: coquelicot_compl.is_derive_n_cos.
- move=> y k kLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_cos.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    apply: continuous_opp.
    by apply: coquelicot_compl.continuous_sin.
  by apply: coquelicot_compl.continuous_cos.
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
    by apply: coquelicot_compl.continuous_sin.
  by apply: coquelicot_compl.continuous_cos.
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
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_cos.
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
by apply/is_derive_n_unique/coquelicot_compl.is_derive_n_exp.
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
  by apply: coquelicot_compl.continuous_exp.
- right => y yD.
  rewrite Derive_n_exp.
  by have := exp_pos y; lra.
move=> m y mLn yB.
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_exp.
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
  by apply/is_derive_n_unique/(coquelicot_compl.is_derive_n_inv _).
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
    apply: coquelicot_compl.continuous_Rinv_comp.
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
  apply: coquelicot_compl.ex_derive_n_is_derive_n.
  by apply: coquelicot_compl.is_derive_n_inv; lra.
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
  apply: coquelicot_compl.continuous_Rinv_comp.
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
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_inv; lra.
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
  by apply/is_derive_n_unique/(coquelicot_compl.is_derive_n_ln _).
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
    by apply: coquelicot_compl.continuous_ln; lra.
  apply: continuous_ext_loc.
  pose z := Rmin (y - a / 2) (b + 1 - y).
    have Pz : 0 < z by apply: Rmin_pos; lra.
    exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
    apply/sym_equal/Derive_n_ln.
    rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
    by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
  apply: continuous_scal; first apply: continuous_const.
  apply: coquelicot_compl.continuous_Rinv_comp.
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
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_ln; lra.
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
by apply/is_derive_n_unique/coquelicot_compl.is_derive_n_sin.
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
  apply: coquelicot_compl.ex_derive_n_is_derive_n.
  by apply: coquelicot_compl.is_derive_n_sin.
- move=> y k kLn yB.
  apply: continuous_ext => [u|].
    apply/sym_equal.
    by exact: Derive_n_sin.
  case: odd; apply: continuous_scal; try apply: continuous_const.
    by apply: coquelicot_compl.continuous_cos.
  by apply: coquelicot_compl.continuous_sin.
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
    by apply: coquelicot_compl.continuous_cos.
  by apply: coquelicot_compl.continuous_sin.
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
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_sin.
Qed.

End Sin.


(*****************************************************************************)
(*                                                                           *)
(*    Interpolation theorems for sqrt                                        *)
(*                                                                           *)
(*****************************************************************************)


Section DoubleFact.

Fixpoint dfact_rec (n : nat) :=
  if n is n1.+2 then muln n (dfact_rec n1) else 1%nat.

Definition dfact := nosimpl dfact_rec.

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
    by apply/is_derive_n_unique/coquelicot_compl.is_derive_n_sqrt.
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
    by apply: coquelicot_compl.continuous_sqrt; lra.
  apply: continuous_ext_loc.
  pose z := Rmin (y - a / 2) (b + 1 - y).
    have Pz : 0 < z by apply: Rmin_pos; lra.
    exists (mkposreal _ Pz) => z1 /AbsRing_norm_compat2 Hz1.
    apply/sym_equal/Derive_n_sqrt.
    rewrite /abs /minus /plus /opp /z /= Rmult_1_l in Hz1.
    by move: Hz1; rewrite /Rmin; case: Rle_dec; split_Rabs; lra.
  apply: continuous_scal; last first.
    apply: coquelicot_compl.continuous_Rinv_comp.
      by apply: continuous_pow.
    by apply: pow_nonzero; lra.
  apply: continuous_scal; last first.
    by apply: coquelicot_compl.continuous_sqrt.
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
apply: coquelicot_compl.ex_derive_n_is_derive_n.
by apply: coquelicot_compl.is_derive_n_sqrt; lra.
Qed.

End Sqrt.