From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_trigo CPoly_interpolation.
Import Rtrigo_def.
Import Rtrigo1.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Lemma continuous_pow m x : continuous (pow^~ m) x.
Proof.
elim: m => [|m IH] //=.
  by apply: continuous_const.
apply: continuous_mult IH.
apply: continuous_id.
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