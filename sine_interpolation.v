From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_trigo CPoly_interpolation.
Import Rtrigo_def.
Import Rtrigo1.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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


