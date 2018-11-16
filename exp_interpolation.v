From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_interpolation.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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


