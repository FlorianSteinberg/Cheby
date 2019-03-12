From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Require Import Rstruct CPoly CPoly_trigo CPoly_interpolation.
Import Rtrigo_def.
Import Rtrigo1.
Require Import Reals Coquelicot.Coquelicot Interval.Interval_tactic Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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

Lemma continuous_pow m x : continuous (pow^~ m) x.
Proof.
elim: m => [|m IH] //=.
  by apply: continuous_const.
apply: continuous_mult IH.
apply: continuous_id.
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