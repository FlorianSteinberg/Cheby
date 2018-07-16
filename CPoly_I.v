From mathcomp Require Import all_ssreflect all_algebra.
Require Import Rstruct Reals Psatz Poly_complements CPoly CPoly_exec CPoly_interpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GRing.Theory.
Local Open Scope ring_scope.
Require Import ZArith.
Require Import Interval.Interval_specific_ops.
Require Import Interval.Interval_bigint_carrier.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_missing.
Require Import Interval.Interval_xreal.
Require Import Interval.Interval_definitions.
Require Import Interval.Interval_float_sig.
Require Import Interval.Interval_interval.
Require Import Interval.Interval_interval_float_full.
Require Import Interval.Interval_integral.
Require Import Interval.Interval_bisect.

Module SFBI2 := SpecificFloat BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

Module MyClenshawStuff (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.

Notation mant := BigIntRadix2.smantissa_type.
Notation xpnt := BigIntRadix2.exponent_type.
Check I.fromZ 0.
Notation D := F.type.
Notation ID := (Interval_interval_float.f_interval F.type).
Notation XR := Interval_xreal.ExtendedR.
Notation Xreal := Interval_xreal.Xreal.
Notation "x '\contained_in' I" := (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation lower := I.lower.
Notation upper := I.upper.
Notation diam I := (I.upper I - I.lower I).
Notation bounded := I.bounded.

Section stuff.
Variable prec: F.precision.
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sub I J := (I.sub prec I J).
Notation scl2 I := (I.scale2 I (F.ZtoS 1)).
Notation div I J := (I.div prec I J).
Notation I0 := (I.fromZ 0).

Fixpoint CbIA q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := CbIA q' x in
   let a1 := sub (add a (scl2 (mul (fst t) x))) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition CshawIA p x := sub (CbIA p x).1 (mul (CbIA p x).2 x).

Lemma cntd_I0:
	forall x, x \contained_in I0 -> x = 0%R.
Proof.
move => x.
rewrite /contains/I.convert/=.
rewrite  F.fromZ_correct => /= [[]].
rewrite !/IZR.
lra.
Qed.

Lemma mul_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (mul I J).
Proof.
by apply I.mul_correct.
Qed.

Lemma sub_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof.
by apply I.sub_correct.
Qed.

Lemma add_correct_R x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof.
by apply I.add_correct.
Qed.

Lemma div_correct_R x y I J:
	x\contained_in I -> y \contained_in J -> is_zero y = false -> (x / y) \contained_in (div I J).
Proof.
intros.
have /=:= I.div_correct prec I J (Xreal x) (Xreal y).
rewrite /Xdiv' H1 /= => crct.
by apply crct.
Qed.

Lemma scl2_correct_R x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
intros.
suff -> :(Xreal (x *+ 2)) = (Xmul (Xreal x) (Xreal (bpow radix2 1))).
	by apply I.scale2_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma scale2_correct_R x z I:
	x \contained_in I -> (x * (powerRZ 2 z)) \contained_in (I.scale2 I (F.ZtoS z)).
Proof.
intros.
replace (Xreal (x * (powerRZ 2 z))) with (Xmul (Xreal x) (Xreal (bpow radix2 z))).
	by apply I.scale2_correct.
congr Xreal.
by rewrite bpow_powerRZ.
Qed.

Lemma neg_correct_R x I:
	x \contained_in I -> (-x) \contained_in (I.neg I).
Proof.
by move => xeI; have /=:= (I.neg_correct I (Xreal x) xeI).
Qed.

Lemma stuff (p : {poly R}):
	(forall i : nat, p`_i \contained_in nth I0 [::] i) -> p = 0.
Proof.
move => prp.
apply polyP => i.
rewrite coef0.
apply cntd_I0.
move: (prp i).
by rewrite nth_default.
Qed.

Lemma I00:
	0 \contained_in I0.
Proof.
by rewrite /=F.fromZ_correct/=; lra.
Qed.

Lemma CbIA_crct (p: seq R) (pI: seq ID) (x: R) (I: ID):
	(forall i, (p`_i) \contained_in (nth I0 pI i)) -> x \contained_in I  -> size p = size pI ->
		(Cb p x).1 \contained_in (CbIA pI I).1 /\ (Cb p x).2 \contained_in (CbIA pI I).2.
Proof.
move => prp xJ.
elim: pI p prp => [[ | a p]// prp _ | J pI ih [ | a p]// prp eq].
	by split; apply I00.
rewrite /=.
case: (ih p) => // [i | | ih1 ih2 ].
		by apply (prp (S i)).
	by case: eq.
split => //.
apply sub_correct_R => //.
apply add_correct_R; first exact: (prp 0%nat).
apply scl2_correct_R.
by apply mul_correct_R.
Qed.

Lemma CshawIA_crct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::] by apply size0nil.
	rewrite /Cshaw/=.
	rewrite /CshawIA/CbIA.
	replace (Xreal 0) with (Xsub (Xreal 0) (Xreal 0)) by
		by rewrite Xsub_split/Xadd/Xneg Ropp_0 Rplus_0_r.
	apply sub_correct_R; first exact: I00.
	by apply mul_correct_R; first exact: I00.
apply sub_correct_R; first by apply CbIA_crct.
by apply mul_correct_R; first by apply CbIA_crct.
Qed.

Lemma CshawIA_correct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (CshawIA pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::].
		by apply size0nil.
	rewrite /Cshaw /= /CshawIA/CbIA.
	apply sub_correct_R; first exact I00.
	by apply mul_correct_R; first exact I00.
rewrite /Cshaw/CshawIA.
apply sub_correct_R; first by apply CbIA_crct.
by apply mul_correct_R; first by apply CbIA_crct.
Qed.

Definition m_ i n := match n with
	| 0 => 0
	| S n' => (IZR (Z.of_nat (2 * i + 1)) / IZR (Z.of_nat (2 * n)))%R
end.

Definition mI_ i n := match n with
	| 0 => I0
	| S n' =>	div (I.fromZ (Z.of_nat (2* i + 1))) (I.fromZ (Z.of_nat (2 * n)))
end.

Lemma Zofnat_pos n: (0 < n)%nat -> (0 < Z.of_nat n)%Z.
Proof. by case: n. Qed.

Lemma mI_correct i n: m_ i n \contained_in mI_ i n.
Proof.
case: n => [ | n]; first exact I00.
apply /div_correct_R; try apply I.fromZ_correct.
rewrite /is_zero /Req_bool Rcompare_Gt => //.
by apply /IZR_lt /Zofnat_pos.
Qed.

Definition mu_ i n:= cos (m_ i n * PI).

Lemma IZR_Zof_nat n : IZR (Z.of_nat n) = n%:R.
Proof. by rewrite -INR_IZR_INZ natr_INR. Qed.

Lemma mu_cheby_nodes i n: (i < n)%nat -> mu_ i n = (cheby_nodes n)`_i.
Proof.
case: n => // n ineq.
rewrite /mu_/m_.
rewrite /cheby_nodes.
rewrite (nth_map 0%nat); last by rewrite size_iota.
f_equal; rewrite nth_iota => //.
rewrite add0n /Rdiv.
have -> : IZR (Z.of_nat (2 * i + 1)) = i.*2.+1%:R.
	by rewrite IZR_Zof_nat addn1 mul2n.
have -> : IZR (Z.of_nat (2 * n.+1)) = (n.+1).*2%:R.
	by rewrite IZR_Zof_nat mul2n.
lra.
Qed.

Definition piI := I.pi prec.
Definition muI_ i n:= I.cos prec (mul (mI_ i n) piI).

Lemma cos_correct_R x I:
	x \contained_in I -> (cos x) \contained_in (I.cos prec I).
Proof. by move => xcI; have /=:= I.cos_correct prec I (Xreal x) xcI. Qed.

Lemma atan_correct_R x I:
	x \contained_in I -> (atan x) \contained_in (I.atan prec I).
Proof. by move => xcI; have /=:= I.atan_correct prec I (Xreal x) xcI. Qed.

Lemma muI_correct i n: mu_ i n \contained_in muI_ i n.
Proof.
by apply /cos_correct_R /mul_correct_R; [apply mI_correct | apply I.pi_correct].
Qed.

Definition Icheby_nodes (n : nat) := [seq muI_ i n | i <- seq.iota 0%nat n].

Lemma size_Icheby_nodes n: size (Icheby_nodes n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma Icheby_nodes_correct n i:
	(cheby_nodes n)`_ i \contained_in nth I0 (Icheby_nodes n) i.
Proof.
case E: (i < n)%nat; last first.
	rewrite !nth_default; first exact: I00.
		by rewrite size_cheby_nodes leqNgt E.
	by rewrite size_Icheby_nodes leqNgt E.
rewrite (nth_map 0%nat); last by rewrite size_iota.
rewrite nth_iota => //; rewrite add0n.
rewrite -mu_cheby_nodes => //.
apply muI_correct.
Qed.

Definition FtoI (a: D) := (Interval.Interval_interval_float.Ibnd a a).

Lemma FtoI_correct a: (D2R a) \contained_in (FtoI a).
Proof. by rewrite /= /D2R; split; case E: (F.toX a) => //=; lra. Qed.

Definition Ischeby_nodes (a b : D) (n : nat) :=
	map (fun I => I.scale2 (add (add (mul (sub (FtoI b) (FtoI a)) I) (FtoI a)) (FtoI b)) (F.ZtoS (-1))) (Icheby_nodes n).

Lemma size_Ischeby_nodes a b n : size (Ischeby_nodes a b n) = n.
Proof. by rewrite size_map size_Icheby_nodes. Qed.

Lemma Ischeby_nodes_correct a b n i:
	(scheby_nodes (D2R a) (D2R b) n)`_ i \contained_in nth I0 (Ischeby_nodes a b n) i.
Proof.
case E: (i < n)%nat; last first.
	rewrite !nth_default; first exact: I00.
		by rewrite size_scheby_nodes leqNgt E.
	by rewrite /Ischeby_nodes size_map /Icheby_nodes size_map size_iota leqNgt E.
rewrite (nth_map I0); last by rewrite size_map size_iota.
rewrite (nth_map 0%R) /Rdiv; last by rewrite size_cheby_nodes.
have ->: (/ 2 = powerRZ 2 (-1)) %R by rewrite /powerRZ Pos2Nat.inj_1 pow_1.
apply scale2_correct_R.
apply add_correct_R; last exact: FtoI_correct.
apply add_correct_R; last exact: FtoI_correct.
apply mul_correct_R; last exact: Icheby_nodes_correct.
by apply sub_correct_R; apply: FtoI_correct.
Qed.

Section CMSin.
Context (a b : D).
Notation I := (Interval.Interval_interval_float.Ibnd a b).

Lemma sin_correct_R x I:
	x \contained_in I -> (sin x) \contained_in (I.sin prec I).
Proof. by move => xcI; have /=:= I.sin_correct prec I (Xreal x) xcI. Qed.

Definition value_list n:= map sin (scheby_nodes (D2R a) (D2R b) n).

Definition Ivalue_list n := map (I.sin prec) (Ischeby_nodes a b n).

Lemma Ivalue_list_correct n i: (value_list n)`_i \contained_in nth I0 (Ivalue_list n) i.
Proof.
case E: (i < n)%nat; last first.
	rewrite !nth_default; first exact: I00.
		by rewrite size_map size_scheby_nodes leqNgt E.
	by rewrite size_map size_Ischeby_nodes leqNgt E.
rewrite (nth_map I0); last by rewrite size_Ischeby_nodes.
rewrite (nth_map 0%R); last by rewrite size_scheby_nodes.
exact/sin_correct_R /Ischeby_nodes_correct.
Qed.

Definition c_ k n := Cshaw (value_list n) (mu_ k n).
Definition cI_ k n := CshawIA (Ivalue_list n) (muI_ k n).

Lemma cI_correct k n:
	c_ k n \contained_in cI_ k n.
Proof.
rewrite /c_ /cI_.
apply CshawIA_correct; first by move => i; apply Ivalue_list_correct.
	exact: muI_correct.
by rewrite size_map size_scheby_nodes size_map size_Ischeby_nodes.
Qed.

Fixpoint fact p := match p with
	| 0 => 1%positive
	| S n => ((Pos.of_nat (S n)) * (fact n))%positive
end.

Fixpoint gamma n x := match n with
		| 0 => - sin x
		| 0.+1 => -cos x
		| 0.+2 => sin x
		| 0.+3 => cos x
		| n.+4 => gamma n x
	end.

Fixpoint Gamma (n: nat) I := match n with
	| 0 => I.neg (I.sin prec I)
	| 0.+1 => I.neg (I.cos prec I)
	| 0.+2 => I.sin prec I
	| 0.+3 => I.cos prec I
	| n.+4 => Gamma n I
end.

Require Import Coquelicot.Coquelicot.
Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

Ltac toR := rewrite /GRing.add /GRing.opp /GRing.zero /GRing.mul /GRing.inv
  /GRing.one //=.

Lemma induc P:
	P 0%nat -> P 1%nat -> P 2%nat -> P 3%nat -> (forall n, P n -> P (n.+4)) -> forall n, P n.
Proof.
intros.
elim: n {-2}n (leqnn n) => [[]// | n Hn[|[|[|[|m]]]]// Hm].
by apply /X3 /Hn /leP; move/leP: Hm; lia.
Qed.

Lemma Derive_n_sin n x: 	sin^(n + 2) x = gamma n x.
Proof.
apply is_derive_n_unique.
suff ->: gamma n x = (if odd (n + 2) then (-1) ^ (n +2)./2 * cos x else (-1) ^ (n + 2)./2 * sin x) by apply coquelicot_compl.is_derive_n_sin.
move: n; apply induc => /=; try toR; try lra.
move => n; case: (odd (n+2)) => /= ->; toR.
	rewrite -!Rmult_assoc.
	have ->: (-1 * -1) = 1 by lra.
	by rewrite Rmult_1_l.
rewrite -!Rmult_assoc.
have ->: (-1 * -1) = 1 by lra.
by rewrite Rmult_1_l.
Qed.

Lemma Gamma_correct x n:
	x \contained_in I -> (gamma n x) \contained_in (Gamma n I).
Proof.
intros; move: n.
by apply induc; try apply neg_correct_R; try apply sin_correct_R; try apply cos_correct_R.
Qed.

Lemma lower_Gamma_correct x n:
	F.toX (I.lower (Gamma n I)) <> Xnan ->
	x \contained_in I -> 0 <= D2R (I.lower (Gamma n I)) -> 0 <= sin^(n + 2) x.
Proof.
intros.
rewrite Derive_n_sin.
have /=:= Gamma_correct n H0.
case: (Gamma n I) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX l) => //.
move => r ineq _ [ineq' _].
lra.
Qed.

Lemma upper_Gamma_correct x n:
	F.toX (I.upper (Gamma n I)) <> Xnan ->
	x \contained_in I -> D2R (I.upper (Gamma n I)) <= 0 -> sin^(n + 2) x <= 0.
Proof.
intros.
rewrite Derive_n_sin.
have /=:= Gamma_correct n H0.
case: (Gamma n I) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX u) => //.
move => r ineq _ [_ ineq'].
lra.
Qed.

Let diamI :=	match I with
	| Interval.Interval_interval_float.Inan => Interval.Interval_interval_float.Inan
	| Interval.Interval_interval_float.Ibnd l u =>
		(I.sub prec (Interval.Interval_interval_float.Ibnd u u) (Interval.Interval_interval_float.Ibnd l l))
end.

Let diamImul2:= I.scale diamI (F.ZtoS 1).
Let radI := I.scale diamI (F.ZtoS (-1)).
Let radIdiv2:= I.scale diamI (F.ZtoS (-2)).

(* Definition V n I := I.power_pos prec J (Pos.of_nat n). *)

Definition Delta (n: nat) I :=
	let J := I.lower_extent (I.abs (Gamma (n.+3) I)) in I.meet J (I.neg J).

End CMSin.
End stuff.

End MyClenshawStuff.
Module V := MyClenshawStuff  SFBI2.

Require Import QArith.
Check V.CshawIA.
Print s_float.
From Bignums Require Import BigQ.
Check bigQ.
Definition a := 1%bigQ.
Compute (2 * 4)%bigQ.
Print s_float.
Import Interval.Interval_specific_ops.
Definition D2Q (d: s_float bigZ bigZ) := match d with
	| Fnan => 0%bigQ
	| Float m e => (BigQ.Qz m * (2^([e]%bigZ)))%bigQ
end.

Locate PtoP.
Definition I1 := I.fromZ (-1)%Z.
Definition I2 := I.fromZ (2)%Z.
Definition I3 := I.fromZ (3)%Z.
Definition lst := [:: I1; I2].
Check I1.
Import Interval.Interval_interval_float.
Definition mapIQ I := match I with
	| Inan => Inan
	| Ibnd a b => Ibnd (D2Q a) (D2Q b)
end.
Compute (mapIQ (V.CshawIA (SFBI2.PtoP 5) [::I.fromZ(-1); (I.fromZ (2)%Z)] (I.fromZ (-1)))).
Print V.CbIA.
Compute V.Gamma (SFBI2.PtoP 15) 0%nat I1.
Compute (Cshaw [::ratz (-1); ratz (2)] (ratz (-1))).
Compute (V.piI (SFBI2.PtoP 100)).











