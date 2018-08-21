From mathcomp Require Import all_ssreflect all_algebra.
Require Import Rstruct Reals Psatz under.
Require Import Poly_complements CPoly CPoly_exec CPoly_interpolation.
Require Import Coquelicot.Coquelicot.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Require Import ZArith.
From Interval Require Import Interval_specific_ops Interval_missing Interval_xreal.
From Interval Require Import Interval_definitions Interval_float_sig Interval_interval.
From Interval Require Import Interval_interval_float_full Interval_integral Interval_bisect.

Module SFBI2 := SpecificFloat Interval.Interval_bigint_carrier.BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

Module CPoly_interval (F : FloatOps with Definition even_radix := true).

Module I := FloatIntervalFull F.

Section CPoly_interval.
Notation mant := Interval.Interval_bigint_carrier.BigIntRadix2.smantissa_type.
Notation xpnt := Interval.Interval_bigint_carrier.BigIntRadix2.exponent_type.
Check I.fromZ 0.
Notation D := F.type.
Notation ID := (Interval_interval_float.f_interval F.type).
Notation "x '\contained_in' I" := (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation I0 := (I.fromZ 0).
Notation scl2 I := (I.scale2 I (F.ZtoS 1)).
Variable prec: F.precision.
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sub I J := (I.sub prec I J).
Notation div I J := (I.div prec I J).

Section Interval_lemmas.
Definition FtoI (a: D) := (Interval.Interval_interval_float.Ibnd a a).

Lemma FtoI_correct a: (D2R a) \contained_in (FtoI a).
Proof. by rewrite /= /D2R; split; case E: (F.toX a) => //=; lra. Qed.

Lemma I020:
	forall x, x \contained_in I0 -> x = 0%R.
Proof. move => x; rewrite /= F.fromZ_correct => /= [[]]; rewrite !/IZR; lra. Qed.

Lemma I00:
	0 \contained_in I0.
Proof. by rewrite /=F.fromZ_correct/=; lra. Qed.

Lemma mul_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (mul I J).
Proof. by apply I.mul_correct. Qed.

Lemma sub_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof. by apply I.sub_correct. Qed.

Lemma add_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof. by apply I.add_correct. Qed.

Lemma div_correct x y I J:
	x\contained_in I -> y \contained_in J -> is_zero y = false -> (x / y) \contained_in (div I J).
Proof.
intros.
have /=:= I.div_correct prec I J (Xreal x) (Xreal y).
rewrite /Xdiv' H1 /= => crct.
by apply crct.
Qed.

Lemma scl2_correct x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
intros.
suff -> :(Xreal (x *+ 2)) = (Xmul (Xreal x) (Xreal (bpow radix2 1))).
	by apply I.scale2_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma scale2_correct x z I:
	x \contained_in I -> (x * (powerRZ 2 z)) \contained_in (I.scale2 I (F.ZtoS z)).
Proof.
intros.
replace (Xreal (x * (powerRZ 2 z))) with (Xmul (Xreal x) (Xreal (bpow radix2 z))).
	by apply I.scale2_correct.
congr Xreal.
by rewrite bpow_powerRZ.
Qed.

Lemma neg_correct x I:
	x \contained_in I -> (-x) \contained_in (I.neg I).
Proof. by apply I.neg_correct. Qed.

Lemma stuff (p : {poly R}):
	(forall i : nat, p`_i \contained_in nth I0 [::] i) -> p = 0.
Proof.
move => prp.
apply polyP => i.
rewrite coef0.
apply I020.
move: (prp i).
by rewrite nth_default.
Qed.

Lemma sin_correct x J:
	x \contained_in J -> (sin x) \contained_in (I.sin prec J).
Proof. by apply I.sin_correct. Qed.

Lemma cos_correct x I:
	x \contained_in I -> (cos x) \contained_in (I.cos prec I).
Proof. by apply I.cos_correct. Qed.

Lemma atan_correct x I:
	x \contained_in I -> (atan x) \contained_in (I.atan prec I).
Proof. by apply I.atan_correct. Qed.

Lemma Zofnat_pos n: (0 < n)%nat -> (0 < Z.of_nat n)%Z.
Proof. by case: n. Qed.

Lemma IZR_Zof_nat n : IZR (Z.of_nat n) = n%:R.
Proof. by rewrite -INR_IZR_INZ natr_INR. Qed.
End Interval_lemmas.

Section ICshaw.

Fixpoint ICb q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := ICb q' x in
   let a1 := sub (add a (scl2 (mul (fst t) x))) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition ICshaw p x := sub (ICb p x).1 (mul (ICb p x).2 x).

Lemma ICb_crct (p: seq R) (pI: seq ID) (x: R) (I: ID):
	(forall i, (p`_i) \contained_in (nth I0 pI i)) -> x \contained_in I  -> size p = size pI ->
		(Cb p x).1 \contained_in (ICb pI I).1 /\ (Cb p x).2 \contained_in (ICb pI I).2.
Proof.
move => prp xJ.
elim: pI p prp => [[ | a p]// prp _ | J pI ih [ | a p]// prp eq].
	by split; apply I00.
rewrite /=.
case: (ih p) => // [i | | ih1 ih2 ].
		by apply (prp (S i)).
	by case: eq.
split => //.
apply sub_correct => //.
apply add_correct; first exact: (prp 0%nat).
by apply /scl2_correct /mul_correct.
Qed.

Lemma ICshaw_crct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (ICshaw pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::] by apply size0nil.
	rewrite /Cshaw/=.
	rewrite /ICshaw/ICb.
	replace (Xreal 0) with (Xsub (Xreal 0) (Xreal 0)) by
		by rewrite Xsub_split/Xadd/Xneg Ropp_0 Rplus_0_r.
	apply sub_correct; first exact: I00.
	by apply mul_correct; first exact: I00.
apply sub_correct; first by apply ICb_crct.
by apply mul_correct; first by apply ICb_crct.
Qed.

Lemma ICshaw_correct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	(forall i, p`_i \contained_in (nth I0 pI i)) -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (ICshaw pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::].
		by apply size0nil.
	rewrite /Cshaw /= /ICshaw/ICb.
	apply sub_correct; first exact I00.
	by apply mul_correct; first exact I00.
rewrite /Cshaw/ICshaw.
apply sub_correct; first by apply ICb_crct.
by apply mul_correct; first by apply ICb_crct.
Qed.
End ICshaw.

Section Icheby_nodes.
Definition m n i:= match n with
	| 0 => 0
	| S n' => (IZR (Z.of_nat (2 * i + 1)) / IZR (Z.of_nat (2 * n)))%R
end.

Definition mu n i:= cos (m n i * PI).

Lemma mu_cheby_nodes n i: (i < n)%nat -> mu n i = (cheby_nodes n)`_i.
Proof.
case: n => // n ineq.
rewrite /mu/m.
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

Definition Im n i:= match n with
	| 0 => I0
	| S n' =>	div (I.fromZ (Z.of_nat (2* i + 1))) (I.fromZ (Z.of_nat (2 * n)))
end.

Lemma Im_correct n i: m n i \contained_in Im n i.
Proof.
case: n => [ | n]; first by apply I00.
apply /div_correct; try apply I.fromZ_correct.
rewrite /is_zero /Req_bool Rcompare_Gt => //.
by apply /IZR_lt /Zofnat_pos.
Qed.

Definition Ipi := I.pi prec.
Definition Imu n i:= I.cos prec (mul (Im n i) Ipi).

Lemma Imu_correct n i: mu n i \contained_in Imu n i.
Proof.
by apply /cos_correct /mul_correct; [apply Im_correct | apply I.pi_correct].
Qed.

Definition Icheby_nodes (n : nat) := [seq Imu n i | i <- seq.iota 0%nat n].

Lemma size_Icheby_nodes n: size (Icheby_nodes n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma Icheby_nodes_correct n i: (cheby_nodes n)`_ i \contained_in nth I0 (Icheby_nodes n) i.
Proof.
case E: (i < n)%nat; last first.
	rewrite !nth_default; first exact: I00.
		by rewrite size_cheby_nodes leqNgt E.
	by rewrite size_Icheby_nodes leqNgt E.
rewrite (nth_map 0%nat); last by rewrite size_iota.
rewrite nth_iota => //; rewrite add0n.
rewrite -mu_cheby_nodes => //.
apply Imu_correct.
Qed.

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
apply /scale2_correct /add_correct; last exact: FtoI_correct.
apply add_correct; last exact: FtoI_correct.
apply mul_correct; last exact: Icheby_nodes_correct.
by apply sub_correct; apply: FtoI_correct.
Qed.
End Icheby_nodes.

Section cheby_coefs.
Context (f: R -> R).
Notation iota:= seq.iota.

Definition value_list n:= map f (cheby_nodes n).

Lemma value_list_correct n i: (i < n)%nat ->
	(value_list n)`_ i = f (cheby_nodes n)`_i.
Proof.
by intros; rewrite (nth_map 0%RR); last rewrite size_cheby_nodes.
Qed.

Fixpoint Tvalues (n : nat) (i : nat) (j: nat) {struct i} : R :=
  if i is i1.+1 then
    if i1 is i2.+1 then mu n j *+2 * Tvalues n i1 j - Tvalues n i2 j
    else mu n j
  else 1.

Lemma TvaluesSS n i j:
	(Tvalues n i.+2 j) = (mu n j *+2* Tvalues n i.+1 j - Tvalues n i j)%R.
Proof. done. Qed.

Lemma Tvalues_correct n i j: Tvalues n i j = (pT _ i).[mu n j].
Proof.
elim/induc2: i => [ | | i ih1 ih2]; first by rewrite pT0 /= hornerC.
	by rewrite pT1 hornerX.
rewrite pTSS TvaluesSS ih1 ih2.
by rewrite hornerD hornerN hornerM mulr2n hornerD hornerX.
Qed.

Definition Tvalue_list n j := map (Tvalues n j) (iota 0 n).

Lemma Tvalue_list_correct n i j: (j < n)%nat -> (Tvalue_list n i)`_j = ('T_i).[(cheby_nodes n)`_j].
Proof.
intros; rewrite (nth_map 0%nat); last by rewrite size_iota.
by rewrite nth_iota // Tvalues_correct -mu_cheby_nodes.
Qed.

Lemma dsprod_coef_P2CP l n:
	(size l <= n.+1)%nat -> CPoly (map (dsprod_coef (Poly l) n) (iota 0 n.+1)) = CPoly (P2CP l).
Proof.
move => ineq.
rewrite P2CP_spec; last by  rewrite unitfE; apply /eqP; rewrite natr_INR; toR; lra.
rewrite /CPoly size_map size_iota.
under eq_bigr ? rewrite (nth_map 0%nat); last by rewrite size_iota.
under eq_bigr ? rewrite nth_iota.
rewrite -dsprod_cheby_eq //.
by apply /leq_trans; first exact/ size_Poly.
Qed.

Definition cheby_coefs n j := ((if j == 0%nat then 1 else 2%R) / INR (n.+1))%R * \sum_(i < n.+1) (value_list n.+1)`_i * (Tvalue_list n.+1 j)`_i.

Lemma dsprod_coefs n j:
	cheby_coefs n j = dsprod_coef (interpolation f (cheby_nodes n.+1)) n j.
Proof.
intros.
rewrite dsprod_coef_interpolation //.
rewrite /cheby_coefs /value_list /Tvalue_list.
congr (_ * _) => //.
under [LHS] eq_bigr ? rewrite (nth_map 0%nat); last by rewrite size_iota.
under [LHS] eq_bigr ? rewrite Tvalues_correct nth_iota.
rewrite [RHS](big_nth 0%RR) big_mkord size_cheby_nodes.
apply eq_bigr => i _.
rewrite (nth_map 0%RR); last by rewrite size_cheby_nodes.
by congr (_ * _); last by rewrite mu_cheby_nodes // add0n.
Qed.

Definition cheby_coef_list n := match n with
	| 0 => [::]
	| n.+1 => map (cheby_coefs n) (iota 0 n.+1)
end.

Lemma cheby_coef_list_spec n: 
	CPoly (cheby_coef_list n) = interpolation f (cheby_nodes n).
Proof.
case: n => [ | n]; first by rewrite CPoly_nil.
intros; rewrite -[RHS]polyseqK.
rewrite -P2CP_spec; last by rewrite unitfE; apply /eqP; rewrite natr_INR; toR; lra.
rewrite -(@dsprod_coef_P2CP _ n); last by rewrite -{2}[n.+1](size_cheby_nodes) interpolation_size.
f_equal; apply (@eq_from_nth _ 0%RR) => [ | i]; first by rewrite !size_map.
rewrite size_map size_iota => ineq.
rewrite !(nth_map 0%nat); try by rewrite size_iota.
rewrite !nth_iota // dsprod_coefs //.
by f_equal; rewrite [RHS]polyseqK.
Qed.
End cheby_coefs.

Definition Ienv f F:=
	forall x I, x \contained_in I -> (f x) \contained_in (F I).
Notation "F \is_envelope_of f":= (Ienv f F) (at level 70).

Section Icheby_coefs.
Context (f: R -> R).
Context (If: ID -> ID).
Hypothesis env: If \is_envelope_of f.
Notation iota:= seq.iota.

Definition Ivalue_list n:= map If (Icheby_nodes n).

Lemma Ivalue_list_correct n i: (i < n)%nat ->
	(f (cheby_nodes n)`_i) \contained_in nth I0 (Ivalue_list n) i.
Proof.
intros.
rewrite (nth_map I0); last by rewrite size_map size_iota.
exact/env/Icheby_nodes_correct.
Qed.

Fixpoint ITvalues (n : nat) (i : nat) (j: nat) {struct i} : ID :=
  if i is i1.+1 then
    if i1 is i2.+1 then sub (mul (scl2 (Imu n j))  (ITvalues n i1 j)) (ITvalues n i2 j)
    else Imu n j
  else I.fromZ 1.

Lemma ITvaluesSS n i j:
	(ITvalues n i.+2 j) = sub (mul (scl2 (Imu n j))  (ITvalues n i.+1 j)) (ITvalues n i j).
Proof. done. Qed.

Lemma ITvalues_correct n i j: (pT _ i).[mu n j] \contained_in ITvalues n i j.
Proof.
rewrite -Tvalues_correct.
elim/ induc2: i => [ | | i ih1 ih2]; first by rewrite /= F.fromZ_correct; lra.
	by apply Imu_correct.
rewrite ITvaluesSS TvaluesSS.
apply sub_correct; last exact/ih1.
apply mul_correct; last exact/ih2.
exact/scl2_correct/Imu_correct.
Qed.

Definition ITvalue_list n j := map (ITvalues n j) (iota 0 n).

Lemma ITvalue_list_correct n i j: (j < n)%nat ->
	('T_i).[(cheby_nodes n)`_j] \contained_in nth I0 (ITvalue_list n i) j.
Proof.
intros.
rewrite -Tvalue_list_correct //.
rewrite !(nth_map 0%nat); try by rewrite size_iota.
rewrite Tvalues_correct nth_iota //.
exact/ITvalues_correct.
Qed.

Fixpoint Isum n (F: nat -> ID):= match n with
	| 0 => I0
	| S n' => add (Isum n' F) (F n')
end.

Lemma Isum_correct n A a:
	(forall i, (i < n)%nat -> a i \contained_in A i) -> (\sum_(i< n) a i) \contained_in (Isum n A).
Proof.
elim: n; intros.
	rewrite big1; last by case.
	by rewrite /Isum; apply I00.
rewrite big_ord_recr /=.
apply add_correct; last exact/H0.
apply/H => i ineq.
exact/H0/leqW.
Qed.

Definition Icheby_coefs n j := mul (div (if j == 0%nat then I.fromZ 1 else I.fromZ 2) (I.fromZ (Z.of_nat (n.+1)))) (Isum n.+1 (fun i => mul (nth I0 (Ivalue_list n.+1) i) (nth I0 (ITvalue_list n.+1 j) i))).

Lemma Icheby_coefs_correct n j:
	dsprod_coef (interpolation f (cheby_nodes n.+1)) n j \contained_in (Icheby_coefs n j).
Proof.
rewrite -dsprod_coefs.
apply mul_correct.
	apply div_correct; first by case: ifP => _; apply I.fromZ_correct.
		by rewrite INR_IZR_INZ; apply I.fromZ_correct.
	rewrite /is_zero.
	apply Req_bool_false.
	have ->: (0 = INR 0)%R by rewrite /=.
	by move => /INR_eq eq.
apply (@Isum_correct _ (fun i : nat => mul (nth I0 (Ivalue_list n.+1) i) (nth I0 (ITvalue_list n.+1 j) i)) (fun i => (value_list f n.+1)`_i * (Tvalue_list n.+1 j)`_i)).
move => i ineq.
apply mul_correct.
	rewrite value_list_correct //.
	by apply Ivalue_list_correct.
rewrite Tvalue_list_correct //.
exact/ ITvalue_list_correct.
Qed.

Definition Icheby_coef_list n := match n with
	| 0 => [::]
	| n.+1 => map (Icheby_coefs n) (iota 0 n.+1)
end.

Lemma Icheby_coef_list_correct n i:
	(cheby_coef_list f n)`_i  \contained_in (nth I0 (Icheby_coef_list n) i).
Proof.
case: n => [ | n]; first by rewrite !nth_default //; apply I00.
case E: (i < n.+1)%nat; last first.
	by rewrite !nth_default; first exact I00; rewrite size_map size_iota leqNgt E.
rewrite !(nth_map 0%nat); try by rewrite size_iota.
rewrite nth_iota //dsprod_coefs.
exact/Icheby_coefs_correct.
Qed.
End Icheby_coefs.

Section scheby_coefs.
Context (a b : R).
Context (f: R -> R).

Definition svalue_list n:= map f (scheby_nodes a b n).

Lemma svalue_list_correct n i: (i < n)%nat ->
	(svalue_list n)`_i = f (scheby_nodes a b n)`_i.
Proof. by intros; rewrite (nth_map 0%RR); last rewrite size_scheby_nodes. Qed.

Definition scheby_coefs n j := ((if j == 0%nat then 1 else 2) / INR (n.+1))%R * \sum_(i < n.+1) (svalue_list n.+1)`_i * (Tvalue_list n.+1 j)`_i.

Lemma sdsprod_coefs n j:
	a != b -> scheby_coefs n j = sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n j.
Proof.
intros.
rewrite sdsprod_coef_interpolation_pT //.
rewrite /scheby_coefs /svalue_list /Tvalue_list.
congr (_ * _) => //.
under [LHS] eq_bigr ? rewrite (nth_map 0%nat); last by rewrite size_iota.
under [LHS] eq_bigr ? rewrite Tvalues_correct nth_iota.
apply eq_bigr => i _.
rewrite (nth_map 0%RR); last by rewrite size_scheby_nodes.
congr (_ * _); last by rewrite mu_cheby_nodes // add0n.
by rewrite /scheby_nodes (nth_map 0%RR) // size_cheby_nodes.
Qed.

Definition scheby_coef_list n := match n with
	| 0 => [::]
	| n.+1 => map (scheby_coefs n) (seq.iota 0 n.+1)
end.

Definition CPolyab l := \sum_(i < (size l)) l`_i *: 'T^(a,b)_i.

Axiom foo : forall A, A.

Lemma scheby_coef_list_spec n: b != a ->
	CPolyab (scheby_coef_list n) = interpolation f (scheby_nodes a b n).
Proof.
intros.
case: n => [ | n]; first by rewrite /CPolyab /= big_ord0.
rewrite [RHS](@sdsprod_cheby_eq a b n); [ | | ]; last first.
- by apply /leq_trans; first exact/interpolation_size; rewrite size_scheby_nodes.
- by apply /eqP => eq; move /eqP: H; rewrite eq.
rewrite /CPolyab size_map size_iota.
suff eq: forall i, (i < n.+1)%nat -> (scheby_coef_list n.+1)`_i = sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n i.
	by under eq_bigr ? rewrite eq.
move => i ineq.
rewrite (nth_map 0%nat); last by rewrite size_iota.
rewrite nth_iota //.
apply sdsprod_coefs.
by apply /eqP => eq; move /eqP: H; rewrite eq.
Qed.

Definition CM_correct L Delta f I := forall l x, (forall i, l`_i \contained_in nth I0 L i) ->
	x \contained_in I -> Rabs (f x - (CPolyab l).[x]) \contained_in Delta.
End scheby_coefs.

Section Ischeby_coefs.
Context (a b : D).
Context (f: R -> R).
Context (If: ID -> ID).
Hypothesis env: If \is_envelope_of f.
Notation iota:= seq.iota.

Definition Isvalue_list n := map If (Ischeby_nodes a b n).

Lemma Isvalue_list_correct n i:
	(svalue_list (D2R a) (D2R b) f n)`_i \contained_in (nth I0 (Isvalue_list n) i).
Proof.
case E: (i < n)%nat; last first.
	rewrite !nth_default; first exact/I00; rewrite size_map.
		by rewrite size_scheby_nodes leqNgt E.
	by rewrite size_Ischeby_nodes leqNgt E.
rewrite svalue_list_correct // (nth_map I0); last by rewrite size_Ischeby_nodes.
exact /env/Ischeby_nodes_correct.
Qed.

Definition Ischeby_coefs n j := mul (div (if j == 0%nat then I.fromZ 1 else I.fromZ 2) (I.fromZ (Z.of_nat (n.+1)))) (Isum n.+1 (fun i => mul (nth I0 (Isvalue_list n.+1) i) (nth I0 (ITvalue_list n.+1 j) i))).

Lemma Ischeby_coefs_correct n j: (D2R a) != (D2R b) ->
	sdsprod_coef (D2R a) (D2R b) (interpolation f (scheby_nodes (D2R a) (D2R b) n.+1)) n j \contained_in (Ischeby_coefs n j).
Proof.
intros.
rewrite -sdsprod_coefs //.
apply mul_correct.
	apply div_correct; first by case: ifP => _; apply I.fromZ_correct.
		by rewrite INR_IZR_INZ; apply I.fromZ_correct.
	rewrite /is_zero.
	apply Req_bool_false.
	have ->: (0 = INR 0)%R by rewrite /=.
	by move => /INR_eq eq.
apply (@Isum_correct _ (fun i : nat => mul (nth I0 (Isvalue_list n.+1) i) (nth I0 (ITvalue_list n.+1 j) i)) (fun i => (svalue_list (D2R a) (D2R b) f n.+1)`_i * (Tvalue_list n.+1 j)`_i)).
move => i ineq.
apply mul_correct; first by apply Isvalue_list_correct.
rewrite Tvalue_list_correct //.
exact/ ITvalue_list_correct.
Qed.

Definition Ischeby_coef_list n := match n with
	| 0 => [::]
	| n.+1 => map (Ischeby_coefs n) (iota 0 n.+1)
end.

Lemma Ischeby_coef_list_correct n i: D2R a != D2R b ->
	(scheby_coef_list (D2R a) (D2R b) f n)`_i  \contained_in (nth I0 (Ischeby_coef_list n) i).
Proof.
intros.
case: n => [ | n]; first by rewrite !nth_default //; apply I00.
case E: (i < n.+1)%nat; last first.
	by rewrite !nth_default; first exact I00; rewrite size_map size_iota leqNgt E.
rewrite !(nth_map 0%nat); try by rewrite size_iota.
rewrite nth_iota //sdsprod_coefs //.
exact/Ischeby_coefs_correct.
Qed.

End Ischeby_coefs.

Section CMSin.
Context (a b : D) (annan: F.toX a <> Xnan) (bnnan: F.toX b <> Xnan).
Notation I := (Interval.Interval_interval_float.Ibnd a b).
Context (f: R -> R).

Lemma ineq_cntd x:
	x \contained_in I <-> (D2R a <= x <= D2R b)%R.
Proof.
rewrite /contains /I.convert /D2R.
case: (F.toX a) annan => [ | ar]// _.
by case: (F.toX b) bnnan => [ | br] //= _.
Qed.

Notation Isin := (I.sin prec).
Lemma env: Isin \is_envelope_of sin.
Proof. exact/ sin_correct. Qed.

Definition Ischeby_coef_list_sin n:= Ischeby_coef_list a b Isin n.

Fixpoint fact p := match p with
	| 0 => 1%positive
	| S n => ((Pos.of_nat (S n)) * (fact n))%positive
end.

Fixpoint gamma n x := match n with
		| 0 => sin x
		| 0.+1 => cos x
		| 0.+2 => - sin x
		| 0.+3 => - cos x
		| n.+4 => gamma n x
	end.

Fixpoint Igamma (n: nat) J := match n with
	| 0 => (I.sin prec J)
	| 0.+1 => (I.cos prec J)
	| 0.+2 => I.neg (I.sin prec J)
	| 0.+3 => I.neg (I.cos prec J)
	| n.+4 => Igamma n J
end.

Lemma induc4 P:
	P 0%nat -> P 1%nat -> P 2%nat -> P 3%nat -> (forall n, P n -> P (n.+4)) -> forall n, P n.
Proof.
intros.
elim: n {-2}n (leqnn n) => [[]// | n Hn[|[|[|[|m]]]]// Hm].
by apply /X3 /Hn /leP; move/leP: Hm; lia.
Qed.

Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

Lemma gamma_correct n x: 	sin^(n) x = gamma n x.
Proof.
apply is_derive_n_unique.
suff ->: gamma n x = (if odd n then ((-1) ^ n./2 * cos x)%R else ((-1) ^ n./2 * sin x))%R by apply coquelicot_compl.is_derive_n_sin.
move: n; apply induc4 => /=; try toR; try lra.
move => n; case: (odd n) => /= ->; toR.
	rewrite -!Rmult_assoc.
	have ->: ((-1 * -1) = 1)%R by lra.
	by rewrite Rmult_1_l.
rewrite -!Rmult_assoc.
have ->: ((-1 * -1) = 1)%R by lra.
by rewrite Rmult_1_l.
Qed.

Lemma Igamma_correct n:
	(Igamma n) \is_envelope_of (sin^(n)).
Proof.
move => x I xI; rewrite gamma_correct /Igamma /gamma.
by elim/induc4: n; try apply/neg_correct; try exact /sin_correct; try exact/cos_correct.
Qed.

Definition bound n := I.abs (Igamma n.+1 I).

Lemma Iabs_correct x J:
	x \contained_in J -> Rabs x \contained_in (I.abs J).
Proof. by apply I.abs_correct. Qed.

Lemma bound_correct x n: x \contained_in I ->
	Rabs (sin^(n.+1) x) \contained_in (bound n).
Proof. by intros; apply/Iabs_correct/Igamma_correct. Qed.

Lemma upper_bound_correct x n: x \contained_in I ->
	F.toX (I.upper (bound n)) <> Xnan -> (Rabs (sin^(n.+1) x) <= D2R (I.upper (bound n)))%R.
Proof.
intros.
rewrite /D2R.
case E': (bound n) H0 => [ | /=l u]; first by rewrite F.nan_correct.
case E: (F.toX u) => [ | r] //= _.
have:= bound_correct n H.
by rewrite E' /= E => [[_]].
Qed.

Lemma lower_Igamma_correct x n:
	F.toX (I.lower (Igamma n I)) <> Xnan ->
	x \contained_in I -> 0 <= D2R (I.lower (Igamma n I)) -> (0 <= sin^(n) x)%R.
Proof.
intros.
have /=:= Igamma_correct n H0.
case: (Igamma n) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX l) => //.
move => r ineq _ [ineq' _].
have: (0 <= r) %R.
	move/eqP: ineq.
	rewrite /Num.Def.ler /= /GRing.zero/= /Rleb.
	by case: (Rle_dec 0 r).
lra.
Qed.

(* The additional assumption should not be necessary, as the enclusures of the sin-
function should always be contained in [-1,1]. The Interval library does not contain such
a result, so I don't see an easy way to verify that it is true. *)
Lemma upper_Igamma_correct x n:
	F.toX (I.upper (Igamma n I)) <> Xnan ->
	x \contained_in I -> D2R (I.upper (Igamma n I)) <= 0 -> (sin^(n) x <= 0)%R.
Proof.
intros.
have /=:= Igamma_correct n H0.
case: (Igamma n) H1 H; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX u) => //.
move => r ineq _ [_ ineq'].
have: (r <= 0) %R.
	move/eqP: ineq.
	rewrite /Num.Def.ler /= /GRing.zero/= /Rleb.
	by case: (Rle_dec r 0).
lra.
Qed.

End CMSin.

End CPoly_interval.