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

Definition I1 := I.fromZ 1.
Definition I2 := I.fromZ 2.

Fixpoint Iilist n (f g : ID -> ID) k :=
  if n is n.+1 then g k :: (Iilist n f g (f k))
  else [::].

Lemma size_Iilist n f g k : size (Iilist n f g k) = n.
Proof. by elim: n k => //= n IH k; rewrite IH. Qed.

Lemma nth_Iilist n u f g k i : (i < n)%nat ->
  nth u (Iilist n f g k) i = g (ssrnat.iter i f k).
Proof.
elim: n i k u => //= n IH [|i] //= k u L.
by rewrite IH // -iterSr.
Qed.

Definition m n i:=
  if n is 0 then 0 else (INR (i.*2.+1) / INR (n.*2))%R.

Definition mu n i:= cos (m n i * PI).

Lemma mu_cheby_nodes n i: (i < n)%nat -> mu n i = (cheby_nodes n)`_i.
Proof.
case: n => // n ineq.
rewrite /mu /m /cheby_nodes (nth_map 0%nat); last by rewrite size_iota.
congr cos; rewrite nth_iota //.
rewrite add0n /Rdiv !natr_INR.
lra.
Qed.

Definition Imlist n v2n := 
   Iilist n (fun x => add I2 x) (fun x => div x v2n) I1.

Lemma Iiter_add21 i :
  INR (i.*2.+1) \contained_in ssrnat.iter i [eta I.add prec I2] I1.
Proof.
have v1D : 1 \contained_in I1 by apply: I.fromZ_correct.
have v2D : 2 \contained_in I2 by apply: I.fromZ_correct.
elim: i => // j IH.
rewrite doubleS 2!S_INR Rplus_assoc Rplus_comm iterS.
by apply: add_correct.
Qed.

Lemma Imlist_correct n i u v2n :
   (i < n)%nat -> 
   (2 * INR n)%R \contained_in v2n ->
   m n i \contained_in nth u (Imlist n v2n) i.
Proof.
case: n => // n iLb v2nD; rewrite /Im nth_Iilist //.
apply: div_correct; first by apply: Iiter_add21.
  by rewrite -mul2n mult_INR.
rewrite /is_zero /Req_bool Rcompare_Gt => //.
by apply/(lt_INR 0)/ltP.
Qed.

Definition Ipi := I.pi prec.

Definition Icheby_nodes n v2n := 
   Iilist n (fun x => add I2 x) (fun x => I.cos prec (div (mul x Ipi) v2n)) I1.

Lemma Imulist_correct n u v2n i:
   (i < n)%nat -> 
   (2 * INR n)%R \contained_in v2n ->
    mu n i \contained_in nth u (Icheby_nodes n v2n) i.
Proof.
case: n =>  // n iLn v2nD.
rewrite nth_Iilist //.
apply: cos_correct => //.
have ->: (m n.+1 i * PI = INR i.*2.+1 * PI / INR n.+1.*2)%R.
  by rewrite /m /Rdiv; lra.
apply: div_correct.
- apply: mul_correct; first by apply: Iiter_add21.
  by apply: I.pi_correct.
- by rewrite -mul2n mult_INR.
rewrite /is_zero /Req_bool Rcompare_Gt => //.
by apply/(lt_INR 0)/ltP.
Qed.

Lemma size_Icheby_nodes n v2n: size (Icheby_nodes n v2n) = n.
Proof. by rewrite size_Iilist. Qed.

Lemma Icheby_nodes_correct n v2n i: 
   (2 * INR n)%R \contained_in v2n ->
   (cheby_nodes n)`_ i \contained_in nth I0 (Icheby_nodes n v2n) i.
Proof.
move=> v2nD.
have [nLi|iLn] := leqP n i.
	rewrite !nth_default; first by exact: I00.
		by rewrite size_cheby_nodes.
	by rewrite size_Icheby_nodes.
case: n iLn v2nD => [|n] // iLn v2nD.
rewrite (nth_map 0%nat); last by rewrite size_iota.
rewrite nth_iota => //; rewrite add0n.
have -> : (i.*2.+1%:R * PI / n.+1.*2%:R = i.*2.+1%:R / n.+1.*2%:R * PI)%R.
  by lra.
rewrite !natr_INR.
rewrite -[cos _]/(mu n.+1 i).
by apply: Imulist_correct.
Qed.

Definition Ischeby_nodes (a b : D) (n : nat) v2n :=
  [seq I.scale2 
         (add (add (mul (sub (FtoI b) (FtoI a)) i) (FtoI a)) (FtoI b)) 
         (F.ZtoS (-1)) | i <- Icheby_nodes n v2n].

Lemma size_Ischeby_nodes a b n v2n : size (Ischeby_nodes a b n v2n) = n.
Proof. by rewrite size_map size_Icheby_nodes. Qed.

Lemma Ischeby_nodes_correct a b n v2n i :
  (2 * INR n)%R \contained_in v2n ->
	(scheby_nodes (D2R a) (D2R b) n)`_ i \contained_in nth I0 (Ischeby_nodes a b n v2n) i.
Proof.
move=> v2nD.
have [nLi|iLn] := leqP n i.
	rewrite !nth_default; first exact: I00.
		by rewrite size_scheby_nodes.
	by rewrite size_map size_Icheby_nodes.
rewrite (nth_map I0); last by rewrite size_Icheby_nodes.
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

Definition value_list n:= [seq f i | i <- cheby_nodes n].

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

Lemma Tvalue_list_correct n i j: (j < n)%nat -> 
    (Tvalue_list n i)`_j = ('T_i).[(cheby_nodes n)`_j].
Proof.
move=> *; rewrite (nth_map 0%nat); last by rewrite size_iota.
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

Definition cheby_coefs n j := 
   ((if j == 0%nat then 1 else 2%R) / INR (n.+1))%R * \sum_(i < n.+1) (value_list n.+1)`_i * (Tvalue_list n.+1 j)`_i.

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

Definition cheby_coef_list n :=
  [seq cheby_coefs n.-1 i | i <- iota 0 n].

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

Definition Ivalue_list n v2n := [seq If i | i <- Icheby_nodes n v2n].

Lemma Ivalue_list_correct n v2n i: (i < n)%nat ->
  (2 * INR n)%R \contained_in v2n ->
	(f (cheby_nodes n)`_i) \contained_in nth I0 (Ivalue_list n v2n) i.
Proof.
move=> iLn v2nD.
rewrite (nth_map I0) ?size_Icheby_nodes //.
exact/env/Icheby_nodes_correct.
Qed.

Fixpoint IT3values l1 l2 l3 : seq ID :=
  if l1 is m::l1 then
    if l2 is v1::l2 then 
      if l3 is v2::l3 then sub (mul (scl2 m)  v2) v1 :: IT3values l1 l2 l3
      else [::]
    else [::]
  else [::].

Lemma size_IT3values l1 l2 l3  :
  size l2 = size l1 -> size l3 = size l1 ->
  size (IT3values l1 l2 l3) = size l1.
Proof.
elim: l1 l2 l3 => // a l1 IH [|b l2] [|c l3] //= [] H1 [] H2.
by rewrite IH.
Qed.

Lemma IT3values_correct l1 l2 l3 n m k  :
  size l2 = size l1 -> size l3 = size l1 ->
  (forall i, (i < size l1)%nat -> (cheby_nodes n)`_(m + i) \contained_in nth I0 l1 i) ->
  (forall i, (i < size l2)%nat -> (pT _ k).[(cheby_nodes n)`_(m + i)] \contained_in nth I0 l2 i) ->
  (forall i, (i < size l3)%nat -> (pT _ k.+1).[(cheby_nodes n)`_(m + i)] \contained_in nth I0 l3 i) ->
  (forall i, (i < size (IT3values l1 l2 l3))%nat -> 
      (pT _ k.+2).[(cheby_nodes n)`_(m + i)] \contained_in nth I0 (IT3values l1 l2 l3) i).
Proof.
elim: l1 l2 l3 m k => // a l1 IH  [|b l2] // [|c l3] //= m k [] Hs2 [] Hs3 Hl1 Hl2 Hl3 [|i] /= H.
  rewrite pTSS !hornerE.
  apply: sub_correct; last first.
    by have /= := Hl2 0%nat; rewrite addn0; apply.
  apply: mul_correct; last first.
    by have /= := Hl3 0%nat; rewrite addn0; apply.
  rewrite -mulr2n.
  apply: scl2_correct.
  by have /= := Hl1 0%nat; rewrite addn0; apply.
rewrite -addSnnS; apply: IH => //.
- by move=> i1 Hi1; rewrite addSnnS; apply: Hl1.
- by move=> i1 Hi1; rewrite addSnnS; apply: Hl2.
by move=> i1 Hi1; rewrite addSnnS; apply: Hl3.
Qed.

Fixpoint ITvalues_rec (n : nat) l1 l2 l3 : seq (seq ID) :=
  if n is n1.+1 then
    let l4 := IT3values l1 l2 l3 in
    l4 :: ITvalues_rec n1 l1 l3 l4
  else [::].

Lemma size_ITvalues_rec n l1 l2 l3  :
  size (ITvalues_rec n l1 l2 l3) = n.
Proof.
by elim: n l1 l2 l3 => //= n IH l1 l2 l3; rewrite IH.
Qed.

Lemma size_size_ITvalues_rec n l1 l2 l3 p :
  size l2 = size l1 -> size l3 = size l1 ->
  (p < n)%nat -> size (nth [::] (ITvalues_rec n l1 l2 l3) p) = size l1.
Proof.
elim: n l1 l2 l3 p => //= n IH l1 l2 l3 [H1 H2 _|p H1 H2 Hi] //=.
  by rewrite size_IT3values.
apply: IH => //.
by rewrite size_IT3values.
Qed.

Lemma ITvalues_rec_correct l1 l2 l3 n m k  :
  size l2 = size l1 -> size l3 = size l1 ->
  (forall i, (i < size l1)%nat -> (cheby_nodes n)`_i \contained_in nth I0 l1 i) ->
  (forall i, (i < size l2)%nat -> (pT _ k).[(cheby_nodes n)`_i] \contained_in nth I0 l2 i) ->
  (forall i, (i < size l3)%nat -> (pT _ k.+1).[(cheby_nodes n)`_i] \contained_in nth I0 l3 i) ->
  (forall i p,
      let l4 := nth [::] (ITvalues_rec m l1 l2 l3) p in
      (p < m)%nat -> 
      (i < size l1)%nat -> 
      (pT _(k.+2 + p)).[(cheby_nodes n)`_(i)] \contained_in nth I0 l4 i).
Proof.
elim: m k l1 l2 l3 => // m1 IH k l1 l2 l3 Hs2 Hs3 Hl1 Hl2 Hl3 i [/= _ H|p] /=.
  rewrite addn0 -{2}[i]add0n.
  apply: IT3values_correct => //.
  by rewrite size_IT3values.
move=> H11 H2; rewrite -addSnnS.
apply: IH => //.
- by rewrite size_IT3values.
move=> i1 Hi1.
rewrite -{2}[i1]add0n.
by apply: IT3values_correct.
Qed.

Definition ITvalues n l1 l2 :=
  if n is n1.+1 then 
     l1 ::
     if n1 is n2.+1 then
       l2 :: ITvalues_rec n2 l2 l1 l2
     else [::]
  else [::].

Lemma size_ITvalue n l1 l2 : size (ITvalues n l1 l2) = n.
Proof.
case: n => // [] [|n] //=.
by rewrite size_ITvalues_rec.
Qed.

Lemma size_size_ITvalues n l1 l2 p :
  size l1 = n -> size l2 = n ->
  (p < n)%nat -> size (nth [::] (ITvalues n l1 l2) p) = n.
Proof.
case: n => // [] [|n] //=; first by case: p.
case: p => //=.
case => [|p] Hl1 Hl2 Hp //.
by rewrite size_size_ITvalues_rec ?Hl2.
Qed.

Lemma ITvalues_correct n l1 l2 v2n p i :
      l1 = nseq n I1 ->
      (2 * INR n)%R \contained_in v2n ->
      l2 = Icheby_nodes n v2n ->
      (p < n)%nat -> 
      (i < n)%nat -> 
      (pT _(i)).[mu n p] \contained_in nth I0 (nth [::] (ITvalues n l1 l2) i) p.
Proof.
case: n => // [] [|n] // l1D v2nD l2D.
  case: p => // _; case: i => //.
  rewrite pT0 hornerE [ITvalues _ _ _]/= {2}/nth => _.
  rewrite l1D nth_nseq.
  by apply: I.fromZ_correct.
move=> Hp Hi.
rewrite [ITvalues _ _]/=.
case: i Hi => [|[|i]].
- rewrite [ITvalues _ _ _]/= {2}/nth pT0 hornerE.
  rewrite l1D (@nth_nseq _ _ (n.+2)) Hp =>  _.
  by apply: I.fromZ_correct.
- rewrite [ITvalues _ _ _]/= l2D {2}/nth pT1 hornerE => _.
  rewrite mu_cheby_nodes //.
  by apply: Icheby_nodes_correct.
move=> Hi.
rewrite [nth [::] _ _]/=.
rewrite -{1}[i.+1]add1n -addSn.
rewrite mu_cheby_nodes //.
apply: ITvalues_rec_correct => //.
- by rewrite l1D l2D size_Icheby_nodes /= size_nseq.
- by move=> j Hj; rewrite l2D; apply: Icheby_nodes_correct.
- move=> j Hj.
  rewrite l1D pT0 hornerE (@nth_nseq _ _ (n.+2)).
  move: Hj; rewrite l1D /= size_nseq => ->.
  by apply: I.fromZ_correct.
- move=> j Hj.
  rewrite pT1 hornerE l2D.
  by apply: Icheby_nodes_correct.
by rewrite l2D size_Icheby_nodes.
Qed.

(*
End Icheby_coefs.
End CPoly_interval.
End CPoly_interval.

Module V := CPoly_interval SFBI2.

Export V.

From Bignums Require Import BigZ.

Print SFBI2.precision.
Print Interval_bigint_carrier.BigIntRadix2.exponent_type.

Definition I1 := I.fromZ 1.
Definition I2 := I.fromZ 2.

Compute (fun x => ITvalues 10%bigZ x (I.fromZ (Z.of_nat x))) 3%N.

*)

Fixpoint Isum (F : ID -> ID -> ID) l1 l2 :=
  if l1 is a :: l1 then
  if l2 is b :: l2 then
     add (F a b) (Isum F l1 l2)  
  else I0
  else I0.

Lemma Isum_correct n g G (l1 l2 : seq R) Il1 Il2:
  (forall x y X Y, x \contained_in X -> y \contained_in Y
      -> g x y \contained_in G X Y) ->
  size l1 = n -> size l2 = n ->
  size Il1 = n -> size Il2 = n ->
  (forall i, (i < n)%nat -> nth 0 l1 i \contained_in nth I0 Il1 i) ->
  (forall i, (i < n)%nat -> nth 0 l2 i \contained_in nth I0 Il2 i) ->
  (\sum_(i < n) (g (nth 0 l1 i) (nth 0 l2 i)))
      \contained_in (Isum G Il1 Il2).
Proof.
move=> H; elim: l1 l2 Il1 Il2 n => 
   [|a l1 IH] [|b l2] [|A Il1] [|B Il2] [|n] //.
  move=> _ _ _ _ _ _ .
  by rewrite big_ord0; apply: I.fromZ_correct.
move=> [sl1] [sl2] [sIl1] [sIl2] Cl1 Cl2.
rewrite big_ord_recl /=.
apply: add_correct.
  apply: H; first by have /= := Cl1 0%nat; apply.
  by have /= := Cl2 0%nat; apply.
apply: IH => // i Hi; first by apply: (Cl1 i.+1).
by apply: (Cl2 i.+1).
Qed.

Definition Icheby_coefs vn vl1 vl2 :=
  let g x y := mul (If x) y in 
  let res := [seq div (mul I2 (Isum g vl1 i)) vn | i <- vl2] in
  if res is a :: res1 then (div a I2) :: res1
  else res.

Lemma size_Icheby_coefs_correct vn vl1 vl2 :
  size (Icheby_coefs vn vl1 vl2) = size vl2.
Proof.
rewrite /Icheby_coefs.
case E : [seq _ | _ <- _] => [|a l].
  by rewrite -E size_map.
apply: etrans (_ : _ = size (a :: l)) _ => //.
by rewrite -E size_map.
Qed.

Lemma Icheby_coefs_correct n vn v2n l1 vl1 vl2 j :
   l1 = nseq n.+1 I1 ->
   (2 * INR n.+1)%R \contained_in v2n ->
   INR n.+1 \contained_in vn ->
   vl1 = Icheby_nodes n.+1 v2n ->
   vl2 = ITvalues n.+1 l1 vl1 ->
   (j < n.+1)%nat ->
	dsprod_coef (interpolation f (cheby_nodes n.+1)) n j \contained_in 
             (nth I0 (Icheby_coefs vn vl1 vl2) j).
Proof.
move=> v1D v2nD vnD vl1D -> jL.
rewrite -dsprod_coefs.
rewrite /cheby_coefs /Icheby_coefs.
have := size_ITvalue n.+1 l1 vl1.
case E : ITvalues => [|a l] // _.
have -> : a = nth [::] (ITvalues n.+1 l1 vl1) 0 by rewrite E.
rewrite map_cons.
case: j jL => [|j] jL; set s := \sum_(i < _) _.
  rewrite eqxx {1}/nth.
  rewrite -[((1 / INR n.+1)%R * s)%RR]/((1 / INR n.+1 * s))%R.
  have -> : ((1 / INR n.+1) *  s = 
             ((2 * s) / INR n.+1) / 2)%R.
    by field; apply: (not_INR _ 0).
  apply: div_correct; last 2 first.
  - by apply: I.fromZ_correct.
  - by case: is_zero_spec=> //; lra.
  apply: div_correct => //; last first.
    by case: is_zero_spec=> // /(INR_eq _ 0).
  apply: mul_correct.
    by apply: I.fromZ_correct.
  have ->: s = 
      \sum_(i < n.+1)
        f ((cheby_nodes n.+1)`_i) * (Tvalue_list n.+1 0)`_i.
    apply: eq_bigr => i _; congr (_ * _).
    by rewrite (nth_map 0) // size_cheby_nodes.
  apply: (@Isum_correct n.+1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
  - move=> x y X Y Hx Hy; apply: mul_correct => //.
    by apply: env.
  - by rewrite size_cheby_nodes.
  - by rewrite size_map size_iota.
  - by rewrite vl1D size_Icheby_nodes.
  - rewrite size_size_ITvalues //.
      by rewrite v1D size_nseq.
    by rewrite vl1D size_Icheby_nodes.
  - move=> i Hi; rewrite vl1D.
    by apply: Icheby_nodes_correct.
  move=> i Hi.
  rewrite Tvalue_list_correct // -mu_cheby_nodes //.
  by apply: ITvalues_correct vl1D _ _.
set u := (_ * _)%RR.
have {u}->: (u = (2 * s) / INR n.+1)%R.
  rewrite /u; set v := INR _.
  toR; rewrite /u /=.
  by field; apply: (not_INR _ 0).
have -> : forall a b, nth I0 (a ::  b) j.+1 = nth I0 b j by [].
rewrite (nth_map [::]); last first.
  by rewrite -ltnS  -[(size l).+1]/(size (a :: l)) -E size_ITvalue.
apply: div_correct => //; last first.
  by case: is_zero_spec=> // /(INR_eq _ 0).
apply: mul_correct.
  by apply: I.fromZ_correct.
have ->: s = 
    \sum_(i < n.+1)
        f ((cheby_nodes n.+1)`_i) * (Tvalue_list n.+1 j.+1)`_i.
  apply: eq_bigr => i _; congr (_ * _).
  by rewrite (nth_map 0) // size_cheby_nodes.
apply: (@Isum_correct n.+1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
- move=> x y X Y Hx Hy; apply: mul_correct => //.
  by apply: env.
- by rewrite size_cheby_nodes.
- by rewrite size_map size_iota.
- by rewrite vl1D size_Icheby_nodes.
- rewrite -[nth [::] l j]/(nth [::] (a :: l) j.+1).
  rewrite -E size_size_ITvalues //.
    by rewrite v1D size_nseq.
  by rewrite vl1D size_Icheby_nodes.
- move=> i Hi; rewrite vl1D.
  by apply: Icheby_nodes_correct.
move=> i Hi.
rewrite Tvalue_list_correct // -mu_cheby_nodes //.
rewrite -[nth [::] l j]/(nth [::] (a :: l) j.+1) -E.
by apply: ITvalues_correct vl1D _ _.
Qed.

End Icheby_coefs.

Section scheby_coefs.

Context (a b : R).
Context (f: R -> R).

Definition svalue_list n:= [seq f i | i <- scheby_nodes a b n].

Lemma svalue_list_correct n i: (i < n)%nat ->
	(svalue_list n)`_i = f (scheby_nodes a b n)`_i.
Proof. by intros; rewrite (nth_map 0%RR); last rewrite size_scheby_nodes. Qed.

Definition scheby_coefs n j := 
   ((if j == 0%nat then 1 else 2) / INR (n.+1))%R * \sum_(i < n.+1) 
            (svalue_list n.+1)`_i * (Tvalue_list n.+1 j)`_i.

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

Definition scheby_coef_list n := [seq scheby_coefs n.-1 i | i <- seq.iota 0 n].

Definition CPolyab l := \sum_(i < (size l)) l`_i *: 'T^(a,b)_i.

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

Definition CM_correct L Delta f I := 
  forall l x, (forall i, l`_i \contained_in nth I0 L i) ->
 	x \contained_in I -> Rabs (f x - (CPolyab l).[x]) \contained_in Delta.

End scheby_coefs.

Section Ischeby_coefs.
Context (a b : D).
Context (f: R -> R).
Context (If: ID -> ID).
Hypothesis env: If \is_envelope_of f.

Definition Isvalue_list n v2n := [seq If i | i <- Ischeby_nodes a b n v2n].

Lemma Isvalue_list_correct n v2n i: (i < n)%nat ->
  (2 * INR n)%R \contained_in v2n ->
  (f (scheby_nodes (D2R a) (D2R b) n)`_i) \contained_in nth I0 (Isvalue_list n v2n) i.
Proof.
move=> iLn v2nD.
rewrite (nth_map I0) ?size_Ischeby_nodes //.
exact/env/Ischeby_nodes_correct.
Qed.

Lemma Ischeby_coefs_correct n vn v2n l1 vl1 vl2 vl3 j :
   (F.cmp a b = Xlt \/ F.cmp a b = Xgt) ->
   l1 = nseq n.+1 I1 ->
   (2 * INR n.+1)%R \contained_in v2n ->
   INR n.+1 \contained_in vn ->
   vl1 = Icheby_nodes n.+1 v2n ->
   vl2 = ITvalues n.+1 l1 vl1 ->
   vl3 = Ischeby_nodes a b n.+1 v2n ->
   (j < n.+1)%nat ->
	sdsprod_coef (D2R a) (D2R b)
    (interpolation f (scheby_nodes (D2R a) (D2R b) n.+1)) n j \contained_in 
             (nth I0 (Icheby_coefs If vn vl3 vl2) j).
Proof.
move=> DD v1D v2nD vnD vl1D -> -> jL.
rewrite -sdsprod_coefs //; last first.
  apply/eqP.
  move: DD; rewrite F.cmp_correct.
  rewrite /D2R  /Xcmp; do 2 case: F.toX => //=.
  - by case; discriminate.
  - by move=> r []; discriminate.
  - by move=> r []; discriminate.
  move=> r1 r2; case: Rcompare_spec; try lra.
  by move=> _ []; discriminate.
rewrite /scheby_coefs /Icheby_coefs.
have := size_ITvalue n.+1 l1 vl1.
case E : ITvalues => [|a1 l] // _.
have -> : a1 = nth [::] (ITvalues n.+1 l1 vl1) 0 by rewrite E.
rewrite map_cons.
case: j jL => [|j] jL; set s := \sum_(i < _) _.
  rewrite eqxx {1}/nth.
  rewrite -[((1 / INR n.+1)%R * s)%RR]/((1 / INR n.+1 * s))%R.
  have -> : ((1 / INR n.+1) *  s = 
             ((2 * s) / INR n.+1) / 2)%R.
    by field; apply: (not_INR _ 0).
  apply: div_correct; last 2 first.
  - by apply: I.fromZ_correct.
  - by case: is_zero_spec=> //; lra.
  apply: div_correct => //; last first.
    by case: is_zero_spec=> // /(INR_eq _ 0).
  apply: mul_correct.
    by apply: I.fromZ_correct.
  have ->: s = 
      \sum_(i < n.+1)
        f ((scheby_nodes (D2R a) (D2R b) n.+1)`_i) * (Tvalue_list n.+1 0)`_i.
    apply: eq_bigr => i _; congr (_ * _).
    by rewrite (nth_map 0) // size_scheby_nodes.
  apply: (@Isum_correct n.+1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
  - move=> x y X Y Hx Hy; apply: mul_correct => //.
    by apply: env.
  - by rewrite size_scheby_nodes.
  - by rewrite size_map size_iota.
  - by rewrite size_Ischeby_nodes.
  - rewrite size_size_ITvalues //.
      by rewrite v1D size_nseq.
    by rewrite vl1D size_Icheby_nodes.
  - move=> i Hi.
    by apply: Ischeby_nodes_correct.
  move=> i Hi.
  rewrite Tvalue_list_correct // -mu_cheby_nodes //.
  by apply: ITvalues_correct vl1D _ _.
set u := (_ * _)%RR.
have {u}->: (u = (2 * s) / INR n.+1)%R.
  rewrite /u; set v := INR _.
  toR; rewrite /u /=.
  by field; apply: (not_INR _ 0).
have -> : forall a b, nth I0 (a ::  b) j.+1 = nth I0 b j by [].
rewrite (nth_map [::]); last first.
  by rewrite -ltnS  -[(size l).+1]/(size (a1 :: l)) -E size_ITvalue.
apply: div_correct => //; last first.
  by case: is_zero_spec=> // /(INR_eq _ 0).
apply: mul_correct.
  by apply: I.fromZ_correct.
have ->: s = 
    \sum_(i < n.+1)
        f ((scheby_nodes (D2R a) (D2R b) n.+1)`_i) * (Tvalue_list n.+1 j.+1)`_i.
  apply: eq_bigr => i _; congr (_ * _).
  by rewrite (nth_map 0) // size_scheby_nodes.
apply: (@Isum_correct n.+1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
- move=> x y X Y Hx Hy; apply: mul_correct => //.
  by apply: env.
- by rewrite size_scheby_nodes.
- by rewrite size_map size_iota.
- by rewrite size_Ischeby_nodes.
- rewrite -[nth [::] l j]/(nth [::] (a1 :: l) j.+1).
  rewrite -E size_size_ITvalues //.
    by rewrite v1D size_nseq.
  by rewrite vl1D size_Icheby_nodes.
- move=> i Hi.
  by apply: Ischeby_nodes_correct.
move=> i Hi.
rewrite Tvalue_list_correct // -mu_cheby_nodes //.
rewrite -[nth [::] l j]/(nth [::] (a1 :: l) j.+1) -E.
by apply: ITvalues_correct vl1D _ _.
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
move=> HX.
rewrite /D2R.
case E': (bound n) (HX) => [ | /=l u]; first by rewrite F.nan_correct.
case E: (F.toX u) => [ | r] //= _.
have:= bound_correct n HX.
by rewrite E' /= E => [[_]].
Qed.

Lemma lower_Igamma_correct x n:
	F.toX (I.lower (Igamma n I)) <> Xnan ->
	x \contained_in I -> 0 <= D2R (I.lower (Igamma n I)) -> (0 <= sin^(n) x)%R.
Proof.
move=> HX HC HP.
have /=:= Igamma_correct n HC.
case: (Igamma n) HP HX; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX l) => //.
move => r ineq _ [ineq' _].
suff: (0 <= r)%R by lra.
by apply/RleP.
Qed.

(* The additional assumption should not be necessary, as the enclusures of the sin-
function should always be contained in [-1,1]. The Interval library does not contain such
a result, so I don't see an easy way to verify that it is true. *)
Lemma upper_Igamma_correct x n:
	F.toX (I.upper (Igamma n I)) <> Xnan ->
	x \contained_in I -> D2R (I.upper (Igamma n I)) <= 0 -> (sin^(n) x <= 0)%R.
Proof.
move=> HX HC HS.
have /=:= Igamma_correct n HC.
case: (Igamma n) HS HX; rewrite /D2R/proj_val; first by rewrite F.nan_correct.
move => l u /=.
case: (F.toX u) => //.
move => r ineq _ [_ ineq'].
suff: (r <= 0)%R by lra.
by apply/RleP.
Qed.

End CMSin.

End CPoly_interval.

End CPoly_interval.
Module V := CPoly_interval SFBI2.

Export V.

From Bignums Require Import BigZ.

Definition I1 := I.fromZ 1.
Definition I2 := I.fromZ 2.
Definition prec := 20%bigZ.
Definition n := 10%nat.
Definition vn := I.fromZ (Z.of_nat n.+1).
Definition v2n := I.fromZ (2 * Z.of_nat n.+1).
Definition a := I1.
Definition b := I2.
Definition l1 :=
  Eval vm_compute in  nseq n.+1 I1.
Definition vl1 := 
  Eval vm_compute in Icheby_nodes prec n.+1 v2n.
Definition vl2 :=
  Eval vm_compute in ITvalues prec n.+1 l1 vl1.
Definition vl3 := 
  Eval vm_compute in Ischeby_nodes prec (I.lower a) (I.upper b) n.+1 v2n.
Eval vm_compute in 
  Icheby_coefs prec (I.sin prec) vn vl3 vl2.
