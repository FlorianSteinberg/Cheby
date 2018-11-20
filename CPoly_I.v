From mathcomp Require Import all_ssreflect all_algebra.
Require Import String Rstruct Reals Psatz under.
Require Import Poly_complements CPoly CPoly_exec CPoly_interpolation.
Require Import Coquelicot.Coquelicot.
Require Import sine_interpolation cos_interpolation exp_interpolation.
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

Lemma I020 x : x \contained_in I0 -> x = 0%R.
Proof. rewrite /= F.fromZ_correct => /= [[]]; rewrite !/IZR; lra. Qed.

Lemma I00: 0 \contained_in I0.
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
	x \contained_in I -> y \contained_in J -> is_zero y = false -> (x / y) \contained_in (div I J).
Proof.
move=> xI yJ yZ.
have /= := I.div_correct prec I J (Xreal x) (Xreal y) xI yJ.
by rewrite /Xdiv' yZ.
Qed.

Lemma scl2_correct x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
move=> xI.
suff -> :(Xreal (x *+ 2)) = (Xmul (Xreal x) (Xreal (bpow radix2 1))).
	by apply I.scale2_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma scale2_correct x z I:
	x \contained_in I -> (x * (powerRZ 2 z)) \contained_in (I.scale2 I (F.ZtoS z)).
Proof.
move=> xI.
rewrite (_ : Xreal (x * (powerRZ 2 z)) = Xmul (Xreal x) (Xreal (bpow radix2 z))).
	by apply I.scale2_correct.
congr Xreal.
by rewrite bpow_powerRZ.
Qed.

Lemma neg_correct x I:
	x \contained_in I -> (-x) \contained_in (I.neg I).
Proof. by apply I.neg_correct. Qed.

Lemma abs_correct x I:
	x \contained_in I -> Rabs x \contained_in (I.abs I).
Proof. by apply I.abs_correct. Qed.

Lemma power_pos_correct x I (n : nat) : 
  (0 < n)%nat ->
  x \contained_in I -> (x ^ n) \contained_in I.power_pos prec I (Pos.of_nat n).
Proof.
move=> nP.
have := I.power_pos_correct prec (Pos.of_nat n) I (Xreal x).
rewrite /= /I.extension /= Nat2Pos.id //.
by case: n nP.
Qed.

Lemma sin_correct x J:
	x \contained_in J -> (sin x) \contained_in (I.sin prec J).
Proof. by apply I.sin_correct. Qed.

Lemma cos_correct x I:
	x \contained_in I -> (cos x) \contained_in (I.cos prec I).
Proof. by apply I.cos_correct. Qed.

Lemma exp_correct x I:
	x \contained_in I -> (exp x) \contained_in (I.exp prec I).
Proof. by apply I.exp_correct. Qed.

Lemma atan_correct x I:
	x \contained_in I -> (atan x) \contained_in (I.atan prec I).
Proof. by apply I.atan_correct. Qed.

End Interval_lemmas.

(*****************************************************************************)
(* Clenshaw algorithm on [-1; 1] for interval arithmetic                     *)
(*****************************************************************************)

Section ICshaw.

Fixpoint ICb q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := ICb q' x in
   let a1 := sub (add a (scl2 (mul (fst t) x))) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition ICshaw p x := 
  let: (i1, i2) := ICb p x in sub i1 (mul i2 x).

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
have := ICb_crct prp xJ eq.
rewrite /Cshaw/ICshaw; case: ICb => i j [H1 H2].
apply sub_correct => //.
by apply mul_correct.
Qed.
End ICshaw.

(*****************************************************************************)
(* Clenshaw algorithm on [a; b] for interval arithmetic                      *)
(*****************************************************************************)

Section IsCshaw.

Definition IsCshaw a b p x := 
  let x1 := (div (sub (sub (scl2 x) b) a) (sub b a)) in
  ICshaw p x1.

Lemma IsCshaw_correct n (p: seq R) (P: seq ID) (x a b : R) (X A B : ID) :
  a != b -> size p = n -> size P = n ->
	(forall i, p`_i \contained_in (nth I0 P i)) -> 
  x \contained_in X -> 
  a \contained_in A -> 
  b \contained_in B -> 
		(\sum_(i < n) p`_ i *: 'T^(a,b)_i).[x] \contained_in IsCshaw A B P X.
Proof.
move=> aDb Sp SP IP IX IA IB.
rewrite horner_sum.
have -> : \sum_(i < n) (p`_i *: 'T^(a,b)_i).[x] =
          \sum_(i < n) p`_i * ('T_i).[(Tab a b).[x]].
  apply: eq_bigr => i _.
  by rewrite /pTab !hornerE horner_comp !hornerE.
have -> : \sum_(i < n) p`_i * ('T_i).[(Tab a b).[x]] =
           (\sum_(i < n) p`_i *: 'T_i).[(Tab a b).[x]].
  by rewrite horner_sum; apply: eq_bigr => i _; rewrite !hornerE.
rewrite -Sp -Cshaw_spec.
apply: ICshaw_correct; rewrite ?SP //.
rewrite !hornerE.
toR;  rewrite /Rinvx ifT; last first.
  by apply/eqP; move/eqP: aDb; lra.
rewrite (_ : _ + _ = (2 * x - b - a) / (b - a))%R; last first.
  by field; move/eqP: aDb; lra.
apply: div_correct.
- apply: sub_correct => //.
  apply: sub_correct => //.
  rewrite (_ : 2 * x = x *+ 2)%R.
    by apply: scl2_correct.
  by rewrite mulr2n; toR; lra.
- by apply: sub_correct.
rewrite /is_zero; case: Req_bool_spec => //.
by move/eqP: aDb; lra.
Qed.

End IsCshaw.

(*****************************************************************************)
(* Chebyshev nodes on [-1; 1] : Icheby_nodes                                 *)
(* Chebyshev nodes on [ a; b] : Ischeby_nodes                                *)
(*****************************************************************************)


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

(*****************************************************************************)
(* Chebyshev coefficient on [-1; 1] for real numbers                         *)
(*****************************************************************************)

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


(*****************************************************************************)
(* Chebyshev coefficient on [-1; 1] for interval arithmetic                  *)
(*****************************************************************************)

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

Lemma size_Icheby_coefs vn vl1 vl2 :
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

(*****************************************************************************)
(* Chebyshev coefficient on [a; b] for real numbers                          *)
(*****************************************************************************)

Section scheby_coefs.

Context (a b : R).
Context (f : R -> R).

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

Lemma size_scheby_coef_list n :
  size (scheby_coef_list n) = n.
Proof. by rewrite size_map size_iota. Qed.

Lemma scheby_coef_list_spec n: b != a ->
	CPolyab a b (scheby_coef_list n) = interpolation f (scheby_nodes a b n).
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

End scheby_coefs.

(*****************************************************************************)
(* Chebyshev coefficient on [a; b] for interval arithmetic                   *)
(*****************************************************************************)

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

Record cms := CMS { 
  P : seq ID; 
  Delta : ID
 }.

Definition cms_correct n a b f (c : cms) :=
  let:  CMS P Delta  := c in 
  size P = n.+1 /\
  exists p : seq R, 
   [/\ size p = n.+1, 
       forall i, p`_i \contained_in nth I0 P i &
     forall x, x \contained_in I.bnd a b ->
     exists d : R,
       d \contained_in Delta /\ 
       f x = ((CPolyab (D2R a) (D2R b) p).[x] + d)%R].

Lemma cms_correct_eval n a b f c x X :
  let:  CMS P Delta  := c in 
  F.cmp a b = Xlt ->
  cms_correct n a b f c -> 
  (x \contained_in X) -> (I.subset X (I.bnd a b)) ->
  f x \contained_in add (IsCshaw (I.bnd a a) (I.bnd b b) P X) Delta.
Proof.
case: c => P Delta aLb; case => SP [p [Sp pIP fE]] xIX XS.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have [] := fE x.
  have := subset_contains _ _ (I.subset_correct _ _ XS).
  by apply.
move=> y [Hy ->].
apply: add_correct => //.
apply: IsCshaw_correct => //.
- by rewrite SP.
- by rewrite /D2R /=; case: F.toX  => //= r; lra.
by rewrite /D2R /=; case: F.toX  => //= r; lra.
Qed.

Lemma cms_correct_ext n a b f g c :
  (forall x, x \contained_in I.bnd a b -> f x = g x) ->
  cms_correct n a b g c ->  cms_correct n a b f c.
Proof.
case: c=> P Delta H [SP [p [H1p H2p H3p]]].
split => //.
exists p; split => // x Hx.
have [d [Hd HHd]] := H3p x Hx; exists d; split => //.
by rewrite H.
Qed.

(*****************************************************************************)
(* Constant Chebyshev model                                                  *)
(*****************************************************************************)

Definition const_cms n x := CMS (x :: nseq n I0) I0.

Lemma const_cms_correct n a b x X :
   x \contained_in X ->
   cms_correct n a b (fun _ => x) (const_cms n X).
Proof.
split; first by rewrite /= size_nseq.
exists (x :: nseq n 0); split => //.
- by rewrite /= size_nseq.
- move=> [|i] /=.
    by rewrite /D2R; case: F.toX => //= r; lra.
  by rewrite !nth_nseq; case: leqP => _; apply: I.fromZ_correct.
move=> y Hy; exists 0; split; first by apply: I.fromZ_correct.
rewrite /CPolyab /= big_ord_recl big1 => [|i Hi] /=.
  by rewrite !hornerE horner_comp pT0 hornerE mulr1.
by rewrite nth_nseq if_same scale0r.
Qed.

Definition constZ_cms n z := const_cms n (I.fromZ z).

Lemma constZ_cms_correct n a b z :
   cms_correct n a b (fun _ => (IZR z)) (constZ_cms n z).
Proof. by apply/const_cms_correct/I.fromZ_correct. Qed.


(*****************************************************************************)
(* Variable Chebyshev model                                                  *)
(*****************************************************************************)

Definition var_cms a b n := 
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
   CMS (I.scale2 (add Ia Ib) (F.ZtoS (-1)) ::
        I.scale2 (sub Ib Ia) (F.ZtoS (-1)):: nseq n.-1 I0) I0.

Lemma var_cms_correct n a b :
   F.cmp a b = Xlt ->
   cms_correct n.+1 a b (fun x => x) (var_cms a b n.+1).
Proof.
move=> aLb.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
split; first by rewrite /= size_nseq.
have F x : (x / 2 = x * powerRZ 2 (-1))%R.
  by rewrite /=; field.
exists ((D2R a + D2R b) / 2 :: (D2R b - D2R a) / 2 :: nseq n 0)%R; split => //.
- by rewrite /= size_nseq.
- move=> [|[|i]].
  - rewrite F. 
    by apply/scale2_correct/add_correct;
       rewrite /D2R /=; case: F.toX  => //= r; lra.
  - rewrite !F.
    by apply/scale2_correct/sub_correct;
       rewrite /D2R /=; case: F.toX  => //= r; lra.
  rewrite [_ `_ _]nth_nseq [nth _ _ _]nth_nseq !if_same.
  by apply: (I.fromZ_correct 0).
move=> y Hy; exists 0; split; first by apply: I.fromZ_correct.
rewrite /CPolyab /= !big_ord_recl big1 => [|i Hi] /=.
  rewrite !hornerE !horner_comp pT0 pT1 !hornerE /=.
  toR; rewrite /Rinvx ifT; last by apply/eqP; have/eqP:= F2; lra.
  by field; have/eqP:= F2; lra.
by rewrite nth_nseq if_same scale0r.
Qed.

(*****************************************************************************)
(* Opposite Chebyshev model                                                  *)
(*****************************************************************************)

Definition opp_cms (c : cms) :=
  let: CMS P Delta := c in
  CMS [seq I.neg i | i <- P] (I.neg Delta).

Lemma opp_cms_correct n a b c f :
   cms_correct n a b f c -> 
   cms_correct n a b (fun x => -(f x))%R (opp_cms c).
Proof.
case: c => [P Delta] [Sp [p [H1p H2p H3p]]].
split; first by rewrite size_map.
exists [seq - i | i <- p]; split; first by rewrite size_map.
  move=> i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite !nth_default ?(size_map, Sp, H1p) //.
    by apply: I.fromZ_correct.
  rewrite (nth_map I0) ?Sp // ?(nth_map 0%R) ?H1p //.
  by apply: neg_correct.
move=> x /H3p [d [H1d H2d]]; exists (- d); split => //.
  by apply: neg_correct.
by rewrite CPolyabN H2d !hornerE; toR; lra.
Qed.


(*****************************************************************************)
(* Addition Chebyshev model                                                  *)
(*****************************************************************************)

(* Could be optimized removing the zip *)
Definition add_cms (c1 c2 : cms) :=
  let: CMS P1 Delta1 := c1 in
  let: CMS P2 Delta2 := c2 in
  CMS [seq (add i.1 i.2) | i <- (zip P1 P2)]  (add Delta1 Delta2).

Lemma add_cms_correct n a b c1 c2 f1 f2 :
   cms_correct n a b f1 c1 -> cms_correct n a b f2 c2 ->
   cms_correct n a b (fun x => f1 x + f2 x)%R (add_cms c1 c2).
Proof.
case: c1 => [P1 Delta1] [Sp1 [p1 [H1p1 H2p1 H3p1]]].
case: c2 => [P2 Delta2] [Sp2 [p2 [H1p2 H2p2 H3p2]]].
split; first by rewrite size_map size1_zip ?Sp1 ?Sp2.
exists [seq i.1 + i.2 | i <- (zip p1 p2)]; split.
- by rewrite size_map size1_zip // H1p1 H1p2.
- move=> i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite !nth_default ?(size_map, size1_zip, Sp1, H1p1, Sp2, H1p2) //.
    by apply: I.fromZ_correct.
  rewrite (nth_map 0) ?size1_zip ?H1p1 ?H1p2 //.
  rewrite (nth_map (I0,I0)) ?size1_zip ?Sp1 ?Sp2 //.
  rewrite !nth_zip ?H1p1 ?H1p2 ?Sp1 ?Sp2 //=.
  by apply: add_correct.
move=> x Hx.
have  [d1 [H1d1 H2d1]] := H3p1 _ Hx.
have  [d2 [H1d2 H2d2]] := H3p2 _ Hx.
exists (d1 + d2); split => //.
  by apply: add_correct.
rewrite CPolyabD ?H1p1 ?H1p2 //.
by rewrite H2d1 H2d2 hornerE; toR; lra.
Qed.

(*****************************************************************************)
(* Subtraction Chebyshev model                                               *)
(*****************************************************************************)

(* Could be optimized removing the zip *)
Definition sub_cms (c1 c2 : cms) :=
  let: CMS P1 Delta1 := c1 in
  let: CMS P2 Delta2 := c2 in
  CMS [seq (sub i.1 i.2) | i <- (zip P1 P2)]  (sub Delta1 Delta2).

Lemma sub_cms_correct n a b c1 c2 f1 f2 :
   cms_correct n a b f1 c1 -> cms_correct n a b f2 c2 ->
   cms_correct n a b (fun x => f1 x - f2 x)%R (sub_cms c1 c2).
Proof.
case: c1 => [P1 Delta1] [Sp1 [p1 [H1p1 H2p1 H3p1]]].
case: c2 => [P2 Delta2] [Sp2 [p2 [H1p2 H2p2 H3p2]]].
split; first by rewrite size_map size1_zip ?Sp1 ?Sp2.
exists [seq i.1 - i.2 | i <- (zip p1 p2)]; split.
- by rewrite size_map size1_zip // H1p1 H1p2.
- move=> i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite !nth_default ?(size_map, size1_zip, Sp1, H1p1, Sp2, H1p2) //.
    by apply: I.fromZ_correct.
  rewrite (nth_map 0) ?size1_zip ?H1p1 ?H1p2 //.
  rewrite (nth_map (I0,I0)) ?size1_zip ?Sp1 ?Sp2 //.
  rewrite !nth_zip ?H1p1 ?H1p2 ?Sp1 ?Sp2 //=.
  by apply: sub_correct.
move=> x Hx.
have  [d1 [H1d1 H2d1]] := H3p1 _ Hx.
have  [d2 [H1d2 H2d2]] := H3p2 _ Hx.
exists (d1 - d2); split => //.
  by apply: sub_correct.
rewrite CPolyabB ?H1p1 ?H1p2 //.
by rewrite H2d1 H2d2 !hornerE; toR; lra.
Qed.

Section CMSin.

Context (a b : D) (annan : F.toX a <> Xnan) (bnnan : F.toX b <> Xnan).

Context (f : R -> R).

Definition Ia := I.bnd a a.

Lemma a_in_Ia : D2R a \contained_in Ia.
Proof. by rewrite /D2R /Ia /=; case: F.toX  => //= r; lra. Qed.

Definition Ib := I.bnd b b.

Lemma b_in_Ib : D2R b \contained_in Ib.
Proof. by rewrite /D2R /Ib /=; case: F.toX  => //= r; lra. Qed.

Definition Iab := I.bnd a b.

Lemma in_Iab x : (D2R a <= x <= D2R b)%R -> x \contained_in Iab.
Proof. rewrite /= /D2R; (do 2 case: F.toX) => //= r1; lra. Qed. 

Definition I01 := I.bnd (F.fromZ 0) (F.fromZ 1).

Lemma I01_correct x z I :
   (0 <= x <= z)%R -> z \contained_in I -> x \contained_in I.mul prec I01 I.
Proof.
move=> xB zI.
pose t := x / z.
have [zZ|zNZ]: (z = 0%R) \/ (z <> 0%R) by lra.
  have -> : x = (0 * z)%R by lra.
  apply: mul_correct => //=.
  by rewrite !F.fromZ_correct; lra.
have->: x = ((x / z) * z)%R by field.
apply: mul_correct => //.
rewrite /= !F.fromZ_correct; split.
  by apply: Rdiv_pos_compat; lra.
by apply/Rle_div_l; lra.
Qed.

Lemma Rabs_join x I : 
  Rabs x \contained_in I -> x \contained_in (I.join (I.neg I) I).
Proof.
move=> H.
apply: I.join_correct.
split_Rabs; [left|right]; last by [].
rewrite (_ : x = (--x)%R); last by lra.
by apply: neg_correct.
Qed.

Lemma Rabs_I01_max y i I J g :
  (i \contained_in I) ->
  (forall x, x \contained_in I -> Rabs (g x) \contained_in J)%R ->
  (forall z, 
    (forall x, x \contained_in I -> Rabs (g x) <= z)%R ->
    (Rabs y <= z))%R ->
  (Rabs y \contained_in (I.mul prec I01 J)).
Proof.
move=> iII.
case: J => // l u.
move=> H1 H2.
case E : (F.toX u) => [|x1]; last first.
  pose z := x1.
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: (H2 z) => x /H1 /= [_].
    by rewrite E.
  rewrite  /= E.
  case E1 : (F.toX l) => [|x2] //=.
    split=> //; rewrite /z; lra.
  have := H1 _ iII.
  rewrite /= E1 E /z; lra.
case E1 : (F.toX l) => [|x2].
  rewrite /= /I.sign_large_ /= !F.cmp_correct !F.fromZ_correct /= F.zero_correct /=.
  case: Rcompare_spec; try lra.
  case: Rcompare_spec; try lra.
  have := F.mul_correct rnd_DN prec (F.fromZ 1) l.
  have := F.mul_correct rnd_UP prec (F.fromZ 1) u.
  rewrite E1 /= E /= !F.fromZ_correct /= => -> -> //.
rewrite /= /I.sign_large_ /= !F.cmp_correct !F.fromZ_correct /= F.zero_correct /=.
case: Rcompare_spec; try lra.
case: Rcompare_spec; try lra.
rewrite E1 /= E /=.
case: Rcompare_spec => /=.
- have := F.mul_correct rnd_DN prec (F.fromZ 1) l.
  have := F.mul_correct rnd_UP prec (F.fromZ 1) u.
  rewrite E1 /= E /= !F.fromZ_correct /= => -> -> //.
- move=> HH1 _ _; split => //.
  apply: Rle_trans (_ : round F.radix rnd_DN (F.prec prec) 0 <= _)%R.
    apply: Generic_fmt.round_le; try lra.
  rewrite /round Generic_fmt.round_0; split_Rabs; lra.
- have := F.mul_correct rnd_DN prec (F.fromZ 0) l.
  have := F.mul_correct rnd_UP prec (F.fromZ 1) u.
  rewrite E1 /= E /= !F.fromZ_correct /= => -> ->.
  rewrite Rmult_0_l.
  rewrite /round Generic_fmt.round_0; split_Rabs; lra.
have := F.mul_correct rnd_DN prec (F.fromZ 0) l.
have := F.mul_correct rnd_UP prec (F.fromZ 1) u.
rewrite E1 /= E /= !F.fromZ_correct /= => -> ->.
rewrite Rmult_0_l.
rewrite /round Generic_fmt.round_0; split_Rabs; lra.
Qed.


(*****************************************************************************)
(*                             Factorial                                     *)
(*****************************************************************************)

Fixpoint mfact_rec n p := 
  if n is n1.+1 then (p * (mfact_rec n1 p.+1))%nat 
  else 1%nat.

Lemma mfact_recE n p : mfact_rec n p.+1 = ((n + p)`! %/ p`!)%nat.
Proof.
elim: n p => //= [|n IH] p.
  by rewrite divnn add0n fact_gt0.
rewrite IH muln_divA; first by rewrite factS divnMl // addnS.
elim: (n) => //= n1 IH1.
apply: dvdn_trans IH1 _.
rewrite addSn factS.
by apply/dvdn_mull/dvdnn.
Qed.

Fixpoint Ifact_rec n p := 
  if n is n1.+1 then mul p (Ifact_rec n1 (add I1 p)) 
  else I1.

Definition Ifact n := Ifact_rec n I1.

Lemma Ifact_correct n : INR (n`!) \contained_in Ifact n.
Proof.
rewrite /Ifact (_ : n`! = (n + 0)`! %/ 0`!)%nat; last first.
  by rewrite addn0 divn1.
rewrite -mfact_recE.
have : INR 1 \contained_in I1 by apply: I.fromZ_correct.
elim: n 1%nat I1 => [|n IH] m M H; first by apply: I.fromZ_correct.
lazy iota beta delta [mfact_rec Ifact_rec]. 
rewrite mult_INR.
apply: mul_correct => //.
apply: IH.
rewrite S_INR Rplus_comm.
apply: add_correct => //.
by apply: I.fromZ_correct.
Qed.

(*****************************************************************************)
(* Naive way to check if an interval is of constant sign                     *)
(*****************************************************************************)

Definition s0P := I.bnd (F.fromZ 0) F.nan.
Definition sN0 := I.bnd F.nan (F.fromZ 0).

Definition csign i :=  (I.subset i s0P) || (I.subset i sN0).

Lemma csign_correct I :
  csign I ->    (forall x, x \contained_in I -> (x >= 0)%R)
             \/ (forall x, x \contained_in I -> (x <= 0)%R) .
Proof.
rewrite /csign.
have := I.subset_correct I s0P.
case: I.subset => /= [/(_ isT) H _|_].
  left => x; case: I H => //= l u.
  rewrite F.fromZ_correct /=.
  case: F.toX => //= [|r].
    by rewrite /le_lower /= => [] [].
  by rewrite /le_lower /=; lra.
have := I.subset_correct I sN0.
case: I.subset => /= [/(_ isT) H _|_] //.
right => x.
case: I H => //= l u.
rewrite F.fromZ_correct /=.
case: (F.toX l) => //= [|r]; case: (F.toX u) => //= [[]//|r1].
  by lra.
by lra.
Qed.


(*****************************************************************************)
(* Derivative of sin for interval arithmetic                                 *)
(*****************************************************************************)

Lemma sin_env: I.sin prec \is_envelope_of sin.
Proof. exact: sin_correct. Qed.

Fixpoint bsin b x := if b then cos x else sin x.

Definition Ibsin b J := if b then I.cos prec J else I.sin prec J.

Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

Lemma Ibsin_correct n:
 (Ibsin (odd n)) \is_envelope_of (fun x => (-1) ^ (odd n./2) * sin^(n) x)%R.
Proof.
move=> x X Hx.
rewrite Derive_n_sin /Ibsin; case: odd.
  rewrite -!expr_Rexp -Rmult_assoc -[(-1) ^+ n./2]signr_odd.
  case: odd; rewrite ?expr0 ?expr1.
    rewrite (_ : -1 * -1  * cos x = cos x)%R; last by lra.
    by apply: cos_correct.
  rewrite (_ : 1 * 1  * cos x = cos x)%R; last by lra.
  by apply: cos_correct.
rewrite -!expr_Rexp -Rmult_assoc -[(-1) ^+ n./2]signr_odd.
case: odd; rewrite ?expr0 ?expr1.
  rewrite (_ : -1 * -1  * sin x = sin x)%R; last by lra.
  by apply: sin_correct.
rewrite (_ : 1 * 1  * sin x = sin x)%R; last by lra.
by apply: sin_correct.
Qed.

(*****************************************************************************)
(* Error of sin                                                              *)
(*****************************************************************************)

Definition sin_error (b1 : bool) P zn z2n nn :=
  let v := Ibsin b1 Iab in
  let Ic := 
    if csign v then
      let Ida := I.abs (I.sub prec (I.sin prec Ia) (IsCshaw Ia Ib P Ia)) in
      let Idb := I.abs (I.sub prec (I.sin prec Ib) (IsCshaw Ia Ib P Ib)) in
      I.mul prec I01 (I.join Ida Idb)
    else
      I.div prec
        (I.mul prec (I.power_pos prec (I.sub prec Ib Ia) zn) 
                    (I.mul prec I01 (I.abs (Ibsin (~~b1) Iab))))
       (I.mul prec (I.power_pos prec I2 z2n) (Ifact nn))
   in  I.join (I.neg Ic) Ic.

Definition sin_cms n b1 vn zn z2n vl2 vl3 :=
  let P := Icheby_coefs (I.sin prec) vn vl3 vl2 in
  CMS P (sin_error b1 P zn z2n n.+1).

Lemma sin_cms_correct n b1 vn v2n zn z2n vl2 vl3 :    
  F.cmp a b = Xlt ->
  b1 = odd n ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  zn = Pos.of_nat n.+1 ->
  z2n = Pos.of_nat n.*2.+1 ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b sin (sin_cms n b1 vn zn z2n vl2 vl3).
Proof.
move=> aLb b1E vnE v2nE znE z2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia := a_in_Ia.
have Hib := b_in_Ib.
pose iv := interpolation sin (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /sin_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) sin n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.sin prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I.fromZ_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: sin_env.
  - by left.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (sin x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  by have := Hx; rewrite /D2R /=; (do 2 case: F.toX).
apply: Rabs_join.
have [/csign_correct H|_] := boolP (csign _).
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: sin_scheby_ge => //.
    case: H => H.
      right => x1 /in_Iab Hx1.
      apply: H.
      rewrite /Ibsin b1E; case: odd.
        by apply: cos_correct.
      by apply: sin_correct.
    left => x1 /in_Iab Hx1.
    apply: H.
    rewrite /Ibsin b1E; case: odd.
      by apply: cos_correct.
    by apply: sin_correct.
  rewrite /Rmax; case: Rle_dec => _.
    apply: I.join_correct.
    right.
    apply/abs_correct/sub_correct.
      by apply/sin_correct/b_in_Ib.
    rewrite -scheby_coef_list_spec //.
    apply: IsCshaw_correct => //.
    by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
  apply: I.join_correct.
  left.
  apply/abs_correct/sub_correct.
    by apply/sin_correct/a_in_Ia.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
set u := (_ - _)%R.
pose e : R := (expn 2 n.+1.*2.-1 * n.+1 `!) %:R.
pose v := ((D2R b - D2R a)^+ n.+1).
have vP : (0 < v)%R.
  rewrite /v expr_Rexp.
  by apply: pow_lt; toR; lra.
have vE: (0 < e)%R.
  rewrite /e natr_INR.
  apply: (lt_INR 0).
  by apply/ltP; rewrite muln_gt0 expn_gt0 fact_gt0.
have -> : Rabs u = ((v * Rabs (u / v * e)) / e)%R.
  rewrite Rabs_mult Rabs_div; try lra.
  rewrite (Rabs_pos_eq v); try lra.
  rewrite (Rabs_pos_eq e); try lra.
  by field; lra.
apply: div_correct; last by case: is_zero_spec => //; lra.
 apply: mul_correct.
    rewrite /v expr_Rexp znE.
    apply: power_pos_correct => //.
    by apply: sub_correct.
  apply: Rabs_I01_max => [||z Hz].
  - suff: (D2R a) \contained_in Iab by apply.
    by apply: in_Iab; lra.
  - move=> y YC.
    apply: abs_correct.
    rewrite b1E.
    by apply: (Ibsin_correct n.+1).
  rewrite Rabs_mult Rabs_div; try lra.
  rewrite (Rabs_pos_eq v); try lra.
  rewrite (Rabs_pos_eq e); try lra.
  suff: (Rabs u <= v / e * z)%R.
    move=> HH.
    have-> : (z = (v / e * z) / v * e)%R by field; lra.
    apply: Rmult_le_compat_r; try lra.
    apply: Rmult_le_compat_r => //.
    by have := Rinv_0_lt_compat _ vP; lra.
  apply: ierror_sin => // y Hy.
  have /Hz : y \contained_in Iab by apply: in_Iab.
  rewrite Derive_n_sin -[odd n.+1]/(~~ odd n).
  case: (odd n).
    rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
    case: odd => /=.
      by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) Ropp_involutive !Rmult_1_l.
    by rewrite !Rmult_1_l.
  rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
  case: odd => /=.
    by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) Ropp_involutive !Rmult_1_l.
  by rewrite !Rmult_1_l.
rewrite [e]natr_INR mult_INR.
apply: mul_correct.
  rewrite -pow_expn pow_INR z2nE.
  apply: power_pos_correct => //.
  by rewrite /= F.fromZ_correct; lra.
by apply: Ifact_correct.
Qed.

(*****************************************************************************)
(* Derivative of cos for interval arithmetic                                 *)
(*****************************************************************************)

Lemma cos_env: I.cos prec \is_envelope_of cos.
Proof. exact: cos_correct. Qed.

Fixpoint bcos b x := if b then sin x else cos x.

Definition Ibcos b J := if b then I.sin prec J else I.cos prec J.

Lemma Ibcos_correct n:
 (Ibcos (odd n)) \is_envelope_of 
   (fun x => (-1) ^ (odd n) * (-1) ^ (odd n./2) * cos^(n) x)%R.
Proof.
move=> x X Hx.
rewrite Derive_n_cos /Ibcos; case: odd.
  rewrite -!expr_Rexp -Rmult_assoc -[(-1) ^+ n./2]signr_odd.
  case: odd; rewrite ?expr0 ?expr1.
    rewrite (_ : -1 * -1 * -1  * - sin x = sin x)%R; last by lra.
    by apply: sin_correct.
  rewrite (_ : -1 * 1 * 1  * - sin x = sin x)%R; last by lra.
  by apply: sin_correct.
rewrite -!expr_Rexp -Rmult_assoc -[(-1) ^+ n./2]signr_odd.
case: odd; rewrite ?expr0 ?expr1.
  rewrite (_ : 1 * -1 * -1  * cos x = cos x)%R; last by lra.
  by apply: cos_correct.
rewrite (_ : 1 * 1 * 1  * cos x = cos x)%R; last by lra.
by apply: cos_correct.
Qed.

(*****************************************************************************)
(* Error of cos                                                              *)
(*****************************************************************************)

Definition cos_error (b1 : bool) P zn z2n nn :=
  let v := Ibcos b1 Iab in
  let Ic := 
    if csign v then
      let Ida := I.abs (I.sub prec (I.cos prec Ia) (IsCshaw Ia Ib P Ia)) in
      let Idb := I.abs (I.sub prec (I.cos prec Ib) (IsCshaw Ia Ib P Ib)) in
      I.mul prec I01 (I.join Ida Idb) 
    else
      I.div prec
         (I.mul prec (I.power_pos prec (I.sub prec Ib Ia) zn) 
                     (I.mul prec I01 (I.abs (Ibcos (~~b1) Iab))))
         (I.mul prec (I.power_pos prec I2 z2n) (Ifact nn))
   in I.join (I.neg Ic) Ic.

Definition cos_cms n b1 vn zn z2n vl2 vl3 :=
  let P := Icheby_coefs (I.cos prec) vn vl3 vl2 in
  CMS P (cos_error b1 P zn z2n n.+1).

Lemma cos_cms_correct n b1 vn v2n zn z2n vl2 vl3 :    
  F.cmp a b = Xlt ->
  b1 = odd n ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  zn = Pos.of_nat n.+1 ->
  z2n = Pos.of_nat n.*2.+1 ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b cos (cos_cms n b1 vn zn z2n vl2 vl3).
Proof.
move=> aLb b1E vnE v2nE znE z2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia := a_in_Ia.
have Hib := b_in_Ib.
pose iv := interpolation sin (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /cos_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) cos n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.cos prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I.fromZ_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: cos_env.
  - by left.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (cos x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  by have := Hx; rewrite /D2R /=; (do 2 case: F.toX).
apply: Rabs_join.
have [/csign_correct H|_] := boolP (csign _).
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: cos_scheby_ge => //.
    case: H => H.
      right => x1 /in_Iab Hx1.
      apply: H.
      rewrite /Ibsin b1E; case: odd.
        by apply: sin_correct.
      by apply: cos_correct.
    left => x1 /in_Iab Hx1.
    apply: H.
    rewrite /Ibsin b1E; case: odd.
      by apply: sin_correct.
    by apply: cos_correct.
  rewrite /Rmax; case: Rle_dec => _.
    apply: I.join_correct.
    right.
    apply/abs_correct/sub_correct.
      by apply/cos_correct/b_in_Ib.
    rewrite -scheby_coef_list_spec //.
    apply: IsCshaw_correct => //.
    by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
  apply: I.join_correct.
  left.
  apply/abs_correct/sub_correct.
    by apply/cos_correct/a_in_Ia.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
set u := (_ - _)%R.
pose e : R := (expn 2 n.+1.*2.-1 * n.+1 `!) %:R.
pose v := ((D2R b - D2R a)^+ n.+1).
have vP : (0 < v)%R.
  rewrite /v expr_Rexp.
  by apply: pow_lt; toR; lra.
have vE: (0 < e)%R.
  rewrite /e natr_INR.
  apply: (lt_INR 0).
  by apply/ltP; rewrite muln_gt0 expn_gt0 fact_gt0.
have -> : Rabs u = ((v * Rabs (u / v * e)) / e)%R.
  rewrite Rabs_mult Rabs_div; try lra.
  rewrite (Rabs_pos_eq v); try lra.
  rewrite (Rabs_pos_eq e); try lra.
  by field; lra.
apply: div_correct; last by case: is_zero_spec => //; lra.
 apply: mul_correct.
    rewrite /v expr_Rexp znE.
    apply: power_pos_correct => //.
    by apply: sub_correct.
  apply: Rabs_I01_max => [||z Hz].
  - suff: (D2R a) \contained_in Iab by apply.
    by apply: in_Iab; lra.
  - move=> y YC.
    apply: abs_correct.
    rewrite b1E.
    by apply: (Ibcos_correct n.+1).
  rewrite Rabs_mult Rabs_div; try lra.
  rewrite (Rabs_pos_eq v); try lra.
  rewrite (Rabs_pos_eq e); try lra.
  suff: (Rabs u <= v / e * z)%R.
    move=> HH.
    have-> : (z = (v / e * z) / v * e)%R by field; lra.
    apply: Rmult_le_compat_r; try lra.
    apply: Rmult_le_compat_r => //.
    by have := Rinv_0_lt_compat _ vP; lra.
  apply: ierror_cos => // y Hy.
  have /Hz : y \contained_in Iab by apply: in_Iab.
  rewrite Derive_n_cos -[odd n.+1]/(~~ odd n).
  case: (odd n).
    rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
    case: odd => /=.
      by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) Ropp_involutive !Rmult_1_l.
    by rewrite !Rmult_1_l.
  rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
  case: odd => /=.
    by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) !Ropp_involutive !Rmult_1_l.
  rewrite expr0 !(Rmult_1_l, Rmult_1_r).
  by rewrite -Ropp_mult_distr_l -Ropp_mult_distr_r Rmult_1_l Ropp_involutive.
rewrite [e]natr_INR mult_INR.
apply: mul_correct.
  rewrite -pow_expn pow_INR z2nE.
  apply: power_pos_correct => //.
  by rewrite /= F.fromZ_correct; lra.
by apply: Ifact_correct.
Qed.

Lemma exp_env: I.exp prec \is_envelope_of exp.
Proof. exact: exp_correct. Qed.

(*****************************************************************************)
(* Error of exp                                                              *)
(*****************************************************************************)

Definition exp_error P :=
  let Ida := I.abs (I.sub prec (I.exp prec Ia) (IsCshaw Ia Ib P Ia)) in
  let Idb := I.abs (I.sub prec (I.exp prec Ib) (IsCshaw Ia Ib P Ib)) in
  let Ic := I.mul prec I01 (I.join Ida Idb) in
  I.join (I.neg Ic) Ic.

Definition exp_cms vn vl2 vl3 :=
  let P := Icheby_coefs (I.exp prec) vn vl3 vl2 in
  CMS P (exp_error P).

Lemma exp_cms_correct n vn v2n vl2 vl3 :    
  F.cmp a b = Xlt ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b exp (exp_cms vn vl2 vl3).
Proof.
move=> aLb vnE v2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia := a_in_Ia.
have Hib := b_in_Ib.
pose iv := interpolation exp (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /exp_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) exp n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.exp prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I.fromZ_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: exp_env.
  - by left.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (exp x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  by have := Hx; rewrite /D2R /=; (do 2 case: F.toX).
apply: Rabs_join.
apply: I01_correct.
  split; first by split_Rabs; lra.
  apply: exp_scheby_ge => //.
  rewrite /Rmax; case: Rle_dec => _.
  apply: I.join_correct.
  right.
  apply/abs_correct/sub_correct.
    by apply/exp_correct/b_in_Ib.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
apply: I.join_correct.
left.
apply/abs_correct/sub_correct.
  by apply/exp_correct/a_in_Ia.
rewrite -scheby_coef_list_spec //.
apply: IsCshaw_correct => //.
by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
Qed.

End CMSin.

End CPoly_interval.

End CPoly_interval.
Module V := CPoly_interval SFBI2.

Export V.

From Bignums Require Import BigZ.

Definition I1 := I.fromZ 1.
Definition I2 := I.fromZ 2.
Definition prec := 50%bigZ.
Definition n := 25%nat.
Definition zn := 
  Eval vm_compute in Pos.of_nat n.+1.
Definition z2n := 
  Eval vm_compute in (2 * zn)%positive.
Definition vn := 
  Eval vm_compute in I.fromZ (Zpos zn).
Definition v2n := 
  Eval vm_compute in I.fromZ (Zpos z2n).
Definition a := I.lower I1.
Definition b := I.upper I2.

Time
Definition l1 :=
  Eval vm_compute in nseq n.+1 I1.

Time
Definition vl1 := 
  Eval vm_compute in Icheby_nodes prec n.+1 v2n.
Time
Definition vl2 :=
  Eval vm_compute in ITvalues prec n.+1 l1 vl1.
Time
Definition vl3 := 
  Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Time
Definition coefs :=
  Eval vm_compute in 
  Icheby_coefs prec (I.sin prec) vn vl3 vl2.

Definition ob :=
  Eval vm_compute in odd n.

Time
Definition scms :=
  Eval vm_compute in
  sin_cms prec a b n ob vn zn z2n vl2 vl3.

Compute "Delta sin"%string.
Compute Delta scms.

Time
Definition ccms :=
  Eval vm_compute in
  cos_cms prec a b n ob vn zn z2n vl2 vl3.

Compute "Delta cos"%string.
Compute Delta ccms.

Time
Definition ecms :=
  Eval vm_compute in
  exp_cms prec a b vn vl2 vl3.

Compute "Delta exp"%string.
Compute Delta ecms.


