From mathcomp Require Import all_ssreflect all_algebra.
Require Import String Rstruct Reals Psatz under.
Require Import Poly_complements CPoly CPoly_exec CPoly_interpolation.
Require Import Coquelicot.Coquelicot.
Require Import CFun_interpolation.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.
Require Import ZArith.
From Interval Require Import Specific_ops Missing.Stdlib Xreal.
From Interval Require Import Basic Float Sig Interval.

Module SFBI2 := SpecificFloat Specific_bigint.BigIntRadix2.
Module I := Float_full.FloatIntervalFull SFBI2.

Module CPoly_interval (F : FloatOps with Definition sensible_format := true).
Module I := Float_full.FloatIntervalFull F.

Section CPoly_interval.

Variable prec: F.precision.

Notation mant := Specific_bigint.BigIntRadix2.smantissa_type.
Notation xpnt := Specific_bigint.BigIntRadix2.exponent_type.
 
Notation D := F.type.
Notation ID := (Float.f_interval F.type).
Notation "x '\contained_in' I" := 
  (contains (I.convert I) (Xreal x)) (at level 20).
Notation D2R := I.T.toR.
Notation I0 := (I.bnd F.zero F.zero).
Notation scl2 I := (I.mul prec I ((I.fromZ prec 2))).
Notation add I J := (I.add prec I J).
Notation mul I J := (I.mul prec I J).
Notation sqr I := (I.sqr prec I).
Notation sub I J := (I.sub prec I J).
Notation div I J := (I.div prec I J).

Definition chalf := F.div2 (F.fromZ 1).

Lemma chalf_correct :  F.toX chalf = Xreal (/ 2).
Proof.
rewrite F.div2_correct //=; last first.
  by rewrite /D2R F.fromZ_correct //= Rabs_R1; lra.
by rewrite F.fromZ_correct // Xdiv_split Xmul_1_l /= /Xinv' is_zero_false.
Qed.

Notation div2 I := (I.mul_mixed prec I chalf).

Notation "l '\lcontained_in' L" :=
 (forall i,  l`_i \contained_in nth I0 L i) (at level 20).

Section Interval_lemmas.

Definition FtoI (a: D) := (Float.Ibnd a a).

Lemma FtoI_correct a : F.real a -> (D2R a) \contained_in (FtoI a).
Proof.
move=> aR /=.
rewrite (I.F'.valid_lb_real _ aR) (I.F'.valid_ub_real _ aR) /=.
by rewrite /D2R; case: F.toX => //= r; lra.
Qed.

Lemma I020 x : x \contained_in I0 -> x = 0%R.
Proof. 
rewrite /= F.zero_correct; case: F.valid_lb; case: F.valid_ub => //=; lra. 
Qed.
 
Lemma I0_correct: 0 \contained_in I0.
Proof. 
rewrite /= F.zero_correct /= I.F'.valid_lb_zero I.F'.valid_ub_zero => /=; lra.
Qed.

Lemma mul_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x * y) \contained_in (mul I J).
Proof. by apply I.mul_correct. Qed.

Lemma sqr_correct x I :
	x \contained_in I -> (x * x) \contained_in sqr I.
Proof. by apply I.sqr_correct. Qed.

Lemma sub_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x - y) \contained_in (sub I J).
Proof. by apply I.sub_correct. Qed.

Lemma add_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x + y) \contained_in (add I J).
Proof. by apply I.add_correct. Qed.

Lemma inv_correct x I:
	x \contained_in I -> (/ x)%R \contained_in (I.inv prec I).
Proof.
move=> xI.
have /= := I.inv_correct prec I (Xreal x) xI.
rewrite /Xinv'; case: is_zero => //=; case: I.inv => //= l b.
by case: F.valid_lb => //=; case: F.valid_ub.
Qed.

Lemma div_correct_prec p x y I J:
	x \contained_in I -> y \contained_in J -> 
    (x / y)%R \contained_in (I.div p I J).
Proof.
move=> xI yJ.
have /= := I.div_correct p I J (Xreal x) (Xreal y) xI yJ.
rewrite /Xdiv'; case: is_zero => //; case: I.div => //= l b.
by case: F.valid_lb => //=; case: F.valid_ub.
Qed.

Lemma div_correct x y I J:
	x \contained_in I -> y \contained_in J -> (x / y)%R \contained_in (div I J).
Proof. by apply: div_correct_prec. Qed.

Lemma scl2_correct x I:
	x \contained_in I -> (x *+ 2) \contained_in (scl2 I).
Proof.
move=> xI.
suff -> : Xreal (x *+ 2) = Xmul (Xreal x) (Xreal (Raux.bpow radix2 1)).
  apply: mul_correct => //.
  by apply: I.fromZ_correct.
congr Xreal.
by have ->: (x*2 = x + x)%R by lra.
Qed.

Lemma div2_correct x I: x \contained_in I -> (x / 2) \contained_in (div2  I).
Proof.
move=> xI.
have -> : Xreal (x / 2) = Xmul (Xreal x) (Xreal (/2)) by [].
rewrite -chalf_correct.
by apply: I.mul_mixed_correct.
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

Lemma ln_correct x I:
	x \contained_in I -> (ln x) \contained_in (I.ln prec I).
Proof.
move=> xI.
have /= := I.ln_correct prec _ _ xI.
rewrite /Xln'; case: is_positive => //; case: I.ln => //= l u.
by case: F.valid_lb => //=; case: F.valid_ub.
Qed.

Lemma sqrt_correct x I:
	x \contained_in I -> (sqrt x) \contained_in (I.sqrt prec I).
Proof.
move=> xI.
have /= := I.sqrt_correct prec _ _ xI.
by rewrite /Xsqrt'; case: is_negative => //; case: I.sqrt.
Qed.

Lemma atan_correct x I:
	x \contained_in I -> (atan x) \contained_in (I.atan prec I).
Proof. by apply I.atan_correct. Qed.

End Interval_lemmas.

Section ExtraDef.

Definition I1 := I.fromZ prec 1.
Definition I2 := I.fromZ prec 2.
Definition I01 := I.bnd (F.fromZ 0) (F.fromZ 1).
Definition Im11 := I.bnd (F.fromZ (-1)) (F.fromZ 1).

Lemma in_01 (x : R) : (0 <= x <= 1)%R -> x \contained_in I01.
Proof.
move=> xB.
by rewrite /= !(I.F'.valid_lb_real, I.F'.valid_ub_real, 
               F.real_correct, F.fromZ_correct).
Qed.

Lemma I01_correct x z I :
   (0 <= x <= z)%R -> z \contained_in I -> x \contained_in I.mul prec I01 I.
Proof.
move=> xB zI.
pose t := x / z.
have [zZ|zNZ]: (z = 0%R) \/ (z <> 0%R) by lra.
  have -> : x = (0 * z)%R by lra.
  apply: mul_correct => //.
  by apply: in_01; lra.
have->: x = ((x / z) * z)%R by field.
apply: mul_correct => //.
apply: in_01; split.
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


Lemma containedE x l u : 
  x \contained_in Float.Ibnd l u -> 
  [/\ F.valid_lb l = true, F.valid_ub u = true, 
      F.classify l <> Fpinfty, F.classify u <> Fminfty &
      (forall x y, F.toX l = Xreal x -> F.toX u = Xreal y -> (x <= y)%R)].
Proof.
rewrite /=.
rewrite F.valid_lb_correct F.valid_ub_correct.
((do 2 (case: F.classify => //=); do 2 (case: F.toX => //=))) => *;
try lra; split => // x2 y2 []<- []<-; lra.
Qed.

Lemma Freal_fromZ n :
  (Z.abs n <= 256)%Z -> F.real (F.fromZ n) = true.
Proof.
move/F.fromZ_correct=> /=.
by rewrite F.real_correct => ->.
Qed.

Lemma classify_fromZ n :
  (Z.abs n <= 256)%Z -> F.classify (F.fromZ n) = Freal.
Proof.
move/F.fromZ_correct=> H1; apply: I.F'.classify_real.
by rewrite F.real_correct H1.
Qed.

Lemma valid_lb_fromZ n :
  (Z.abs n <= 256)%Z -> F.valid_lb (F.fromZ n) = true.
Proof.
move/F.fromZ_correct=> H1; apply: I.F'.valid_lb_real.
by rewrite F.real_correct H1.
Qed.

Lemma valid_ub_fromZ n :
  (Z.abs n <= 256)%Z -> F.valid_ub (F.fromZ n) = true.
Proof.
move/F.fromZ_correct=> H1; apply: I.F'.valid_ub_real.
by rewrite F.real_correct H1.
Qed.

Lemma Rabs_I01_max y i I J g :
  (i \contained_in I) ->
  (forall x, x \contained_in I -> Rabs (g x) \contained_in J)%R ->
  (forall z,
    (forall x, x \contained_in I -> Rabs (g x) <= z)%R ->
    (Rabs y <= z))%R ->
  (Rabs y \contained_in (I.mul prec I01 J)).
Proof.
move=> iII H1.
have := (H1 _ iII); move: H1.
case: J => // l u.
move=> H1 HH H2.
have /containedE[V1 V2 V3 V4 V5] := HH.
rewrite /= V1 V2 /= in HH.
case E : (F.toX u) V5 HH => [|x1]; last first.
  move=> V5 HH.
  pose z := x1.
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: (H2 z) => x /H1 /=.
  by rewrite V1 V2 /=  => [] []; rewrite E. 
  rewrite  /= E V1 V2 /=.
  case E1 : (F.toX l) V5 HH => [|x2] //= V5 HH.
    by split=> //; rewrite /z; lra.
  have := V5 _ _ (refl_equal _) (refl_equal _).
  by rewrite /z; lra.
move=> _.
case E1 : (F.toX l) => [|x2] [V5 _].
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: Rle_refl.
  by rewrite /= V1 V2 /= E E1.
rewrite /= /I.sign_large_ /= F.cmp_correct // F.fromZ_correct //.
rewrite classify_fromZ // I.F'.classify_zero /= F.zero_correct //=.
case: Raux.Rcompare_spec => /=; try lra.
have El : F.classify l = Freal.
  by apply: I.F'.classify_real; rewrite F.real_correct E1.
move=> _.
rewrite /= F.cmp_correct // classify_fromZ // I.F'.classify_zero.
rewrite F.fromZ_correct // F.zero_correct /=.
case: Raux.Rcompare_spec => /=; try lra.
move=> _.
rewrite [F.cmp u F.zero]F.cmp_correct I.F'.classify_zero E /=.
case xE : (F.cmp l F.zero).
- suff : Rabs y \contained_in
  Float.Ibnd (F.mul_DN prec (F.fromZ 0) l) (F.mul_UP prec (F.fromZ 1) u).
    by case: F.classify V4.
  move: xE; rewrite F.cmp_correct // El I.F'.classify_zero E1 /= F.zero_correct;
  case: Raux.Rcompare_spec => // x2E0.
  have [|-> /= Hl] := F.mul_DN_correct prec (F.fromZ 0) l.
    left.
    rewrite /F.is_non_neg_real E1 /= /F.is_non_neg_real.
    rewrite F.fromZ_correct //=; lra. 
  have [|-> /= Hu] := F.mul_UP_correct prec (F.fromZ 1) u.
    left.
    rewrite /F.is_non_neg /= I.F'.valid_ub_real ?Freal_fromZ //=.
    rewrite F.fromZ_correct // E V2.
    repeat split => //; lra.
  split.
    move: Hl; case: F.toX => //= r.
    rewrite E1 F.fromZ_correct //= /le_lower /=.
    move=> HH.
    by split_Rabs; lra.
  move: Hu; case: (F.toX (F.mul_UP _ _ _)) => //= r.
  by rewrite E; case: F.toX.
- suff : Rabs y \contained_in
  Float.Ibnd (F.mul_DN prec (F.fromZ 1) l) (F.mul_UP prec (F.fromZ 1) u).
    by case: F.classify V4.
  move: xE; rewrite F.cmp_correct // El I.F'.classify_zero E1 /= F.zero_correct;
  case: Raux.Rcompare_spec => // x2_lt0.
  have [|-> /= Hl] := F.mul_DN_correct prec (F.fromZ 1) l.
    right; right; left.
    rewrite /F.is_non_pos E1 /= /F.is_non_neg.
    rewrite I.F'.valid_ub_real ?Freal_fromZ //= F.fromZ_correct // V1.
    repeat split => //; lra.
  have [|-> /= Hu] := F.mul_UP_correct prec (F.fromZ 1) u.
    left.
    rewrite /F.is_non_neg /= I.F'.valid_ub_real ?Freal_fromZ //=.
    rewrite F.fromZ_correct // E V2.
    repeat split => //; lra.
  split.
    move: Hl; case: F.toX => //= r.
    rewrite E1 F.fromZ_correct //= /le_lower /=.
    rewrite Rmult_1_l.
    move=> HH.
    by split_Rabs; lra.
  move: Hu; case: (F.toX (F.mul_UP _ _ _)) => //= r.
  by rewrite E; case: F.toX.
- suff : Rabs y \contained_in
  Float.Ibnd (F.mul_DN prec (F.fromZ 0) l) (F.mul_UP prec (F.fromZ 1) u).
    by case: F.classify V4.
  move: xE; rewrite F.cmp_correct // El I.F'.classify_zero E1 /= F.zero_correct;
  case: Raux.Rcompare_spec => // x2_gt0.
  have [|-> /= Hl] := F.mul_DN_correct prec (F.fromZ 0) l.
    left.
    rewrite /F.is_non_neg_real E1 /= /F.is_non_neg_real.
    rewrite F.fromZ_correct //=; lra. 
  have [|-> /= Hu] := F.mul_UP_correct prec (F.fromZ 1) u.
    left.
    rewrite /F.is_non_neg /= I.F'.valid_ub_real ?Freal_fromZ //=.
    rewrite F.fromZ_correct // E V2.
    repeat split => //; lra.
  split.
    move: Hl; case: F.toX => //= r.
    rewrite E1 F.fromZ_correct //= /le_lower /=.
    move=> HH.
    by split_Rabs; lra.
  move: Hu; case: (F.toX (F.mul_UP _ _ _)) => //= r.
  by rewrite E; case: F.toX.
case: F.classify V4 xE => //; rewrite F.cmp_correct ?El /= I.F'.classify_zero /=.
by rewrite E1 /= F.zero_correct /=; case: Raux.Rcompare.
by rewrite E1 /= F.zero_correct /=; case: Raux.Rcompare.
by rewrite E1 /= F.zero_correct /=; case: Raux.Rcompare.
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
case: I.subset => [/(_ isT) H _|_].
  rewrite /= valid_lb_fromZ //= I.valid_ub_nan F.fromZ_correct //= in H.
  left => x; case: I H => //= l u.
  case: F.valid_lb => //=; last by lra.
  case: F.valid_ub => //=; last by lra.
  case: F.toX => //= [|r1]; case: F.toX => //= [|r2].
  - by case => // [] [] [].
  - by case => // [] [] [].
  - case => // [] [] []; lra.
  case => //; try lra.
  by case => [] [H1 | H1]; lra.
right => x; case: I H => // l u /andP[_ H1] H2.
have /containedE[V1 V2 V3 V4 _] := H2.
move: H1 H2 => /=.
rewrite V1 V2 /= classify_fromZ //.
rewrite F.cmp_correct classify_fromZ //= F.fromZ_correct //.
case E : F.classify V4 => // _.
case E1 : F.toX => [|r] //=.
by case: Raux.Rcompare_spec => //; lra.
Qed.

(*****************************************************************************)
(* Checking positivity                                                       *)
(*****************************************************************************)

Definition Fpos x := 
  if F.cmp F.zero x is Xlt then 
    if F.classify x is Fpinfty then false else true
  else false.

Lemma Fpos_correct x : (if Fpos x then 0 < D2R x else D2R x <= 0)%R.
Proof.
rewrite /Fpos /D2R F.cmp_correct /= F.zero_correct /=.
rewrite I.F'.classify_zero.
case E : F.classify => //.
- case: F.toX => //= [|r]; try lra.
  case: Raux.Rcompare_spec; lra.
- case E1 : F.toX => [|r] //=; try lra.
  have: F.classify x = Freal.
    rewrite I.F'.classify_real //.
    by rewrite F.real_correct E1.
  by rewrite E.
- case E1 : F.toX => [|r] //=; try lra.
  have: F.classify x = Freal.
    rewrite I.F'.classify_real //.
    by rewrite F.real_correct E1.
  by rewrite E.
case E1 : F.toX => [|r] //=; try lra.
have: F.classify x = Freal.
  rewrite I.F'.classify_real //.
  by rewrite F.real_correct E1.
by rewrite E.
Qed.

Definition Fneg x := 
  if F.cmp x F.zero is Xlt then
    if F.classify x is Fminfty then false else true
  else false.

Lemma Fneg_correct x : (if Fneg x then D2R x < 0 else 0 <= D2R x)%R.
Proof.
rewrite /Fneg /D2R F.cmp_correct /= F.zero_correct /=.
rewrite I.F'.classify_zero.
case E : F.classify => //.
- case: F.toX => //= [|r]; try lra.
  case: Raux.Rcompare_spec; lra.
- case E1 : F.toX => [|r] //=; try lra.
  have: F.classify x = Freal.
    rewrite I.F'.classify_real //.
    by rewrite F.real_correct E1.
  by rewrite E.
- case E1 : F.toX => [|r] //=; try lra.
  have: F.classify x = Freal.
    rewrite I.F'.classify_real //.
    by rewrite F.real_correct E1.
  by rewrite E.
case E1 : F.toX => [|r] //=; try lra.
have: F.classify x = Freal.
  rewrite I.F'.classify_real //.
  by rewrite F.real_correct E1.
by rewrite E.
Qed.

End ExtraDef.

(*****************************************************************************)
(* Clenshaw algorithm on [-1; 1] for interval arithmetic                     *)
(*****************************************************************************)

Section ICshaw.

Fixpoint ICb q (x : ID) : ID * ID :=
 if q is a :: q' then
   let t := ICb q' x in
   let a1 := sub (add a (mul (fst t) x)) (snd t) in
   (a1, (fst t)) else (I0, I0).

Definition ICshaw p x :=
  let: (i1, i2) := ICb p (scl2 x) in sub i1 (mul i2 x).

Lemma ICb_crct (p: seq R) (pI: seq ID) (x: R) (I: ID):
	(p \lcontained_in pI) -> x \contained_in I  -> size p = size pI ->
		(Cb p x).1 \contained_in (ICb pI I).1 /\ 
    (Cb p x).2 \contained_in (ICb pI I).2.
Proof.
move => prp xJ.
elim: pI p prp => [[ | a p]// prp _ | J pI ih [ | a p]// prp eq].
	by split; apply I0_correct.
rewrite /=.
case: (ih p) => // [i | | ih1 ih2 ].
		by apply (prp (S i)).
	by case: eq.
split => //.
apply sub_correct => //.
apply add_correct; first exact: (prp 0%nat).
by apply: mul_correct.
Qed.

Lemma ICshaw_correct (p: seq R) (pI: seq ID) (x: R) (J: ID):
	p \lcontained_in pI -> x \contained_in J -> size p = size pI ->
		(Cshaw p x) \contained_in (ICshaw pI J).
Proof.
move => prp xJ.
case: pI p prp => [p prp eq | I pI p prp eq].
	have ->: p = [::].
		by apply size0nil.
	rewrite /Cshaw /= /ICshaw/ICb.
	apply sub_correct; first exact I0_correct.
	by apply mul_correct; first exact I0_correct.
have := ICb_crct prp (scl2_correct xJ) eq.
rewrite /Cshaw/ICshaw; case: Cb => i1 j1; case: ICb => I1 J1 [H1 H2].
apply sub_correct => //.
by apply mul_correct.
Qed.
End ICshaw.

(*****************************************************************************)
(* Clenshaw algorithm on [a; b] for interval arithmetic                      *)
(*****************************************************************************)

Section IsCshaw.

Definition IsCshaw a b p x :=
  let x1 := div (sub (sub (scl2 x) b) a) (sub b a) in
  ICshaw p x1.

Lemma IsCshaw_correct n (p: seq R) (P: seq ID) (x a b : R) (X A B : ID) :
  a != b -> size p = n -> size P = n ->
	p \lcontained_in P ->
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
by apply: sub_correct.
Qed.

End IsCshaw.

(*****************************************************************************)
(* Chebyshev nodes on [-1; 1] : Icheby_nodes                                 *)
(* Chebyshev nodes on [ a; b] : Ischeby_nodes                                *)
(*****************************************************************************)


Section Icheby_nodes.

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
by rewrite -mul2n mult_INR.
Qed.

Lemma size_Icheby_nodes n v2n: size (Icheby_nodes n v2n) = n.
Proof. by rewrite size_Iilist. Qed.

Lemma Icheby_nodes_correct n v2n i:
   (2 * INR n)%R \contained_in v2n ->
   (cheby_nodes n)`_ i \contained_in nth I0 (Icheby_nodes n v2n) i.
Proof.
move=> v2nD.
have [nLi|iLn] := leqP n i.
	rewrite !nth_default; first by exact: I0_correct.
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
  [seq div2
         (add (add (mul (sub (FtoI b) (FtoI a)) i) (FtoI a)) (FtoI b))
         | i <- Icheby_nodes n v2n].

Lemma size_Ischeby_nodes a b n v2n : size (Ischeby_nodes a b n v2n) = n.
Proof. by rewrite size_map size_Icheby_nodes. Qed.

Lemma Ischeby_nodes_correct a b n v2n i :
  (2 * INR n)%R \contained_in v2n -> F.real a -> F.real b ->
	(scheby_nodes (D2R a) (D2R b) n)`_ i
     \contained_in nth I0 (Ischeby_nodes a b n v2n) i.
Proof.
move=> v2nD aF bF.
have [nLi|iLn] := leqP n i.
	rewrite !nth_default; first exact: I0_correct.
		by rewrite size_scheby_nodes.
	by rewrite size_map size_Icheby_nodes.
rewrite (nth_map I0); last by rewrite size_Icheby_nodes.
rewrite (nth_map 0%R) /Rdiv; last by rewrite size_cheby_nodes.
apply/div2_correct/add_correct; last by apply: FtoI_correct.
apply add_correct; last by apply: FtoI_correct.
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
	(size l <= n.+1)%nat ->
  CPoly (map (dsprod_coef (Poly l) n) (iota 0 n.+1)) = CPoly (P2CP l).
Proof.
move => ineq.
rewrite P2CP_spec; last first.
  by rewrite unitfE; apply /eqP; rewrite natr_INR; toR; lra.
rewrite /CPoly size_map size_iota.
under eq_bigr ? rewrite (nth_map 0%nat); last by rewrite size_iota.
under eq_bigr ? rewrite nth_iota.
rewrite -dsprod_cheby_eq //.
by apply /leq_trans; first exact/ size_Poly.
Qed.

Definition cheby_coefs n j :=
   ((if j == 0%nat then 1 else 2%R) / INR (n.+1))%R *
        \sum_(i < n.+1) (value_list n.+1)`_i * (Tvalue_list n.+1 j)`_i.

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
rewrite -P2CP_spec; last first.
  by rewrite unitfE; apply /eqP; rewrite natr_INR; toR; lra.
rewrite -(@dsprod_coef_P2CP _ n); last first.
  by rewrite -{2}[n.+1](size_cheby_nodes) interpolation_size.
f_equal; apply (@eq_from_nth _ 0%RR) => [ | i]; first by rewrite !size_map.
rewrite size_map size_iota => ineq.
rewrite !(nth_map 0%nat); try by rewrite size_iota.
rewrite !nth_iota // dsprod_coefs //.
by f_equal; rewrite [RHS]polyseqK.
Qed.
End cheby_coefs.

Definition Ienv f a b F :=
	forall x I,
    (a <= x <= b)%R -> x \contained_in I -> (f x) \contained_in (F I).

Notation "F \is_envelope_of f":= (Ienv f (-1) 1 F) (at level 70).

Notation "F \is_envelope_of[ a , b ] f":=
  (Ienv f (D2R a) (D2R b) F) (at level 70).

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
rewrite (nth_map I0) ?size_Icheby_nodes //; last first.
apply: env; last by exact: Icheby_nodes_correct.
suff : (-1 < (cheby_nodes n)`_i < 1)%R by lra.
apply: cheby_nodes_bound.
by apply: mem_nth; rewrite size_cheby_nodes.
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
  (forall i, (i < size l1)%nat -> 
    (cheby_nodes n)`_(m + i) \contained_in nth I0 l1 i) ->
  (forall i, (i < size l2)%nat -> 
    (pT _ k).[(cheby_nodes n)`_(m + i)] \contained_in nth I0 l2 i) ->
  (forall i, (i < size l3)%nat -> 
    (pT _ k.+1).[(cheby_nodes n)`_(m + i)] \contained_in nth I0 l3 i) ->
  (forall i, (i < size (IT3values l1 l2 l3))%nat ->
    (pT _ k.+2).[(cheby_nodes n)`_(m + i)] \contained_in 
                     nth I0 (IT3values l1 l2 l3) i).
Proof.
elim: l1 l2 l3 m k => // a l1 IH  [|b l2] // [|c l3] 
                      //= m k [] Hs2 [] Hs3 Hl1 Hl2 Hl3 [|i] /= H.
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
  (forall i, (i < size l1)%nat -> 
       (cheby_nodes n)`_i \contained_in nth I0 l1 i) ->
  (forall i, (i < size l2)%nat -> 
       (pT _ k).[(cheby_nodes n)`_i] \contained_in nth I0 l2 i) ->
  (forall i, (i < size l3)%nat -> 
       (pT _ k.+1).[(cheby_nodes n)`_i] \contained_in nth I0 l3 i) ->
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

Lemma Isum_correct n a b c d g G (l1 l2 : seq R) Il1 Il2:
  (forall x y X Y,
     (a <= x <= b)%R -> (c <= y <= d)%R -> x \contained_in X -> 
         y \contained_in Y
      -> g x y \contained_in G X Y) ->
  size l1 = n -> size l2 = n ->
  size Il1 = n -> size Il2 = n ->
  (forall i, (i < n)%nat -> nth 0 l1 i \contained_in nth I0 Il1 i) ->
  (forall i, (i < n)%nat -> nth 0 l2 i \contained_in nth I0 Il2 i) ->
  (forall i, (i < n)%nat -> (a <= nth 0 l1 i <= b)%R) ->
  (forall i, (i < n)%nat -> (c <= nth 0 l2 i <= d)%R) ->
  (\sum_(i < n) (g (nth 0 l1 i) (nth 0 l2 i)))
      \contained_in (Isum G Il1 Il2).
Proof.
move=> H; elim: l1 l2 Il1 Il2 n =>
   [|a1 l1 IH] [|b1 l2] [|A1 Il1] [|B1 Il2] [|n] //.
  move=> _ _ _ _ _ _ _ _.
  by rewrite big_ord0; apply: I0_correct.
move=> [sl1] [sl2] [sIl1] [sIl2] Cl1 Cl2 Inl1 Inl2.
rewrite big_ord_recl /=.
apply: add_correct.
  apply: H.
  - by apply: (Inl1 0%nat).
  - by apply: (Inl2 0%nat).
  - by have /= := Cl1 0%nat; apply.
  by have /= := Cl2 0%nat; apply.
apply: IH => // i Hi; first by apply: (Cl1 i.+1).
- by apply: (Cl2 i.+1).
- by apply: (Inl1 i.+1).
by apply: (Inl2 i.+1).
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
  apply: div_correct; last first.
  - by apply: I.fromZ_correct.
  apply: div_correct => //.
  apply: mul_correct.
    by apply: I.fromZ_correct.
  have ->: s =
      \sum_(i < n.+1)
        f ((cheby_nodes n.+1)`_i) * (Tvalue_list n.+1 0)`_i.
    apply: eq_bigr => i _; congr (_ * _).
    by rewrite (nth_map 0) // size_cheby_nodes.
  apply: (@Isum_correct n.+1 (-1) (1) (-1) (1)
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
  - move=> x y X Y Ix Iy Hx Hy; apply: mul_correct => //.
    by apply: env.
  - by rewrite size_cheby_nodes.
  - by rewrite size_map size_iota.
  - by rewrite vl1D size_Icheby_nodes.
  - rewrite size_size_ITvalues //.
      by rewrite v1D size_nseq.
    by rewrite vl1D size_Icheby_nodes.
  - move=> i Hi; rewrite vl1D.
    by apply: Icheby_nodes_correct.
  - move=> i Hi.
    rewrite Tvalue_list_correct // -mu_cheby_nodes //.
    by apply: ITvalues_correct vl1D _ _.
  - move=> i Hi.
    suff : (-1 < nth 0 (cheby_nodes n.+1) i < 1)%R by lra.
    apply: cheby_nodes_bound.
    by apply: mem_nth; rewrite size_cheby_nodes.
  - move=> i Hi.
    by rewrite Tvalue_list_correct //= pT0 hornerE; toR; lra.
set u := (_ * _)%RR.
have {u}->: (u = (2 * s) / INR n.+1)%R.
  rewrite /u; set v := INR _.
  toR; rewrite /u /=.
  by field; apply: (not_INR _ 0).
have -> : forall a b, nth I0 (a ::  b) j.+1 = nth I0 b j by [].
rewrite (nth_map [::]); last first.
  by rewrite -ltnS  -[(size l).+1]/(size (a :: l)) -E size_ITvalue.
apply: div_correct => //.
apply: mul_correct.
  by apply: I.fromZ_correct.
have ->: s =
    \sum_(i < n.+1)
        f ((cheby_nodes n.+1)`_i) * (Tvalue_list n.+1 j.+1)`_i.
  apply: eq_bigr => i _; congr (_ * _).
  by rewrite (nth_map 0) // size_cheby_nodes.
apply: (@Isum_correct n.+1 (-1) 1 (-1) (1)
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
- move=> x y X Y Ix Iy Hx Hy; apply: mul_correct => //.
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
- move=> i Hi.
  rewrite Tvalue_list_correct // -mu_cheby_nodes //.
  rewrite -[nth [::] l j]/(nth [::] (a :: l) j.+1) -E.
  by apply: ITvalues_correct vl1D _ _.
- move=> i Hi.
  suff : (-1 < nth 0 (cheby_nodes n.+1) i < 1)%R by lra.
  apply: cheby_nodes_bound.
  by apply: mem_nth; rewrite size_cheby_nodes.
move=> i Hi.
rewrite Tvalue_list_correct //= -CPoly_trigo.pT_Cheby.
  apply: COS_bound.
suff : (-1 < (cheby_nodes n.+1)`_i < 1)%R by toR; lra.
apply: cheby_nodes_bound.
by apply: mem_nth; rewrite size_cheby_nodes.
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
	a != b -> scheby_coefs n j = 
            sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n j.
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
suff eq: forall i, (i < n.+1)%nat -> 
      (scheby_coef_list n.+1)`_i = 
       sdsprod_coef a b (interpolation f (scheby_nodes a b n.+1)) n i.
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
Hypothesis env: If \is_envelope_of[a, b] f.

Definition Isvalue_list n v2n := [seq If i | i <- Ischeby_nodes a b n v2n].


Lemma Isvalue_list_correct n v2n i: (i < n)%nat ->
  (F.cmp a b = Xlt) -> F.real a -> F.real b ->
  (2 * INR n)%R \contained_in v2n ->
  (f (scheby_nodes (D2R a) (D2R b) n)`_i) \contained_in 
              nth I0 (Isvalue_list n v2n) i.
Proof.
move=> iLn aLb aF bF v2nD.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
rewrite (nth_map I0) ?size_Ischeby_nodes //.
apply: env; last by exact: Ischeby_nodes_correct.
apply: scheby_nodes_boundW => //.
by apply: mem_nth; rewrite size_scheby_nodes.
Qed.

Lemma Ischeby_coefs_correct n vn v2n l1 vl1 vl2 vl3 j :
   (F.cmp a b = Xlt) -> F.real a -> F.real b ->
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
move=> aLb aF bF v1D v2nD vnD vl1D -> -> jL.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
rewrite -sdsprod_coefs //; last by apply/eqP; lra.
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
  apply: div_correct; last first.
    by apply: I.fromZ_correct.
  apply: div_correct => //.
  apply: mul_correct.
    by apply: I.fromZ_correct.
  have ->: s =
      \sum_(i < n.+1)
        f ((scheby_nodes (D2R a) (D2R b) n.+1)`_i) * (Tvalue_list n.+1 0)`_i.
    apply: eq_bigr => i _; congr (_ * _).
    by rewrite (nth_map 0) // size_scheby_nodes.
  apply: (@Isum_correct n.+1 (D2R a) (D2R b) (-1) 1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
  - move=> x y Ix Iy X Y Hx Hy; apply: mul_correct => //.
    by apply: env.
  - by rewrite size_scheby_nodes.
  - by rewrite size_map size_iota.
  - by rewrite size_Ischeby_nodes.
  - rewrite size_size_ITvalues //.
      by rewrite v1D size_nseq.
    by rewrite vl1D size_Icheby_nodes.
  - move=> i Hi.
    by apply: Ischeby_nodes_correct.
  - move=> i Hi.
    rewrite Tvalue_list_correct // -mu_cheby_nodes //.
    by apply: ITvalues_correct vl1D _ _.
  - move=> i Hi.
    apply: scheby_nodes_boundW => //.
    by apply: mem_nth; rewrite size_scheby_nodes.
  move=> i Hi.
  rewrite Tvalue_list_correct //= -CPoly_trigo.pT_Cheby.
    by apply: COS_bound.
  suff : (-1 < (cheby_nodes n.+1)`_i < 1)%R by toR; lra.
  apply: cheby_nodes_bound.
  by apply: mem_nth; rewrite size_cheby_nodes.
set u := (_ * _)%RR.
have {u}->: (u = (2 * s) / INR n.+1)%R.
  rewrite /u; set v := INR _.
  toR; rewrite /u /=.
  by field; apply: (not_INR _ 0).
have -> : forall a b, nth I0 (a ::  b) j.+1 = nth I0 b j by [].
rewrite (nth_map [::]); last first.
  by rewrite -ltnS  -[(size l).+1]/(size (a1 :: l)) -E size_ITvalue.
apply: div_correct => //.
apply: mul_correct.
  by apply: I.fromZ_correct.
have ->: s =
    \sum_(i < n.+1)
        f ((scheby_nodes (D2R a) (D2R b) n.+1)`_i) * (Tvalue_list n.+1 j.+1)`_i.
  apply: eq_bigr => i _; congr (_ * _).
  by rewrite (nth_map 0) // size_scheby_nodes.
apply: (@Isum_correct n.+1 (D2R a) (D2R b) (-1) 1
            (fun x y =>  f x * y)
            (fun x y =>  mul (If x)  y)) => //.
- move=> x y X Y Ix Iy Hx Hy; apply: mul_correct => //.
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
- move=> i Hi.
  rewrite Tvalue_list_correct // -mu_cheby_nodes //.
  rewrite -[nth [::] l j]/(nth [::] (a1 :: l) j.+1) -E.
  by apply: ITvalues_correct vl1D _ _.
- move=> i Hi.
  apply: scheby_nodes_boundW => //.
  by apply: mem_nth; rewrite size_scheby_nodes.
move=> i Hi.
rewrite Tvalue_list_correct //= -CPoly_trigo.pT_Cheby.
  by apply: COS_bound.
suff : (-1 < (cheby_nodes n.+1)`_i < 1)%R by toR; lra.
apply: cheby_nodes_bound.
by apply: mem_nth; rewrite size_cheby_nodes.
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
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  cms_correct n a b f c ->
  (x \contained_in X) -> (I.subset X (I.bnd a b)) ->
  f x \contained_in add (IsCshaw (I.bnd a a) (I.bnd b b) P X) Delta.
Proof.
case: c => P Delta aLb aF bF; case => SP [p [Sp pIP fE]] xIX XS.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have [] := fE x.
  have := subset_contains _ _ (I.subset_correct _ _ XS).
  by apply.
move=> y [Hy ->].
apply: add_correct => //.
apply: IsCshaw_correct => //.
- by rewrite SP.
- by apply: FtoI_correct.
by apply: FtoI_correct.
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
(* Error Chebyshev model                                                     *)
(*****************************************************************************)

Definition error_cms n := CMS (nseq n.+1 I0) (I.bnd F.nan F.nan).

Lemma error_cms_correct n a b f :
   cms_correct n a b f (error_cms n).
Proof.
split; first by rewrite /= size_nseq.
exists (nseq n.+1 0); split => //.
- by rewrite /= size_nseq.
- move=> [|i].
    rewrite /= I.F'.valid_lb_zero I.F'.valid_ub_zero /= F.zero_correct.
    by toR; lra.
  by rewrite !nth_nseq; case: leqP => _; apply: I0_correct.
move=> y Hy; exists (f y); split.
  rewrite /= I.F'.valid_lb_nan I.F'.valid_ub_nan /=.
  by rewrite I.F'.nan_correct.
rewrite horner_CPolyab [CPoly _]big1 ?hornerE // => i _.
rewrite nth_nseq ifT ?scale0r //.
by have := ltn_ord i; rewrite {2}size_nseq.
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
  by rewrite !nth_nseq; case: leqP => _; apply: I0_correct.
move=> y Hy; exists 0; split; first by apply: I0_correct.
rewrite /CPolyab /= big_ord_recl big1 => [|i Hi] /=.
  by rewrite !hornerE horner_comp pT0 hornerE mulr1.
by rewrite nth_nseq if_same scale0r.
Qed.

Definition constZ_cms n z := const_cms n (I.fromZ prec z).

Lemma constZ_cms_correct n a b z :
   cms_correct n a b (fun _ => (IZR z)) (constZ_cms n z).
Proof. by apply/const_cms_correct/I.fromZ_correct. Qed.

(*****************************************************************************)
(* Variable Chebyshev model                                                  *)
(*****************************************************************************)

Definition var_cms a b n :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
   CMS (div2 (add Ia Ib) :: div2 (sub Ib Ia) :: nseq n.-1 I0) I0.

Lemma var_cms_correct n a b :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n.+1 a b (fun x => x) (var_cms a b n.+1).
Proof.
move=> aLb aF bF.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
split; first by rewrite /= size_nseq.
exists ((D2R a + D2R b) / 2 :: (D2R b - D2R a) / 2 :: nseq n 0)%R; split => //.
- by rewrite /= size_nseq.
- move=> [|[|i]].
  - by apply/div2_correct/add_correct; apply: FtoI_correct.
  - by apply/div2_correct/sub_correct; apply: FtoI_correct.
  rewrite [_ `_ _]nth_nseq [nth _ _ _]nth_nseq !if_same.
  by apply: I0_correct.
move=> y Hy; exists 0; split; first by apply: I0_correct.
rewrite /CPolyab /= !big_ord_recl big1 => [|i Hi] /=.
  rewrite !hornerE !horner_comp pT0 pT1 !hornerE /=.
  toR; rewrite /Rinvx ifT; last by apply/eqP; have/eqP:= F2; lra.
  by field; have/eqP:= F2; lra.
by rewrite nth_nseq if_same scale0r.
Qed.

(*****************************************************************************)
(* Opposite Chebyshev model                                                  *)
(*****************************************************************************)

Definition Iopp_Cpoly l := [seq I.neg i | i <- l].

Lemma size_Iopp_Cpoly P : size (Iopp_Cpoly P) = size P.
Proof. by rewrite size_map. Qed.

Lemma Iopp_Cpoly_correct p1 P1 :
  size p1 = size P1 ->
  p1 \lcontained_in P1 ->
  opp_Cpoly p1 \lcontained_in Iopp_Cpoly P1.
Proof.
elim: p1 P1 => [[|A P1]| a p1 IH [|b p2] Sp1 H1 [|i]] //.
  by apply: neg_correct (H1 0%nat).
apply: IH; first by case: Sp1.
by move=> i1; apply: (H1 i1.+1).
Qed.

Definition opp_cms (c : cms) :=
  let: CMS P Delta := c in
  CMS (Iopp_Cpoly P) (I.neg Delta).

Lemma opp_cms_correct n a b c f :
   cms_correct n a b f c ->
   cms_correct n a b (fun x => -(f x))%R (opp_cms c).
Proof.
case: c => [P Delta] [Sp [p [H1p H2p H3p]]].
split; first by rewrite size_map.
exists (opp_Cpoly p); split; first by rewrite size_map.
  by apply: Iopp_Cpoly_correct; rewrite ?Sp.
move=> x /H3p [d [H1d H2d]]; exists (- d); split => //.
  by apply: neg_correct.
rewrite horner_CPolyab opp_Cpoly_spec hornerE -horner_CPolyab.
rewrite H2d; toR; lra.
Qed.


(*****************************************************************************)
(* Addition Chebyshev model                                                  *)
(*****************************************************************************)

Fixpoint Iadd_Cpoly l1 l2 :=
  if l1 is a :: l3 then
    if l2 is b :: l4 then add a b :: Iadd_Cpoly l3 l4
    else l1
  else l2.

Lemma size_Iadd_Cpoly P1 P2 :
  size (Iadd_Cpoly P1 P2) = maxn (size P1) (size P2).
Proof.
elim: P1 P2 => [P2|a P1 IH [|b P2]] /=; first by rewrite max0n.
  by rewrite maxn0.
by rewrite IH maxnSS.
Qed.

Notation "l '\lcontained_in' L" :=
 (forall i,  l`_i \contained_in nth I0 L i) (at level 20).

Lemma Iadd_Cpoly_correct  p1 p2 P1 P2 :
  size p1 = size P1 -> size p2 = size P2 ->
  p1 \lcontained_in P1 ->
  p2 \lcontained_in P2 ->
  add_Cpoly p1 p2 \lcontained_in Iadd_Cpoly P1 P2.
Proof.
elim: p1 p2 P1 P2 => [[|b p2] [|A P1] [|B P2]|
                      a p1 IH [|b p2] [|A P1] [|B P2] Sp1 Sp2 H1 H2 [|i]] //.
- by apply: add_correct (H1 0%nat) (H2 0%nat).
apply: IH; first by case: Sp1.
- by case: Sp2.
- by move=> i1; apply: (H1 i1.+1).
by move=> i1; apply: (H2 i1.+1).
Qed.

Definition add_cms (c1 c2 : cms) :=
  let: CMS P1 Delta1 := c1 in
  let: CMS P2 Delta2 := c2 in
  CMS (Iadd_Cpoly P1 P2) (add Delta1 Delta2).

Lemma add_cms_correct n a b c1 c2 f1 f2 :
   cms_correct n a b f1 c1 -> cms_correct n a b f2 c2 ->
   cms_correct n a b (fun x => f1 x + f2 x)%R (add_cms c1 c2).
Proof.
case: c1 => [P1 Delta1] [Sp1 [p1 [H1p1 H2p1 H3p1]]].
case: c2 => [P2 Delta2] [Sp2 [p2 [H1p2 H2p2 H3p2]]].
split; first by rewrite size_Iadd_Cpoly Sp1 Sp2 maxnn.
exists (add_Cpoly p1 p2); split.
- by rewrite size_add_Cpoly H1p1 H1p2 maxnn.
- apply: Iadd_Cpoly_correct => //.
    by rewrite H1p1 Sp1.
  by rewrite H1p2 Sp2.
move=> x Hx.
have  [d1 [H1d1 H2d1]] := H3p1 _ Hx.
have  [d2 [H1d2 H2d2]] := H3p2 _ Hx.
exists (d1 + d2); split => //.
  by apply: add_correct.
rewrite horner_CPolyab add_Cpoly_spec hornerE.
rewrite -!horner_CPolyab ?H1p1 ?H1p2 //.
by rewrite H2d1 H2d2 hornerE; toR; lra.
Qed.

(*****************************************************************************)
(* Scaling                                                                   *)
(*****************************************************************************)

Fixpoint Iscal_Cpoly k l :=
  if l is a :: l1 then mul k a :: Iscal_Cpoly k l1 else [::].

Lemma size_Iscal_Cpoly k P : size (Iscal_Cpoly k P) = size P.
Proof. by elim: P => //= _ l ->. Qed.

Lemma Iscal_Cpoly_correct  k p K P :
  size p = size P ->
  k \contained_in K ->
  p \lcontained_in P ->
  scal_Cpoly k p \lcontained_in Iscal_Cpoly K P.
Proof.
move=> sH kCK.
elim: p P sH => [|a p]; first by case.
move=> IH [|A P] //= [] sH sI [|i] /=.
  apply: mul_correct => //.
  by apply: (sI 0%nat).
apply: IH => // j.
by apply: (sI j.+1).
Qed.

(*****************************************************************************)
(* Subtraction Chebyshev model                                               *)
(*****************************************************************************)

Fixpoint Isub_Cpoly l1 l2 :=
  if l1 is a :: l3 then
    if l2 is b :: l4 then sub a b :: Isub_Cpoly l3 l4
    else l1
  else [seq I.neg i | i <- l2].

Lemma size_Isub_Cpoly P1 P2 :
  size (Isub_Cpoly P1 P2) = maxn (size P1) (size P2).
Proof.
elim: P1 P2 => [P2|a P1 IH [|b P2]] /=; first by rewrite size_map max0n.
  by rewrite maxn0.
by rewrite IH maxnSS.
Qed.

Lemma Isub_Cpoly_correct  p1 p2 P1 P2 :
  size p1 = size P1 -> size p2 = size P2 ->
  p1 \lcontained_in P1 ->
  p2 \lcontained_in P2 ->
  sub_Cpoly p1 p2 \lcontained_in Isub_Cpoly P1 P2.
Proof.
elim: p1 p2 P1 P2 => [[|b p2] [|A P1] [|B P2]|
                      a p1 IH [|b p2] [|A P1] [|B P2] Sp1 Sp2 H1 H2 [|i]] //.
- move=> _ Sp2 _ H [|i] /=.
    by apply/neg_correct/(H 0%nat).
- apply: Iopp_Cpoly_correct; first by case: Sp2.
  by move=> i1; apply: (H i1.+1).
- by apply: sub_correct (H1 0%nat) (H2 0%nat).
apply: IH; first by case: Sp1.
- by case: Sp2.
- by move=> i1; apply: (H1 i1.+1).
by move=> i1; apply: (H2 i1.+1).
Qed.

Definition sub_cms (c1 c2 : cms) :=
  let: CMS P1 Delta1 := c1 in
  let: CMS P2 Delta2 := c2 in
  CMS (Isub_Cpoly P1 P2) (sub Delta1 Delta2).

Lemma sub_cms_correct n a b c1 c2 f1 f2 :
   cms_correct n a b f1 c1 -> cms_correct n a b f2 c2 ->
   cms_correct n a b (fun x => f1 x - f2 x)%R (sub_cms c1 c2).
Proof.
case: c1 => [P1 Delta1] [Sp1 [p1 [H1p1 H2p1 H3p1]]].
case: c2 => [P2 Delta2] [Sp2 [p2 [H1p2 H2p2 H3p2]]].
split; first by rewrite size_Isub_Cpoly ?Sp1 ?Sp2 maxnn.
exists (sub_Cpoly p1 p2); split.
- by rewrite size_sub_Cpoly H1p1 H1p2 maxnn.
- by apply: Isub_Cpoly_correct; rewrite ?Sp1 ?Sp2.
move=> x Hx.
have  [d1 [H1d1 H2d1]] := H3p1 _ Hx.
have  [d2 [H1d2 H2d2]] := H3p2 _ Hx.
exists (d1 - d2); split => //.
  by apply: sub_correct.
rewrite horner_CPolyab sub_Cpoly_spec hornerD hornerN ?H1p1 ?H1p2 //.
rewrite -!horner_CPolyab H2d1 H2d2 !hornerE /=; toR; lra.
Qed.

(*****************************************************************************)
(* Eval range  model                                                          *)
(*****************************************************************************)

Definition eval_range_poly (P : seq ID) :=
  if P is p :: P1 then
        foldl (fun x y => add x (mul y Im11)) p P1 else I0.

Lemma eval_range_poly_correct n p P x (a b : D) :
       (F.cmp a b = Xlt)%R -> F.real a -> F.real b ->
       size p = n ->
       size P = n ->
       p \lcontained_in P ->
       x \contained_in (I.bnd a b)  ->
       (\sum_(i < n) p`_i *: 'T^(D2R a, D2R b)_i).[x] \contained_in
      eval_range_poly P.
Proof.
move=> aLb aF bF sp sP pIP xIab.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).  
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
rewrite /eval_range_poly.
case: n P p sP sp pIP => [/= [] // [] // _ _ _ /=|].
  rewrite I.F'.valid_lb_zero I.F'.valid_ub_zero /=.
  by rewrite F.zero_correct /= big_ord0 hornerE; toR; lra.
elim=> [ [//|p1 [|]//] [//|p1p [|]// _ _ pIP]|
   n IH [|p1 [|p2 P]] // [|p1p [|p2p p]]// [] sP [] sp pIP].
  rewrite /CPolyab big_ord1 /= !hornerE horner_comp pT0 hornerE mulr1.
  by apply: (pIP 0%N).
rewrite [_ :: P]lastI big_ord_recr /=.
rewrite (eq_bigr (fun i : 'I_n.+1 =>
      (p1p :: seq.belast p2p p)`_i *: 'T^(D2R a,D2R b)_i)); last first.
  move=> i1 _.
  rewrite lastI nth_rcons size_belast ifT //=.
  by have := ltn_ord i1; rewrite -{2}sp.
rewrite foldl_rcons.
rewrite hornerE.
apply: add_correct; last first.
  rewrite hornerE.
  apply: mul_correct.
    have /= := pIP n.+1.
    by rewrite (last_nth I0) sP.
  rewrite I.bnd_correct; last 2 first. 
    by apply: valid_lb_fromZ.
    by apply: valid_ub_fromZ.
  rewrite /= !F.fromZ_correct //.  
  rewrite horner_comp -CPoly_trigo.pT_Cheby.
    apply: COS_bound.
  apply: Tab_bound => //.
  move: xIab aLb.
  rewrite F.cmp_correct I.bnd_correct /= /D2R.
  - by rewrite !I.F'.real_correct.
  - by apply: I.F'.valid_lb_real.
  by apply: I.F'.valid_ub_real.
apply:  (IH (p1 :: (seq.belast p2 P))) => //=.
- by rewrite size_belast sP.
- by rewrite size_belast sp.
move=> j /=.
case: (leqP n.+1 j) => [nLj|jLn].
  rewrite !nth_default //.
  - by apply: I0_correct.
  - by rewrite /= size_belast sp.
  by rewrite /= size_belast sP.
have := pIP j.
rewrite /= [p2p :: p]lastI [p2 :: P]lastI /=.
by rewrite -!rcons_cons !nth_rcons /= !size_belast sp sP jLn.
Qed.

Definition eval_range_cms (c : cms) :=
  let: CMS P Delta := c in
  add (eval_range_poly P) Delta.

Lemma CPolyabE n (a b : R) p x (sp : size p = n) :
   a != b ->
   (CPolyab a b p).[x] = (\sum_(i < n) p`_i *: 'T^(a,b)_i).[x].
Proof.
move=> aDb.
rewrite horner_CPolyab !horner_sum /= sp.
apply: eq_bigr => j _.
rewrite [LHS]hornerE [RHS]hornerE; congr (_ * _).
rewrite horner_pTab; congr (_.[_]).
rewrite !hornerE -mulr_natl natr_INR //=.
have F : b + - a != 0.
  have := (@subr_eq0 _ b a).
  by toR => ->; rewrite eq_sym.
toR; rewrite /Rinvx ifT //.
by field; apply/eqP.
Qed.

Lemma subset_contained a b i x :
  F.real a -> F.real b -> I.subset i (I.bnd a b) ->
  x \contained_in i -> x \contained_in I.bnd a b.
Proof.
move=> aF bF iH.
case: i iH; rewrite //= => l u H1 H2.
have /containedE[V1 V2 V3 V4 V5] := H2.
move: H1 H2.
rewrite !I.F'.classify_real //.
rewrite !F.cmp_correct /=.
rewrite ![F.classify a]I.F'.classify_real //=.
rewrite ![F.classify b]I.F'.classify_real //=.
case : F.classify V3 => // _.
case : F.classify V4 => // _; rewrite ?andbF //=.
rewrite V1 V2 /= !I.F'.valid_lb_real //= !I.F'.valid_ub_real //=.
by (do 4! case: F.toX => //=);
    try (by move=> r1 r2; case: Raux.Rcompare_spec => //; lra);
    try (by move=> r1 r2 r3; case: Raux.Rcompare_spec => //; lra);
    try (by move=> r1 r2 r3 r4; do! case: Raux.Rcompare_spec => //; lra).
Qed.

Lemma eval_range_cms_correct n a b f c i x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n a b f c ->
   I.subset i (I.bnd a b) ->
   x \contained_in i -> f x \contained_in eval_range_cms c.
Proof.
move=> aLb aF bF.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
case: c => P Delta [Hs [p [H1p H2p H3p]]] Hi Hx.
have Hy : x \contained_in I.bnd a b.
  by apply: subset_contained Hi _.
have [d [H1d ->]] := H3p _ Hy.
rewrite /=.
apply: add_correct => //.
rewrite (CPolyabE _ H1p) //.
by apply: eval_range_poly_correct.
Qed.

Lemma isubset_refl i : I.subset i i.
Proof.
case: i => //= l u; apply/andP; split.
  rewrite F.cmp_correct.
  case E : F.classify => //.
  case E1 : F.toX => //= [|r]; last first.
    by case: Raux.Rcompare_spec; try lra.
  have := F.real_correct l.
  have := F.classify_correct l.
  by rewrite E1 /= E => ->.
rewrite F.cmp_correct.
case E : F.classify => //.
case E1 : F.toX => //= [|r]; last first.
  by case: Raux.Rcompare_spec; try lra.
have := F.real_correct u.
have := F.classify_correct u.
by rewrite E1 /= E => ->.
Qed.

(* Should be something simpler *)
Lemma eval_range_cms_subset n a b c d f cm x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   F.cmp c d = Xlt -> F.real c -> F.real d ->
   cms_correct n a b f cm ->
   I.subset (eval_range_cms cm) (I.bnd c d) ->
   x \contained_in I.bnd a b -> f x \contained_in (I.bnd c d).
Proof.
move=> aLb aF bF cLd cF dF Hc Hi Hx.
have := eval_range_cms_correct aLb aF bF Hc (isubset_refl _) Hx.
by apply: subset_contained.
Qed.

(*****************************************************************************)
(* Multiplication Chebyshev model                                            *)
(*****************************************************************************)

Fixpoint Iabs_mul_Cpoly n (a : ID) acc l :=
 if n is n1.+1 then
   if l is b :: l1 then 
         Iabs_mul_Cpoly n1 a (div2 (mul a b) :: acc) l1
   else (ncons n.+1 I0 acc)
 else  Iadd_Cpoly (I0 :: acc) [seq (div2 (mul a i) ) | i <- l].

Lemma size_Iabs_mul_Cpoly n (a : R) A acc Acc l L :
  size acc = size Acc -> size l = size L ->
  size (Iabs_mul_Cpoly n A Acc L) = size (abs_mul_Cpoly n a acc l).
Proof.
elim: n acc Acc l L => [acc Acc l L H1 H2|n IH acc Acc [|b l] [|B L] H1 H2 //].
- by rewrite size_Iadd_Cpoly size_add_Cpoly /= !size_map H1 H2.
- by rewrite !size_ncons H1.
apply: IH => //=; first by rewrite H1.
by case: H2.
Qed.

Lemma Iabs_mul_Cpoly_correct n a A acc Acc l L :
  size acc = size Acc -> size l = size L ->
  a \contained_in A -> acc \lcontained_in Acc -> l \lcontained_in L ->
  abs_mul_Cpoly n a acc l \lcontained_in Iabs_mul_Cpoly n A Acc L.
Proof.
elim: n acc Acc l L => [acc Acc [|b l] [|B L] H1 H2 H3 H4 H5 i|
                        n IH acc Acc [|b l] [|B L] H1 H2 H3 H4 H5 i] //.
- apply: Iadd_Cpoly_correct => //=; first by rewrite H1.
  move=> [|i1]; first by apply: I0_correct.
  by apply: H4.
- apply: Iadd_Cpoly_correct => //=.
  - by rewrite H1.
  - by rewrite !size_map.
  - move=> [|i1]; first by apply: I0_correct.
    by apply: H4.
  move=> i1.
  have [lLi1|i1Ll] := leqP (size l).+1 i1.
    rewrite /= !nth_default ?size_map -?H2//.
    - by apply: I0_correct.
    - by rewrite /= size_map.
    by rewrite /= size_map; case: H2 => <-.
  pose f b :=  a * b / 2%:R.
  have /=-> := @nth_map _ 0 _ 0 f _ (_ :: _) => //.
  pose F b := div2 (mul A b).
  have /=-> := @nth_map _ I0 _ I0 F _ (_ :: _); last first.
    by case: H2 => <-.
  rewrite (_ :  f _ = (a * (b :: l)`_i1) / 2)%R; last first.
    rewrite /f /=; toR; rewrite /Rinvx ifT //.
    by apply/eqP; toR; lra.
  by apply/div2_correct/mul_correct.
- rewrite !nth_ncons; case: leqP => _ //.
  by apply: I0_correct.
apply: IH => //=.
- by rewrite H1.
- by case: H2.
- move=> [|i1].
    rewrite (_ : _ / _ = ((a * b) / 2)%R); last first.
      rewrite /=; toR; rewrite /Rinvx ifT; first by field.
      by apply/eqP; lra.
    apply/div2_correct/mul_correct => //.
    by apply: H5 0%nat.
  by apply: H4 i1.
by move=> i1; apply: H5 i1.+1.
Qed.

Definition Iadd_mul_Cpoly n (a : ID) l :=
  ncons n I0 [seq div2 (mul a i) | i <- l].

Lemma size_Iadd_mul_Cpoly n (a : R) A l L :
  size l = size L ->
  size (Iadd_mul_Cpoly n A L) = size (add_mul_Cpoly n a l).
Proof.
by move=> H; rewrite !size_ncons !size_map H.
Qed.

Lemma Iadd_mul_Cpoly_correct n a A l L :
  size l = size L ->
  a \contained_in A -> l \lcontained_in L ->
  add_mul_Cpoly n a l \lcontained_in Iadd_mul_Cpoly n A L.
Proof.
move=> Hs Ha Hl i.
rewrite !nth_ncons; case: leqP => H; last by apply: I0_correct.
have [lLi1|i1Ll] := leqP (size l) (i - n)%nat.
  rewrite !nth_default ?size_map -?Hs //.
  by apply: I0_correct.
rewrite (nth_map 0) // (nth_map I0) -?Hs //.
rewrite (_ : _ / _ = ((a * l`_(i - n)) / 2)%R); last first.
  rewrite /=; toR; rewrite /Rinvx ifT; first by field.
  by apply/eqP; lra.
by apply/div2_correct/mul_correct.
Qed.

Fixpoint Imul_rec_Cpoly n l1 l2 :=
  if l1 is a :: l3 then
    let v1 := Iabs_mul_Cpoly n a [::] l2 in
    let v2 := Iadd_mul_Cpoly n a l2 in
    Iadd_Cpoly (Iadd_Cpoly v1 v2) (Imul_rec_Cpoly n.+1 l3 l2)
  else [::].

Lemma size_Imul_rec_Cpoly n (l1 : seq R) l2 L1 L2 :
  size l1 = size L1 -> size l2 = size L2 ->
  size (Imul_rec_Cpoly n L1 L2) = size (mul_rec_Cpoly n l1 l2).
Proof.
elim: l1 L1 n => [[|]|a l1 IH [|A L1] n // [H1] H2] //=.
rewrite !size_Iadd_Cpoly !size_add_Cpoly.
rewrite (@size_Iabs_mul_Cpoly _ a _ [::] _ l2) //.
rewrite (@size_Iadd_mul_Cpoly _ a _ l2) //.
by rewrite IH.
Qed.

Lemma Imul_rec_Cpoly_correct n p1 p2 P1 P2 :
  size p1 = size P1 -> size p2 = size P2 ->
  p1 \lcontained_in P1 ->
  p2 \lcontained_in P2 ->
  mul_rec_Cpoly n p1 p2 \lcontained_in Imul_rec_Cpoly n P1 P2.
Proof.
elim: p1 p2 P1 P2 n => [p2 [|A P1] P2 n |
                      a p1 IH p2 [|A P1] P2 n // [Sp1] Sp2 H1 H2] //.
apply: Iadd_Cpoly_correct => //.
- rewrite size_add_Cpoly size_Iadd_Cpoly.
  congr (maxn _ _).
    by apply/sym_equal/size_Iabs_mul_Cpoly.
  by apply/sym_equal/size_Iadd_mul_Cpoly.
apply/sym_equal/size_Imul_rec_Cpoly => //.
  apply: Iadd_Cpoly_correct.
  - by apply/sym_equal/size_Iabs_mul_Cpoly.
  - by apply/sym_equal/size_Iadd_mul_Cpoly.
  - apply: Iabs_mul_Cpoly_correct => //.
      by apply: H1 0%nat.
    by move=> i; rewrite !nth_nil; apply: I0_correct.
  apply: Iadd_mul_Cpoly_correct => //.
  by apply: H1 0%nat.
apply: IH => //.
by move=> i; apply: H1 i.+1.
Qed.

Definition Imul_Cpoly (l1 l2 : seq ID) := Imul_rec_Cpoly 0 l1 l2.

Lemma size_Imul_Cpoly (l1 : seq R) l2 L1 L2 :
  size l1 = size L1 -> size l2 = size L2 ->
  size (Imul_Cpoly L1 L2) = size (mul_Cpoly l1 l2).
Proof. exact: size_Imul_rec_Cpoly. Qed.

Lemma Imul_Cpoly_correct p1 p2 P1 P2 :
  size p1 = size P1 -> size p2 = size P2 ->
  p1 \lcontained_in P1 ->
  p2 \lcontained_in P2 ->
  mul_Cpoly p1 p2 \lcontained_in Imul_Cpoly P1 P2.
Proof. exact: Imul_rec_Cpoly_correct. Qed.

Fixpoint Isplit_Cpoly n l :=
  if n is n1.+1 then
    if l is a :: l1 then
        let: (l2,l3) := Isplit_Cpoly n1 l1 in (a :: l2, I0 :: l3)
    else (nseq n I0, [::])
  else ([::], l).

Lemma size_Isplit_Cpoly1 n l : size (Isplit_Cpoly n l).1 = n.
Proof.
elim: n l => //= n IH [|a l] /=; first by rewrite size_nseq.
by case: Isplit_Cpoly (IH l) => /= l1 _ ->.
Qed.

Lemma size_Isplit_Cpoly2 n (l : seq R) L :
 size l = size L ->
 size (Isplit_Cpoly n L).2 = size (split_Cpoly n l).2.
Proof.
elim: n l L => //= n IH [|a l] [|A L] //= [H].
by have := IH l L; case: Isplit_Cpoly => L1 L2; 
   case: split_Cpoly => l1 l2 /= ->.
Qed.

Lemma Isplit_Cpoly_correct1 n (p : seq R) P :
  size p = size P ->
  p \lcontained_in P ->
  (split_Cpoly n p).1 \lcontained_in (Isplit_Cpoly n P).1.
Proof.
elim: n p P => [p P _ _| n IH [|a p] [|A P] H1 H2] //=.
- by move=> i; rewrite !nth_nil; apply: I0_correct.
- move=> i; rewrite !(@nth_nseq _ _ n.+1) !if_same.
  by apply: I0_correct.
case: H1 => /IH; case: split_Cpoly => p1 p2; 
                case: Isplit_Cpoly => P1 P2 /= H [|i].
  by apply: H2 0%nat.
apply: H => i1.
by apply: H2 i1.+1.
Qed.

Lemma Isplit_Cpoly_correct2 n (p : seq R) P :
  size p = size P ->
  p \lcontained_in P ->
  (split_Cpoly n p).2 \lcontained_in (Isplit_Cpoly n P).2.
Proof.
elim: n p P => [p P _ _| n IH [|a p] [|A P] H1 H2] //=.
case: H1 => /IH; case: split_Cpoly => p1 p2;
                 case: Isplit_Cpoly => P1 P2 /= H [|i].
  by apply: I0_correct.
apply: H => i1.
by apply: H2 i1.+1.
Qed.

Definition mul_cms n a b (c1 c2 : cms) :=
  let: CMS P1 Delta1 := c1 in
  let: CMS P2 Delta2 := c2 in
  let: P3 := Imul_Cpoly P1 P2 in
  let: (P4, P5) := Isplit_Cpoly n.+1 P3 in
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Iab := I.bnd a b in
  let Delta3 := eval_range_poly P1  in
  let Delta4 := eval_range_poly P2  in
  let Delta5 := eval_range_poly P5  in
  CMS P4 (add Delta5 (add (mul Delta1 Delta4)
                     (add (mul Delta2 Delta3)
                          (mul Delta1 Delta2)))).

Lemma mul_cms_correct n a b c1 c2 f1 f2 :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n a b f1 c1 -> cms_correct n a b f2 c2 ->
   cms_correct n a b (fun x => f1 x * f2 x)%R (mul_cms n a b c1 c2).
Proof.
move=> aLb aF bF.
have a_in_Ia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have b_in_Ib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
case: c1 => [P1 Delta1] [Sp1 [p1 [H1p1 H2p1 H3p1]]].
case: c2 => [P2 Delta2] [Sp2 [p2 [H1p2 H2p2 H3p2]]].
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
rewrite /cms_correct /mul_cms.
case E : Isplit_Cpoly => [P4 P5].
split.
  by rewrite -[P4]/(P4,P5).1 -E size_Isplit_Cpoly1.
pose p := mul_Cpoly p1 p2.
exists (split_Cpoly n.+1 p).1.
split => //.
- by rewrite split_Cpoly_size1.
- rewrite -[P4]/(P4, P5).1 -E.
  apply: Isplit_Cpoly_correct1.
  by rewrite (@size_Imul_Cpoly p1 p2) ?Sp1 ?Sp2.
- by apply: Imul_Cpoly_correct; rewrite ?Sp1 ?Sp2.
move=> x xIab.
have [d1 [H1d1 H2d1]] := H3p1 _ xIab.
have [d2 [H1d2 H2d2]] := H3p2 _ xIab.
pose sp := split_Cpoly n.+1 p.
pose Cp := CPolyab (D2R a) (D2R b).
exists ((Cp sp.2).[x] + d1 * (Cp p2).[x] +
           d2 * (Cp p1).[x] + d1 * d2).
split.
  rewrite -!addrA.
  apply: add_correct.
    apply: eval_range_poly_correct => //.
      rewrite -[P5]/(P4, P5).2 -E (@size_Isplit_Cpoly2 n.+1 p) //.
      by rewrite (@size_Imul_Cpoly p1 p2) ?Sp1 ?Sp2.
    rewrite -[P5]/(P4, P5).2 -E.
    apply: Isplit_Cpoly_correct2 => //.
      by rewrite (@size_Imul_Cpoly p1 p2) ?Sp1 ?Sp2.
    by apply: Imul_Cpoly_correct; rewrite ?Sp1 ?Sp2.
  apply: add_correct.
    apply: mul_correct => //.
    by apply: eval_range_poly_correct; rewrite ?Sp1 ?Sp2.
  apply: add_correct.
    apply: mul_correct => //.
    by apply: eval_range_poly_correct; rewrite ?Sp1 ?Sp2.
  by apply: mul_correct.
rewrite /Cp H2d1 H2d2 /p /sp -addrA.
set x1 := _.[_]; set x2 := _.[_].
set x3 := _.[_]; set x4 := _.[_].
suff F : x1 * x2 = x3 + x4.
  by move: F; toR => F; ring[F].
rewrite /x1 /x2 /x3 /x4 !horner_CPolyab.
rewrite -hornerM -hornerD -horner_split_Cpoly mul_Cpoly_correct //.
by apply/eqP; toR; lra.
Qed.

(*****************************************************************************)
(* Scale 2  Chebyshev model                                                  *)
(*****************************************************************************)

Definition Iscl2_Cpoly l := [seq scl2 i | i <- l].

Lemma size_Iscl2_Cpoly P : size (Iscl2_Cpoly P) = size P.
Proof. by rewrite size_map. Qed.

Lemma Iscl2_Cpoly_correct  p P :
  size p = size P -> p \lcontained_in P ->
  scl2_Cpoly p \lcontained_in Iscl2_Cpoly P.
Proof.
elim: p P => [[|A P1] | a p1 IH [|A P1] Sp H [|i]] //=.
  by apply: scl2_correct (H 0%nat).
apply: IH; first by case: Sp.
by move=> i1; apply: (H i1.+1).
Qed.

Definition scl2_cms (c: cms) :=
  let: CMS P Delta := c in
  CMS (Iscl2_Cpoly P) (scl2 Delta).

Lemma scl2_cms_correct n a b c f :
   cms_correct n a b f c ->
   cms_correct n a b (fun x => f x *+ 2)%R (scl2_cms c).
Proof.
case: c => [P Delta] [Sp [p [H1p H2p H3p]]].
split; first by rewrite size_Iscl2_Cpoly Sp.
exists (scl2_Cpoly p); split.
- by rewrite size_scl2_Cpoly H1p.
- by apply: Iscl2_Cpoly_correct; rewrite // H1p Sp.
move=> x Hx.
have  [d [H1d H2d]] := H3p _ Hx.
exists (d *+ 2); split => //.
  by apply: scl2_correct.
rewrite horner_CPolyab scl2_Cpoly_spec hornerE hornerMn /=.
rewrite -!horner_CPolyab ?H1p //.
by rewrite H2d mulrnDl [d *+ 2]mulr2n addrA.
Qed.


(*****************************************************************************)
(* Composition Chebyshev model                                               *)
(*****************************************************************************)

Section ICb.

Variable n : nat.
Variables a b : D.

Fixpoint ICb_cms (q : seq ID) (x : cms) : (cms * cms) :=
 if q is c :: q' then
   let t := ICb_cms q' x in
   let a1 := sub_cms (add_cms (const_cms n c) 
                     (mul_cms n a b (fst t) x)) (snd t) in
   (a1, (fst t)) else
   let cm := const_cms n I0 in (cm,cm).

Lemma ICb_cms_correct p P f c :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   p \lcontained_in P ->
   size p = size P ->
   cms_correct n a b f c ->
   cms_correct n a b (fun x => (Cb p (f x)).1) (ICb_cms P c).1
  /\
   cms_correct n a b (fun x => (Cb p (f x)).2) (ICb_cms P c).2.
Proof.
move=> aLb aF bF.
case: c => [P1 Delta1].
elim: p P => [[|//] _ _ H|a1 p IH [|A1 P] // H Hs Hc].
by split; apply/const_cms_correct/I0_correct.
case: (IH P) => [i|||IH1 IH2] //; first by apply: H i.+1.
  by case: Hs.
split => //.
apply: sub_cms_correct => //.
apply: add_cms_correct.
  by apply/const_cms_correct/(H 0%nat).
apply: mul_cms_correct => //.
Qed.

Definition ICshaw_cms p x :=
  let: (i1, i2) := ICb_cms p (scl2_cms x) in sub_cms i1 (mul_cms n a b i2 x).

Lemma ICshaw_cms_correct p P f c :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   p \lcontained_in P ->
   size p = size P ->
   cms_correct n a b f c ->
   cms_correct n a b ((Cshaw p) \o f) (ICshaw_cms P c).
Proof.
move=> aLb aF bF Hp Hs Hc.
have [H1 H2] := ICb_cms_correct aLb aF bF Hp Hs (scl2_cms_correct Hc).
pose k x := (Cb p (f x *+ 2)).1 - (Cb p (f x *+ 2)).2 * f x.
apply: (@cms_correct_ext _ _ _ _ k) => [x Hx |].
  by rewrite /Cshaw /k /=; case: Cb.
rewrite /k /ICshaw_cms.
case: ICb_cms H1 H2 => I1 I2 H1 H2.
apply: sub_cms_correct => //.
by apply: mul_cms_correct.
Qed.

Definition IsCshaw_cms c d p x :=
  let C := I.bnd c c in
  let D := I.bnd d d in
  let cm := I.inv prec (sub D C) in
  let cm1 := scl2 cm in
  let cm2 := mul (add C D) cm in
  let x1 := sub_cms (mul_cms n a b (const_cms n cm1) x) (const_cms n cm2) in
  ICshaw_cms p x1.

Lemma IsCshaw_cms_correct c d p P f cm :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   F.cmp c d = Xlt -> F.real c -> F.real d ->
   (forall x, x \contained_in I.bnd a b -> f x \contained_in (I.bnd c d)) ->
   p \lcontained_in P ->
   size p = size P ->
   cms_correct n a b f cm ->
   cms_correct n a b (fun x => (CPolyab (D2R c) (D2R d) p).[f x]) 
                     (IsCshaw_cms c d P cm).
Proof.
move=> aLb aF bF cLd cF dF HI Hp Hs Hc.
have F1 : (D2R c < D2R d)%R.
  have := F.cmp_correct c d; rewrite cLd.
  rewrite (I.F'.classify_real _ cF) (I.F'.classify_real _ dF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R c != D2R d by apply/eqP; lra.
apply: cms_correct_ext => [x Hx|].
  rewrite horner_CPolyab //.
pose k := (Cshaw p) \o (fun x => (Tab (D2R c) (D2R d)).[f x]).
apply: (@cms_correct_ext _ _ _ _ k) => [x Hx|] //.
  by rewrite /k /= Cshaw_spec //.
apply: ICshaw_cms_correct => //.
apply: cms_correct_ext => [x Hx|].
  rewrite !hornerE mulNr (_ : 1 + 1 = 2%:R); last by toR; ring.
  by rewrite [_/_]mulr_natl.
have Fc : D2R c \contained_in I.bnd c c by apply: FtoI_correct.
have Fb : D2R d \contained_in I.bnd d d by apply: FtoI_correct.
have FF : (D2R d - D2R c)^-1 \contained_in
             I.inv prec (sub (I.bnd d d) (I.bnd c c)).
  rewrite /GRing.inv [_ _  (_ - _)]/= /Rinvx.
  rewrite ifT; last by rewrite subr_eq0 eq_sym.
  by apply/inv_correct/sub_correct.
apply: sub_cms_correct.
  apply: mul_cms_correct => //.
  apply: const_cms_correct.
  by apply: scl2_correct.
apply: const_cms_correct.
apply: mul_correct => //.
by apply: add_correct.
Qed.

End ICb.

Definition eval_shaw_cms a b (c : cms) I :=
  let: CMS P Delta := c in
  add (IsCshaw (I.bnd a a) (I.bnd b b) P I) Delta.

Lemma eval_shaw_cms_correct n a b f c i x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n a b f c ->
   I.subset i (I.bnd a b) ->
   x \contained_in i -> f x \contained_in eval_shaw_cms a b c i.
Proof.
move=> aLb aF bF.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
case: c => P Delta [Hs [p [H1p H2p H3p]]] Hi Hx.
have Hy : x \contained_in I.bnd a b.
  by apply: subset_contained Hx.
have [d [H1d ->]] := H3p _ Hy.
apply: add_correct => //.
have->: (CPolyab (D2R a) (D2R b) p).[x] =
        (\sum_(i < n.+1) p`_i *: 'T^(D2R a, D2R b)_i).[x].
  rewrite horner_CPolyab !horner_sum H1p.
  apply: eq_bigr => j _.
  rewrite [LHS]hornerE [RHS]hornerE; congr (_ * _).
  rewrite horner_pTab; congr (_.[_]).
  rewrite !hornerE -mulr_natl natr_INR //=.
  have F : D2R b + - D2R a != 0.
    have := (@subr_eq0 _ (D2R b) (D2R a)).
    by toR => ->; rewrite eq_sym.
  toR; rewrite /Rinvx ifT //.
  by field; apply/eqP.
by apply: IsCshaw_correct => //; apply: FtoI_correct.
Qed.

(* Should be something simpler *)
Lemma eval_shaw_cms_subset n a b c d f cm x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   F.cmp c d = Xlt -> F.real c -> F.real d ->
   cms_correct n a b f cm ->
   I.subset (eval_shaw_cms a b cm (I.bnd a b)) (I.bnd c d) ->
   x \contained_in I.bnd a b -> f x \contained_in (I.bnd c d).
Proof.
move=> aLb aF bF cLd cF dF Hc Hi Hx.
have := eval_shaw_cms_correct aLb aF bF Hc (isubset_refl _) Hx.
by apply: subset_contained.
Qed.

Definition eval_cms a b (c : cms) I :=
  I.meet (eval_shaw_cms a b c I) (eval_range_cms c).

Lemma eval_cms_correct n a b f c i x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n a b f c ->
   I.subset i (I.bnd a b) ->
   x \contained_in i -> f x \contained_in eval_cms a b c i.
Proof.
move=> aLb aF bF cmsC iSab xIi.
apply: I.meet_correct.
  apply: eval_shaw_cms_correct cmsC _ _ => //.
by apply: eval_range_cms_correct cmsC iSab _.
Qed.

(* Should be something simpler *)
Lemma eval_cms_subset n a b c d f cm x :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   F.cmp c d = Xlt -> F.real c -> F.real d ->
   cms_correct n a b f cm ->
   I.subset (eval_cms a b cm (I.bnd a b)) (I.bnd c d) ->
   x \contained_in I.bnd a b -> f x \contained_in (I.bnd c d).
Proof.
move=> aLb aF bF cLd cF dF Hc Hi Hx.
have := eval_cms_correct aLb aF bF Hc (isubset_refl _) Hx.
by apply: subset_contained.
Qed.

Definition comp_cms n a b c d (c1 c2 : cms) :=
  let: CMS P2 Delta2 := c2 in
  let: CMS P  Delta := IsCshaw_cms n a b c d P2 c1 in
  CMS P (add Delta Delta2).

Lemma comp_cms_correct n a b c d f1 f2 c1 c2 :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   F.cmp c d = Xlt -> F.real c -> F.real d ->
   I.subset (eval_range_cms c1) (I.bnd c d) ->
   cms_correct n a b f1 c1 ->
   cms_correct n c d f2 c2 ->
   cms_correct n a b (f2 \o f1) (comp_cms n a b c d c1 c2).
Proof.
move=> aLb aF bF cLd cF dF.
case: c2 => [P2 Delta2] Hs Hc1 [Sp2 [p2 [H1p2 H2p2 H3p2]]].
have Hsp2 : size p2 = size P2 by rewrite Sp2 H1p2.
have F x:
  x \contained_in I.bnd a b -> f1 x \contained_in I.bnd c d.
  move=> Hx.
  by apply: eval_range_cms_subset Hc1 Hs Hx.
have := IsCshaw_cms_correct aLb aF bF cLd cF dF F H2p2 Hsp2 Hc1.
rewrite /comp_cms.
case: IsCshaw_cms => P3 Delta3 [H1P3 [p3 [H1p3 H2p3 H3p3]]].
split => //.
exists p3; split => // x Hx.
have [d3 [H1d3 H2d3]] := H3p3 x Hx.
have F1 : (f1 x) \contained_in I.bnd c d.
  by apply: eval_range_cms_subset Hc1 _ _.
have [d2 [H1d2 H2d2]] := H3p2 _ F1.
exists (d3 + d2); split; first by apply: add_correct.
rewrite [_ x]H2d2 H2d3; toR; ring.
Qed.

Section CMSin.

Variable (a b : D).

(*****************************************************************************)
(* Derivative of sin for interval arithmetic                                 *)
(*****************************************************************************)

Lemma sin_env a1 b1 : I.sin prec \is_envelope_of[a1, b1] sin.
Proof.  by move=> *; exact: sin_correct. Qed.

Fixpoint bsin b x := if b then cos x else sin x.

Definition Ibsin b J := if b then I.cos prec J else I.sin prec J.

Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

Lemma Ibsin_correct a1 b1 n:
 (Ibsin (odd n)) \is_envelope_of[a1, b1]
      (fun x => (-1) ^ (odd n./2) * sin^(n) x)%R.
Proof.
move=> x X Ix Hx.
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
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Iab := I.bnd a b in
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
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  b1 = odd n ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  zn = Pos.of_nat n.+1 ->
  z2n = Pos.of_nat n.*2.+1 ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b sin (sin_cms n b1 vn zn z2n vl2 vl3).
Proof.
move=> aLb aF bF b1E vnE v2nE znE z2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
have Hiab x : (D2R a <= x <= D2R b)%R -> x \contained_in I.bnd a b.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  (do 2 case: F.toX) => //= r1; lra.
have Hiabr x : (F.cmp a b = Xlt) -> (x \contained_in I.bnd a b) -> 
                   (D2R a <= x <= D2R b)%R.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.                   
  rewrite /= F.cmp_correct /D2R !I.F'.classify_real //=.
  by (do 2 case: F.toX).
pose iv := interpolation sin (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /sin_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) sin n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.sin prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: sin_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (sin x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by(do 2 case: F.toX).
apply: Rabs_join.
have [/csign_correct H|_] := boolP (csign _).
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: sin_scheby_ge => //.
    case: H => H.
      right => x1 /Hiab Hx1.
      apply: H.
      rewrite /Ibsin b1E; case: odd.
        by apply: cos_correct.
      by apply: sin_correct.
    left => x1 /Hiab Hx1.
    apply: H.
    rewrite /Ibsin b1E; case: odd.
      by apply: cos_correct.
    by apply: sin_correct.
  rewrite /Rmax; case: Rle_dec => _.
    apply: I.join_correct.
    right.
    apply/abs_correct/sub_correct.
      by apply/sin_correct/Hib.
    rewrite -scheby_coef_list_spec //.
    apply: IsCshaw_correct => //.
    by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
  apply: I.join_correct.
  left.
  apply/abs_correct/sub_correct.
    by apply/sin_correct/Hia.
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
apply: div_correct => //.
  apply: mul_correct.
    rewrite /v expr_Rexp znE.
    apply: power_pos_correct => //.
    by apply: sub_correct.
  apply: Rabs_I01_max => [||z Hz].
  - suff: (D2R a) \contained_in I.bnd a b by apply.
    by apply: Hiab; lra.
  - move=> y YC.
    apply: abs_correct.
    rewrite b1E.
    apply: (Ibsin_correct n.+1) => //.
    by apply: Hiabr.
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
  have /Hz : y \contained_in I.bnd a b by apply: Hiab.
  rewrite Derive_n_sin -[odd n.+1]/(~~ odd n).
  case: (odd n).
    rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
    case: odd => /=.
      by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse)
                   Ropp_involutive !Rmult_1_l.
    by rewrite !Rmult_1_l.
  rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
  case: odd => /=.
    by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) 
                 Ropp_involutive !Rmult_1_l.
  by rewrite !Rmult_1_l.
rewrite [e]natr_INR mult_INR.
apply: mul_correct.
  rewrite -pow_expn pow_INR z2nE.
  apply: power_pos_correct => //.
  have -> : (INR 2) = IZR 2 by [].
  by apply: I.fromZ_correct.
by apply: Ifact_correct.
Qed.

End CMSin.

Section CMAtan.

Variable (a b : D).

(*****************************************************************************)
(* Derivative of atan for interval arithmetic                                *)
(*****************************************************************************)

Lemma atan_env a1 b1 : I.atan prec \is_envelope_of[a1, b1] atan.
Proof.  by move=> *; exact: atan_correct. Qed.

(*****************************************************************************)
(* Error of atan                                                             *)
(*****************************************************************************)

Fixpoint Ieval_atan_rec m mZ (bv : bool) (iZ jZ : Z) (xI xI2 resI : ID) := 
  if m is m1.+2 then
  let iZ1 := (iZ + 2)%Z in 
  let jZ1 := ((jZ * mZ  / iZ1) * (mZ - 1) / (iZ1 + 1))%Z in
  let res1 := (I.add prec (I.mul prec resI xI2)
                   (if bv then I.neg (I.fromZ prec jZ1) 
                          else I.fromZ prec jZ1)) in
  Ieval_atan_rec m1 (mZ - 2)%Z (~~ bv) iZ1 jZ1 xI xI2 res1
  else if m is 1%nat then I.mul prec xI resI else resI.

Definition Ieval_atan m x := 
  let mZ := Z.of_nat m in
  let mZ1 := (mZ + 1)%Z in
  Ieval_atan_rec m mZ true 0%Z mZ1 x (I.sqr prec x) (I.fromZ prec mZ1).

Lemma Ieval_atan_rec_correct m mZ bv i iZ j jZ x xI xI2 res resI :
   mZ = Z.of_nat m ->
   iZ = Z.of_nat i ->
   jZ = Z.of_nat j ->
   x \contained_in xI ->
   (x * x)%RR \contained_in xI2 ->
   res \contained_in resI ->
   eval_atan_rec m bv i j x res
   \contained_in
   Ieval_atan_rec m mZ bv iZ jZ xI xI2 resI.
Proof.
elim/ltn_ind: m mZ bv i iZ j jZ x xI xI2 res resI
   =>  [] [|[|m]] IH //= mZ bv i iZ j jZ x xI xI2 res resI
      mZE iZE jZE xC x2C resC.
  by  apply mul_correct.
have F : 
    Z.of_nat
     (j * m.+2 %/ i.+2 * m.+1 %/ i.+3) =
    ((jZ * mZ / (iZ + 2) * (mZ - 1) /
     (iZ + 2 + 1)))%Z.
  rewrite !(natDivP, Nat2Z.inj_mul, div_Zdiv)  //.
  congr  (_ * _ / _ * _ / _)%Z => //=.
  + by rewrite Pos2Z.inj_succ Zpos_P_of_succ_nat; lia.
  + by rewrite mZE Pos2Z.inj_succ Zpos_P_of_succ_nat; lia.
  by rewrite iZE !(Pos2Z.inj_succ, Zpos_P_of_succ_nat); lia.
apply IH => //.
  + by rewrite mZE Pos2Z.inj_succ Zpos_P_of_succ_nat; lia.
  + by rewrite iZE /= Pos2Z.inj_succ Zpos_P_of_succ_nat; lia.
apply: add_correct.
  rewrite Rmult_assoc.
  by apply: mul_correct.
rewrite -IZR_Zof_nat F.
case: bv.
  rewrite -Ropp_mult_distr_l Rmult_1_l.
  apply: (@neg_correct _ (I.bnd _ _)).
  by apply: I.fromZ_correct.
rewrite Rmult_1_l.
by apply: I.fromZ_correct.
Qed.

Lemma Ieval_atan_correct m x xI :
   x \contained_in xI -> eval_atan m x \contained_in Ieval_atan m xI.
Proof.
move=> xIxI.
apply: Ieval_atan_rec_correct => //.
- by rewrite /= Zpos_P_of_succ_nat; lia.
- by apply sqr_correct.
rewrite -IZR_Zof_nat (_ : (Z.of_nat m.+1 = Z.of_nat m + 1)%Z).
  by apply: I.fromZ_correct.
by rewrite /= Zpos_P_of_succ_nat; lia.
Qed.

(*
Derive_n atan k.+1 x = (-1)^+ k * k`!%:R * (poly_atan k).[x] / (1 + x ^ 2)^k.+1.
*)

Definition IDerive_n_atan n pn on xI :=
  let kf := Ieval_atan n xI in
  let df := I.power_pos prec (I.add prec (I.fromZ prec 1) (I.sqr prec xI)) pn in
  if on then div kf df else I.neg (div kf df).

Lemma IDerive_n_atan_correct n pn on x xI :
 x \contained_in xI -> ~~ on = odd n -> pn = Pos.of_nat n.+1 ->
 (Derive_n atan n.+1 x / n`!%:R)\contained_in
  IDerive_n_atan n pn on xI.
Proof.
move=> xIxI onE pnE.
rewrite Derive_n_atan /IDerive_n_atan -signr_odd -onE.
have F x1 y1 z1 t1 : 
  (0 < y1 -> 0 < z1 -> x1 * y1 * t1 / z1 / y1 = x1 * t1 / z1)%R.
  by move=> y1P z1P; field; lra.
rewrite {}F; last 2 first.
- by rewrite natr_INR; apply/lt_0_INR/leP/fact_gt0.
- by apply: pow_lt; nra.
case: {onE}on.
  rewrite Rmult_1_l.
  apply: div_correct.
    rewrite /poly_atan -eval_atan_cor.
    by apply: Ieval_atan_correct.
  rewrite pnE.
  apply: power_pos_correct => //.
  apply: add_correct; first by apply: I.fromZ_correct.
  replace (x ^ 2)%R with (x * x)%R by ring.
  by apply: sqr_correct.
rewrite -Ropp_mult_distr_l Rmult_1_l Ropp_div.
apply: neg_correct.
apply: div_correct.
  rewrite /poly_atan -eval_atan_cor.
  by apply: Ieval_atan_correct.
rewrite pnE.
apply: power_pos_correct => //.
apply: add_correct; first by apply: I.fromZ_correct.
replace (x ^ 2)%R with (x * x)%R by ring.
by apply: sqr_correct.
Qed.

Definition atan_error (b1 : bool) P zn z2n nn :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Iab := I.bnd a b in
  let v := Ieval_atan nn Iab in
  let Ic :=
    if csign v then
      let Ida := I.abs (I.sub prec (I.atan prec Ia) (IsCshaw Ia Ib P Ia)) in
      let Idb := I.abs (I.sub prec (I.atan prec Ib) (IsCshaw Ia Ib P Ib)) in
      I.mul prec I01 (I.join Ida Idb)
    else
      I.div prec
        (I.mul prec (I.power_pos prec (I.sub prec Ib Ia) zn)
                    (I.mul prec I01 (I.abs (IDerive_n_atan 
                                           nn.-1 (zn)%positive (~~ b1) Iab))))
       (I.mul prec (I.power_pos prec I2 z2n) (I.fromZ prec (Zpos zn)))
   in  I.join (I.neg Ic) Ic.
   
Definition atan_cms n b1 vn zn z2n vl2 vl3 :=
  let P := Icheby_coefs (I.atan prec) vn vl3 vl2 in
  CMS P (atan_error b1 P zn z2n n.+1).

Lemma atan_cms_correct n b1 vn v2n zn z2n vl2 vl3 :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  b1 = odd n ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  zn = Pos.of_nat n.+1 ->
  z2n = Pos.of_nat n.*2.+1 ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b atan (atan_cms n b1 vn zn z2n vl2 vl3).
Proof.
move=> aLb aF bF b1E vnE v2nE znE z2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
have Hiab x : (D2R a <= x <= D2R b)%R -> x \contained_in I.bnd a b.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  by (do 2 case: F.toX) => //= r1; lra.
have Hiabr x : (F.cmp a b = Xlt) -> (x \contained_in I.bnd a b) -> 
                     (D2R a <= x <= D2R b)%R.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.                   
  rewrite /= F.cmp_correct /D2R !I.F'.classify_real //=.
  by (do 2 case: F.toX).
pose iv := interpolation atan (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /atan_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) atan n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.atan prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: atan_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (atan x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by(do 2 case: F.toX).
apply: Rabs_join.
have [/csign_correct H|_] := boolP (csign _).
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: atan_scheby_ge => //.
    case: H => H.
      right => x1 /Hiab Hx1.
      apply: H.
      rewrite /poly_atan -eval_atan_cor.
      by apply: Ieval_atan_correct.
    left => x1 /Hiab Hx1.
    apply: H.
    rewrite /poly_atan -eval_atan_cor.
    by apply: Ieval_atan_correct.
  rewrite /Rmax; case: Rle_dec => _.
    apply: I.join_correct.
    right.
    apply/abs_correct/sub_correct.
      by apply/atan_correct/Hib.
    rewrite -scheby_coef_list_spec //.
    apply: IsCshaw_correct => //.
    by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
  apply: I.join_correct.
  left.
  apply/abs_correct/sub_correct.
    by apply/atan_correct/Hia.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
set u := (_ - _)%R.
pose e : R := (expn 2 n.+1.*2.-1 * n.+1)%:R.
pose v := ((D2R b - D2R a)^+ n.+1).
have vP : (0 < v)%R.
  rewrite /v expr_Rexp.
  by apply: pow_lt; toR; lra.
have vE: (0 < e)%R.
  rewrite /e natr_INR.
  apply: (lt_INR 0).
  by apply/ltP; rewrite muln_gt0 expn_gt0.
have -> : Rabs u = ((v * Rabs (u / v * e)) / e)%R.
  rewrite Rabs_mult Rabs_div; try lra.
  rewrite (Rabs_pos_eq v); try lra.
  rewrite (Rabs_pos_eq e); try lra.
  by field; lra.
apply: div_correct => //; last first.
  rewrite /e natr_INR mult_INR.
  apply: mul_correct.
    rewrite -pow_expn pow_INR z2nE.
    apply: power_pos_correct => //.
    by apply: I.fromZ_correct; lra.
  rewrite znE INR_IZR_INZ -Pos.of_nat_succ.
  by apply: I.fromZ_correct.
apply: mul_correct.
  rewrite /v expr_Rexp znE.
  apply: power_pos_correct => //.
  by apply: sub_correct.
apply: Rabs_I01_max => [||z Hz].
- suff: (D2R a) \contained_in I.bnd a b by apply.
  by apply: Hiab; lra.
- move=> y YC.
  apply: abs_correct.
  apply: IDerive_n_atan_correct; first by exact YC. 
    by rewrite b1E negbK.
  by rewrite znE.
rewrite Rabs_mult Rabs_div; try lra.
rewrite (Rabs_pos_eq v); try lra.
rewrite (Rabs_pos_eq e); try lra.
suff: (Rabs u <= v / e * z)%R.
  move=> HH.
  have-> : (z = (v / e * z) / v * e)%R by field; lra.
  apply: Rmult_le_compat_r; try lra.
  apply: Rmult_le_compat_r => //.
  by have := Rinv_0_lt_compat _ vP; lra.
apply: ierror_atan => // y Hy.
have /Hz : y \contained_in I.bnd a b by apply: Hiab.
rewrite Derive_n_atan.
rewrite !Rabs_mult Rabs_exprN1 Rmult_1_l.
rewrite [_.+1.-1]/= -!Rabs_mult.
have F x1 y1 z1 : 
    (0 < x1 -> 0 < z1 -> x1 * y1 * / z1 * / x1 = y1 / z1)%R.
  by move=> x1P z1P; field; lra.
rewrite {}F; last 2 first.
- by rewrite natr_INR; apply/lt_0_INR/leP/fact_gt0.
- by apply: pow_lt; nra.
- rewrite Rabs_div.
  rewrite [Rabs (_ ^ _)]Rabs_pos_eq //.
  by apply: pow_le; nra.
suff: (0 < (1 + y ^ 2) ^ n.+1)%R by lra.
by apply: pow_lt; nra.
Qed.

End CMAtan.

Section CMNorm.

Variable (a b : D).

Definition D2I d := I.bnd d d.

Definition norm_cms c :=
  let: CMS P1 Delta1 := c in
  let: P2 := [seq (D2I (I.midpoint i)) | i <- P1] in
  let  c1 := CMS (Isub_Cpoly P1 P2) Delta1 in
  CMS P2 (eval_range_cms c1).

Lemma norm_cms_correct n c f :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   cms_correct n a b f c -> cms_correct n a b f (norm_cms c).
Proof.
move=> aLb aF bF.
case: c => [] P1 Delta1 [SP1 [p [H1p H2p H3]]].
split; first by rewrite size_map.
exists [seq D2R (I.midpoint i) | i <- P1].
split; first by rewrite size_map.
  move=> i; have := H2p i.
  have [nLi|iLn] := leqP n.+1 i.
    by rewrite !nth_default ?size_map ?SP1 ?H1p.
  rewrite !(nth_map I0) ?SP1 // => Hn.
  have : exists p, p \contained_in (nth I0 P1 i).
    by exists p`_i.
  move=> /(I.midpoint_correct) [H1 H2].
  apply: FtoI_correct.
  by rewrite F.real_correct H1.
move=> x Hx.
have [d [H1d H2d]] := H3 x Hx.
set P2 := [seq _ | i <- _].
set P3 := [seq _ | i <- _].
exists (f x - (CPolyab (D2R a) (D2R b) P3).[x])%R.
split; last by rewrite H2d; lra.
rewrite H2d.
pose g x := ((CPolyab (D2R a) (D2R b) p).[x] + d -
             (CPolyab (D2R a) (D2R b) P3).[x])%R.
apply: (@eval_range_cms_correct _ _ _ g) aLb aF bF _ _ Hx => //; last first.
  by apply: isubset_refl.
split.
  by rewrite size_Isub_Cpoly size_map SP1 maxnn.
exists (sub_Cpoly p P3).
split.
- by rewrite size_sub_Cpoly size_map H1p SP1 maxnn.
- apply: Isub_Cpoly_correct => //.
  - by rewrite SP1.
  - by rewrite !size_map.
  move=> j.
  have [nLj|jLn] := leqP n.+1 j.
    rewrite !nth_default ?size_map ?SP1 ?H1p //.
    by apply: I0_correct.
  rewrite !(nth_map I0) ?SP1 //.
  have : exists p, p \contained_in (nth I0 P1 j).
    by exists p`_j.
  move=> /(I.midpoint_correct) [H1 H2].
  apply: FtoI_correct.
  by rewrite F.real_correct H1.
move=> x1 Hx1.
exists (g x1 - (CPolyab (D2R a) (D2R b) (sub_Cpoly p P3)).[x1])%R.
split; last by lra.
rewrite /g !horner_CPolyab sub_Cpoly_spec.
rewrite (_ : _ - _ = d)%R // 2!hornerE; toR; lra.
Qed.

End CMNorm.

Section CMCos.

Variable (a b : D).

Notation "f ^( n )" := (Derive_n f n) (at level 2, format "f ^( n )").

(*****************************************************************************)
(* Derivative of cos for interval arithmetic                                 *)
(*****************************************************************************)

Lemma cos_env a1 b1 : I.cos prec \is_envelope_of[a1, b1] cos.
Proof. by move=> *; exact: cos_correct. Qed.

Fixpoint bcos b x := if b then sin x else cos x.

Definition Ibcos b J := if b then I.sin prec J else I.cos prec J.

Lemma Ibcos_correct a1 b1 n:
 (Ibcos (odd n)) \is_envelope_of[a1, b1]
   (fun x => (-1) ^ (odd n) * (-1) ^ (odd n./2) * cos^(n) x)%R.
Proof.
move=> x X Ix Hx.
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
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Iab := I.bnd a b in
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
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  b1 = odd n ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  zn = Pos.of_nat n.+1 ->
  z2n = Pos.of_nat n.*2.+1 ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b cos (cos_cms n b1 vn zn z2n vl2 vl3).
Proof.
move=> aLb aF bF b1E vnE v2nE znE z2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
have Hiab x : (D2R a <= x <= D2R b)%R -> x \contained_in I.bnd a b.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  by (do 2 case: F.toX) => //= r1; lra.
have Hiabr x : (F.cmp a b = Xlt) -> (x \contained_in I.bnd a b) -> 
               (D2R a <= x <= D2R b)%R.
  rewrite /= /D2R I.F'.valid_lb_real // I.F'.valid_ub_real //=.                   
  rewrite /= F.cmp_correct /D2R !I.F'.classify_real //=.
  by (do 2 case: F.toX).
pose iv := interpolation sin (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /cos_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) cos n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.cos prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: cos_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (cos x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
apply: Rabs_join.
have [/csign_correct H|_] := boolP (csign _).
  apply: I01_correct.
    split; first by split_Rabs; lra.
    apply: cos_scheby_ge => //.
    case: H => H.
      right => x1 /Hiab Hx1.
      apply: H.
      rewrite /Ibsin b1E; case: odd.
        by apply: sin_correct.
      by apply: cos_correct.
    left => x1 /Hiab Hx1.
    apply: H.
    rewrite /Ibsin b1E; case: odd.
      by apply: sin_correct.
    by apply: cos_correct.
  rewrite /Rmax; case: Rle_dec => _.
    apply: I.join_correct.
    right.
    apply/abs_correct/sub_correct.
      by apply/cos_correct/Hib.
    rewrite -scheby_coef_list_spec //.
    apply: IsCshaw_correct => //.
    by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
  apply: I.join_correct.
  left.
  apply/abs_correct/sub_correct.
    by apply/cos_correct/Hia.
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
apply: div_correct.
 apply: mul_correct.
    rewrite /v expr_Rexp znE.
    apply: power_pos_correct => //.
    by apply: sub_correct.
  apply: Rabs_I01_max => [||z Hz].
  - suff: (D2R a) \contained_in I.bnd a b by apply.
    by apply: Hiab; lra.
  - move=> y YC.
    apply: abs_correct.
    rewrite b1E.
    apply: (Ibcos_correct n.+1) => //.
    by apply: Hiabr.
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
  have /Hz : y \contained_in I.bnd a b by apply: Hiab.
  rewrite Derive_n_cos -[odd n.+1]/(~~ odd n).
  case: (odd n).
    rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
    case: odd => /=.
      by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) 
                   Ropp_involutive !Rmult_1_l.
    by rewrite !Rmult_1_l.
  rewrite -!expr_Rexp signr_odd -signr_odd expr_Rexp.
  case: odd => /=.
    by rewrite !(Ropp_mult_distr_l_reverse, Ropp_mult_distr_r_reverse) 
                  !Ropp_involutive !Rmult_1_l.
  rewrite expr0 !(Rmult_1_l, Rmult_1_r).
  by rewrite -Ropp_mult_distr_l -Ropp_mult_distr_r Rmult_1_l Ropp_involutive.
rewrite [e]natr_INR mult_INR.
apply: mul_correct.
  rewrite -pow_expn pow_INR z2nE.
  apply: power_pos_correct => //.
  by apply: I.fromZ_correct; lra.
by apply: Ifact_correct.
Qed.

End CMCos.

Section CMExp.

Variable (a b : D).

(*****************************************************************************)
(* Chebyshev model for exp                                                   *)
(*****************************************************************************)

Definition exp_error P :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Ida := I.abs (I.sub prec (I.exp prec Ia) (IsCshaw Ia Ib P Ia)) in
  let Idb := I.abs (I.sub prec (I.exp prec Ib) (IsCshaw Ia Ib P Ib)) in
  let Ic := I.mul prec I01 (I.join Ida Idb) in
  I.join (I.neg Ic) Ic.

Definition exp_cms vn vl2 vl3 :=
  let P := Icheby_coefs (I.exp prec) vn vl3 vl2 in
  CMS P (exp_error P).

Lemma exp_env a1 b1 : I.exp prec \is_envelope_of[a1, b1] exp.
Proof. move=> *; exact: exp_correct. Qed.

Lemma exp_cms_correct n vn v2n vl2 vl3 :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b exp (exp_cms vn vl2 vl3).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
pose iv := interpolation exp (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /exp_cms; split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) exp n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.exp prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: exp_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (exp x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
  rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
apply: Rabs_join.
apply: I01_correct.
  split; first by split_Rabs; lra.
  apply: exp_scheby_ge => //.
  rewrite /Rmax; case: Rle_dec => _.
  apply: I.join_correct.
  right.
  apply/abs_correct/sub_correct.
    by apply/exp_correct/Hib.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
apply: I.join_correct.
left.
apply/abs_correct/sub_correct.
  by apply/exp_correct/Hia.
rewrite -scheby_coef_list_spec //.
apply: IsCshaw_correct => //.
by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
Qed.

End CMExp.

Section CMLn.

Variable (a b : D).

(*****************************************************************************)
(* Chebyshev Model of ln                                                     *)
(*****************************************************************************)

Definition ln_error P :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Ida := I.abs (I.sub prec (I.ln prec Ia) (IsCshaw Ia Ib P Ia)) in
  let Idb := I.abs (I.sub prec (I.ln prec Ib) (IsCshaw Ia Ib P Ib)) in
  let Ic := I.mul prec I01 (I.join Ida Idb) in
  I.join (I.neg Ic) Ic.

Definition ln_cms n vn vl2 vl3 :=
  if Fpos a then
    let P := Icheby_coefs (I.ln prec) vn vl3 vl2 in
    CMS P (ln_error P)
  else error_cms n.

Lemma ln_env a1 b1 : I.ln prec \is_envelope_of[a1, b1] ln.
Proof. by move=> *; apply: ln_correct. Qed.

Lemma ln_cms_correct n vn v2n vl2 vl3 :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b ln (ln_cms n vn vl2 vl3).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
pose iv := interpolation ln (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /ln_cms.
have := Fpos_correct a; case: Fpos => [aP|aN]; last first.
  split; first by rewrite size_nseq.
  exists (nseq n.+1 0); split => //.
  - by rewrite size_nseq.
  - by move=> i; rewrite !nth_nseq !if_same; apply: I0_correct.
  move=> x Hx; set u := _.[_]; exists (ln x - u); split; last by toR; lra.
  by rewrite /= I.F'.valid_lb_nan I.F'.valid_ub_nan /= I.F'.nan_correct.
split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) ln n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.ln prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: ln_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (ln x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
apply: Rabs_join.
apply: I01_correct.
  split; first by split_Rabs; lra.
  apply: ln_scheby_ge => //.
  rewrite /Rmax; case: Rle_dec => _.
  apply: I.join_correct.
  right.
  apply/abs_correct/sub_correct.
    by apply: ln_correct.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
apply: I.join_correct.
left.
apply/abs_correct/sub_correct.
  by apply: ln_correct.
rewrite -scheby_coef_list_spec //.
apply: IsCshaw_correct => //.
by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
Qed.

End CMLn.

Section CMSqrt.

Variable (a b : D).

(*****************************************************************************)
(* Chebyshev Model of sqrt                                                   *)
(*****************************************************************************)

Definition sqrt_error P :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Ida := I.abs (I.sub prec (I.sqrt prec Ia) (IsCshaw Ia Ib P Ia)) in
  let Idb := I.abs (I.sub prec (I.sqrt prec Ib) (IsCshaw Ia Ib P Ib)) in
  let Ic := I.mul prec I01 (I.join Ida Idb) in
  I.join (I.neg Ic) Ic.

Definition sqrt_cms n vn vl2 vl3 :=
  if Fpos a then
    let P := Icheby_coefs (I.sqrt prec) vn vl3 vl2 in
    CMS P (sqrt_error P)
  else error_cms n.

Lemma sqrt_env a1 b1 : I.sqrt prec \is_envelope_of[a1, b1] sqrt.
Proof. by move=> *; apply: sqrt_correct. Qed.

Lemma sqrt_cms_correct n vn v2n vl2 vl3 :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b sqrt (sqrt_cms n vn vl2 vl3).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
pose iv := interpolation ln (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /sqrt_cms.
have := Fpos_correct a; case: Fpos => [aP|aN]; last first.
  split; first by rewrite size_nseq.
  exists (nseq n.+1 0); split => //.
  - by rewrite size_nseq.
  - by move=> i; rewrite !nth_nseq !if_same; apply: I0_correct.
  move=> x Hx; set u := _.[_]; exists (sqrt x - u); split; last by toR; lra.
  by rewrite /= I.F'.valid_lb_nan I.F'.valid_ub_nan I.F'.nan_correct.
split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) sqrt n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.sqrt prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: sqrt_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (sqrt x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
apply: Rabs_join.
apply: I01_correct.
  split; first by split_Rabs; lra.
  apply: sqrt_scheby_ge => //.
  rewrite /Rmax; case: Rle_dec => _.
  apply: I.join_correct.
  right.
  apply/abs_correct/sub_correct.
    by apply: sqrt_correct.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
apply: I.join_correct.
left.
apply/abs_correct/sub_correct.
  by apply: sqrt_correct.
rewrite -scheby_coef_list_spec //.
apply: IsCshaw_correct => //.
by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
Qed.

End CMSqrt.

Section CMInvx.

Variable (a b : D).

(******************************************************************************)
(* Chebyshev model of invx                                                    *)
(******************************************************************************)

Definition invx_error P :=
  let Ia := I.bnd a a in
  let Ib := I.bnd b b in
  let Ida := I.abs (I.sub prec (I.inv prec Ia) (IsCshaw Ia Ib P Ia)) in
  let Idb := I.abs (I.sub prec (I.inv prec Ib) (IsCshaw Ia Ib P Ib)) in
  let Ix := I.mul prec I01 (I.join Ida Idb) in
  I.join (I.neg Ix) Ix.

Definition invx_cms n vn vl2 vl3 :=
   if Fpos a || (Fneg b) then
     let P := Icheby_coefs (I.inv prec) vn vl3 vl2 in
     CMS P (invx_error P)
   else (error_cms n).

Lemma invx_env a1 b1 : I.inv prec \is_envelope_of[a1, b1] Rinv.
Proof. by move=> *; apply: inv_correct. Qed.

Lemma invx_cms_correct n vn v2n vl2 vl3 :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl3 = Ischeby_nodes a b n.+1 v2n ->
  cms_correct n a b Rinv (invx_cms n vn vl2 vl3).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl3E.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have F3 : D2R b != D2R a by rewrite eq_sym.
have Hia : D2R a \contained_in I.bnd a a by apply: FtoI_correct.
have Hib : D2R b \contained_in I.bnd b b by apply: FtoI_correct.
pose iv := interpolation ln (scheby_nodes (D2R a) (D2R b) n.+1).
rewrite /cms_correct /invx_cms.
case E : (_ || _); last first.
  split; first by rewrite size_nseq.
  exists (nseq n.+1 0); split => //.
  - by rewrite size_nseq.
  - by move=> i; rewrite !nth_nseq !if_same; apply: I0_correct.
  move=> x Hx; set u := _.[_]; exists (/x - u); split; last by toR; lra.
  by rewrite /= I.F'.valid_lb_nan I.F'.valid_ub_nan I.F'.nan_correct.
split.
  by rewrite size_Icheby_coefs vl2E size_ITvalue.
pose p := scheby_coef_list (D2R a) (D2R b) Rinv n.+1.
have Hp i : p`_i \contained_in nth I0 (Icheby_coefs (I.inv prec) vn vl3 vl2) i.
  have [nLi|iLn] := leqP n.+1 i.
    rewrite /scheby_coef_list !nth_default //.
    - by apply: I0_correct.
    - by rewrite size_map size_iota.
    by rewrite size_Icheby_coefs vl2E size_ITvalue.
  rewrite (nth_map 0%nat) ?size_iota // nth_iota // add0n.
  rewrite sdsprod_coefs //.
  apply: Ischeby_coefs_correct => //.
  - by apply: invx_env.
  - by apply: v2nE.
  - by apply: vl2E.
  by apply: vl3E.
exists p; split => // [|x Hx].
  by rewrite size_scheby_coef_list.
exists (/x - (CPolyab (D2R a) (D2R b) p).[x])%R; split; last by lra.
rewrite scheby_coef_list_spec //.
have Ix : (D2R a <= x <= D2R b)%R.
  have := aLb; rewrite F.cmp_correct.
  have := Hx; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
apply: Rabs_join.
apply: I01_correct.
  split; first by split_Rabs; lra.
  apply: inv_scheby_ge => //.
  have := Fpos_correct a; have := Fneg_correct b.
  by case: Fpos E => //; case: Fneg => //; lra.
rewrite /Rmax; case: Rle_dec => _.
  apply: I.join_correct.
  right.
  apply/abs_correct/sub_correct.
    by apply: inv_correct.
  rewrite -scheby_coef_list_spec //.
  apply: IsCshaw_correct => //.
  by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
apply: I.join_correct.
left.
apply/abs_correct/sub_correct.
  by apply: inv_correct.
rewrite -scheby_coef_list_spec //.
apply: IsCshaw_correct => //.
by rewrite size_Icheby_coefs size_scheby_coef_list vl2E size_ITvalue.
Qed.

End CMInvx.

Section CMInv.

Variable (a b : D).

(*****************************************************************************)
(* Chebyshev model of inv                                                    *)
(*****************************************************************************)

Definition inv_cms n vn vl2 vl1 f_cms :=
  let v := eval_range_cms f_cms in
  if I.bounded v then
    let c := I.lower v in
    let d := I.upper v in
    let t := F.cmp c d in
    if t is Xlt then
  (* could be optimized *)
      let vl3 := [seq div2
         (add
            (add (mul (sub (FtoI d) (FtoI c)) i)
              (FtoI c)) (FtoI d))
      | i <- vl1] in
      comp_cms n a b c d f_cms (invx_cms c d n vn vl2 vl3)
    else if t is Xeq then
            if F.cmp c F.zero is Xeq then error_cms n
                                     else const_cms n (I.inv prec (I.bnd c c))
         else error_cms n
  else error_cms n.

Lemma inv_cms_correct n vn v2n vl2 vl1 f f_cms :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl1 = Icheby_nodes n.+1 v2n ->
  cms_correct n a b f f_cms ->
  cms_correct n a b (fun x => /(f x)) (inv_cms n vn vl2 vl1 f_cms).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl1E Hf.
rewrite /inv_cms.
case E : I.bounded; last by apply: error_cms_correct.
case E1 : F.cmp; try by apply: error_cms_correct.
  pose k := (/(D2R (I.lower (eval_range_cms f_cms))))%R.
  apply: (@cms_correct_ext _ _ _ _ (fun _ => k)) => [x Hx|].
    have := eval_range_cms_correct aLb aF bF Hf (isubset_refl _) Hx.
    rewrite /k.
    case: eval_range_cms E E1 => //= u l.
    rewrite /D2R => /andP[uF lF].
    rewrite F.cmp_correct !I.F'.classify_real //.
    rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
    case: F.toX => [|xu] //=; case: F.toX => [|xl] //.
    case: Raux.Rcompare_spec => // -> _ H.
    by congr (/ _); lra.
  rewrite F.cmp_correct F.zero_correct I.F'.classify_zero.
  have [/I.lower_bounded_correct [lH1 lH2] 
        /I.upper_bounded_correct [uH1 uH2]] := I.bounded_correct _ E.
  rewrite I.F'.classify_real; last by rewrite F.real_correct lH1.
  case E2 : Xcmp.
  - by apply: error_cms_correct.
  - apply: const_cms_correct.
    apply: inv_correct => //=.
    rewrite I.F'.valid_lb_real; last by rewrite F.real_correct lH1.
    rewrite I.F'.valid_ub_real /=; last by rewrite F.real_correct lH1.
    by rewrite /D2R lH1 /=; lra.
  - apply: const_cms_correct.
    apply: inv_correct => /=.
    rewrite I.F'.valid_lb_real; last by rewrite F.real_correct lH1.
    rewrite I.F'.valid_ub_real /=; last by rewrite F.real_correct lH1.
    by rewrite /D2R lH1 /=; lra.
  move: E1 E2; rewrite F.cmp_correct.
  rewrite I.F'.classify_real; last by rewrite F.real_correct lH1.
  rewrite I.F'.classify_real; last by rewrite F.real_correct uH1.
  rewrite lH1 uH1 /=.
  case: Raux.Rcompare_spec => // eH.
  by case: Raux.Rcompare_spec.
have [/I.lower_bounded_correct [lH1 lH2] 
      /I.upper_bounded_correct [uH1 uH2]] := I.bounded_correct _ E.
apply: comp_cms_correct => //.
- by rewrite F.real_correct lH1.
- by rewrite F.real_correct uH1.
- case: eval_range_cms E lH1 uH1 => //= l u /andP[lF uF] lH1 uH1.
  rewrite F.cmp_correct I.F'.classify_real; last first.
    by rewrite F.real_correct lH1.
  rewrite F.cmp_correct I.F'.classify_real; last first.
    by rewrite F.real_correct uH1.
  rewrite lH1 uH1 /=.
  by do 2 (case: Raux.Rcompare_spec=> /=; try lra).
apply: invx_cms_correct => //.
- by rewrite F.real_correct lH1.
- by rewrite F.real_correct uH1.
- by exact: v2nE.
- by exact: vl2E.
by rewrite vl1E.
Qed.

End CMInv.

Section CMDiv.

Variable (a b : D).

(*****************************************************************************)
(* Chebyshev model of div                                                    *)
(*****************************************************************************)

Definition div_cms n vn vl2 vl1 f_cms g_cms :=
   mul_cms n a b f_cms (inv_cms a b n vn vl2 vl1 g_cms).

Lemma div_cms_correct n vn v2n vl2 vl1 g1 g2 g1_cms g2_cms :
  F.cmp a b = Xlt -> F.real a -> F.real b ->
  INR n.+1 \contained_in vn ->
  (2 * INR n.+1) \contained_in v2n ->
  vl2 = ITvalues n.+1 (nseq n.+1 I1) (Icheby_nodes n.+1 v2n) ->
  vl1 = Icheby_nodes n.+1 v2n ->
  cms_correct n a b g1 g1_cms ->
  cms_correct n a b g2 g2_cms ->
  cms_correct n a b (fun x => (g1 x) / (g2 x))%R 
                    (div_cms n vn vl2 vl1 g1_cms g2_cms).
Proof.
move=> aLb aF bF vnE v2nE vl2E vl1E Hg1 Hg2.
apply: mul_cms_correct => //.
apply: inv_cms_correct => //.
- by exact: v2nE.
- by exact: vl2E.
- by exact: vl1E.
Qed.

End CMDiv.

Section CMbelast.

Definition belast_cms (c : cms) :=
  let: CMS P Delta := c in
  let P1 := behead (seq.belast I0 P) in
  let Delta1 := add Delta (mul (last I0 P) Im11) in
  CMS P1 Delta1.

Lemma belast_cms_correct n a b c f :
   (F.cmp a b = Xlt)%R -> F.real a -> F.real b ->
   cms_correct n.+1 a b f c -> cms_correct n a b f (belast_cms c).
Proof.
move=> aLb aF bF.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
case: c => P Delta [PS [p [pS pH xH]]].
split; first by rewrite size_behead size_belast PS.
exists (behead (seq.belast 0%R p)); split.
- by rewrite size_behead size_belast pS.
- have : 0 \contained_in I0 by apply: I0_correct.
  move: PS pS pH.
  rewrite -[0]/0%R.
  elim: n.+2 {xH}p P 0%R I0 => //; first by case=> // [] [].
  move=> m IH [|x p] // [|X P] // d D [PS] [pS] iH dH i.
  rewrite !nth_behead /=. 
  have := iH i; rewrite !lastI.
  rewrite !nth_rcons !size_belast PS pS.
  case: leqP => // H.
  by rewrite !nth_default ?size_belast ?PS ?pS.
move=> x xI.
have [d [dI fxE]] := xH _ xI.
exists (d + last 0 p * ('T^(D2R a, D2R b)_n.+1).[x]); split.
  apply: add_correct => //.
  apply: mul_correct => //.
    rewrite (last_nth 0%R) (last_nth I0) PS pS.
    by have := pH n.+1.
  red.
  rewrite /= valid_lb_fromZ // valid_ub_fromZ //= !F.fromZ_correct //.
  rewrite horner_comp -CPoly_trigo.pT_Cheby.
    by apply: COS_bound.
  apply: Tab_bound => //.
  have := aLb; rewrite F.cmp_correct.
  have := xI; rewrite /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  by (do 2 case: F.toX).
have aDb : D2R a != D2R b by apply/eqP; toR; lra.
rewrite {}fxE (CPolyabE _ pS) //.
have /CPolyabE-> //: size (behead (seq.belast 0 p)) = n.+1.
  by rewrite size_behead size_belast pS.
case: {pH xH}p pS => //= y p [pS].
rewrite big_ord_recr /=.
rewrite !hornerE /= !Rplus_assoc; congr (_.[_] + _)%R.
  apply: eq_bigr => [] [i iH] _ /=.
  by rewrite lastI // nth_rcons size_belast pS iH.
rewrite Rplus_comm.
congr (_ + _ * _)%RR.
by rewrite (last_nth 0) pS.
Qed.

End CMbelast.

Section CMInt.

Fixpoint int_Cpoly_rec (i a : R) (l : seq R) : seq R :=
 (if l is (b :: l1) then
    if l1 is (c :: l2) then 
      (a - c) / i :: int_Cpoly_rec (i + 2) b l1
    else [:: a / i; b / (i + 2)]
  else [:: a / i])%R.

Lemma size_int_Cpoly_rec (i a : R) (l : seq R) :
  size (int_Cpoly_rec i a l) = (size l).+1.
Proof.
elim: l i a => //= b [|c l] // IH i a.
by have /= -> := IH (i + 2) b.
Qed.

Lemma int_Cpoly_rec0 (i a : R) : int_Cpoly_rec i a [::] = [:: (a  / i)%R].
Proof. by []. Qed.

Lemma int_Cpoly_rec1 (i a b : R) :
   (int_Cpoly_rec i a [:: b] =  [:: a / i; b / (i + 2)])%R.
Proof. by []. Qed.

Lemma int_Cpoly_recSS (i a b c : R) (l : seq R) :
   int_Cpoly_rec i a (b :: c :: l) = 
     ((a - c) / i :: int_Cpoly_rec (i + 2) b (c :: l))%R.
Proof. by []. Qed.

Lemma int_Cpoly_rec_correct i j a l : 
  (j <= size l)%nat -> 
  (int_Cpoly_rec i a l)`_ j =
   (((a :: l)`_j - (a :: l)`_j.+2) / (i + 2 * j%:R))%R.
Proof.
elim: l i j a. 
  by move=> i [|j] //= a _; congr (_ / _)%R; toR; lra.
move=> b [|c l] IH i j a.
  rewrite int_Cpoly_rec1 /=.
  by case: j=> [|[|]] _ //=; congr (_ / _)%R; toR; lra.
rewrite int_Cpoly_recSS.
case: j => [|j] H.
  by congr (_ / _)%R; toR; lra.
rewrite -nth_behead IH //=.
congr (_ / _)%R.
by rewrite (natrD _ 1%nat); toR; lra.
Qed.

Definition int_Cpoly a b (l : seq R) : seq R := 
  if l is c :: l1 then 
     0 :: scal_Cpoly  ((b - a) / 2)%R 
    (add_Cpoly
     ((c / 2) :: (nseq (size l1) 0))%R
     (int_Cpoly_rec 2 c l1))
  else [:: 0].

Lemma size_cons (A : Type) (a : A) l : size (a :: l) = (size l).+1.
Proof. by []. Qed.

Lemma size_int_Cpoly (a b : R) (l : seq R) :
  size (int_Cpoly a b l) = (size l).+1.
Proof.
case: l => // c l.
rewrite /int_Cpoly !size_cons size_map size_add_Cpoly size_cons size_nseq.
by rewrite size_int_Cpoly_rec maxnn.
Qed.

Lemma int_Cpoly0_correct a b l : (int_Cpoly a b l)`_ 0 = 0.
Proof. by case: l. Qed.

Lemma int_Cpoly_correct1 a b l : 
  ((int_Cpoly a b l)`_ 1 = 
      ((b - a) / 2)%R * (l`_0 / 2 + (l`_0 - l`_2) / 2))%R.
Proof.
case: l => [/=|c [/=|d [|e l]]] //=.
- by toR; lra.
- by toR; rewrite Rminus_0_r.
by toR; rewrite Rminus_0_r.
Qed.

Lemma coef_add_Cpoly (K : ringType) (l1 l2 : seq K) i :
  (add_Cpoly l1 l2)`_i = l1`_i + l2`_i.
Proof.
elim: l1 l2 i => //=.
  by move=> l2 i; rewrite nth_nil add0r.
by move=> a l1 IH [|b l2] [|i] //=; rewrite addr0.
Qed.

Lemma int_Cpoly_correct a b j l : 
  (j.+1 < size l)%nat -> 
  ((int_Cpoly a b l)`_ j.+2 =
     ((b - a) / 2)%R * ((l`_j.+1 - l`_j.+3) / (2 * j.+2%:R)))%R.
Proof.
case: l => // c [|d [|e l]] //.
  case: j => //= _; toR.
  rewrite (_ : (2 + 2 = 4)%R); last by lra.
  rewrite (_ : (2 * (1 + 1) = 4)%R); last by lra.
  by lra.
move=> sH; rewrite /= !ltnS in sH.
rewrite /int_Cpoly int_Cpoly_recSS.
rewrite -[_ `_ j.+2]/ ((scal_Cpoly ((b - a) / 2)%R
   (add_Cpoly (nseq (size [:: d, e & l]) 0)
      (int_Cpoly_rec (2 + 2) d (e :: l))))`_j).
rewrite (nth_map 0); last first.
  rewrite size_add_Cpoly size_nseq.
  by apply: leq_ltn_trans _ (leq_maxl _ _).
rewrite coef_add_Cpoly nth_nseq int_Cpoly_rec_correct //=.
rewrite ltnS sH add0r.
congr (_ * (_ / _)%R).
rewrite (natrD _ 2%nat); toR; lra.
Qed.

Lemma divE x y : y != 0 -> (x / y)%R = x / y.
Proof. by move=> yNz;toR; rewrite /Rinvx ifT. Qed.

Lemma natr_posR i : (0 <= i%:R)%R.
Proof.
by elim: i => [|i]; rewrite ?natrS; toR; try lra.
Qed.

Lemma int_Cpoly_deriv a b l : a != b ->
  (CPolyab a b (int_Cpoly a b l))^`() = CPolyab a b l.
Proof.
move=> aDb.
case: l => [|c [|d l]].
- by rewrite /= /CPolyab /= big_ord1 big_ord0 scale0r deriv0.
- rewrite /CPolyab /= big_ord_recr /= !big_ord1 /= scale0r add0r.
  rewrite mulrC -scalerA derivZ; congr (_ _ _); first by toR; lra.
  rewrite -deriv_pTab0 //.
  congr ((_ *: _)^`()).
    by toR; rewrite /Rinvx ifT //; apply/eqP; lra.
  by apply/eqP; toR; lra.
rewrite /CPolyab size_int_Cpoly !size_cons.
have <- := @big_mkord _ _ _ _ predT 
                 (fun i => (int_Cpoly a b (c :: d :: l))`_i *: 'T^(a,b)_i).
have <- := @big_mkord _ _ _ _ predT 
                 (fun i => (c :: d :: l)`_i *: 'T^(a,b)_i).
rewrite -[RHS]deriv_sum_pTab //.
- congr (_ _).
  rewrite [LHS]big_ltn // [in LHS]big_ltn // [in RHS]big_ltn //.
  rewrite !addrA; congr (_ + _); last first.
    rewrite big_nat_cond [RHS]big_nat_cond.
    apply: eq_bigr => [] [|[|i]] //; rewrite andbT !ltnS => /andP[_ iLl].
    rewrite int_Cpoly_correct //.
    congr (_ *: _).
    rewrite (_ : (2 * i.+2%:R)%R =(i.+2).*2%:R); last first.
      by rewrite -addnn natrD; toR; lra.
    rewrite -!divE; try by (toR; lra).
      by apply/eqP; toR; lra.
    apply/eqP.
    by rewrite -addnn natrD !natrS; have := natr_posR i; toR; lra.
  rewrite int_Cpoly0_correct scale0r add0r int_Cpoly_correct1.
  rewrite -scalerDl; congr ( _ *: _).
  set x := _ `_ _; set y := _ `_ _.
  rewrite -!divE //; try by apply/eqP; toR; lra.
  by toR; lra.
- by rewrite nth_default.
- by rewrite nth_default.
by apply: Rchar.
Qed.

Lemma Rint_Cpoly (a b a1 b1 : R) l :
  a != b ->
  RInt (horner (CPolyab a b l)) a1 b1 = 
    (CPolyab a b (int_Cpoly a b l)).[b1] - 
    (CPolyab a b (int_Cpoly a b l)).[a1].
Proof.
move=> aDb.
toR; rewrite -[(_ + - _)%R]RInt_Derive_horner.
apply: RInt_ext => x H.
congr horner.
by rewrite int_Cpoly_deriv.
Qed.

Fixpoint Iint_Cpoly_rec i a l :=
 if l is (b :: l1) then
    if l1 is (c :: l2) then 
      div (sub a c) i :: Iint_Cpoly_rec (add i I2) b l1
    else [:: div a i; div b (add i I2)]
  else [:: div a i].

Lemma size_Iint_Cpoly_rec i a l :
  size (Iint_Cpoly_rec i a l) = (size l).+1.
Proof.
elim: l i a => //= b [|c l] // IH i a.
by have /= -> := IH (add i I2) b.
Qed.

Lemma Iint_Cpoly_recSS i a b c l :
   Iint_Cpoly_rec i a (b :: c :: l) = 
     (div (sub a c) i :: Iint_Cpoly_rec (add i I2) b (c :: l))%R.
Proof. by []. Qed.

Lemma Iint_Cpoly_rec_contains n i ii a ia l il : 
  size l = n -> size il = n ->
  i \contained_in ii -> a \contained_in ia -> l \lcontained_in il ->
  int_Cpoly_rec i a l \lcontained_in Iint_Cpoly_rec ii ia il.
Proof.
elim: n i ii a ia l il => //=.
  move=> i ii a ia [|//] [] //= _ _ iH aH _ [|k] //=.
  by apply: div_correct.
move=> n IH i ii a ia [|b [|c l]] // [|ib [|ic il]] //.
- move=> /= _ _ iH aH /(_ 0%nat) bH [|[|]] //=.
  - by apply: div_correct.
  - apply: div_correct => //.
    apply: add_correct => //.
    by apply: I.fromZ_correct.
  move=> k; rewrite !nth_nil.
  by apply: I0_correct.
- by move<-.
- by move<-.
rewrite int_Cpoly_recSS Iint_Cpoly_recSS => sL sIL iH aH bclH [|k].
  apply: div_correct => //.
  apply: sub_correct => //.
  by apply: (bclH 1%nat).
apply: IH => //.
- by case: sL.
- by case: sIL.
- apply: add_correct => //.
    by apply: I.fromZ_correct.
  by apply: (bclH 0%nat).
by move=> u; apply: (bclH u.+1).
Qed.

Definition Iint_Cpoly A B l := 
  if l is a :: l1 then 
  I0 :: Iscal_Cpoly  (div (sub B A) I2)%R 
     (Iadd_Cpoly  
       ((div a I2) :: (nseq (size l1) I0))%R
       (Iint_Cpoly_rec I2 a l1))
  else [:: I0].

Lemma size_Iint_Cpoly a b l :
  size (Iint_Cpoly a b l) = (size l).+1.
Proof.
case: l => // c l.
rewrite /Iint_Cpoly !size_cons size_Iscal_Cpoly size_Iadd_Cpoly.
by rewrite size_cons size_nseq size_Iint_Cpoly_rec maxnn.
Qed.

Lemma Iint_Cpoly_contains n a ia b ib l il : 
  size l = n -> size il = n -> 
  a \contained_in ia -> b \contained_in ib -> l \lcontained_in il ->
  int_Cpoly a b l \lcontained_in Iint_Cpoly ia ib il.
Proof.
case: n l il => [|n] [|c l] [|ic il] // lS ilS aH bH slH [|k].
- by apply: I0_correct.
- rewrite /= !nth_nil.
  by apply: I0_correct.
- by apply: I0_correct.
rewrite /int_Cpoly /Iint_Cpoly.
have [{}lS] := lS; have [{}ilS] := ilS.
apply: Iscal_Cpoly_correct.
  rewrite  size_add_Cpoly  size_Iadd_Cpoly /= !size_nseq.
  by rewrite size_int_Cpoly_rec size_Iint_Cpoly_rec lS ilS.
- apply: div_correct; first by apply: sub_correct.
  by apply: I.fromZ_correct.
apply: Iadd_Cpoly_correct => //=.
- by rewrite !size_nseq lS ilS.
- by rewrite size_int_Cpoly_rec size_Iint_Cpoly_rec lS ilS.
- case => [|i] /=.
    apply: div_correct; first by apply: (slH 0%nat).
    by apply: I.fromZ_correct.
  by rewrite !nth_nseq !if_same; apply: I0_correct.
apply: Iint_Cpoly_rec_contains => //.
- by rewrite lS ilS.
- by apply: I.fromZ_correct.
- by apply: (slH 0%nat).
by move=> i; apply: (slH i.+1).
Qed.


Definition int_cms a b (c : cms) d :=
  let: CMS P Delta := c in
  let P1 := Iint_Cpoly (I.bnd a a) (I.bnd b b) P in
  let P2 := Isub_Cpoly P1 [:: IsCshaw (I.bnd a a) (I.bnd b b) P1 d] in
  let Delta1 := mul Delta (sub (I.bnd a b) d) in
  let Delta2 := I.abs Delta1 in
  CMS P2 (I.join (I.neg Delta2) Delta2).

Lemma subset_contains d i1 i2 :
   I.subset i1 i2 -> d \contained_in i1 -> d \contained_in i2.
Proof.
move/I.subset_correct; case: i1; case: i2 => //= l2 u2.
  case: F.valid_lb => //=; case: F.valid_ub => //.
move=> l1 u1.
case: F.valid_lb => //=; case: F.valid_ub => //=; try lra.
by case: F.valid_lb => //=; case: F.valid_ub => //=; try lra;
   rewrite /le_lower /=;
   case El1 : (F.toX l1) => [|l1E]; case El2 : (F.toX l2) => [|l2E];
  case Eu1 : (F.toX u1) => [|u1E]; case Eu2 : (F.toX u2) => [|u2E] //=; lra.
Qed.

Lemma interval_r_connect x y z i :
   (x <= y <= z)%R -> 
   x \contained_in i -> z \contained_in i -> y \contained_in i.
Proof.
case: i => //= l u xLyLz.
case: F.valid_lb => //=; try lra.
case: F.valid_ub => //=; try lra.
case El : (F.toX l) => [|lE]; case Eu : (F.toX u) => [|uE] //=; lra.
Qed.

Lemma int_cms_correct n a b c d id f :
   F.cmp a b = Xlt -> F.real a -> F.real b ->
   d \contained_in id ->
   I.subset id (I.bnd a b) ->
   cms_correct n a b f c -> 
   ex_RInt f (D2R a) (D2R b) ->
   cms_correct n.+1 a b (RInt f d) (int_cms a b c id).
Proof.
move=> aLb aF bF dH idS.
have F1 : (D2R a < D2R b)%R.
  have := F.cmp_correct a b; rewrite aLb.
  rewrite (I.F'.classify_real _ aF) (I.F'.classify_real _ bF).
  rewrite /D2R; case: F.toX; case: F.toX =>  //= r1 r2.
  by case: Raux.Rcompare_spec.
have F2 : D2R a != D2R b by apply/eqP; lra.
have dabH : d \contained_in I.bnd a b by apply: subset_contains idS _.
case: c => P Delta [sPH [p [spH pH ecH]]] iH; split.
  by rewrite size_Isub_Cpoly size_Iint_Cpoly sPH /= maxnSS maxn0.
exists
 (sub_Cpoly 
 (int_Cpoly (D2R a) (D2R b) p)
  [::(CPolyab (D2R a) (D2R b) (int_Cpoly (D2R a) (D2R b) p)).[d]]); split.
- by rewrite size_sub_Cpoly size_int_Cpoly spH maxnSS maxn0.
- apply: Isub_Cpoly_correct => //.
  - by rewrite size_int_Cpoly size_Iint_Cpoly spH sPH.
  - by apply: Iint_Cpoly_contains spH sPH _ _ _ => //; apply: FtoI_correct.
  case=> /=.
    apply: IsCshaw_correct => //; try by apply FtoI_correct.
      by rewrite size_int_Cpoly size_Iint_Cpoly sPH spH.    
    by apply: Iint_Cpoly_contains spH sPH _ _ _ => //; apply: FtoI_correct.
  by move=> i /=; rewrite !nth_nil; apply: I0_correct.
move=> x xH; set v := (_.[_]).
exists (RInt f d x - v)%R; split; last by lra.
rewrite {}/v horner_CPolyab sub_Cpoly_spec CPolyC.
rewrite 2!hornerE hornerC -!horner_CPolyab -Rint_Cpoly //.
rewrite -[(_ - _)%R](@RInt_minus _ f); last 2 first.
- have [->| [dLx|xLd]] : (d = x \/ (d < x) \/ (x < d))%R by lra.
  * by apply: ex_RInt_point.
  * apply: ex_RInt_Chasles_1; last first.
      apply: ex_RInt_Chasles_2; last by exact: iH.
      have := aLb; rewrite F.cmp_correct.
      have := dabH; rewrite /D2R /= !I.F'.classify_real //=.
      rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
      by (do 2 case: F.toX).
    split; first by lra.
    move: aLb xH.
    rewrite F.cmp_correct /D2R /=.
    rewrite /D2R /= !I.F'.classify_real //=.
    rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
    case: F.toX => //= ar; case: F.toX => // br.
    by case: Raux.Rcompare_spec => //=; lra.
  apply: ex_RInt_swap.
  apply: ex_RInt_Chasles_1; last first.
    apply: ex_RInt_Chasles_2; last by exact: iH.
    have := aLb; rewrite F.cmp_correct.
    have := xH; rewrite /D2R /= !I.F'.classify_real //=.
    rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
    by (do 2 case: F.toX).
  split; first by lra.
  move: aLb dabH.
  rewrite F.cmp_correct /D2R /= !I.F'.classify_real //=.
  rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
  case: F.toX => //= ar; case: F.toX => // br.
  by case: Raux.Rcompare_spec => //=; lra.
- by apply: integrable_horner.
have [->| [dLx|xLd]] : (d = x \/ (d < x) \/ (x < d))%R by lra.
- rewrite RInt_point.
  case: (ecH _ xH) => t [] tH _.
  apply/Rabs_join/abs_correct.
  rewrite (_ : zero = t * (d - d))%R;  last by rewrite /zero /=; lra.
  apply: mul_correct => //.
  by apply: sub_correct.
- apply/Rabs_join/abs_correct.
  case: Delta ecH => // l u ecH.
  have [z [/containedE[V1 V2 V3 V4 V5] _]]:= ecH _ xH.
  set f1 : R -> R := (fun _ => _); set v : R := RInt _ _ _.
  suff [d1 [d1H ->]] :
     exists d1, d1 \contained_in (I.bnd l u) /\ v = d1 * (x - d).
    apply: mul_correct => //.
    by apply: sub_correct.
  have f1H : ex_RInt f1 d x.
    apply: ex_RInt_minus.
      apply: ex_RInt_Chasles_1; last first.
        apply: ex_RInt_Chasles_2; last by exact: iH.
        move: aLb dabH.
        rewrite F.cmp_correct /D2R /= !I.F'.classify_real //=.
        rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
        by case: F.toX => //= ar; case: F.toX.
      split; first by lra.
      move: aLb xH.
      rewrite F.cmp_correct /D2R /= !I.F'.classify_real //=.
      rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
      case: F.toX => //= ar; case: F.toX => // br.
      by case: Raux.Rcompare_spec => //=; lra.
    by apply: integrable_horner.
  exists (v / (x - d))%R; split; last by toR; field; lra.
  red => /=.
  rewrite V1 V2.
  case El: F.toX => [|xl]; case Eu: F.toX => [|xu] //; split => //.
  - have : (v <= RInt (fun=> xu) d x)%R.
      apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
      rewrite /f1 => x1 x1H.
      case: (ecH _ (_ : x1 \contained_in _)).
        by apply: interval_r_connect (_ : (d <= x1 <= x)%R) _ _ => //; lra.
      move=> x2 [x2H ->].
      suff: (x2 <= xu)%R by rewrite /minus /plus /opp /=; toR; lra.
      move: x2H; rewrite /=; 
      case: F.valid_lb => /=; try lra.
      case: F.valid_ub => /=; try lra.
      by case; rewrite /= Eu.
    rewrite RInt_const /scal /= /mult /=.
    rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
    by field; lra.
  - have : (RInt (fun=> xl) d x <= v)%R.
      apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
      rewrite /f1 => x1 x1H.
      case: (ecH _ (_ : x1 \contained_in _)).
        by apply: interval_r_connect (_ : (d <= x1 <= x)%R) _ _ => //; lra.
      move=> x2 [x2H ->].
      suff: (xl <= x2)%R by rewrite /minus /plus /opp /=; toR; lra.
      move: x2H; rewrite /=.
      case: F.valid_lb => /=; try lra.
      case: F.valid_ub => /=; try lra.
      by case; rewrite /= El.
    rewrite RInt_const /scal /= /mult /=.
    rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
    by field; lra.
  - have : (RInt (fun=> xl) d x <= v)%R.
      apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
      rewrite /f1 => x1 x1H.
      case: (ecH _ (_ : x1 \contained_in _)).
        by apply: interval_r_connect (_ : (d <= x1 <= x)%R) _ _ => //; lra.
      move=> x2 [x2H ->].
      suff: (xl <= x2)%R by rewrite /minus /plus /opp /=; toR; lra.
      move: x2H; rewrite /= V1 V2 /=. 
      by case; rewrite /= El.
    rewrite RInt_const /scal /= /mult /=.
    rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
    by field; lra.  
  have : (v <= RInt (fun=> xu) d x)%R.
    apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
    rewrite /f1 => x1 x1H.
    case: (ecH _ (_ : x1 \contained_in _)).
      by apply: interval_r_connect (_ : (d <= x1 <= x)%R) _ _ => //; lra.
    move=> x2 [x2H ->].
    suff: (x2 <= xu)%R by rewrite /minus /plus /opp /=; toR; lra.
    move: x2H; rewrite /=; 
    case: F.valid_lb => /=; try lra.
    case: F.valid_ub => /=; try lra.
    by case; rewrite /= Eu.
  rewrite RInt_const /scal /= /mult /=.
  rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
  by field; lra.
apply/Rabs_join/abs_correct.
case: Delta ecH => // l u ecH.
have [z [/containedE[V1 V2 V3 V4 V5] _]]:= ecH _ xH.
set f1 : R -> R := (fun _ => _); set v : R := RInt _ _ _.
suff [d1 [d1H ->]] :
  exists d1, d1 \contained_in (I.bnd l u) /\ v = d1 * (x - d).
  apply: mul_correct => //.
  by apply: sub_correct.
have f1H : ex_RInt f1 x d.
  apply: ex_RInt_minus.
    apply: ex_RInt_Chasles_1; last first.
      apply: ex_RInt_Chasles_2; last by exact: iH.
      move: aLb xH.
      rewrite F.cmp_correct /D2R /= !I.F'.classify_real //=.
      rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
      by case: F.toX => //= ar; case: F.toX.
    split; first by lra.
    move: aLb dabH.
    rewrite F.cmp_correct /D2R /= !I.F'.classify_real //=.
    rewrite I.F'.valid_lb_real //= I.F'.valid_ub_real //=.
    case: F.toX => //= ar; case: F.toX => // br.
    by case: Raux.Rcompare_spec => //=; lra.
  by apply: integrable_horner.
have f1NH : ex_RInt f1 d x by apply: ex_RInt_swap.
exists (v / (x - d))%R; split; last first.
  by toR; field; lra.
red => /=.
rewrite V1 V2.
case El: F.toX => [|xl]; case Eu: F.toX => [|xu] //; split => //.
- have : (- v <= RInt (fun=> xu) x d)%R.
    rewrite [(- _)%R](@opp_RInt_swap _ (_ : R -> R)) //.
    apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
    rewrite /f1 => x1 x1H.
    case: (ecH _ (_ : x1 \contained_in _)).
      by apply: interval_r_connect (_ : (x <= x1 <= d)%R) _ _ => //; lra.
    move=> x2 [x2H ->].
    suff: (x2 <= xu)%R by rewrite /minus /plus /opp /=; toR; lra.
    move: x2H; rewrite /=. 
    case: F.valid_lb => /=; try lra.
    case: F.valid_ub => /=; try lra.
    by case; rewrite /= Eu.
  rewrite RInt_const /scal /= /mult /=.
  rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
  by field; lra.
- have : (RInt (fun=> xl) x d <= - v)%R.
    rewrite [(- _)%R](@opp_RInt_swap _ (_ : R -> R)) //.
    apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
    rewrite /f1 => x1 x1H.
    case: (ecH _ (_ : x1 \contained_in _)).
      by apply: interval_r_connect (_ : (x <= x1 <= d)%R) _ _ => //; lra.
    move=> x2 [x2H ->].
    suff: (xl <= x2)%R by rewrite /minus /plus /opp /=; toR; lra.
    move: x2H; rewrite /=. 
    case: F.valid_lb => /=; try lra.
    case: F.valid_ub => /=; try lra.
    by case; rewrite /= El.
  rewrite RInt_const /scal /= /mult /=.
  rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
  by field; lra.
- have : (RInt (fun=> xl) x d <= - v)%R.
    rewrite [(- _)%R](@opp_RInt_swap _ (_ : R -> R)) //.
    apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
    rewrite /f1 => x1 x1H.
    case: (ecH _ (_ : x1 \contained_in _)).
      by apply: interval_r_connect (_ : (x <= x1 <= d)%R) _ _ => //; lra.
    move=> x2 [x2H ->].
    suff: (xl <= x2)%R by rewrite /minus /plus /opp /=; toR; lra.
    move: x2H; rewrite /=. 
    case: F.valid_lb => /=; try lra.
    case: F.valid_ub => /=; try lra.
    by case; rewrite /= El.
  rewrite RInt_const /scal /= /mult /=.
  rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
  by field; lra.
have : (- v <= RInt (fun=> xu) x d)%R.
  rewrite [(- _)%R](@opp_RInt_swap _ (_ : R -> R)) //.
  apply: RInt_le => //; try lra; first by apply: ex_RInt_const.
  rewrite /f1 => x1 x1H.
  case: (ecH _ (_ : x1 \contained_in _)).
    by apply: interval_r_connect (_ : (x <= x1 <= d)%R) _ _ => //; lra.
  move=> x2 [x2H ->].
  suff: (x2 <= xu)%R by rewrite /minus /plus /opp /=; toR; lra.
  move: x2H; rewrite /=. 
  case: F.valid_lb => /=; try lra.
  case: F.valid_ub => /=; try lra.
  by case; rewrite /= Eu.
rewrite RInt_const /scal /= /mult /=.
rewrite {1}(_ : v = (v / (x - d) * (x - d))%R); try nra.
by field; lra.
Qed.

End CMInt.

Section CMFexpr.

Notation D := F.type.

(* language *)

Inductive fexpr :=
  fmul  (_ _ : fexpr) |
  fdiv  (_ _ : fexpr) |
  fadd  (_ _ : fexpr) |
  fsub  (_ _ : fexpr) |
  fcomp (_ _ : fexpr) |
  fvar | fconst (v : R) (iv : F.precision -> ID) 
                (H : forall p, v \contained_in iv p) |
  fln | fsqrt | fexp | finv |
  fatan | fsin | fcos.

Definition fconstz (v : Z) := fconst (fun prec => I.fromZ_correct prec v).

Definition fconstq (v1 : Z) (v2 : Z) :=
  fconst (fun prec => 
     div_correct_prec prec (I.fromZ_correct prec v1) (I.fromZ_correct prec v2)).

Declare Scope fexpr_scope.
Delimit Scope fexpr_scope with fexpr.

Fixpoint fexpr_eval e :=
(match e with
| fmul  e1 e2 => (fun u => (fexpr_eval e1 u) *  (fexpr_eval e2 u))
| fdiv  e1 e2 => (fun x => (fexpr_eval e1 x) /  (fexpr_eval e2 x))%R
| fadd  e1 e2 => (fun x => (fexpr_eval e1 x) +  (fexpr_eval e2 x))
| fsub  e1 e2 => (fun x => (fexpr_eval e1 x) -  (fexpr_eval e2 x))
| fcomp e1 e2 => (fexpr_eval e1) \o (fexpr_eval e2)
| fvar => (fun x => x)
| fconst v1 _ _ => (fun x => v1)
| fln => ln
| fsqrt => sqrt
| fexp => exp
| finv => Rinv
| fatan => atan
| fsin => sin
| fcos => cos
end)%R.

Fixpoint fexpr_ieval e :=
match e with
| fmul  e1 e2 => (fun i => mul (fexpr_ieval e1 i) (fexpr_ieval e2 i))
| fdiv  e1 e2 => (fun i => div (fexpr_ieval e1 i) (fexpr_ieval e2 i))
| fadd  e1 e2 => (fun i => add (fexpr_ieval e1 i) (fexpr_ieval e2 i))
| fsub  e1 e2 => (fun i => sub (fexpr_ieval e1 i) (fexpr_ieval e2 i))
| fcomp e1 e2 => (fexpr_ieval e1) \o (fexpr_ieval e2)
| fvar => (fun x => x)
| fconst _ v2 _ => (fun x => v2 prec)
| fln => I.ln prec
| fsqrt => I.sqrt prec
| fexp => I.exp prec
| finv => I.inv prec
| fatan => I.atan prec
| fsin => I.sin prec
| fcos => I.cos prec
end.

Lemma fexpr_ieval_correct e i x :
  x \contained_in i -> (fexpr_eval e) x \contained_in (fexpr_ieval e i).
Proof.
elim: e i x.
- move=> e1 IH1 e2 IH2 i x Hx.
  by apply: mul_correct (IH1 _ _ _) (IH2 _ _ _).
- move=> e1 IH1 e2 IH2 i x Hx.
  by apply: div_correct (IH1 _ _ _) (IH2 _ _ _).
- move=> e1 IH1 e2 IH2 i x Hx.
  by apply: add_correct (IH1 _ _ _) (IH2 _ _ _).
- move=> e1 IH1 e2 IH2 i x Hx.
  by apply: sub_correct (IH1 _ _ _) (IH2 _ _ _).
- move=> e1 IH1 e2 IH2 i x Hx.
  by apply/IH1/IH2.
- by [].
- by move=> v iv H i c xH; apply: H.
- by move => i x Hx; apply: ln_correct.
- by move => i x Hx; apply: sqrt_correct.
- by move => i x Hx; apply: exp_correct.
- by move => i x Hx; apply: inv_correct.
- by move => i x Hx; apply: atan_correct.
- by move => i x Hx; apply: sin_correct.
by move => i x Hx; apply: cos_correct.
Qed.

Fixpoint fexpr_cms n b1 vn zn z2n a b (vl1 : seq ID) vl2 (vl3 : seq ID) e :=
match e with
| fmul  e1 e2 =>
    mul_cms n a b (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e1)
                  (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e2)
| fdiv  e1 e2 =>
    div_cms a b n vn vl2 vl1
        (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e1)
        (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e2)
| fadd  e1 e2 =>
    add_cms (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e1)
            (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e2)
| fsub  e1 e2 =>
    sub_cms (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e1)
            (fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e2)
| fcomp e1 e2 =>
    let c2 := fexpr_cms n b1 vn zn z2n a b vl1 vl2 vl3 e2 in
    let v := eval_range_cms c2 in
    if I.bounded v then
      let c := I.lower v in
      let d := I.upper v in
      let t := F.cmp c d in
      if t is Xlt then
        let vl4 :=
             [seq div2
                  (add
                       (add (mul (sub (FtoI d) (FtoI c)) i)
                       (FtoI c)) (FtoI d))
                | i <- vl1] in
        comp_cms n a b c d c2 (fexpr_cms n b1 vn zn z2n c d vl1 vl2 vl4 e1)
      else if t is Xeq then
         const_cms n (fexpr_ieval e1 (I.bnd c c))
         else error_cms n
  else error_cms n
| fvar => var_cms a b n
| fconst _ v _ => const_cms n (v prec)
| fln => ln_cms a b n vn vl2 vl3
| fsqrt => sqrt_cms a b n vn vl2 vl3
| fexp => exp_cms a b vn vl2 vl3
| finv => invx_cms a b n vn vl2 vl3
| fatan => atan_cms a b n b1 vn zn z2n vl2 vl3
| fsin => sin_cms a b n b1 vn zn z2n vl2 vl3
| fcos => cos_cms a b n b1 vn zn z2n vl2 vl3
end.

Lemma fexpr_cms_correct n b1 vn v2n zn z2n a b vl1 vl2 vl3 e :
       F.cmp a b = Xlt -> F.real a -> F.real b ->
       b1 = odd n.+1 ->
       INR n.+2 \contained_in vn ->
       (2 * INR n.+2) \contained_in v2n ->
       zn = Pos.of_nat n.+2 ->
       z2n = Pos.of_nat n.+1.*2.+1 ->
       vl1 = Icheby_nodes n.+2 v2n ->
       vl2 = ITvalues n.+2 (nseq n.+2 I1) (Icheby_nodes n.+2 v2n) ->
       vl3 = Ischeby_nodes a b n.+2 v2n ->
       cms_correct n.+1 a b (fexpr_eval e)
         (fexpr_cms n.+1 b1 vn zn z2n a b vl1 vl2 vl3 e).
Proof.
move=> aLb aF bF b1E vnE v2nE znE z2nE vl1E vl2E vl3E.
elim: e a b aF bF vl3 aLb vl3E.
- move=> e1 IH1 e2 IH2 a b vl3 aLb aF bF vl3E.
  apply: mul_cms_correct => //; first by apply: IH1.
  by apply: IH2.
- move=> e1 IH1 e2 IH2 a b vl3 aLb aF bF vl3E.
  apply: div_cms_correct v2nE vl2E _ _ _ => //; first by apply: IH1.
  by apply: IH2.
- move=> e1 IH1 e2 IH2 a b vl3 aLb aF bF vl3E.
  apply: add_cms_correct => //; first by apply: IH1.
  by apply: IH2.
- move=> e1 IH1 e2 IH2 a b vl3 aLb aF bF vl3E.
  apply: sub_cms_correct => //; first by apply: IH1.
  by apply: IH2.
- move=> e1 IH1 e2 IH2 a b aF bF vl3 aLb vl3E /=.
  case E: I.bounded; last by apply: error_cms_correct.
  have [/I.lower_bounded_correct [lH1 lH2]
        /I.upper_bounded_correct [uH1 uH2]] := I.bounded_correct _ E.
  case E1: F.cmp; try by apply: error_cms_correct.
    set u := I.lower _ in lH1 E1 *.
    set v := I.upper _ in uH1 E1 *.
    apply: cms_correct_ext.
      move=> x Hx.
      have F1 : fexpr_eval e2 x \contained_in
                    (eval_range_cms (fexpr_cms n.+1 b1 vn zn z2n a
                                    b vl1 vl2 vl3 e2)).
        apply: eval_range_cms_correct (aLb) (aF) (bF) _ _ Hx => //.
          by apply: IH2.
        by apply: isubset_refl.
      rewrite /= (_ : fexpr_eval e2 x = D2R u); first by apply: refl_equal.
      set e := eval_range_cms _ in F1.
      have /lH2 : exists x, x \contained_in e by exists (fexpr_eval e2 x).
      rewrite -/u -/v -/e => cH.
      rewrite cH /= lH1 uH1 // in F1.
      move: E1; rewrite F.cmp_correct !I.F'.classify_real; last 2 first.
      - by rewrite F.real_correct uH1.
      - by rewrite F.real_correct lH1.
      rewrite uH1 lH1 /=; case: Raux.Rcompare_spec => //.
      by rewrite /D2R; lra.
    apply: const_cms_correct.
    apply: fexpr_ieval_correct.
    apply: FtoI_correct.
    by rewrite F.real_correct lH1.
  apply: comp_cms_correct => //.
  - by rewrite F.real_correct lH1.
  - by rewrite F.real_correct uH1.
  - case: eval_range_cms {E1}E lH1 lH2 uH1 uH2 => //= l u /andP[lF uF] lX _ uX _.
    rewrite !I.F'.classify_real; last 2 first.
    - by rewrite F.real_correct uX.
    - by rewrite F.real_correct lX.
    rewrite !F.cmp_correct // !I.F'.classify_real; last 2 first.
    - by rewrite F.real_correct uX.
    - by rewrite F.real_correct lX.
    by rewrite lX uX /=; do 2 case: Raux.Rcompare_spec => //; lra.
  - by apply: IH2.
  apply: IH1 => //.
  - by rewrite F.real_correct lH1.
  - by rewrite F.real_correct uH1.
  by congr (map _ _).
- by move=> a b aF bF vl3 aLb vl3E; apply: var_cms_correct.
- move=> z1 z2 H a b aF bF vl3 aLb vl3E.
  by apply: const_cms_correct.
- by move=> a b aF bF vl3 aLb vl3E; apply: ln_cms_correct v2nE _ _.
- by move=> a b aF bF vl3 aLb vl3E; apply: sqrt_cms_correct v2nE _ _.
- by move=> a b aF bF vl3 aLb vl3E; apply: exp_cms_correct v2nE _ _.
- by move=> a b aF bF vl3 aLb vl3E; apply: invx_cms_correct v2nE _ _.
- by move=> a b aF bF vl3 aLb vl3E; apply: atan_cms_correct v2nE _ _ _ _.
- by move=> a b aF bF vl3 aLb vl3E; apply: sin_cms_correct v2nE _ _ _ _.
by move=> a b aF bF vl3 aLb vl3E; apply: cos_cms_correct v2nE _ _ _ _.
Qed.

End CMFexpr.

Section CMIexpr.

Notation D := F.type.

(* language *)

Inductive iexpr :=
  imul  (_ _ : iexpr) |
  idiv  (_ _ : iexpr) |
  iadd  (_ _ : iexpr) |
  isub  (_ _ : iexpr) |
  iconst (v : R) (iv : F.precision -> ID) 
                (H : forall p, v \contained_in iv p) |
  iint (v1 : R) (iv1 : F.precision -> ID) 
                (H1 : forall p, v1 \contained_in iv1 p)
      (v2 : R) (iv2 : F.precision -> ID) 
                (H2 : forall p, v2 \contained_in iv2 p)  
                (_ : fexpr)        
                 |
  iln (_ : iexpr) | isqrt (_ : iexpr) | iexp (_ : iexpr) | 
  iinv (_ : iexpr) |
  iatan (_ : iexpr) | isin (_ : iexpr) | icos (_ : iexpr).

Definition iconstz (v : Z) := iconst (fun prec => I.fromZ_correct prec v).

Definition iconstq (v1 : Z) (v2 : Z) :=
  iconst (fun prec => 
     div_correct_prec prec (I.fromZ_correct prec v1) (I.fromZ_correct prec v2)).

Definition iintz (v1 v2 : Z) := 
   iint (fun prec => I.fromZ_correct prec v1) 
        (fun prec => I.fromZ_correct prec v2).
        
Definition iintq (v1 v2 v3 v4 : Z) :=
  iint (fun prec => 
     div_correct_prec prec (I.fromZ_correct prec v1) (I.fromZ_correct prec v2))
       (fun prec => 
     div_correct_prec prec (I.fromZ_correct prec v3) (I.fromZ_correct prec v4)).

Declare Scope iexpr_scope.
Delimit Scope iexpr_scope with iexpr.

Fixpoint iexpr_eval e :=
(match e with
| imul e1 e2 => (iexpr_eval e1) *  (iexpr_eval e2)
| idiv e1 e2 => (iexpr_eval e1) /  (iexpr_eval e2)
| iadd e1 e2 => (iexpr_eval e1) +  (iexpr_eval e2)
| isub e1 e2 => (iexpr_eval e1) -  (iexpr_eval e2)
| iconst v1 _ _ => v1
| iint v1 _ _ v2 _ _ f => RInt (fun x => fexpr_eval f x) v1 v2
| iln e => ln (iexpr_eval e)
| isqrt e => sqrt (iexpr_eval e)
| iexp e => exp (iexpr_eval e)
| iinv e => Rinv (iexpr_eval e)
| iatan e => atan (iexpr_eval e)
| isin e => sin (iexpr_eval e)
| icos e => cos (iexpr_eval e)
end)%R.

Fixpoint iexpr_icheck e :=
(match e with
| imul e1 e2 => (iexpr_icheck e1) || (iexpr_icheck e2)
| idiv e1 e2 => (iexpr_icheck e1) || (iexpr_icheck e2)
| iadd e1 e2 => (iexpr_icheck e1) || (iexpr_icheck e2)
| isub e1 e2 => (iexpr_icheck e1) || (iexpr_icheck e2)
| iconst v1 _ _ => false
| iint v1 _ _ v2 _ _ f => true
| iln e => (iexpr_icheck e)
| isqrt e => (iexpr_icheck e)
| iexp e => (iexpr_icheck e)
| iinv e => (iexpr_icheck e)
| iatan e => (iexpr_icheck e)
| isin e => (iexpr_icheck e)
| icos e => (iexpr_icheck e)
end)%R.

Definition mk_wf e1 e2 f1 f2 :=
  if iexpr_icheck e1 then if iexpr_icheck e2 then f1 /\ f2 else f1 else f2.

Fixpoint iexpr_wf e :=
(match e with
| imul e1 e2 => mk_wf e1 e2 (iexpr_wf e1) (iexpr_wf e2)
| idiv e1 e2 => mk_wf e1 e2 (iexpr_wf e1) (iexpr_wf e2)
| iadd e1 e2 => mk_wf e1 e2 (iexpr_wf e1) (iexpr_wf e2)
| isub e1 e2 => mk_wf e1 e2 (iexpr_wf e1) (iexpr_wf e2)
| iconst v1 _ _ => True
| iint _ v1 _  _ v2 _ f => 
    if I.bounded (v1 prec) && I.bounded (v2 prec) then
      let a := F.min (I.lower (v1 prec)) (I.lower (v2 prec)) in
      let b := F.max (I.upper (v1 prec)) (I.upper (v2 prec)) in
      let t := F.cmp a b in
      if t is Xlt then ex_RInt (fexpr_eval f) (D2R a) (D2R b)
      else True else True
| iln e => (iexpr_wf e)
| isqrt e => (iexpr_wf e)
| iexp e => (iexpr_wf e)
| iinv e => (iexpr_wf e)
| iatan e => (iexpr_wf e)
| isin e => (iexpr_wf e)
| icos e => (iexpr_wf e)
end)%R.

Lemma iexpr_icheck_correct e :
  iexpr_icheck e = false -> iexpr_wf e <-> true.
Proof.
by elim: e => //=; rewrite /mk_wf;
   move=> e1 e1H e2 e2H; case: iexpr_icheck e1H => // ->.
Qed.

Lemma mk_wf_correct e1 e2 :
 mk_wf e1 e2 (iexpr_wf e1) (iexpr_wf e2) <-> (iexpr_wf e1) /\ (iexpr_wf e2).
Proof.
rewrite /mk_wf.
have := @iexpr_icheck_correct e1; have := @iexpr_icheck_correct e2;
do 2 case: iexpr_icheck => //; intuition.
Qed.

Fixpoint iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e :=
match e with
| imul e1 e2 => mul 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e1) 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e2)
| idiv e1 e2 => div
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e1) 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e2)
| iadd e1 e2 => add 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e1) 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e2)
| isub  e1 e2 => sub 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e1) 
         (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e2)
| iconst _ v2 _ => (v2 prec)
| iint _ v1 _ _ v2 _ e => 
    if I.bounded (v1 prec) && I.bounded (v2 prec) then
      let a := F.min (I.lower (v1 prec)) (I.lower (v2 prec)) in
      let b := F.max (I.upper (v1 prec)) (I.upper (v2 prec)) in
      let t := F.cmp a b in
      if t is Xlt then
        let vl2 := 
           ITvalues n.+2 (nseq n.+2 I1) 
                   (Icheby_nodes n.+2 v2n) in
        let vl3 := Ischeby_nodes a b n.+2 v2n in
        let c := fexpr_cms n.+1 b1 vn zn z2n a b vl1 vl2 vl3 e in
        eval_shaw_cms a b (belast_cms (int_cms a b c (v1 prec))) (v2 prec)
      else Float.Inan
    else Float.Inan
| iln e => I.ln prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| isqrt e => I.sqrt prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| iexp e => I.exp prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| iinv e => I.inv prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| iatan e => I.atan prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| isin e => I.sin prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
| icos e => I.cos prec (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e)
end.

Lemma iexpr_ieval_correct n b1 vn v2n zn z2n (vl1 : seq ID) e :
       b1 = odd n.+1 ->
       INR n.+2 \contained_in vn ->
       (2 * INR n.+2) \contained_in v2n ->
       zn = Pos.of_nat n.+2 ->
       z2n = Pos.of_nat n.+1.*2.+1 ->
       vl1 = Icheby_nodes n.+2 v2n ->
  iexpr_wf e ->
  (iexpr_eval e) \contained_in
    (iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID) e).
Proof.
move=> b1E n2H n22H zn2 z2nE vl1E.
elim: e => //.
- move=> e1 IH1 e2 IH2 /mk_wf_correct[e1W e2W].
  by apply: mul_correct (IH1 _) (IH2 _).
- move=> e1 IH1 e2 IH2 /mk_wf_correct[e1W e2W].
  by apply: div_correct (IH1 _) (IH2 _).
- move=> e1 IH1 e2 IH2 /mk_wf_correct[e1W e2W].
  by apply: add_correct (IH1 _) (IH2 _).
- move=> e1 IH1 e2 IH2 /mk_wf_correct[e1W e2W].
  by apply: sub_correct (IH1 _) (IH2 _).
- by move=> v iv H _; apply: H.
- move=> v1 iv1 v1H v2 iv2 v2H e.
  rewrite /iexpr_wf /iexpr_eval /iexpr_ieval.
  case E1: I.bounded => /=; last by [].
  have [/I.lower_bounded_correct [v1lH1 v1lH2]
        /I.upper_bounded_correct [v1uH1 v1uH2]] := I.bounded_correct _ E1.
  case E2: I.bounded => /=; last by [].
  have [/I.lower_bounded_correct [v2lH1 v2lH2]
        /I.upper_bounded_correct [v2uH1 v2uH2]] := I.bounded_correct _ E2.
  have liv1iv2F : F.real (F.min (I.lower (iv1 prec)) (I.lower (iv2 prec))).
    have := F.min_correct (I.lower (iv1 prec)) (I.lower (iv2 prec)).
    rewrite !I.F'.classify_real /=; last 2 first.
    - by rewrite F.real_correct v2lH1.
    - by rewrite F.real_correct v1lH1.
    by rewrite F.real_correct v2lH1 v1lH1 /= => ->.
  have uiv1iv2F : F.real (F.max (I.upper (iv1 prec)) (I.upper (iv2 prec))).
    have := F.max_correct (I.upper (iv1 prec)) (I.upper (iv2 prec)).
    rewrite !I.F'.classify_real /=; last 2 first.
    - by rewrite F.real_correct v2uH1.
    - by rewrite F.real_correct v1uH1.
    by rewrite F.real_correct v2uH1 v1uH1 /= => ->.
  case E3: F.cmp => /= H //.
  have HH : v2 \contained_in iv2 prec by [].
  apply: (@eval_shaw_cms_correct n.+1) => //; last first.
    case: (iv2) v2lH1 v2lH2 v2uH1 v2uH2 liv1iv2F uiv1iv2F E3 HH => //=.
      by rewrite I.F'.nan_correct.
    move=> l1 u1 lX Hx uX _ minF maxF.
    rewrite !I.F'.valid_lb_real; last by rewrite F.real_correct lX.
    rewrite !I.F'.valid_ub_real /=; last by rewrite F.real_correct uX.
    have := F.min_correct (I.lower (iv1 prec)) l1.
    have := F.max_correct (I.upper (iv1 prec)) u1.    
    rewrite !I.F'.classify_real //; last 4 first.
    - by rewrite F.real_correct lX.
    - by rewrite F.real_correct v1lH1.
    - by rewrite F.real_correct uX.
    - by rewrite F.real_correct v1uH1.
    rewrite !F.cmp_correct //=.
    rewrite !I.F'.classify_real //; last 2 first.
    - by rewrite F.real_correct uX.
    - by rewrite F.real_correct lX.
    rewrite uX lX.
    move: minF; rewrite F.real_correct; case: F.toX => // r _.
    move: maxF; rewrite F.real_correct; case: F.toX => //= l _.
    rewrite v1lH1 v1uH1 /= => [] [->] [->].
    case: Raux.Rcompare_spec => //= rLl _.
    case: Raux.Rcompare_spec => //=.
    - by rewrite /Rmin; case: Rle_dec; lra.
    - case: Raux.Rcompare_spec => //=.
      by rewrite /Rmax /Rmin; do 2 case: Rle_dec; lra.
    case: Raux.Rcompare_spec => //=.
    by rewrite /Rmax /Rmin; do 2 case: Rle_dec; lra.
  apply: belast_cms_correct => //.
  apply: int_cms_correct => //.
    have : v1 \contained_in iv1 prec by [].
    case: (iv1) v1lH1 v1lH2 v1uH1 v1uH2 liv1iv2F uiv1iv2F E3 => //=.
      by rewrite I.F'.nan_correct.
    move=> l1 u1 lX Hx uX _ minF maxF.
    rewrite !I.F'.valid_lb_real; last by rewrite F.real_correct lX.
    rewrite !I.F'.valid_ub_real /=; last by rewrite F.real_correct uX.
    have := F.min_correct l1 (I.lower (iv2 prec)).
    have := F.max_correct u1 (I.upper (iv2 prec)).    
    rewrite !I.F'.classify_real //; last 4 first.
    - by rewrite F.real_correct v2lH1.
    - by rewrite F.real_correct lX.
    - by rewrite F.real_correct v2uH1.
    - by rewrite F.real_correct uX.
    rewrite !F.cmp_correct //=.
    rewrite !I.F'.classify_real //; last 2 first.
    - by rewrite F.real_correct uX.
    - by rewrite F.real_correct lX.
    rewrite uX lX.
    move: minF; rewrite F.real_correct; case: F.toX => // r _.
    move: maxF; rewrite F.real_correct; case: F.toX => //= l _.
    rewrite v2lH1 v2uH1 /= => [] [->] [->].
    case: Raux.Rcompare_spec => //= rLl _.
    case: Raux.Rcompare_spec => //=.
    - by rewrite /Rmin; case: Rle_dec; lra.
    - case: Raux.Rcompare_spec => //=.
      by rewrite /Rmax /Rmin; do 2 case: Rle_dec; lra.
    case: Raux.Rcompare_spec => //=.
    by rewrite /Rmax /Rmin; do 2 case: Rle_dec; lra.
  apply: fexpr_cms_correct => //.   
    by [].
  by [].
- by move => i H H1 /=; apply/ln_correct/H.
- by move => i H H1; apply/sqrt_correct/H.
- by move => i H H1; apply/exp_correct/H.
- by move => i H H1; apply/inv_correct/H.
- by move => i H H1; apply/atan_correct/H.
- by move => i H H1; apply/sin_correct/H.
by move => i H H1; apply/cos_correct/H.
Qed.

Definition mk_iexpr_ieval n := 
  let b1 := odd n.+1 in
  let vn := I.fromZ prec (Z.of_nat n.+2) in
  let v2n := I.fromZ prec (Z.of_nat (n.+2).*2) in
  let zn := Pos.of_nat n.+2 in
  let z2n := Pos.of_nat n.+1.*2.+1 in
  let vl1 := Icheby_nodes n.+2 v2n in
  iexpr_ieval n b1 vn v2n zn z2n (vl1 : seq ID).

Lemma mk_iexpr_ieval_correct n e :
  iexpr_wf e -> (iexpr_eval e) \contained_in (mk_iexpr_ieval n e).
Proof.
move=> eW; apply: iexpr_ieval_correct => //.
  suff ->: INR n.+2 = IZR (Z.of_nat n.+2) by apply: I.fromZ_correct.
  by rewrite IZR_Zof_nat; toR.
suff ->: (2 * INR n.+2)%R = IZR (Z.of_nat (n.+2).*2) by apply: I.fromZ_correct.
by rewrite IZR_Zof_nat -addnn natrD; toR; lra.
Qed.

Lemma mk_iexpr_ieval_correct_r n a b e :
  (iexpr_wf e -> 
  I.bounded (mk_iexpr_ieval n e) ->
  a <= D2R (I.lower (mk_iexpr_ieval n e)) ->
   D2R (I.upper (mk_iexpr_ieval n e)) <= b ->
  a <= (iexpr_eval e) <= b)%R.
Proof.
move=> eW eI aL bG.
have /I.bounded_correct[/I.lower_bounded_correct [lH _]
                        /I.upper_bounded_correct [uH _] ] := eI.
have := mk_iexpr_ieval_correct n eW.
move: eI lH uH aL bG ; case: mk_iexpr_ieval => //= l u /andP[lF uF].
rewrite /D2R !I.F'.valid_lb_real // I.F'.valid_ub_real //=.
move=> -> -> /=; lra.
Qed.

End CMIexpr.

End CPoly_interval.

Declare Scope fexpr_scope.
Notation "a * b" := (fmul a b) : fexpr_scope.
Notation "a / b" := (fdiv a b) : fexpr_scope.
Notation "a + b" := (fadd a b) : fexpr_scope.
Notation "a - b" := (fsub a b) : fexpr_scope.
Notation " 'x " := (fvar) : fexpr_scope.
Notation " 'ln(x)' " := (fln) : fexpr_scope.
Notation " 'ln(' e ')' " := (fcomp fln e)
  (format "'ln(' e ')' " ) : fexpr_scope.
Notation " 'sqrt(x)' " := (fsqrt) : fexpr_scope.
Notation " 'sqrt(' e ')' " := (fcomp fsqrt e)
  (format "'sqrt(' e ')' " ) : fexpr_scope.
Notation " 'exp(x)' " := (fexp) : fexpr_scope.
Notation " 'exp(' e ')' " := (fcomp fexp e)
  (format "'exp(' e ')'" ) : fexpr_scope.
Notation " '1/x' " := (finv) : fexpr_scope.
Notation "'/(' x ')'" := (fcomp finv x)
   (format "/( x )" ): fexpr_scope.
Notation "'c(' x , y ')'" := (fconstq x y)
   (format "c( x ,  y ) " ): fexpr_scope.
Notation "'c(' x ')'" := (fconstz x)
   (format "c( x ) " ): fexpr_scope.
Notation " '1' " := (fconstz 1) : fexpr_scope.
Notation " '2' " := (fconstz 2) : fexpr_scope.
Notation " 'PI' " := (fconst (I.pi_correct)) : fexpr_scope.
Notation " 'atan(x)'" := (fatan) (at level 10) : fexpr_scope .
Notation " 'atan(' e ')'" := (fcomp fatan e)
  (format "'atan(' e ')'" ) : fexpr_scope.
Notation " 'sin(x)'" := (fsin) (at level 10) : fexpr_scope .
Notation " 'sin(' e ')'" := (fcomp fsin e)
  (format "'sin(' e ')'" ) : fexpr_scope.
Notation " 'cos(x)'" := (fcos) (at level 10) : fexpr_scope .
Notation " 'cos(' e ')'" := (fcomp fcos e)
  (format "'cos(' e ')'" ) : fexpr_scope.
Delimit Scope fexpr_scope with fexpr.

Declare Scope iexpr_scope.
Notation "a * b" := (imul a b) : iexpr_scope.
Notation "a / b" := (idiv a b) : iexpr_scope.
Notation "a + b" := (iadd a b) : iexpr_scope.
Notation "a - b" := (isub a b) : iexpr_scope.
Notation " 'RInt[' a , b , c , d '](' e ')' " :=
    (iintq a b c d e)
  : iexpr_scope.
Notation " 'RInt[' a , b '](' e ')' " :=
    (iintz a b e)
  : iexpr_scope.
Notation " 'ln(' e ')' " := (iln e)
  (format "'ln(' e ')' " ) : iexpr_scope.
Notation " 'sqrt(' e ')' " := (isqrt e)
  (format "'sqrt(' e ')' " ) : iexpr_scope.
Notation " 'exp(' e ')' " := (iexp e)
  (format "'exp(' e ')'" ) : iexpr_scope.
Notation "'/(' x ')'" := (iinv x)
   (format "/( x )" ): iexpr_scope.
Notation "'c(' x , y ')'" := (iconstq x y)
   (format "c( x ,  y ) " ): iexpr_scope.
Notation "'c(' x ')'" := (iconstz x)
   (format "c( x ) " ): iexpr_scope.
Notation " '1' " := (iconstz 1) : iexpr_scope.
Notation " '2' " := (iconstz 2) : iexpr_scope.
Notation " 'PI' " := (iconst (I.pi_correct)) : iexpr_scope.
Notation " 'atan(' e ')'" := (iatan e)
  (format "'atan(' e ')'" ) : iexpr_scope.
Notation " 'sin(' e ')'" := (isin e)
  (format "'sin(' e ')'" ) : iexpr_scope.
Notation " 'cos(' e ')'" := (icos e)
  (format "'cos(' e ')'" ) : iexpr_scope.
Delimit Scope iexpr_scope with iexpr.


Section Solver.

Definition mk_cms prec n a b f :=
  let ob := odd n in
  let zn := Pos.of_nat n.+1 in
  let z2n :=  (2 * zn - 1)%positive in
  let vn :=  I.fromZ prec (Zpos zn) in
  let v2n :=  I.fromZ prec (Zpos z2n + 1) in
  let l1 :=  nseq n.+1 (I1 prec) in
  let vl1 := Icheby_nodes prec n.+1 v2n in
  let vl2 := ITvalues prec n.+1 l1 vl1 in
  let vl3 := Ischeby_nodes prec a b n.+1 v2n in
  let x := fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 f in x.

Let lem1 n : Z.pos (Pos.of_nat n.+2) = Z.of_nat n.+2.
Proof. by rewrite /Z.of_nat Pos.of_nat_succ. Qed.

Lemma mk_cms_correct prec n a b f :
    F.cmp a b = Xlt -> F.real a -> F.real b ->
    cms_correct n.+1 a b (fexpr_eval f) (mk_cms prec n.+1 a b f).
Proof.
move=> aLb aF bF.
rewrite /mk_cms.
set ob := odd _.
set zn := Pos.of_nat _.
set z2n :=  (_ - _)%positive.
set vn :=  I.fromZ _ _.
set v2n :=  I.fromZ _ _.
set l1 :=  nseq _ _.
set vl1 := Icheby_nodes _ _ _.
set vl2 := ITvalues _ _ _ _.
set vl3 := Ischeby_nodes _ _ _ _ _.
have z2nE : z2n = Pos.of_nat (n.+1).*2.+1.
  rewrite /z2n /zn [in LHS]Nat2Pos.inj_succ //.
  rewrite [RHS]Nat2Pos.inj_succ // !Pplus_one_succ_r.
  rewrite -muln2 Nat2Pos.inj_mul // [Pos.of_nat 2]/=; lia.
apply: fexpr_cms_correct => //.
  rewrite /vn /zn INR_IZR_INZ /Z.of_nat Pos.of_nat_succ.
  by apply: I.fromZ_correct.
rewrite /v2n z2nE INR_IZR_INZ /Z.of_nat Pos.of_nat_succ.
rewrite Nat2Pos.inj_succ // Pplus_one_succ_r.
rewrite -muln2 Nat2Pos.inj_mul // [Pos.of_nat 2]/=.
rewrite [Pos.of_nat n.+2]Nat2Pos.inj_succ // Pplus_one_succ_r.
rewrite -mult_IZR.
rewrite (_ : (Zpos(Pos.of_nat n.+1 * 2 + 1) + 1 =
              2 * Z.pos (Pos.of_nat n.+1 + 1))%Z); last by lia.
by apply: I.fromZ_correct.
Qed.

Fixpoint solve_rec test n a b:=
  if n is n1.+1 then
    if F.cmp a b is Xlt then
    if test a b then true else
    let a1 := I.midpoint (I.bnd a b) in
      let t :=  solve_rec test n1 a a1 in
      if t then solve_rec test n1 a1 b else false
    else false
  else false.

Lemma solve_recE test n a b :
  solve_rec test n.+1 a b =
    if F.cmp a b is Xlt then
    if test a b then true else
    let a1 := I.midpoint (I.bnd a b) in
      let t :=  solve_rec test n a a1 in
      if t then solve_rec test n a1 b else false
    else false.
Proof. by []. Qed.

Definition solve prec n Iab f obj depth :=
  let ob := odd n in
  let zn := Pos.of_nat n.+1 in
  let z2n :=  (2 * zn - 1)%positive in
  let vn :=  I.fromZ prec (Zpos zn) in
  let v2n :=  I.fromZ prec (Zpos z2n + 1) in
  let l1 :=  nseq n.+1 (I1 prec) in
  let vl1 := Icheby_nodes prec n.+1 v2n in
  let vl2 := ITvalues prec n.+1 l1 vl1 in
  let test a1 b1 :=
       let vl3 := Ischeby_nodes prec a1 b1 n.+1 v2n in
       let x := fexpr_cms prec n ob vn zn z2n a1 b1 vl1 vl2 vl3 f in
       let v := eval_range_cms prec x in I.subset v obj
  in  solve_rec test depth (I.lower Iab) (I.upper Iab).

Let D2R := I.T.toR.



Lemma contains_subset a b c:
   contains (I.convert a) (Xreal c) ->
   I.subset a b->
   contains (I.convert b) (Xreal c).
Proof.
move=> H /I.subset_correct; move: H.
case: I.convert => //= [|l1 u1]; first by case: I.convert.
case: I.convert => //= l2 u2.
rewrite /le_lower /le_upper.
by (case : l1 => [|r1]); (case : l2 => [|r2]);
   (case : u1 => [|r3]); (case : u2 => [|r4]) => //=; lra.
Qed.

Definition is_interval a :=
  if a is Float.Ibnd u l then
   if (F.toX u, F.toX l) is (Xreal _, Xreal _) then true else false
  else false.

Lemma D2R_divWl prec a b a1 b1 x
   (i1 := I.div prec (I.fromZ prec a)  (I.fromZ prec  b))
   (i2 := I.div prec (I.fromZ prec a1) (I.fromZ prec b1)) :
  is_interval i1 -> is_interval i2 -> Z.eqb b 0 = false -> Z.eqb b1 0 = false ->
  (IZR a / IZR b <= x <= IZR a1 / IZR b1 ->
   D2R (I.lower i1) <= x  <= D2R (I.upper i2))%R.
Proof.
move=> Hi1 Hi2 bP b1P H.
have := I.div_correct prec (I.fromZ prec a) (I.fromZ prec b)
              (Xreal (IZR a)) (Xreal (IZR b))
             (I.fromZ_correct _ _) (I.fromZ_correct _ _).
move: Hi1.
rewrite /i1 /D2R /I.T.toR /Xdiv'.
case: I.div => //= [] //= l u.
case: Xreal.is_zero_spec => /= [H1|IZR_nZ1].
  by rewrite (eq_IZR _ 0 H1) in bP.
case: F.valid_lb => /=; try lra.
case: F.valid_ub => /=; try lra.
case: F.toX => //= r; case: F.toX => //= r1 _ H1.
have := I.div_correct prec (I.fromZ prec a1) (I.fromZ prec b1)
              (Xreal (IZR a1)) (Xreal (IZR b1))
             (I.fromZ_correct _ _) (I.fromZ_correct _ _).
move: Hi2.
rewrite /i2 /I.T.toR /Xdiv'.
case: I.div => //= [] // l1 u1.
case: Xreal.is_zero_spec => /= [H2|IZR_nZ2].
  by rewrite (eq_IZR _ 0 H2) in b1P.
case: F.toX => //= r2.
case: F.toX => //= r3 _.
case: F.valid_lb => //=; try lra.
case: F.valid_ub => //=; try lra.
Qed.

Lemma D2R_divWr prec a b a1 b1 x 
  (i1 := I.div prec (I.fromZ prec a) (I.fromZ prec b))
  (i2 := I.div prec (I.fromZ prec a1) (I.fromZ prec b1)) :
  is_interval i1 -> is_interval i2 ->
  Z.eqb b 0 = false -> Z.eqb b1 0 = false ->
  (I.T.toR (I.upper i1) <= x <= I.T.toR (I.lower i2) ->
   IZR a / IZR b <= x <= IZR a1 / IZR b1)%R.
Proof.
move=> Hi1 Hi2 bP b1P.
have := I.div_correct prec (I.fromZ prec a) (I.fromZ prec b)
              (Xreal (IZR a)) (Xreal (IZR b))
             (I.fromZ_correct _ _) (I.fromZ_correct _ _).
move: Hi1.
rewrite /i1 /I.T.toR /Xdiv'.
case: I.div => //= [] // u l.
case: Xreal.is_zero_spec => /= [H1|IZR_nZ1].
  by rewrite (eq_IZR _ 0 H1) in bP.
case: F.toX => //= r; case: F.toX => //= r1 _.
case: F.valid_lb => //=; try lra.
case: F.valid_ub => //=; try lra.
have := I.div_correct prec (I.fromZ prec a1) (I.fromZ prec b1)
              (Xreal (IZR a1)) (Xreal (IZR b1))
             (I.fromZ_correct _ _) (I.fromZ_correct _ _).
move: Hi2.
rewrite /i2 /I.T.toR /Xdiv'.
case: I.div => //= [] // u1 l1.
case: Xreal.is_zero_spec => /= [H2|IZR_nZ2].
  by rewrite (eq_IZR _ 0 H2) in b1P.
case: F.valid_lb => //=; try lra.
case: F.valid_ub => //=; try lra.
case: F.toX => //= r2; case: F.toX => //= r3 _ H2.
by lra.
Qed.

Lemma solve_correct prec depth n f a1 a2 b1 b2 c1 c2 d1 d2 x
     (i1 := I.div prec (I.fromZ prec a1) (I.fromZ prec b1))
     (i2 := I.div prec (I.fromZ prec a2) (I.fromZ prec b2))
     (j1 := I.div prec (I.fromZ prec c1) (I.fromZ prec d1))
     (j2 := I.div prec (I.fromZ prec c2) (I.fromZ prec d2))
     (Iab := I.bnd (I.lower i1) (I.upper i2))
     (obj := I.bnd (I.upper j1) (I.lower j2)) :
  is_interval i1 -> is_interval i2 -> is_interval j1 -> is_interval j2 ->
  Z.eqb b1 0 = false -> Z.eqb d1 0 = false ->
  Z.eqb b2 0 = false -> Z.eqb d2 0 = false ->
  F.cmp (I.upper j1) (I.lower j2) = Xlt -> 
  F.real (I.lower i1) -> F.real (I.upper i2) ->
  F.real (I.upper j1) -> F.real (I.lower j2) ->
   solve prec n.+1 Iab f obj depth = true ->
   (IZR a1 / IZR b1 <= x <= IZR a2 / IZR b2)%R ->
   (IZR c1 / IZR d1 <= fexpr_eval f x <= IZR c2 / IZR d2)%R.
Proof.
move=> Ii1 Ii2 Ij1 Ij2 b1P d1P b2P d2P uLv i1F i2F j1F j2F Hs H1.
apply: D2R_divWr Ij1 Ij2 d1P d2P _.
have := D2R_divWl Ii1 Ii2 b1P b2P H1.
move: i1F i2F j1F j2F.
rewrite  -/i1 -/i2 -/j1 -/j2.
rewrite -[I.lower i1] / (I.lower Iab).
rewrite -[I.upper i2] / (I.upper Iab).
rewrite -[I.upper j1] / (I.lower obj).
rewrite -[I.lower j2] / (I.upper obj) => lIF uIF lOF uOF H2.
move: Hs.
rewrite /solve.
set ob := odd _.
set zn := Pos.of_nat _.
set z2n :=  (_ - _)%positive.
set vn :=  I.fromZ _ _.
set v2n :=  I.fromZ _ _.
set l1 :=  nseq _ _.
set vl1 := Icheby_nodes _ _ _.
set vl2 := ITvalues _ _ _ _.
elim: depth (I.lower Iab) (I.upper Iab) lIF uIF H2 => // m IH a b aF bF.
rewrite solve_recE.
case aLb : (F.cmp a b) => //.
have z2nE : z2n = Pos.of_nat (n.+1).*2.+1.
  rewrite /z2n /zn [in LHS]Nat2Pos.inj_succ //.
  rewrite [RHS]Nat2Pos.inj_succ // !Pplus_one_succ_r.
  rewrite -muln2 Nat2Pos.inj_mul // [Pos.of_nat 2]/=; lia.
have [HI aLxLb _|] := boolP (I.subset _ _).
  have: contains (I.convert obj) (Xreal (fexpr_eval f x)).
    apply: contains_subset HI.
    apply: eval_range_cms_correct => //.
    - by exact: aLb.
    - by [].
    - by [].
    - apply: fexpr_cms_correct => //.
        rewrite /vn /zn INR_IZR_INZ /Z.of_nat Pos.of_nat_succ.
        by apply: I.fromZ_correct.
      rewrite /v2n z2nE INR_IZR_INZ /Z.of_nat Pos.of_nat_succ.
      rewrite Nat2Pos.inj_succ // Pplus_one_succ_r.
      rewrite -muln2 Nat2Pos.inj_mul // [Pos.of_nat 2]/=.
      rewrite [Pos.of_nat n.+2]Nat2Pos.inj_succ // Pplus_one_succ_r.
      rewrite -mult_IZR.
      rewrite (_ : (Zpos(Pos.of_nat n.+1 * 2 + 1) + 1 =
                2 * Z.pos (Pos.of_nat n.+1 + 1))%Z); last by lia.
      by apply: I.fromZ_correct.
    - suff: I.subset (I.bnd a b) (I.bnd a b) by apply.
      by apply: isubset_refl.
    move: aLxLb aLb.
    rewrite /D2R /= /I.T.toR.
    rewrite  /= !F.cmp_correct //.
    rewrite !I.F'.classify_real //.
    rewrite I.F'.valid_lb_real // I.F'.valid_ub_real //=.
    by case: F.toX => //=; case: F.toX.
  move: lOF uOF uLv.
  rewrite -[I.upper j1] / (I.lower obj).
  rewrite -[I.lower j2] / (I.upper obj).
  case: (obj) .
    rewrite /D2R /= /I.T.toR.
    by rewrite  /= !F.cmp_correct ?F.nan_correct.
  move=> u1 v1 /= u1F v1F.
  rewrite /D2R /= /I.T.toR I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  rewrite  /= !F.cmp_correct !I.F'.classify_real //.
  by case: F.toX => //=; case: F.toX.
set ma := I.midpoint _.
have := IH a ma.
lazy zeta.
case: solve_rec => //.
have := IH ma b.
case: solve_rec => //.
have [] := I.midpoint_correct (I.bnd a b) => [|V1 V2].
  exists (D2R a) => /=.
  move: aLb; rewrite !F.cmp_correct // !I.F'.classify_real //.
  rewrite /D2R -I.F'.real_correct //.
  rewrite I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  move: aF bF; rewrite !F.real_correct.
  case: F.toX => [|r1] //; case: F.toX => [|r2] //= _ _.
  case: Raux.Rcompare_spec => //; lra.
have mF : F.real ma by rewrite F.real_correct V1. 
move=> / (_  mF bF _ isT) Hv1/ (_  aF mF _ isT) Hv2 MM aLxLb _.
have HH : (D2R a <= D2R ma <= D2R b)%R.
  move: aLb V2; rewrite F.cmp_correct /D2R /=.
  rewrite !I.F'.classify_real // I.F'.valid_lb_real // I.F'.valid_ub_real //=.
  move: V1.
  by rewrite !I.F'.real_correct //= aF bF.
have [HH1|HH1]: (D2R a <= x <= D2R ma \/ D2R ma <= x <= D2R b)%R.
- by lra.
- by apply: Hv2.
by apply: Hv1.
Qed.

End Solver.

(* Tactic to solve box problems :
       a1/b1 <= x <= a2/b2 -> a3/b3 <= f x <= a4/b4
*)

Lemma Rpower_IZR a b :
   Rpower (IZR (Zpos a)) (IZR (Zpos b)) = IZR (Zpos a ^ Zpos b).
Proof.
by rewrite -powerRZ_Rpower ?Raux.IZR_Zpower_pos //; apply: RIneq.IZR_lt.
Qed.

Ltac cheby_solve_tac prec depth degr tang H :=
  rewrite ?Rpower_IZR -?RIneq.mult_IZR;
  match type of H with
  | (_ <= ?x <= _)%R =>
    match goal with
    |- (_ <= ?X <= _)%R =>
        rewrite (_ :  X = fexpr_eval tang x); last by apply: refl_equal
    end
  end;
  apply: (@solve_correct prec depth degr.-1 _ _ _) H;
  match goal with
  |  |- is_true (is_interval ?X) => native_cast_no_check (refl_equal true)
  |  |- is_true (SFBI2.real _) => native_cast_no_check (refl_equal true)
  |  |-  _ = ?X => native_cast_no_check (refl_equal X)
  end.

End CPoly_interval.
