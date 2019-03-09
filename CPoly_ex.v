Require Import Psatz.
From mathcomp Require Import all_ssreflect.
Require Import CPoly_I.
From Bignums Require Import BigZ.
Import Rtrigo_def.
Import Rdefinitions.
Import Rpower.

Coercion fromZ := SFBI2.fromZ.
Coercion PfromZ (x : Z * Z) : SFBI2.type :=
           SFBI2.scale2 (SFBI2.fromZ x.1) (BigZ.of_Z x.2).

Module V := CPoly_interval SFBI2.

Export V.

Open Scope fexpr_scope.

Notation " x * 2^ y " := (Interval_specific_ops.Float x%bigZ y%bigZ) (at level 0) : sollya.
Notation " [ x ; y ] " :=  (Interval_interval_float.Ibnd x y) : sollya.
Notation "[| x1 , x2 , .. , xn |]" := (x1 :: x2 :: .. [:: xn] ..) : sollya.

Open Scope sollya.

Section Example1.

Let prec := 165%bigZ.

Definition ex1 := (sin(x))%fexpr.

Compute ex1.

(* TL = chebyshevform(sin(x), 10 , [3,4]);            *)
(* TL[2];                                             *)
(* TL[3];                                             *)
Time Definition ex1_cms := 
  Eval vm_compute in mk_cms prec 10 3%Z 4%Z (sin(x))%fexpr.

Lemma ex1_correct : cms_correct 10 3%Z 4%Z sin ex1_cms.
Proof.
rewrite (_ : ex1_cms = mk_cms 165%bigZ 10 3%Z 4%Z (sin(x))%fexpr); last first.
  by vm_cast_no_check (refl_equal ex1_cms).
have-> : sin = (fexpr_eval ex1).
  by apply: refl_equal.
by apply: mk_cms_correct.
Qed.

Compute P ex1_cms.
Compute Delta ex1_cms.
Compute Delta (norm_cms prec ex1_cms).
Compute P (norm_cms prec ex1_cms).
Compute eval_range_cms prec ex1_cms.

End Example1.

Section Example4.

(* The precision *)
Let prec := 165%bigZ.

Definition ex4 := (exp(/(cos(x))))%fexpr.

Print ex4.

(* TL = chebyshevform(exp(1/cos(x)), 14, [0, 1]);                 *)
(* TL[2];                                                         *)
(* TL[3];                                                         *)
Time Definition ex4_cms :=
  Eval vm_compute in mk_cms prec 14 0%Z 1%Z ex4.

Lemma ex4_correct :
       cms_correct 14 0%Z 1%Z (fun x => exp (/ (cos x)))%R ex4_cms.
Proof.
have-> : (fun x => exp (/ (cos x))) = fexpr_eval ex4.
  by apply: refl_equal.
have-> : ex4_cms = mk_cms prec 14 0%Z 1%Z ex4.
  by vm_cast_no_check (refl_equal ex4_cms).
by apply mk_cms_correct.
Qed.

Compute P ex4_cms.
Compute Delta ex4_cms.
Compute Delta (norm_cms prec ex4_cms).
Compute P (norm_cms prec ex4_cms).
Compute eval_range_cms prec ex4_cms.

End Example4.

Section Example5.

(* The precision *)
Let prec := 165%bigZ.

Definition ex5 := (exp(x) / (ln(2 + 'x) * cos(x)))%fexpr.

Print ex5.

(* TL = chebyshevform(exp(x) / (log(2 + x) * cos(x)), 15 , [0, 1]); *)
(* TL[2];                                                           *)
(* TL[3];                                                           *)
Time Definition ex5_cms :=
  Eval vm_compute in mk_cms prec 15 0%Z 1%Z ex5.

Lemma ex5_correct :
       cms_correct 15 0%Z 1%Z (fun x => exp x / (ln (2 + x) * cos x))%R ex5_cms.
Proof.
have-> : (fun x => (exp x / (ln (2 + x) * cos x)))%R = fexpr_eval ex5.
  by apply: refl_equal.
have-> : ex5_cms = mk_cms prec 15 0%Z 1%Z ex5.
  by vm_cast_no_check (refl_equal ex5_cms).
by apply mk_cms_correct.
Qed.

Compute P ex5_cms.
Compute Delta ex5_cms.
Compute Delta (norm_cms prec ex5_cms).
Compute P (norm_cms prec ex5_cms).
Compute eval_range_cms prec ex5_cms.

End Example5.

Section Example6.

(* The precision *)
Let prec := 165%bigZ.

Definition ex6 := (sin(exp(x)))%fexpr.

Print ex6.

(* TL = chebyshevform(sin(exp(x)), 10 , [-1, 1]); *)
(* TL[2];                                         *)
(* TL[3];                                         *)
Time Definition ex6_cms :=
  Eval vm_compute in mk_cms prec 10 (-1)%Z 1%Z ex6.

Lemma ex6_correct :
       cms_correct 10 (-1)%Z 1%Z (fun x => sin (exp x))%R ex6_cms.
Proof.
have-> : (fun x => sin (exp x)) = fexpr_eval ex6.
  by apply: refl_equal.
have-> : ex6_cms = mk_cms prec 10 (-1)%Z 1%Z ex6.
  by vm_cast_no_check (refl_equal ex6_cms).
by apply mk_cms_correct.
Qed.

Compute P ex6_cms.
Compute Delta ex6_cms.
Compute Delta (norm_cms prec ex6_cms).
Compute P (norm_cms prec ex6_cms).
Compute eval_range_cms prec ex6_cms.

End Example6.

Section Example10.


(* The precision *)
Let prec := 165%bigZ.

Definition ex10 := (/(1 + c(4%Z) * 'x * 'x))%fexpr.

Print ex10.

(* TL = chebyshevform(1/(1 + 4 * x ^2), 10 , [-1, 1]); *)
(* TL[2];                                             *)
(* TL[3];                                             *)

Time Definition ex10_cms :=
  Eval vm_compute in mk_cms prec 10 (-1)%Z 1%Z ex10.

Lemma ex10_correct :
       cms_correct 10 (-1)%Z 1%Z (fun x => / (1 + 4 * x * x))%R ex10_cms.
Proof.
have-> : (fun x => / (1 + 4 * x * x))%R = (fexpr_eval ex10).
  apply: refl_equal.
have-> : ex10_cms = mk_cms prec 10 (-1)%Z 1%Z ex10.
  by vm_cast_no_check (refl_equal ex10_cms).
by apply mk_cms_correct.
Qed.

Compute P ex10_cms.
Compute Delta ex10_cms.
Compute Delta (norm_cms prec ex10_cms).
Compute P (norm_cms prec ex10_cms).
Compute eval_range_cms prec ex10_cms.

End Example10.


Section Example11.

(* The precision *)
Let prec := 165%bigZ.

Definition ex11 := (sin(x) * sin(x) + cos(x) * cos(x))%fexpr.

Print ex11.

(* TL = chebyshevform(sin(x)^2 + cos(x)^2 , 10, [-1,1]); *)
(* TL[2];                                                *)
(* TL[3];                                                *)
Time Definition ex11_cms :=
  Eval vm_compute in mk_cms prec 10 (-1)%Z 1%Z ex11.

Lemma ex11_correct :
       cms_correct 10 (-1)%Z 1%Z (fun x => sin x * sin x + cos x * cos x)%R 
                  ex11_cms.
Proof.
have-> : (fun x => sin x * sin x + cos x * cos x)%R = (fexpr_eval ex11).
  by apply: refl_equal.
have-> : ex11_cms = mk_cms prec 10 (-1)%Z 1%Z ex11.
  by vm_cast_no_check (refl_equal ex11_cms).
by apply mk_cms_correct.
Qed.

Compute P ex11_cms.
Compute Delta ex11_cms.
Compute Delta (norm_cms prec ex11_cms).
Compute P (norm_cms prec ex11_cms).
Compute eval_range_cms prec ex11_cms.

End Example11.


Section Tang.

(* The precision *)
Let prec := 52%bigZ.

Let Iab := I.div prec (I.bnd (-10831)%Z (10831)%Z) (I.fromZ 1000000).

Let If :=
  let z := 
  I.div prec
   (I.bnd (23)%Z (23)%Z)
   (I.fromZ (27 * 2^33)) in I.bnd (SFBI2.neg (I.lower z)) (I.lower z).
Compute If.
 
Definition tang := exp('x) - 1 - ('x + c(8388676, 2^24) * 'x * 'x
                                 + c(11184876, 2^26) * 'x * 'x * 'x).

Compute solve prec 3 Iab tang If 8.

Lemma tang_correct x :
 ((-10831 / 1000000) <= x <= (10831 / 1000000) ->
  (-23 / (27 * Rpower 2 33%R)) <= (exp x - 1 - (x + 8388676/ Rpower 2 24 * x * x +
                                           11184876 / Rpower 2 26 * x * x * x))
                      <= (23 / (27 * Rpower 2 33)))%R.
Proof.
move=> H.
cheby_solve_tac prec 7 3 tang H. 
Qed.

End Tang.

Section CosSin.

(* The precision *)
Let prec := 165%bigZ.

Definition sin_cos := cos(x) * cos(x) + sin(x) * sin(x).

Let k := 100%Z.
Lemma sin_correct x :
 (3 / 1  <= x <= (4 / 1) ->
  (IZR (2^k -  1) / IZR (2 ^ k)) <= (cos x * cos x + sin x * sin x)
                      <= (IZR (2^k + 1) / IZR (2 ^ k)))%R.
Proof.
move=> H.
cheby_solve_tac prec 4%nat 15%nat sin_cos H.
Time Qed.

End CosSin.
