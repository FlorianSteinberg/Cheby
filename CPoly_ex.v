From mathcomp Require Import all_ssreflect.
Require Import CPoly_I.
From Bignums Require Import BigZ.

Module V := CPoly_interval SFBI2.

Export V.

Open Scope fexpr_scope.

Notation " x * 2^ y " := (Interval_specific_ops.Float x%bigZ y%bigZ) (at level 0) : sollya.
Notation " [ x ; y ] " :=  (Interval_interval_float.Ibnd x y) : sollya.
Notation "[| x1 , x2 , .. , xn |]" := (x1 :: x2 :: .. [:: xn] ..) : sollya.

Open Scope sollya.

Section Example1.

(* Where we evaluate *) 
Let Ia := I.fromZ (3).
Let Ib := I.fromZ (4).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 10%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex1 := (sin(x))%fexpr.

Print ex1.

Time Definition ex1_cms :=
  Eval vm_compute in
  fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex1.

Compute P ex1_cms.
Compute Delta ex1_cms.
Compute Delta (norm_cms prec ex1_cms).
Compute P (norm_cms prec ex1_cms).
Compute eval_range_cms prec ex1_cms.

End Example1.

Section Example4.

(* Where we evaluate *) 
Let Ia := I.fromZ (0).
Let Ib := I.fromZ (1).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 14%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex4 := (exp(/(cos(x))))%fexpr.

Print ex4.

Time Definition ex4_cms :=
  Eval vm_compute in
  fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex4.

Compute P ex4_cms.
Compute Delta ex4_cms.
Compute Delta (norm_cms prec ex4_cms).
Compute P (norm_cms prec ex4_cms).
Compute eval_range_cms prec ex4_cms.

End Example4.

Section Example5.

(* Where we evaluate *) 
Let Ia := I.fromZ (0).
Let Ib := I.fromZ (1).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 15%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex5 := (exp(x) / (ln(2 + 'x) * cos(x)))%fexpr.

Print ex5.

Time Definition ex5_cms :=
  Eval vm_compute in fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex5.

Compute P ex5_cms.
Compute Delta ex5_cms.
Compute Delta (norm_cms prec ex5_cms).
Compute P (norm_cms prec ex5_cms).
Compute eval_range_cms prec ex5_cms.

End Example5.

Section Example6.

(* Where we evaluate *) 
Let Ia := I.fromZ (-1).
Let Ib := I.fromZ (1).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 10%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex6 := (sin(exp(x)))%fexpr.

Print ex6.

Time Definition ex6_cms :=
  Eval vm_compute in fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex6.

Compute P ex6_cms.
Compute Delta ex6_cms.
Compute Delta (norm_cms prec ex6_cms).
Compute P (norm_cms prec ex6_cms).
Compute eval_range_cms prec ex6_cms.

End Example6.

Section Example10.

(* Where we evaluate *) 
Let Ia := I.fromZ (-1).
Let Ib := I.fromZ (1).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 10%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex10 := (/(1 + c(4) * 'x * 'x))%fexpr.

Print ex10.

Time Definition ex10_cms :=
  Eval vm_compute in fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex10.

Compute P ex10_cms.
Compute Delta ex10_cms.
Compute Delta (norm_cms prec ex10_cms).
Compute P (norm_cms prec ex10_cms).
Compute eval_range_cms prec ex10_cms.

End Example10.


Section Example11.

(* Where we evaluate *) 
Let Ia := I.fromZ (-1).
Let Ib := I.fromZ (1).
Let a := I.lower Ia.
Let b := I.upper Ib.
Let Iab := I.join Ia Ib.

(* The precision *)
Let prec := 165%bigZ.

(* The real degree of the polynomial *)
Let n := 10%nat.
Let ob :=   Eval vm_compute in odd n.
Let zn :=  Eval vm_compute in Pos.of_nat n.+1.
Let z2n := Eval vm_compute in (2 * zn)%positive.
Let vn := Eval vm_compute in I.fromZ (Zpos zn).
Let v2n := Eval vm_compute in I.fromZ (Zpos z2n).

(* List of n+1 1 *)
Let l1 := Eval vm_compute in nseq n.+1 I1.

(* Chebyshev nodes in [-1, 1] *)
Let vl1 := Eval vm_compute in Icheby_nodes prec n.+1 v2n.

(* Values of the Chebyshev polynomials at th Chebyshev nodes *)
Let vl2 := Eval vm_compute in ITvalues prec n.+1 l1 vl1.

(* Chebyshev nodes in [a, b] *)
Let vl3 := Eval vm_compute in Ischeby_nodes prec a b n.+1 v2n.

Definition ex11 := (sin(x) * sin(x) + cos(x) * cos(x))%fexpr.

Print ex11.

Time Definition ex11_cms :=
  Eval vm_compute in fexpr_cms prec n ob vn zn z2n a b vl1 vl2 vl3 ex11.

Compute P ex11_cms.
Compute Delta ex11_cms.
Compute Delta (norm_cms prec ex11_cms).
Compute P (norm_cms prec ex11_cms).
Compute eval_range_cms prec ex11_cms.

End Example11.
