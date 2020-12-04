From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz Poly_complements seq_base.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Tcheby.
Variable R : ringType.
Implicit Types (l : seq R) (p: {poly R}) .

(* Chebyshev polynomials introduced via their recursion scheme *)

Fixpoint pT_expanded_def (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+2 * pT_expanded_def n1 - pT_expanded_def n2
    else 'X
  else 1.

Fact pT_key : unit. Proof. by []. Qed.
Definition pT := locked_with pT_key pT_expanded_def.
Canonical pT_unlockable := [unlockable fun pT].

Notation "'T_ n" := (pT n)
  (at level 3, n at level 2, format "''T_' n ").

Lemma pT0 : 'T_0 = 1 :> {poly R}.
Proof. by rewrite unlock /pT_expanded_def. Qed.

Lemma pT1 : 'T_1 = 'X :> {poly R}.
Proof.
by rewrite unlock /pT_expanded_def.
Qed.

Lemma pTSS : forall n, 'T_n.+2 = 'X *+2 * 'T_n.+1 - 'T_n :> {poly R}.
Proof. by move => n; rewrite unlock. Qed.

Notation "'T_ n" := (pT n)
  (at level 3, n at level 2, format "''T_' n ").

Lemma horner1_pT n : ('T_n).[1: R] = 1.
Proof.
elim/ltn_ind: n => [] [|[|n]] IH; first by rewrite pT0 hornerC.
  by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
by rewrite -commr_polyX hornerMX !IH // !mulr1 mulrS [1+ _]addrC addrK.
Qed.

Lemma hornerN1_pT n : ('T_n).[-1: R] = (-1) ^+ n.
Proof.
elim/ltn_ind : n => [] [|[|n]] IH; first by rewrite pT0 hornerC.
  by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
rewrite -commr_polyX hornerMX !IH //.
by rewrite !exprS !(mulN1r, mulrN1, opprK) mulr2n addrK.
Qed.

Lemma commr_pT p n : GRing.comm p ('T_n).
Proof.
elim/ltn_ind : n => [] [|[|n]] IH; first by rewrite pT0; apply: commr1.
  by rewrite pT1; apply: commr_polyX.
rewrite pTSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
 [exact: commr_polyX | apply: IH].
Qed.

Definition pU := fix pU_rec (n : nat) {struct n} : {poly R} :=
  if n is n1.+1 then
    if n1 is n2.+1 then 'X *+ 2 * pU_rec n1 - pU_rec n2
    else 'X *+ 2
  else 1.

Notation "'U_ n" := (pU n)
  (at level 3, n at level 2, format "''U_' n ").

Lemma pU0 : 'U_0 = 1.
Proof. by []. Qed.

Lemma pU1 : 'U_1 = 'X *+ 2.
Proof. by []. Qed.

Lemma pUSS n : 'U_n.+2 = 'X *+ 2 * 'U_n.+1 - 'U_n.
Proof. by []. Qed.

Lemma horner1_pU n : ('U_n).[1] = n.+1%:R.
Proof.
elim/ltn_ind : n => [] [|[|n]] IH; first by rewrite hornerC.
  by rewrite pU1 hornerMn hornerX.
rewrite pUSS hornerD hornerN mulrnAl hornerMn.
rewrite -commr_polyX hornerMX mulr1 !IH //.
rewrite -mulr_natl -natrM -natrB; last first.
  by rewrite mulSn !addSnnS addnS ltnS leq_addr.
by rewrite mul2n -addnn -addSnnS addnK.
Qed.

Lemma commr_pU p n : GRing.comm p ('U_n).
Proof.
elim/ltn_ind : n => [] [|[|n]] IH; first  by exact: commr1.
  by rewrite pU1; apply: commrMn; exact: commr_polyX.
rewrite pUSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
   [exact: commr_polyX | apply: IH].
Qed.

Lemma pT_pU n : 'T_n.+1 = 'U_n.+1 - 'X * 'U_n.
Proof.
have F: pU 1 - 'X * pU 0 = 'X by rewrite pU1 pU0 mulr1 addrK.
elim/ltn_ind : n  => [] [|n] IH; first by rewrite pT1 F.
rewrite pTSS pUSS IH // mulrDr -!addrA; congr (_ + _). 
case: n IH => [_|m IH].
  rewrite pT0 pU0 pU1 addrC mulrN; congr (_ - _).
  by rewrite mulr1 mulrnAl mulrnAr.
rewrite IH // pUSS addrC opprD -!addrA; congr (_ + _).
rewrite mulrDr !mulrN opprB opprK; congr (_ - _).
by rewrite !mulrA commr_polyX.
Qed.

Lemma deriv_pT n: ('T_n.+1)^`() = 'U_n *+ n.+1.
Proof.
elim/ltn_ind : n => [] [|n] IH; first by rewrite pT1 derivX.
rewrite pTSS derivD derivM derivMn derivX !IH // pT_pU.
case: n IH => [_|n IH].
  by rewrite pU0 pU1 pT0 derivN derivC subr0 mulr_natl mulrnBl !mulr1 addrK.
rewrite derivN IH // pUSS mulr_natl !(mulrnDl, mulrnBl).
rewrite !(mulrnAl, mulrnAr) -!mulrnA.
set x := 'X * _; set y := pU n.
rewrite -[x *+ _ + _ *+ _]addrC -3!addrA addrC.
rewrite addrA -[(2 * 2)%N]/(2 + 2)%N mulrnDr.
rewrite mulNrn addrK.
rewrite -mulrnDr mulnC; rewrite -addrA; congr (_ + _)=> //.
  congr (_ *+ _); rewrite !mul2n //.
by rewrite -mulNrn -mulrnDr addnC.
Qed.

Lemma coef_pU : forall n i,
  ('U_n)`_i =
    if (n < i)%N || odd (n + i) then 0 else
    let k := (n - i)./2 in ((-1)^+k * (2^i * 'C(n-k,k))%:R).
Proof.
elim/ltn_ind => [] [|[|n]] IH i.
- by case: i => [|i]; rewrite pU0 ?coefC //= mul1r.
  by rewrite coefMn coefX; case: i=> [|[|i]] //=;
     rewrite ?mul0rn //= -mulr_natl mulr1 mul1r.
rewrite pUSS coefB mulrnAl coefMn coefXM !IH //.
case: i=> [|i].
  rewrite !addn0 mul0rn sub0r subn0 /=; case O1: (odd _).
    by rewrite oppr0.
  rewrite !mul1n /= exprS !mulNr subSS mul1r.
  rewrite -{2 6}[n]odd_double_half O1 add0n subSn -addnn ?leq_addr //.
  by rewrite  addnK !binn.
rewrite !addSn !addnS /=; case O1: (odd _); last first.
   by rewrite !orbT mul0rn  subrr.
rewrite !orbF !subSS; case: leqP=> Hm; last first.
  rewrite ltnS (leq_trans _ Hm); last by  exact: (leq_addl 2 n).
  by rewrite mul0rn  sub0r oppr0.
rewrite ltnS.
move: Hm; rewrite leq_eqVlt; case/orP=> [/eqP->|].
  by rewrite subnn leqnSn !mul1r !bin0 !muln1 subr0 -mulr_natl -natrM.
rewrite ltnS leq_eqVlt; case/orP; [move/eqP->|move=>Him].
  by rewrite leqnn subSnn !subn0 expr0 !bin0
             subr0 !mul1r !muln1 -mulr_natl -natrM expnS.
rewrite leqNgt Him /= subSn; last by exact: ltnW.
have->: ((n - i).+1./2 = (n - i)./2.+1).
 rewrite -{1}[(n - i)%N]odd_double_half.
 rewrite (oddB (ltnW _)) // -oddD O1.
 by rewrite /= (half_bit_double _ false).
have->: ((n - i.+1)./2 = (n - i)./2).
 rewrite subnS -{1}[(n - i)%N]odd_double_half.
 rewrite (oddB (ltnW _)) // -oddD O1.
 by rewrite /= (half_bit_double _ false).
set u := (n - i)./2.
rewrite !subSS subSn.
  rewrite binS mulnDr mulrnDr mulrDr; congr (_ + _).
    by rewrite -mulrnAr -mulr_natl -natrM mulnA expnS.
  by rewrite -mulN1r mulrA exprS.
apply: (leq_trans (half_leq (leq_subr i n))).
by rewrite -{2}[n]odd_double_half -addnn addnA leq_addl.
Qed.

Lemma coef_pUn n : ('U_n)`_n = (2^n)%:R.
Proof.
by rewrite coef_pU ltnn addnn odd_double subnn /= bin0 mul1r muln1.
Qed.

Lemma size_pU_leq n : (size ('U_n) <= n.+1)%N.
Proof. by apply/leq_sizeP=> j Hj; rewrite coef_pU Hj. Qed.

Lemma coef_pT n i :
  ('T_n)`_i =
    if (n < i)%N || odd (n + i) then 0 : R else
    if n is 0 then 1 else
    let k := (n - i)./2 in
    (-1) ^+ k * ((2^i * n * 'C(n-k,k)) %/ (n-k).*2)%:R.
Proof.
case: n => [|n]; first by rewrite pT0 coefC; case: i.
rewrite pT_pU coefB coefXM !coef_pU.
case: leqP; last first.
  by case: i=> [|i] //; rewrite ltnS=> ->; exact: subrr.
case: i => [_|i Hi].
  rewrite addn0; case O1: (odd _); first by exact: subr0.
  rewrite !subr0 !subn0 !mul1n; congr (_ * _); congr (_%:R).
  have F: n.+1 = (n.+1)./2.*2 by rewrite-{1}[(n.+1)%N]odd_double_half O1.
  by rewrite {8}F -[_./2.*2]addnn addnK -F mulKn // mul1n.
rewrite subSS addnS /=; case O1: (odd _); first by rewrite orbT subr0.
rewrite orbF; move: (Hi); rewrite ltnS leqNgt; move/negPf->.
rewrite -mulrBr; congr (_ * _).
rewrite -natrB; last first.
  apply: leq_mul; first rewrite leq_exp2l //.
  by apply: leq_bin2l; apply: leq_sub2r.
congr (_%:R).
have F: (n-i = (n-i)./2.*2)%N
   by rewrite-{1}[(n-i)%N]odd_double_half oddB // -oddD O1.
set u := (n - i)./2.
have F1: (u <= n)%N.
  by apply: leq_trans (leq_subr i _); rewrite F -addnn leq_addl.
rewrite subSn //.
have->: (n - u = i + u)%N.
  rewrite ltnS in Hi; rewrite -{1}(subnK Hi) [(_ + i)%N]addnC.
  by rewrite -addnBA;
     [rewrite {1}F -addnn addnK | rewrite F -addnn leq_addr].
set v := (i + u)%N.
rewrite {2}expnS -!mulnA -mul2n divnMl //.
pose k := (u`! * (v.+1 - u)`!)%N.
have Fk: k != 0%N.
  apply/eqP=> Hk; move: (leqnn k); rewrite {2}Hk leqNgt.
  by rewrite /k !(muln_gt0,fact_gt0).
apply/eqP; rewrite -[_ == _]orFb -(negPf Fk).
have F2: (u <= v)%N by apply: leq_addl.
have F3 : (u <= v.+1)%N   by apply: (leq_trans F2).
have F4: (u + v = n)%N by rewrite addnC -addnA addnn -F addnC subnK.
rewrite -eqn_mul2r mulnBl -!mulnA bin_fact //.
rewrite expnSr -mulnA -mulnBr {1}/k subSn // [(_ - _).+1`!]factS.
rewrite [((_ - _).+1 * _)%N]mulnC 2!mulnA -[('C(_,_) * _ * _)%N]mulnA.
rewrite bin_fact ?leqDl // [(2 * _)%N]mulnC.
rewrite factS [(v.+1 * _)%N]mulnC -!mulnA -mulnBr.
rewrite -subSn // subnBA //.
rewrite [(_ + u)%N]addnC muln2 -addnn !addnA addnK.
rewrite divn_mulAC.
  rewrite -!mulnA bin_fact //.
  rewrite factS [(v.+1 * _)%N]mulnC !mulnA mulnK //.
  by apply/eqP; rewrite -!mulnA addnS F4 [(v`! * _)%N]mulnC.
rewrite dvdn_mull // -F4 -addnS mulnDl dvdn_add //; last first.
  by rewrite /dvdn; apply/eqP; exact: modnMr.
case: {1 2}u=> [|u1]; first by exact: dvdn0.
rewrite -mul_bin_diag.
by rewrite /dvdn; apply/eqP; exact: modnMr.
Qed.

Lemma coef_pTK  n i :
   ~~ odd (n + i) -> (i <= n)%N ->
  let k := (n - i)./2 in
  ('T_n)`_i *+ (n-k).*2 = (-1)^+k * (2^i * n * 'C(n-k,k))%:R :> R.
Proof.
move=> O1 L1; rewrite coef_pT; move/negPf: (O1)->.
move: (L1); rewrite leqNgt; move/negPf->.
case: n L1 O1 => [|n] L1  O1 /=; first by rewrite !muln0 mulr0.
rewrite -mulrnAr; congr (_ * _); rewrite -mulr_natl -natrM; congr (_%:R).
case: i L1 O1 => [|i L1 O1].
  rewrite addn0 subn0=> _ O1.
  have F: n.+1 = (n.+1)./2.*2
    by rewrite-{1}[n.+1]odd_double_half // (negPf O1).
  have ->: (n.+1 - (n.+1)./2 = (n.+1)./2)%N by rewrite {1}F -addnn addnK.
  by rewrite -F mul1n mulKn //.
set u := (n.+1 -i.+1)./2.
have F: (n.+1 - i.+1 = u.*2)%N.
  by rewrite-{1}[(n.+1 - i.+1)%N]odd_double_half
             /u oddB // -oddD (negPf O1).
have->: (n.+1 - u = i.+1 + u)%N.
  rewrite -{1}(subnK L1) [(_ + i.+1)%N]addnC.
  by rewrite -addnBA;
     [rewrite {1}F -addnn addnK | rewrite F -addnn leq_addr].
rewrite expnS -!mul2n -!mulnA divnMl //;  congr (_ * _)%N.
apply/eqP; rewrite mulnC -dvdn_eq.
have->: (n.+1 = u + (i.+1 + u))%N by rewrite addnC -addnA addnn -F addnC subnK.
apply: dvdn_mull.
case: {F}u=> [|u]; first by rewrite !muln1 !addn0 dvdnn.
by rewrite mulnDl dvdn_add //; first rewrite addnS -mul_bin_diag;
   apply: dvdn_mulr; exact: dvdnn.
Qed.

Lemma coef_pTn n : ('T_n)`_n = (2 ^ n.-1)%:R :> R.
Proof.
case: n => [|n]; rewrite coef_pT ltnn addnn odd_double //= subnn subn0.
rewrite mul1r expnS [(2 * _)%N]mulnC -!mulnA [(2 * _)%N]mulnA mul2n.
by rewrite mulnC -!mulnA mulKn // bin0 mul1n.
Qed.

Lemma size_pT_leq n : (size ('T_n) <= n.+1)%N.
Proof.
by apply/leq_sizeP => j Hj; rewrite coef_pT Hj.
Qed.

(* Pell equation *)

Lemma pell n : ('T_n.+1)^+2 - ('X^2 - 1) * ('U_n) ^+ 2 = 1.
Proof.
suff F: (pU n.+1)^+ 2 + (pU n)^+2 = 'X *+ 2 * pU n.+1 * pU n + 1.
  rewrite pT_pU exprS expr1 !mulrDl !mulrDr opprD !mulNr.
  rewrite !addrA addrC opprK mul1r !addrA [_^+2 + _]addrC F.
  apply: trans_equal (addr0 _); rewrite [_+1]addrC -!addrA; congr (_ + _).
  rewrite mulrN mulrA commr_polyX !addrA !mulrDl addrK.
  rewrite -mulrA -commr_pU mulrA addrN sub0r.
  by rewrite mulrN opprK -mulrA -commr_pU exprS expr1 exprS expr1 !mulrA addrN.
elim: n => [| n IH].
  by rewrite pU1 pU0 mulr1 expr1n exprS expr1.
rewrite pUSS exprS !mulrBr !mulrBl -!addrA; congr (_ + _).
  rewrite !(mulrnAl,mulrnAr); do 2 congr (_ *+ _).
  by rewrite -!mulrA; congr (_ * _); rewrite -commr_pU mulrA.
congr (_ + _); first by rewrite -commr_pU -!mulrA commr_pU.
by rewrite opprB addrC addrA IH [_+1]addrC addrK.
Qed.
End Tcheby.

Notation "'T_ n " := (pT _ n)
  (at level 3, n at level 2, format "''T_' n").

Lemma induc2 (P: nat -> Prop):
	P 0%nat -> P 1%nat -> 
  (forall n, P n -> P (n.+1) -> P (n.+2)) -> forall n, P n.
Proof.
move=> HP0 HP1 HPn n.
elim/ltn_ind : n => [] [|[|n]] IH //.
by apply: HPn; apply: IH.
Qed.

Section LINEAR_INDEPENDENCE.
Variable R: unitRingType.

Lemma lreg_neq0 (l x: R): GRing.lreg l -> x != 0 -> l * x != 0.
Proof.
move => Hl;  apply: contra => /eqP H; apply/eqP.
by apply: Hl; rewrite H rm0.
Qed.

Hypothesis lr2 : GRing.lreg (2%:R : R).

Lemma rr2: GRing.rreg (2%:R :R).
Proof.
move => x y; rewrite mulr_natr [y*_]mulr_natr -mulr_natl -[y *+ _]mulr_natl => eq.
by apply lr2.
Qed.

Lemma size_pT n : size ('T_ n : {poly R}) = n.+1.
Proof.
elim/induc2: n => [ | | n ih1 ih2]; first by rewrite pT0 size_poly1.
	by rewrite pT1 size_polyX.
suff/leP leq: (n.+3 <= size ('T_n.+2: {poly R}))%nat by have/leP leq':= size_pT_leq R (n.+2); lia.
apply: gtn_size.
rewrite pTSS coefD coef_opp_poly -scaler_nat -scalerAl coefZ coef_mul_poly.
under eq_bigr do rewrite coefX.
rewrite big_ord_recl big_ord_recl big1; last by move => i _ /=; rewrite !rm0.
rewrite !lift0 -{2 }[ord0.+1]add1n !rm0 !rm1 coef_pTn (coef_pT R n) /=.
have ->: (n < n.+2)%N || odd (n + n.+2) by apply /orP; left.
rewrite rm0 natrX -exprS -[_ ^+ _]mulr1; apply: lreg_neq0; last by rewrite oner_eq0.
by apply GRing.lregX.
Qed.

Lemma pT_neq0 n: 'T_n != 0 :> {poly R}.
Proof. by rewrite -size_poly_eq0 size_pT. Qed.

Lemma coef_pTn_reg n: GRing.rreg ('T_n: {poly R})`_n.
Proof. by rewrite coef_pTn natrX; apply /GRing.rregX /rr2. Qed.

Lemma size_sum_pT (p: {poly R}):
	size (\sum_(i < size p) p`_i *: 'T_i) = size p.
Proof.
rewrite (@size_polybase _ (fun i => 'T_i)) => // [| n ]; first by apply size_pT.
by rewrite lead_coefE size_pT; apply: coef_pTn_reg.
Qed.

Lemma pT_eq (p q : {poly R}):
	p = q <->
	\sum_(i < size p) p`_i *: 'T_ i = \sum_(i < size q) q`_i *: 'T_ i.
Proof.
split=> [->//|/eqP].
rewrite -(@polybase_widen _ (fun i => 'T_i) _ _ (leq_maxl (size p) (size q))).
rewrite -(@polybase_widen _ (fun i => 'T_i) _ _ (leq_maxr (size p) (size q))).
rewrite -subr_eq0 -sumrB.
under eq_bigr do rewrite -scalerBl -coefB; move => /eqP eq.
apply: subr0_eq; rewrite -polyP => i; rewrite coef0.
have [ineq|ineq]:= (ltnP i (maxn (size p) (size q))).
	apply: seqbase_coef_eq0; [exact: size_pT | | exact: eq | exact ineq].
	move => n; rewrite lead_coefE size_pT.
	exact: coef_pTn_reg.
apply/ leq_sizeP; last apply ineq.
by rewrite -[size q]size_opp size_add.
Qed.

Lemma pT_eq0 (p: {poly R}):
	p = 0 <-> \sum_(i < size p) p`_i *: 'T_i = 0.
Proof. by rewrite pT_eq size_poly0 big_ord0. Qed.
End LINEAR_INDEPENDENCE.

Section Multiplication.

Variable (R: unitRingType).

Definition absn m n := (m - n + (n - m))%nat.

Lemma subn_leq m n : (n <= m -> n - m = 0)%nat.
Proof. by move => ineq; apply /eqP; rewrite subn_eq0. Qed.

Lemma absnE m n : absn m n = (if m <= n then n - m else m - n)%nat.
Proof.
rewrite /absn; case: leqP => H; first by rewrite subn_leq.
by rewrite [(n - m)%nat]subn_leq ?addn0 // ltnW.
Qed.

Lemma absnC : commutative absn.
Proof. by move => m n; rewrite /absn addnC. Qed.

Lemma absnn n : absn n n = 0%nat.
Proof. by rewrite /absn !subnn addn0. Qed.

Lemma absn_eq0 m n : (absn m n = 0 -> m = n)%nat.
Proof.
move=>/eqP; rewrite addn_eq0 => H; apply/eqP.
by rewrite eqn_leq.
Qed.

Lemma absnSS n m : absn m.+1 n.+1 = absn m n.
Proof. by rewrite /absn !subSS. Qed.

Lemma abs0n n :	absn 0 n = n.
Proof. by rewrite /absn sub0n subn0 add0n. Qed.

Lemma absn0 n : absn n 0 = n.
Proof. by rewrite absnC abs0n. Qed.

Lemma absn1S n : absn 1 n.+1 = n%nat.
Proof. by rewrite absnSS abs0n. Qed.

Lemma absnS1 n : absn n.+1 1 = n%nat.
Proof. by rewrite absnC absn1S. Qed.

Lemma absn_max_min m n : (absn m n = maxn m n - minn m n)%nat.
Proof.
rewrite /absn maxnE minnE.
case: (leqP n m) => H.
  by rewrite subKn // (subn_leq H) !addn0.
by rewrite (subn_leq) 1?ltnW // subn0 addKn.
Qed.

Lemma subn_eq m n p: (p > 0 -> m - n = p -> m = p + n)%nat.
Proof.
move => pgt E; rewrite -E subnK //.
by apply: ltnW; rewrite -subn_gt0 E.
Qed.

Lemma absnnD n m : absn n (n + m) = m.
Proof.
rewrite /absn (subn_leq); last by rewrite leq_addr.
by rewrite add0n addnC -addnBA// subnn addn0.
Qed.

Lemma subnSn n : (n - n.+1 = 0)%nat.
Proof. by elim: n. Qed.

Lemma absnif n m:
	(absn m n.+1 = if m <= n then (absn m n).+1 else (absn m n).-1)%nat.
Proof.
rewrite absnC !absnE leqNgt ltnS.
case: leqP => //=; first exact: subSn.
by rewrite subnS.
Qed.

Lemma absn_pT n m:
	'X *+2 * 'T_(absn m n.+1) - 'T_(absn m n) = 'T_(absn m n.+2) :> {poly R}.
Proof.
rewrite !absnif; case: leqP => [H|]; first by rewrite ltnW // -pTSS.
rewrite leq_eqVlt => /orP[/eqP<-|ineq].
  rewrite leqnn absnC -[n.+1]addn1 absnnD.
	by rewrite pT0 pT1 mulr1 -addrA subrr addr0.
rewrite leqNgt ineq /= -(subnK ineq) -!addSnnS addnC absnC absnnD /=.
by rewrite pTSS subKr.
Qed.

Lemma mul_pT n m :
	2%:R *: 'T_n * 'T_m = 'T_(n + m) + 'T_(absn m n) :> {poly R}.
Proof.
elim/ltn_ind : n m => // [] [|[|n]] IH m.
- by rewrite pT0 absn0 mulr2n scalerDl scale1r mulrDl mul1r.
- rewrite pT1 scaler_nat add1n.
	case: m => [|m]; first by rewrite pT0 pT1 /absn rm1 mulr2n.
	by rewrite absnS1 pTSS -addrA [-'T_m + 'T_m]addrC subrr rm0.
rewrite pTSS scalerDr mulrDl -!scalerAl mulNr.
rewrite scalerN !scalerAl IH; last by rewrite -ltnS ltnW.
rewrite -scaler_nat -!scalerAl -mulrA -commr_polyX.
rewrite  scalerAl scalerAl scalerAl IH //.
rewrite !addSn pTSS scalerDr mulrDl -scalerAl commr_polyX.
rewrite scalerAl scaler_nat -!addrA.
congr (_ + _).
rewrite opprD addrA [_ - 'T_(n+m)]addrC -addrA.
congr (_ + _).
rewrite -scalerAl commr_polyX scalerAl scaler_nat.
exact: absn_pT.
Qed.

Lemma pT_mulX_weak n :  'X *+ 2 * 'T_n.+1 = 'T_n + 'T_n.+2 :> {poly R}.
Proof. by rewrite pTSS addrCA subrr rm0. Qed.

Lemma pT_mulX n :
  (2%:R : R) \is a GRing.unit -> 'X * 'T_n.+1 = 2%:R ^-1 *: 'T_n + 2%:R ^-1 *: 'T_n.+2 :> {poly R}.
Proof.
move => I2; rewrite pTSS scalerDr addrCA scalerN subrr addr0.
by rewrite -scaler_nat -scalerAl scalerA mulVr // scale1r.
Qed.
End Multiplication.

Section pTab.

Variable R: fieldType.

Definition Tab (a b: R) := 	(1 + 1)/(b - a) *: 'X + (- (a + b) / (b - a))%:P.

Lemma Taba a b: b != a -> (Tab a b).[a] = -1.
Proof.
move =>neq; rewrite /Tab !hornerE.
rewrite opprD !mulrDl mul1r mulrC addrA -[a / (b - a) + _ + _]addrA.
rewrite mulNr subrr rm0 -mulrDl -[a-b]opprB mulNr divrr //.
by rewrite unitfE; apply: contra neq => eq; rewrite -subr_eq0.
Qed.

Lemma Tabb a b: b != a -> (Tab a b).[b] = 1.
Proof.
move => neq; rewrite /Tab !hornerE.
rewrite opprD !mulrDl mul1r mulrC addrC addrA -[- a / (b - a) + _ + _]addrA.
rewrite [- b / (b- a) + _]addrC [- b / _]mulNr subrr rm0 addrC -mulrDl divrr //.
by rewrite unitfE; apply: contra neq => eq; rewrite -subr_eq0.
Qed.

Definition pTab a b n := 'T_n \Po (Tab a b).

Notation "''T^(' a ',' b ')_' n" := (pTab a b n)
  (at level 3, n at level 2, format "''T^(' a ',' b ')_' n").

Lemma size_pTab n a b :
   2%:R != 0 :> R -> a != b -> size ('T^(a,b)_n) = n.+1.
Proof.
move=> H aDb.
have D :  b + - a != 0 by rewrite subr_eq0 eq_sym.
have E : GRing.lreg ((1 + 1) / (b - a)).
  by apply/GRing.lregM; apply/lregP => //; apply: invr_neq0.
rewrite size_comp_poly2 ?size_pT //; first by apply/lregP.
rewrite /Tab size_addl lreg_size ?size_polyX //.
by rewrite size_polyC; case: (_ == _).
Qed.

(* The condition GRing.lreg (2%:R : R) is unnecessary but makes live easier *)
Lemma coef_pTab n a b :
  2%:R != 0 :> R -> 'T^(a, b)_n`_n = (2^n.*2.-1)%:R /(b - a)^+n.
Proof.
move=> H.
rewrite ['T^(a, b)_n]comp_polyE coef_sum.
have rTA k : k%:R = (k%:R)%:A :> {poly R}.
    elim: k => /= [|k IH]; first by rewrite !rm0.
    by rewrite -addn1 !natrD IH scalerDl !rm1 /= scale1r.
have F : (n < size ('T_n : {poly R}))%nat by rewrite size_pT //; apply/lregP.
rewrite (bigD1 (Ordinal F)) //= big1 => [|i /eqP/val_eqP /= H1]; last first.
  rewrite coefZ exprDn coef_sum big1 => [|j _]; first by rewrite rm0.
  rewrite -mulr_natl -polyC_exp mulrCA mulrC.
  rewrite rTA alg_polyC -polyCM coefCM exprZn coefZ.
  rewrite coefXn.
  have : (i < n.+1)%nat.
    by rewrite -[n.+1](@size_pT R) //; apply/lregP.
  rewrite ltnS leq_eqVlt (negPf H1) /= => HH.
  have : (i - j < n)%nat.
    by apply: leq_ltn_trans (leq_subr _ _) HH.
  rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
  by rewrite !rm0.
rewrite coefZ addr0 exprDn coef_sum.
rewrite big_ord_recl /= big1 => [|i _].
  rewrite !rm0 expr0 bin0 !rm1 subn0 exprZn coef_pTn.
  rewrite coefZ coefXn eqxx rm1 -[1 + 1]/(2%:R).
  rewrite expr_div_n mulrA -natrX -natrM -expnD.
  by congr ((_ ^ _)%:R / _); rewrite -addnn; case: (n).
rewrite [bump _ _]add1n.
rewrite -mulr_natl -polyC_exp mulrCA mulrC.
rewrite rTA alg_polyC -polyCM coefCM exprZn coefZ coefXn.
case: i => ii /= _; case: (n) => [|nn].
  by rewrite bin0n !rm0.
have : (nn.+1 - ii.+1 < nn.+1)%nat.
  by apply: leq_ltn_trans (leq_subr _ _) (ltnSn _).
rewrite ltn_neqAle eq_sym => /andP[/negPf-> _].
by rewrite !rm0.
Qed.

Lemma horner_pTab a b n (x: R) :
  ('T^(a,b)_n).[x] = ('T_n).[(x*+2 - a - b) / (b - a)].
Proof.
rewrite /pTab horner_comp /Tab.
rewrite hornerD hornerZ hornerX hornerC.
congr (_.[_]).
rewrite mulr2n -{2 3}[x]mul1r -[1 * x + 1 * x]mulrDl -addrA [RHS]mulrDl.
by rewrite -[-a-b]opprD -{3}[b-a]mulr1 -mulf_div divr1.
Qed.

Lemma horner_pTab_a a b n :
	b != a -> 	('T^(a,b)_n).[a] = ('T_n).[-1].
Proof. by move => ineq; rewrite /pTab horner_comp Taba. Qed.

Lemma horner_pTab_b a b n :
	b != a -> ('T^(a,b)_n).[b] = ('T_n).[1].
Proof. by move => ineq; rewrite /pTab horner_comp Tabb. Qed.

Definition CPolyab a b l : {poly R} := \sum_(i < (size l)) l`_i *: 'T^(a,b)_i.

Lemma CPolyabN a b p :
  (CPolyab a b [seq - i | i <- p] = - (CPolyab a b p)).
Proof.
rewrite /CPolyab size_map -sumrN.
apply: eq_bigr => i _.
by rewrite (nth_map 0) // scaleNr.
Qed.

Lemma CPolyabD a b p q :
  size p = size q ->
  (CPolyab a b [seq i.1 + i.2 | i <- (zip p q)] =
     CPolyab a b p + CPolyab a b q).
Proof.
move=> Hs.
rewrite /CPolyab size_map size1_zip // Hs ?leqnn // -big_split.
apply: eq_bigr => i _.
by rewrite (nth_map 0) ?size2_zip ?Hs // scalerDl nth_zip.
Qed.

Lemma CPolyabB a b p q :
  size p = size q ->
  (CPolyab a b [seq i.1 - i.2 | i <- (zip p q)] =
     CPolyab a b p - CPolyab a b q).
Proof.
move=> Hs.
rewrite /CPolyab size_map size1_zip // Hs ?leqnn // -sumrB.
apply: eq_bigr => i _.
by rewrite (nth_map 0) ?size2_zip ?Hs // scalerBl nth_zip.
Qed.

End pTab.

Notation "''T^(' a ',' b ')_' n" := (pTab a b n)
  (at level 3, n at level 2, format "''T^(' a ',' b ')_' n").

Require Import Rstruct.

Section Int.

Variable R: fieldType.

Lemma deriv_pT0 : ('T_1)^`() = 'T_0 :> {poly R}.
Proof. by rewrite pT1 pT0 derivX. Qed.

Lemma deriv_pT1 : [char R]%RR =i pred0 -> 
  (4%:R^-1 *: 'T_2)^`() = 'T_1 :> {poly R}.
Proof.
move=> /GRing.charf0P Hf.
rewrite derivZ pTSS pT1 pT0 mulrnAl derivB derivMn -expr2 derivXn derivC.
by rewrite subr0 -mulrnA -scaler_nat scalerA mulVf ?Hf ?scale1r.
Qed.

Lemma deriv_pTSS n: (1 < n)%nat -> [char R]%RR =i pred0 -> 
  (n.+1.*2%:R^-1 *: 'T_n.+1 - n.-1.*2%:R^-1 *: 'T_n.-1)^`() = 
    'T_n :> {poly R}.
Proof.
case: n => [] // [] // n _ /GRing.charf0P Hf.
rewrite !(derivB, derivZ, deriv_pT) -!scaler_nat !scalerA.
do 2 rewrite -muln2 natrM invfM mulrC mulrA mulfV ?Hf // mul1r.
rewrite -scalerBr pT_pU pUSS -addrA -opprD -mulr2n mulrnAl -mulrnBl.
rewrite -[(_ + _) *+ _]scaler_nat scalerA mulVf ?Hf // scale1r.
by rewrite addrAC mulr2n addrK.
Qed.

Variables a b : R.

Lemma deriv_Tab : (Tab  a b )^`() = ((1 + 1) / (b - a))%:P.
Proof. by rewrite !derivE addr0 alg_polyC. Qed.

Lemma deriv_pTabn n : 
  ('T^(a,b)_n)^`() = 2%:R / (b - a) *: (('T_n)^`() \Po Tab a b).
Proof. by rewrite deriv_comp deriv_Tab [_ * _%:P]mulrC mul_polyC. Qed.

Lemma deriv_pTab0 : a != b -> 2%:R != 0 :> R ->
 ((b - a) / 2%:R *: 'T^(a,b)_1)^`() = 'T^(a,b)_0 :> {poly R}.
Proof.
move=> aDb twoNZ.
rewrite !derivE deriv_pTabn deriv_pT0 scalerA.
by rewrite mulrA divfK // mulfV ?scale1r // subr_eq0 eq_sym.
Qed.

Lemma deriv_pTab1 : a != b -> [char R]%RR =i pred0 -> 
  (((b - a)/ 8%:R) *: 'T^(a,b)_2)^`() = 'T^(a,b)_1 :> {poly R}.
Proof.
rewrite eq_sym -subr_eq0 => bDaNeq0 Hc.
have /GRing.charf0P Hf := Hc.
rewrite !derivE deriv_pTabn scalerA mulrAC !mulrA [_ * 2%:R]mulrC mulfK //.
rewrite -[8%:R]/((2 * 4)%:R) natrM invfM mulrA mulfV ?Hf // mul1r.
by rewrite -comp_polyZ -derivZ deriv_pT1.
Qed.

Lemma deriv_pTabSS n: (1 < n)%nat -> a != b -> [char R]%RR =i pred0 -> 
  ((b - a) / 2%:R *: (n.+1.*2%:R^-1 *:
    'T^(a,b)_n.+1 - n.-1.*2%:R^-1 *: 'T^(a,b)_n.-1))^`() = 
    'T^(a,b)_n :> {poly R}.
Proof.
rewrite eq_sym -subr_eq0 => n_gt1 bDaNeq0 Hc.
have /GRing.charf0P Hf := Hc.
rewrite !derivE !deriv_pTabn.
rewrite !scalerA ![_ * (_ / _)]mulrC -!scalerA -!scalerBr !scalerA.
rewrite !divfK ?Hf // mulfV // scale1r.
by rewrite -!comp_polyZ -comp_polyB -!derivE deriv_pTSS.
Qed.

Variable f : nat -> R.

Variable k : nat.
Hypothesis fk1 : f (k.+1) = 0.
Hypothesis fk2 : f (k.+2) = 0.


Lemma deriv_sum_pT : (0 < k)%N -> [char R]%RR =i pred0 -> 
  ((f 0 / 2%:R) *: 'T_1 + 
    \sum_(1 <= i < k.+2) ((f i.-1 - f i.+1) / (i.*2%:R)) *: 'T_i)^`() = 
    \sum_(0 <= i < k.+1) f i *: 'T_i.
Proof.
move=> k_gt0 Hc.
have /GRing.charf0P Hf := Hc.
under eq_bigr do rewrite mulrBl scalerBl.
rewrite sumrB.
rewrite big_add1.
have <-/= := @big_add1 _ _ _ 1 k.+4.-1 xpredT (fun i => (f i / i.-1.*2%:R) *: 'T_i.-1).
rewrite big_ltn // big_ltn //.
rewrite [\sum_(_ <= _ < _.+3) _]big_nat_recr //= fk2 mul0r scale0r addr0.
rewrite [\sum_(_ <= _ < _.+2) _]big_nat_recr //= fk1 mul0r scale0r addr0.
rewrite -!addrA -sumrB.
under eq_bigr do rewrite -!scalerA -scalerBr.
rewrite !derivE !deriv_pT0 -[_ *: _^`()]scalerA -derivE deriv_pT1 //.
rewrite addrA -scalerDl -mulrDr -mulr2n -mulr_natl mulfV ?Hf // mulr1.
rewrite (big_morph _ (@derivD R) (@deriv0 R)).
rewrite [RHS]big_ltn //; congr (_ + _).
rewrite [RHS]big_ltn //; congr (_ + _).
rewrite [RHS]big_nat_cond [LHS]big_nat_cond.
apply: eq_bigr => i /andP[/andP[i_gt1 iLk _]].
by rewrite derivE deriv_pTSS.
Qed.

Lemma deriv_sum_pTab : (0 < k)%N -> a != b -> [char R]%RR =i pred0 -> 
  (((b - a) / 2%:R * (f 0 / 2%:R)) *: 'T^(a,b)_1 + 
    \sum_(1 <= i < k.+2)
       ((b - a) / 2%:R * (f i.-1 - f i.+1) / (i.*2%:R)) *: 'T^(a,b)_i)^`() = 
    \sum_(0 <= i < k.+1) f i *: 'T^(a,b)_i.
Proof.
move => k_gt0 aDb Hc.
have /GRing.charf0P Hf := Hc.
under eq_bigr do rewrite mulrBr mulrBl scalerBl.
rewrite sumrB.
rewrite big_add1.
have <-/= := @big_add1 _ _ _ 1 k.+4.-1 xpredT 
             (fun i => ((b - a) / 2%:R  * f i / i.-1.*2%:R) *: 'T^(a,b)_i.-1).
rewrite big_ltn // big_ltn //.
rewrite [\sum_(_ <= _ < _.+3) _]big_nat_recr //= fk2 mulr0 mul0r scale0r addr0.
rewrite [\sum_(_ <= _ < _.+2) _]big_nat_recr //= fk1 mulr0 mul0r scale0r addr0.
rewrite -!addrA -sumrB.
under eq_bigr do rewrite -!scalerA -scalerBr.
rewrite !derivE.
rewrite addrA -scalerDl mulrA -mulrDr -mulrA mulrC.
rewrite -[_ *:  'T^(a,b)_1^`()]scalerA.
rewrite -[_ *: 'T^(a,b)_1^`()]derivE deriv_pTab0 ?Hf //.
rewrite -mulr2n -mulr_natl mulfV ?Hf // mulr1.
rewrite [RHS]big_ltn //; congr (_ _ _).
rewrite [_ * f 1]mulrC -2!mulrA -invfM ?Hf // -natrM -scalerA.
rewrite -derivE deriv_pTab1 //.
rewrite [RHS]big_ltn //; congr (_ _ _).
rewrite (big_morph _ (@derivD R) (@deriv0 R)).
rewrite [RHS]big_nat_cond [LHS]big_nat_cond.
apply: eq_bigr => i /andP[/andP[i_gt1 iLk _]].
by rewrite -!scalerBr !scalerA mulrC -scalerA derivE deriv_pTabSS.
Qed.



End Int.