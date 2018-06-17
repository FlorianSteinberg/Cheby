From mathcomp Require Import all_ssreflect all_algebra.
Require Import under Psatz Poly_complements seq_base.

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
elim: n {-2}n (leqnn n) => [[] // _ |n IH]; first by rewrite pT0 hornerC.
move=> m; rewrite leq_eqVlt; case/orP => [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by rewrite pT1 hornerX.
rewrite pTSS hornerD hornerN mulrnAl hornerMn.
by rewrite -commr_polyX hornerMX !IH // !mulr1 mulrS [1+ _]addrC addrK.
Qed.

Lemma commr_pT p n : GRing.comm p ('T_n).
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first by rewrite pT0; apply: commr1.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH; first by rewrite pT1; apply: commr_polyX.
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
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first by rewrite hornerC.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH.
  by rewrite pU1 hornerMn hornerX.
rewrite pUSS hornerD hornerN mulrnAl hornerMn.
rewrite -commr_polyX hornerMX mulr1 !IH //.
rewrite -mulr_natl -natrM -natrB; last first.
  by rewrite mulSn !addSnnS addnS ltnS leq_addr.
by rewrite mul2n -addnn -addSnnS addnK.
Qed.

Lemma commr_pU p n : GRing.comm p ('U_n).
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH]; first  by exact: commr1.
move=> m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|n] IH.
   rewrite pU1; apply: commrMn; exact: commr_polyX.
rewrite pUSS; apply: commrD; last by apply: commrN; apply: IH.
by rewrite mulrnAl; apply: commrMn; apply: commrM;
   [exact: commr_polyX | apply: IH].
Qed.

Lemma pT_pU n : 'T_n.+1 = 'U_n.+1 - 'X * 'U_n.
Proof.
have F: pU 1 - 'X * pU 0 = 'X by rewrite pU1 pU0 mulr1 addrK.
elim: n {-2}n (leqnn n)=> [[] // _ |m IH]; first by rewrite pT1 F.
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; rewrite pTSS pUSS IH // mulrDr -!addrA; congr (_ + _).
case: m IH=> [_|m IH].
  rewrite pT0 pU0 pU1 addrC mulrN; congr (_ - _).
  by rewrite mulr1 mulrnAl mulrnAr.
rewrite IH // pUSS addrC opprD -!addrA; congr (_ + _).
rewrite mulrDr !mulrN opprB opprK; congr (_ - _).
by rewrite !mulrA commr_polyX.
Qed.

Lemma deriv_pT n: ('T_n.+1)^`() = 'U_n *+ n.+1.
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
  by rewrite pT1 derivX.
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; rewrite pTSS derivD derivM derivMn derivX !IH //.
rewrite pT_pU.
case: m IH=> [_|m IH].
  by rewrite pU0 pU1 pT0 derivN derivC subr0 mulr_natl mulrnBl !mulr1 addrK.
rewrite derivN IH // pUSS mulr_natl !(mulrnDl, mulrnBl).
rewrite !(mulrnAl, mulrnAr) -!mulrnA.
set x := 'X * _; set y := pU m.
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
move=> n; elim: n {-2}n (leqnn n)=> [[] // _ |m IH].
  by case=>[|i]; rewrite pU0 ?coefC //= mul1r.
move=> n; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: m IH=> [_ i|m IH i].
  by rewrite coefMn coefX; case: i=> [|[|i]] //=;
     rewrite ?mul0rn //= -mulr_natl mulr1 mul1r. 
rewrite pUSS coefB mulrnAl coefMn coefXM !IH //.
case: i=> [|i].
  rewrite !addn0 mul0rn sub0r subn0 /=; case O1: (odd _); first by rewrite oppr0.
  rewrite !mul1n /= exprS !mulNr subSS mul1r.
  rewrite -{2 6}[m]odd_double_half O1 add0n subSn -addnn ?leq_addr //.
  by rewrite  addnK !binn.
rewrite !addSn !addnS /=; case O1: (odd _); last first.
   by rewrite !orbT mul0rn  subrr.
rewrite !orbF !subSS; case: leqP=> Hm; last first.
  rewrite ltnS (leq_trans _ Hm); last by  exact: (leq_addl 2 m).
  by rewrite mul0rn  sub0r oppr0.
rewrite ltnS.
move: Hm; rewrite leq_eqVlt; case/orP.
  move/eqP->.
  by rewrite subnn leqnSn !mul1r !bin0 !muln1 subr0 -mulr_natl -natrM.
rewrite ltnS leq_eqVlt; case/orP; [move/eqP->|move=>Him].
  by rewrite leqnn subSnn !subn0 expr0 !bin0 
             subr0 !mul1r !muln1 -mulr_natl -natrM expnS.
rewrite leqNgt Him /= subSn; last by exact: ltnW.
have->: ((m - i).+1./2 = (m - i)./2.+1).
 rewrite -{1}[(m-i)%N]odd_double_half.
 rewrite (odd_sub (ltnW _)) // -odd_add O1.
 by rewrite /= (half_bit_double _ false).
have->: ((m - i.+1)./2 = (m - i)./2).
 rewrite subnS -{1}[(m-i)%N]odd_double_half.
 rewrite (odd_sub (ltnW _)) // -odd_add O1.
 by rewrite /= (half_bit_double _ false).
set u := (m - i)./2.
rewrite !subSS subSn.
  rewrite binS mulnDr mulrnDr mulrDr; congr (_ + _).
    by rewrite -mulrnAr -mulr_natl -natrM mulnA expnS.
  by rewrite -mulN1r mulrA exprS. 
apply: (leq_trans (half_leq (leq_subr i m))).
by rewrite -{2}[m]odd_double_half -addnn addnA leq_addl.
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
   by rewrite-{1}[(n-i)%N]odd_double_half odd_sub // -odd_add O1.
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
  by rewrite-{1}[(n.+1 - i.+1)%N]odd_double_half /u odd_sub // -odd_add (negPf O1).
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

Notation "'T_ n " := (pT _ n) (at level 3, n at level 2, format "''T_' n").

Lemma induc2 (P: nat -> Prop):
	P 0%nat -> P 1%nat -> (forall n, P n -> P (n.+1) -> P (n.+2)) -> forall n, P n.
Proof.
intros.
elim: n {-2}n (leqnn n) => [n ineq | ].
	by have /eqP ->: (n == 0)%nat by rewrite -leqn0.
move => [ih n ineq | ].
	by case: n ineq => //; case.
move => n ih [] // m ineq.
rewrite leq_eqVlt in ineq.
case /orP: ineq => [/eqP -> | ineq ]; last by apply ih.
by apply /H1 /ih => //; apply /ih.
Qed.

Section LINEAR_INDEPENDENCE.
Variable R: unitRingType.

Lemma lreg_neq0 (l x: R):
	GRing.lreg l -> x != 0 -> l* x != 0.
Proof.
move => lreg /eqP ineq.
apply /eqP => eq.
by apply /ineq /lreg; rewrite rm0.
Qed.

Lemma mul2 (p: {poly R}):
	2%:R *: p = p *+ 2.
Proof.
rewrite -polyP => i.
by rewrite coefZ coefD -{2 3}[p`_i]mul1r -mulrDl.
Qed.

Lemma natmuln (p: {poly R}) n:
	n%:R *: p = p *+ n.
Proof.
elim: n => [ | n ih]; first by rewrite !rm0.
by rewrite -polyP => i; rewrite coefZ !mulrS mulrDl coefD -ih coefZ rm1.
Qed.

Variable lr2 : GRing.lreg (2%:R : R).

Lemma rr2: GRing.rreg (2%:R :R).
Proof.
move => x y; rewrite mulr_natr [y*_]mulr_natr -mulr_natl -[y *+ _]mulr_natl => eq.
by apply lr2.
Qed.

Lemma size_pT n : size ('T_ n : {poly R}) = n.+1.
Proof.
move: n; apply: induc2 => [ | | n ih1 ih2].
		by rewrite pT0 size_poly1.
	by rewrite pT1 size_polyX.
suff/leP leq: (n.+3 <= size ('T_n.+2: {poly R}))%nat by have/leP leq':= size_pT_leq R (n.+2); lia.
apply (@gtn_size _ _ (n.+2)).
rewrite pTSS coefD coef_opp_poly -mul2 -scalerAl coefZ coef_mul_poly.
under eq_bigr ? rewrite coefX.
rewrite big_ord_recl big_ord_recl big1; last by move => i _ /=; rewrite !rm0.
rewrite !lift0 -{2 }[ord0.+1]add1n !rm0 !rm1 coef_pTn (coef_pT R n) /=.
have ->: (n < n.+2)%N || odd (n + n.+2) by apply /orP; left.
rewrite rm0 natrX -exprS -[_ ^+ _]mulr1; apply: lreg_neq0; last by rewrite oner_eq0.
by apply GRing.lregX.
Qed.

Lemma pT_neq0 n: 'T_n != 0 :> {poly R}.
Proof.
apply/eqP => /eqP eqn.
by rewrite -size_poly_eq0 size_pT in eqn.
Qed.

Lemma coef_pTn_reg n:
	GRing.rreg ('T_n: {poly R})`_n.
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
under eq_bigr ? rewrite -scalerBl -coefB; move => /eqP eq.
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

Lemma inducleq (P: nat -> Prop):
	P 0%nat -> (forall m: nat, (forall n, (n <= m)%nat -> P n) -> P m.+1) -> forall n, P n.
Proof.
move => P0 induc n.
elim: n {-2}n (leqnn n) => [ | n ih m ineq]; first by move => n; rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt in ineq; case /orP: ineq.
	by move => /eqP ->; apply induc.
by move => ineq; apply ih.
Qed.

Section Multiplication.
Variable (R: unitRingType).
Definition absn m n := (m - n + (n - m))%nat.

Lemma absnC:
	commutative absn.
Proof. by move => m n; rewrite /absn addnC. Qed.

Lemma absnn n:
	absn n n = 0%nat.
Proof. by rewrite /absn !subnn addn0. Qed.

Lemma subn_leq m n:
	(n <= m -> n - m = 0)%nat.
Proof.
by move => ineq; apply /eqP; rewrite subn_eq0.
Qed.

Lemma ltnoreq n m:
	(n < m \/ n = m \/ m< n)%nat.
Proof.
case E: (n == m); first 	by right; left; have /eqP ->: n == m by rewrite E.
have : n != m by apply /eqP; move/eqP: E.
by rewrite neq_ltn; case/orP; [left | right; right].
Qed.

Lemma absn_eq0 m n:
	(absn m n = 0 -> m = n)%nat.
Proof.
by rewrite /absn; case /orP: (leq_total n m) => ineq;
rewrite (subn_leq ineq) ?addn0 ?add0n => /eqP eq;
rewrite subn_eq0 in eq; apply /eqP; rewrite eqn_leq; apply /andP.
Qed.

Lemma absnSn n m:
	absn m.+1 n.+1 = absn m n.
Proof. by rewrite /absn !subSS. Qed.

Lemma abs0n n:
	absn 0 n = n.
Proof. by rewrite /absn sub0n subn0 add0n. Qed.

Lemma absn0 n:
	absn n 0 = n.
Proof. by rewrite /absn sub0n subn0 addn0. Qed.

Lemma absn1S n:
	absn 1 n.+1 = n%nat.
Proof.
by rewrite /absn subn1; suff ->: (1 - n.+1 = 0)%nat by rewrite add0n.
Qed.

Lemma absnS1 n:
	absn n.+1 1 = n%nat.
Proof.
by rewrite /absn subn1; suff ->: (1 - n.+1 = 0)%nat by rewrite addn0.
Qed.

Lemma absn_maxnminn m n:
	(absn m n = maxn m n - minn m n)%nat.
Proof.
rewrite maxnE minnE.
case E: (n == m).
	have/eqP ->: n == m by rewrite E.
	by rewrite !subnn subn0 addn0 subnn absnn.
have: n != m by apply /eqP => /eqP eq; move: eq; rewrite E.
rewrite /absn.
rewrite neq_ltn => /orP or; case: or => ineq.
	rewrite subKn; last exact: (leqW ineq).
	have/eqP ->: (n - m == 0)%nat by rewrite subn_eq0; apply (leqW ineq).
	by rewrite !addn0.
have/eqP ->: (m - n == 0)%nat by rewrite subn_eq0; apply (leqW ineq).
rewrite subn0 add0n addnC.
by rewrite subnK; last exact: (leqW ineq).
Qed.

Lemma subn_eq m n p:
	(p > 0)%N -> (m - n = p)%N -> (m = p + n)%N.
Proof.
move => pgt E.
case E': (n == m).
	rewrite -E;	have /eqP ->: n == m by rewrite E'.
	by rewrite subnn add0n.
have: n != m by apply /eqP => /eqP eq; move: eq; rewrite E'.
rewrite neq_ltn => /orP or; case: or => ineq.
	by rewrite -E subnK; last exact: (leqW ineq).
exfalso.
have /eqP zero: (m - n == 0)%nat.
	by rewrite subn_eq0; apply: (leqW ineq).
move: E zero => -> eq.
by rewrite eq in pgt.
Qed.

Lemma absnnD n m:
	absn n (n + m) = m.
Proof.
rewrite /absn (subn_leq); last by rewrite leq_addr.
by rewrite add0n addnC -addnBA// subnn addn0.
Qed.

Lemma subnSn n:
	(n - n.+1 = 0)%N.
Proof. by elim: n. Qed.

Lemma absnif n m:
	(absn m n.+1 = if m <= n then (absn m n).+1
		else (absn m n).-1)%nat.
Proof.
case: ifP => ineq; first by rewrite /absn subnS subn_leq // subSn//.
	rewrite /absn subnS (@subn_leq m n.+1).
	rewrite (@subn_leq m n).
		by rewrite !addn0.
	by rewrite -ltnS; apply leqW; rewrite leqNgt ltnS ineq.
by rewrite leqNgt ltnS ineq.
Qed.

Lemma absn_pT n m:
	'X *+2 * 'T_(absn m n.+1) - 'T_(absn m n) = 'T_(absn m n.+2):>{poly R}.
Proof.
case E: (m<=n)%nat.
	by rewrite !absnif E; case: ifP => [_ | /eqP ]; [rewrite pTSS | rewrite subn_leq ?leqW].
have ineq: (n.+1 <= m)%nat by apply /leP; move/leP: E; lia.
rewrite leq_eqVlt in ineq; case /orP: ineq => [/eqP eq | ineq].
	rewrite -eq absnn absnC absnif leqnn absnn absnif leqnn absnn.
	by rewrite pT0 pT1 mulr1 -addrA subrr addr0.
rewrite /absn !subnS.
have /eqP ->: (n -m == 0)%nat by rewrite subn_eq0; apply /leP; move/leP: ineq; lia.
have /eqP ->: (n.+1 -m == 0)%nat by rewrite subn_eq0; apply /leP; move/leP: ineq; lia.
have /eqP ->: (n.+2 -m == 0)%nat by rewrite subn_eq0; apply /leP; move/leP: ineq; lia.
rewrite {2}(@Lt.S_pred (m-n) (m-n).-2); last by move/leP: ineq; rewrite /subn/subn_rec; lia.
rewrite {1 2}(@Lt.S_pred (m-n).-1 (m-n).-2); last by move/leP: ineq; rewrite /subn/subn_rec; lia.
by rewrite pTSS opprD addrA subrr opprK add0r.
Qed.

Lemma mul_pT n m:
	2%:R *: 'T_n * 'T_m = 'T_(n + m) + 'T_(absn m n) :> {poly R}.
Proof.
move: n; apply inducleq.
	by rewrite pT0 add0n absn0 mul2 mulr2n mulrDl rm1.
case => [ | n].
	rewrite pT1 mul2 add1n.
	case: m => [ih | m ih]; first by rewrite pT0 pT1 /absn rm1 mulr2n.
	by rewrite absnS1 pTSS -addrA [-'T_m + 'T_m]addrC subrr rm0.
move => ih.
rewrite pTSS scalerDr mulrDl -!scalerAl mulNr scalerN !scalerAl ih //.
rewrite -mul2 -!scalerAl -mulrA -commr_polyX scalerAl scalerAl scalerAl ih //.
rewrite !addSn pTSS scalerDr mulrDl -scalerAl commr_polyX scalerAl mul2 -!addrA; f_equal.
rewrite opprD addrA [_ - 'T_(n+m)]addrC -addrA; f_equal.
rewrite -scalerAl commr_polyX scalerAl mul2.
exact: absn_pT.
Qed.

Lemma pT_mulX_weak n : 
  'X *+ 2 * 'T_n.+1 = 'T_n + 'T_n.+2 :> {poly R}.
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

Definition pTab a b n := 'T_n \Po (Tab a b).

Notation "''T^(' a ',' b ')_' n" := (pTab a b n)
  (at level 3, n at level 2, format "''T^(' a ',' b ')_' n").

Lemma horner_pTab a b n (x: R):
('T^(a,b)_n).[x] = ('T_n).[(x*+2 - a - b) / (b - a)].
Proof.
rewrite /pTab horner_comp /Tab.
rewrite hornerD hornerZ hornerX hornerC.
f_equal.
rewrite mulr2n -{2 3}[x]mul1r -[1 * x + 1 * x]mulrDl -addrA [RHS]mulrDl.
by rewrite -[-a-b]opprD -{3}[b-a]mulr1 -mulf_div divr1.
Qed.

Lemma horner_pTab_a a b n:
	b != a -> 	('T^(a,b)_n).[a] = ('T_n).[-1].
Proof.
move =>/eqP neq.
rewrite horner_pTab mulr2n -[a + a - a]addrA.
f_equal.
have -> : a - a = 0 by apply /eqP; rewrite (subr_eq0 a a).
rewrite rm0 -opprB mulNr divrr => //.
rewrite unitfE.
apply /eqP => /eqP eqn; apply /neq /eqP.
by rewrite -subr_eq0.
Qed.

Lemma horner_pTab_b a b n:
	b != a -> 	('T^(a,b)_n).[b] = ('T_n).[1].
Proof.
move =>/eqP neq.
rewrite horner_pTab mulr2n -!addrA [- a - b]addrC !addrA -[b + b - b]addrA.
have -> : b - b = 0 by apply /eqP; rewrite (subr_eq0 b b).
rewrite rm0 divrr => //.
rewrite unitfE.
apply /eqP => /eqP eqn; apply /neq /eqP.
by rewrite -subr_eq0.
Qed.
End pTab.











