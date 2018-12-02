From mathcomp Require Import all_ssreflect all_algebra.
Require Import Psatz under CPoly Poly_exec Poly_complements seq_base.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GRing.Theory.
Local Open Scope ring_scope.

Section CSHAW.
Variable R : ringType.
Implicit Types (l : seq R) (p: {poly R}) .

(* Interpret a list as Chebychev Coefficients of a polynomial: *)
Definition CPoly (l: seq R): {poly R} := \sum_(i < size l) l`_i *: 'T_i.

Lemma CPoly_nil : CPoly nil = 0 :> {poly R}.
Proof. by rewrite /CPoly big_ord0. Qed.

Lemma CPolyC c: CPoly [::c] = c%:P :> {poly R}.
Proof.
by rewrite /CPoly /= big_ord1 pT0 alg_polyC.
Qed.

Fixpoint lpT (n : nat) {struct n} : seq R :=
  if n is n1.+1 then
    if n1 is n2.+1 then lsub_poly ((lscal_poly (1 + 1) (0%R :: lpT n1))) (lpT n2)
    else [::0; 1]
  else [::1].

Lemma lpTSS n:
	lpT n.+2 = lsub_poly ((lscal_poly (2%:R) (0%R :: lpT n.+1))) (lpT n).
Proof. done.  Qed.

Lemma lpT_spec n:
	Poly (lpT n) = 'T_n.
Proof.
move: n; apply induc2; try rewrite unlock /= !cons_poly_def !rm0 ?rm1//.
move => n ih1 ih2.
rewrite pTSS lpTSS lsub_poly_spec lscal_poly_spec Poly_cons.
rewrite cons_poly_def !rm0 ih1 ih2 commr_polyX scalerAl.
by congr (_ * _ - _); rewrite !mulr2n scalerDl -mulr_algl alg_polyC !rm1.
Qed.

Lemma size_CPoly_leq l : (size (CPoly l) <= size l)%N.
Proof.
apply: (leq_trans (size_sum _ _ _)).
apply/bigmax_leqP => i _.
apply: leq_trans (size_scale_leq _ _) _.
by apply: leq_trans (size_pT_leq _ _) _.
Qed.

Fixpoint Cb l (x : R) :=
 if l is a :: l' then
   let t := Cb l' x in
   let a1 := a + t.1 * x - t.2 in
   (a1, t.1) else (0, 0).

Lemma Cb_nil (r: R):
	Cb [::] r = (0, 0).
Proof. done. Qed.

Lemma Cb_eq0 q x : Poly q  = 0 -> Cb q x = 0.
Proof.
elim: q => //= a q IH.
rewrite cons_poly_def => H.
have := size_MXaddC (Poly q) a.
rewrite {}H size_poly0; case: eqP => // qZ.
case: eqP => // -> _.
by rewrite IH //= !rm0.
Qed.

Lemma Cb_eq q1 q2 x :
  Poly q1 = Poly q2 -> Cb q1 x = Cb q2 x.
Proof.
elim: q1 q2 => [/= q2 H|a q1 IH [/Cb_eq0->//|b q2]]; first by rewrite Cb_eq0.
rewrite /= !cons_poly_def => H.
have H1 : (Poly q1 - Poly q2) * 'X + (a - b)%:P = 0.
  by rewrite polyC_sub mulrBl addrAC addrA H addrK subrr.
have := size_MXaddC (Poly q1 - Poly q2) (a - b).
rewrite {}H1 size_poly0; case: eqP => // /subr0_eq/IH<-.
by case: eqP => // /subr0_eq <-.
Qed.

Definition Cshaw (L: seq R) (x : R) := 
  let: (x1, x2) := Cb L (x *+ 2) in x1 - x2 * x.

Lemma Cshaw_spec (k : seq R) r :
   Cshaw k r = (CPoly k).[r].
Proof.
rewrite /Cshaw /CPoly.
rewrite horner_sum; under eq_bigr ? rewrite hornerZ.
elim: {k}S {-2}k (leqnn (size k).+1) => // n IH [|a [|b k]] H.
- by rewrite big_ord0 /= !rm0.
- by rewrite /= !rm0 big_ord_recr big_ord0 /= pT0 hornerC rm1 rm0.
have /IH/=/eqP : (size (b :: k) < n)%N by rewrite -ltnS.
  rewrite [size _]/= big_ord_recl. 
  rewrite [_ * _ + _]addrC -subr_eq eq_sym.
  pose f (i : 'I_(size k)) := k`_i * ('T_i.+1).[r].
  rewrite (eq_bigr f) {}/f => [/eqP H1|i _] //.
rewrite [size _]/= 2!big_ord_recl.
pose f (i : 'I_(size k)) :=
  (k`_i * ('T_i.+1).[r] * (r *+2)) - (k`_i * ('T_i).[r]).
rewrite (eq_bigr f) {}/f => [|i _]; last first.
  rewrite pTSS !hornerE !mulrnAl hornerMn -commr_polyX hornerMX.
  by set x := 'T_i.+1; rewrite !lift0 /= {}/x mulrBr -mulrnAr mulrA.
rewrite !lift0 sumrB ![_ `_ _]/= -mulr_suml H1 -IH; last first.
  by rewrite -ltnS (ltn_trans _ H).
rewrite pT0 pT1 !hornerE /=.
(* This should be ring *)
case: (Cb _ _) => u1 u2 /=.
rewrite !mulr2n !(mulrDl, mulrDr, opprB, opprD, mulNr ) -!addrA.
do 40 (congr (_ + _); [idtac] || rewrite [RHS]addrC -![in RHS]addrA).
by rewrite opprK addrC addrK.
Qed.
End CSHAW.

Section CP2P.
Variable (R: ringType).

Definition opp_Cpoly := lopp_poly.

Lemma size_opp_Cpoly (l : seq R) : size (opp_Cpoly l) = size l.
Proof. by elim: l => //= a l ->. Qed.

Lemma opp_Cpoly_spec (l : seq R): CPoly (opp_Cpoly l) = -(CPoly l). 
Proof.
rewrite -sumrN.
under eq_bigr ? rewrite -coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
rewrite lopp_poly_spec.
rewrite -(@polybase_widen _ _ _ (size l)).
  by apply: eq_bigr => i _; rewrite coefN coef_Poly scaleNr.
by rewrite size_opp size_Poly.
Qed.

Definition add_Cpoly := ladd_poly.

Lemma size_add_Cpoly (l1 l2 : seq R) : 
  size (add_Cpoly l1 l2) = maxn (size l1) (size l2).
Proof.
elim: l1 l2 => [l2|a l1 IH [|b l2]] /=; first by rewrite max0n.
  by rewrite maxn0.
by rewrite IH maxnSS.
Qed.

Lemma add_Cpoly_spec (l k: seq R):
	CPoly (add_Cpoly l k) = (CPoly l) + (CPoly k).
Proof.
rewrite /add_Cpoly /CPoly.
under eq_bigr ? rewrite -coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
rewrite ladd_poly_spec.
rewrite sumrA.
congr (_ + _).
	rewrite -(@polybase_widen _ _ _ (size l)); last exact: size_Poly.
	by under eq_bigr ? rewrite !coef_Poly.
rewrite -(@polybase_widen _ _ _ (size k)); last exact: size_Poly.
by under eq_bigr ? rewrite !coef_Poly.
Qed.

Definition sub_Cpoly := lsub_poly.

Lemma size_sub_Cpoly (l1 l2 : seq R) : 
  size (sub_Cpoly l1 l2) = maxn (size l1) (size l2).
Proof.
elim: l1 l2 => [l2|a l1 IH [|b l2]] /=; first by rewrite size_map max0n.
  by rewrite maxn0.
by rewrite IH maxnSS.
Qed.

Lemma sub_Cpoly_spec (l k: seq R):
	CPoly (sub_Cpoly l k) = (CPoly l) - (CPoly k).
Proof.
rewrite /sub_Cpoly /CPoly.
under eq_bigr ? rewrite -coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
rewrite lsub_poly_spec sumrA.
congr (_ + _).
	rewrite -(@polybase_widen _ _ _ (size l)); last exact: size_Poly.
  by under eq_bigr ? rewrite !coef_Poly.
rewrite -sumrN.
rewrite -(@polybase_widen _ _ _ (size k)).
   by apply: eq_bigr => i _; rewrite coefN coef_Poly scaleNr.
by rewrite size_opp; exact: size_Poly.
Qed.

Definition scl2_Cpoly (l : seq R) := [seq i *+ 2 | i <- l]. 

Lemma size_scl2_Cpoly l : size (scl2_Cpoly l) = size l.
Proof. by rewrite size_map. Qed.

Lemma scl2_Cpoly_spec (l : seq R):
  CPoly (scl2_Cpoly l) = CPoly l *+ 2.
Proof.
rewrite -sumrMnl.
under eq_bigr ? rewrite -coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
rewrite -(@polybase_widen _ _ _ (size l)).
  apply: eq_bigr => i _.
  by rewrite coef_Poly (nth_map 0) // scalerMnl.
by rewrite -[size l]size_scl2_Cpoly size_Poly.
Qed.

Fixpoint CP2P_rec l (p1 p2 : seq R) :=
match l with
|  a :: l =>
   ladd_poly (lscal_poly a p1)
     (CP2P_rec l (lsub_poly (lscal_poly 2%:R  (0:: p1)) p2) p1)
| _ => [::]
end.

Lemma CP2P_rec_cons a (l l1 l2 : seq R) :
  CP2P_rec (a :: l) l1 l2 =
   ladd_poly (lscal_poly a l1)
     (CP2P_rec l (lsub_poly (lscal_poly 2%:R  (0::l1)) l2) l1).
Proof. by []. Qed.

Lemma CP2P_rec_eq0 (q p1 p2 : seq R):
	Poly q = 0 -> Poly (CP2P_rec q p1 p2) = 0.
Proof.
elim: q p1 p2 => // a q ih /= p1 p2.
move => /cons_poly_inj0 [-> eq].
rewrite ladd_poly_spec lscal_poly_spec.
by rewrite ih // -mul_polyC !rm0.
Qed.

Lemma CP2P_rec_eq (q1 q2 p1 p2: seq R):
  Poly q1 = Poly q2 -> Poly (CP2P_rec q1 p1 p2) = Poly (CP2P_rec q2 p1 p2).
Proof.
elim: q1 q2 p1 p2 => // [q2 p1 p2 eq | a q1 ih q2 p1 p2 eq].
	by rewrite /= CP2P_rec_eq0.
case: q2 eq.
	move => /cons_poly_inj0 [-> eq].
	rewrite ladd_poly_spec lscal_poly_spec.
	rewrite !rm0.
	by apply CP2P_rec_eq0.
move => b q2 /cons_poly_inj [-> eq].
by rewrite !CP2P_rec_cons !ladd_poly_spec !lscal_poly_spec (ih q2).
Qed.

Lemma CP2P_rec_spec n (l: seq R):
   Poly (CP2P_rec l (lpT R n.+1) (lpT R n)) =
      \sum_(i < size l) l`_i *: 'T_(n.+1 + i).
Proof.
elim: l n => [|a l IH] n.
  rewrite /= big1 // => i _.
  by rewrite nth_nil scale0r.
rewrite CP2P_rec_cons ladd_poly_spec lscal_poly_spec.
rewrite big_ord_recl ?addn0 lpT_spec.
congr (_ *: _ + _) => //.
rewrite (IH n.+1).
by apply: eq_bigr => i _; rewrite addnS.
Qed.

Definition CP2P (l : seq R) :=
  match l with 
  | a :: l => 
     ladd_poly [::a] (CP2P_rec l (lpT R 1) (lpT R 0))
  | _ => [::]
  end.

Lemma CP2P_eq0 (q : seq R) :
  Poly q = 0 -> Poly (CP2P q) = 0.
Proof.
case: q => // a q.
rewrite ladd_poly_spec =>/= /cons_poly_inj0 [-> eq].
rewrite cons_poly_def !rm0.
by rewrite CP2P_rec_eq0.
Qed.

Lemma CP2P_eq (q1 q2 : seq R) :
  Poly q1 = Poly q2 -> Poly (CP2P q1) = Poly (CP2P q2).
Proof.
case: q1 q2 => // [q2 /= eq | a q1 q2].
	by rewrite CP2P_eq0.
case: q2 => // [/cons_poly_inj0 [-> eq] | b q2 /cons_poly_inj [-> eq]].
	rewrite ladd_poly_spec /= cons_poly_def !rm0.
	by rewrite CP2P_rec_eq0.
by rewrite !ladd_poly_spec; f_equal; apply CP2P_rec_eq.
Qed.

Lemma CP2P_spec (l : seq R) :
   Poly (CP2P l) = CPoly l.
Proof.
case: l => [ | a l]; first by	rewrite CPoly_nil.
rewrite /CP2P.
rewrite ladd_poly_spec CP2P_rec_spec.
rewrite /CPoly big_ord_recl ?add0n.
by f_equal; rewrite /= cons_poly_def !rm0 pT0 alg_polyC.
Qed.

End CP2P.

Compute (ncons 11 (0%:R: int) [::1]).

Compute CP2P  (ncons 11 (0%:R: int) [::1]).

Section P2CP.

Variable R:unitRingType.

Fixpoint Cmulx_rec (l : seq R) :=
  match l with 
  | a :: ((b :: c :: l) as l1) =>
      (a + c) / 2%:R :: Cmulx_rec l1 
  | l =>  [seq x /2%:R | x <- l]
  end.

Lemma Cmulx_recSS a b c (l : seq R) :
	Cmulx_rec (a :: b :: c :: l) = (a + c) / 2%:R :: Cmulx_rec (b :: c :: l).
Proof. done. Qed.

Lemma size_CPoly_Poly (l: seq R) :
	GRing.lreg (2%:R:R)-> size (CPoly l) = size (Poly l).
Proof. 
rewrite /CPoly => lr2.
pose f (i: 'I_(size l)) := (Poly l)`_i  *: 'T_i.
rewrite (eq_bigr f) {}/f => [ | i _]; last by rewrite coef_Poly.
rewrite polybase_widen; last exact: size_Poly.
by rewrite size_sum_pT.
Qed.

Lemma Cmulx_rec_spec (l : seq R)  n :
	(2%:R:R) \is a GRing.unit ->
  ('X * \sum_(i < size l) l`_i *: 'T_(n.+1 + i))%R =
  (l`_0 / 2%:R) *: 'T_n + (l`_1 / 2%:R) *: 'T_n.+1 +
  \sum_(i < size (Cmulx_rec l)) (Cmulx_rec l)`_i *: 'T_(n.+2 + i) :> {poly R}.
Proof.
move => H.
elim: l n => [|a [|b [|c l]] IH] n.
- by rewrite !big_ord0 mul0r mulr0 !scale0r !add0r. 
- rewrite ![[:: _]`_ _]/= mul0r scale0r addr0.
  rewrite ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![_`_ _]/= !addr0 !addn0 -!scalerA -scalerDr.
  by rewrite -commr_polyX -scalerAl -pT_mulX // commr_polyX.
- rewrite ![[:: _; _]`_ _]/= ![size _]/= !(big_ord0, big_ord_recl).
  rewrite ![[:: _; _]`_ _]/= !addn1 !addn0 !addr0.
  rewrite -commr_polyX mulrDl -!scalerAl commr_polyX pT_mulX //.
  rewrite commr_polyX pT_mulX // scalerDr !scalerA -!addrA; congr (_ + _).
  rewrite [RHS]addrCA; congr (_ + _).
  by rewrite scalerDr !scalerA.
rewrite -[Cmulx_rec _]/((a + c) / 2%:R :: Cmulx_rec  [:: b, c & l]).
set u := [:: b, _ & _].
rewrite -[size _]/(size [:: b, c & l]).+1.
rewrite big_ord_recl mulrDr.
pose f (i : 'I_(size u)) := u`_i *: 'T_(n.+2 + i).
rewrite (eq_bigr f) => [|i _]; last first.
  by congr (_ *: 'T_ _); rewrite !addnS.
rewrite {f}IH.
rewrite ![_`_ _]/= addn0.
rewrite -/u.
set v := Cmulx_rec _.
rewrite -[size (_ :: _)]/(size v).+1.
rewrite [in RHS]big_ord_recl.
rewrite ![_`_ _]/= addn0.
pose f (i : 'I_(size v)) := v`_i *: 'T_(n.+3 + i).
rewrite [in RHS](eq_bigr f) => [|i _]; last first.
  by congr (_ *: 'T_ _); rewrite !addnS.
rewrite !addrA; congr (_ + _).
rewrite addrAC [in RHS] addrAC; congr (_ + _).
rewrite mulrDl scalerDl addrA; congr (_ + _).
rewrite -commr_polyX -scalerAl.
by rewrite commr_polyX pT_mulX // scalerDr !scalerA.
Qed.

Lemma size_Cmulx_rec l : size (Cmulx_rec l) = size l.
Proof. by elim: l => //= a [|b [|c l1]] IH //=; rewrite IH. Qed.

Lemma Cmulx_rec_eq0 L:
	Poly L = 0 -> Poly (Cmulx_rec L) = 0.
Proof.
elim: L => // a L ih.
rewrite [Poly _]/= => /= /cons_poly_inj0 [-> eq].
case: L eq ih => [_ /= | b L]; first by rewrite !cons_poly_def !rm0.
rewrite [Poly _]/= => /cons_poly_inj0 [-> eq] ih.
case: L eq ih => [_ /= | c L]; first by rewrite !cons_poly_def !rm0.
rewrite [Poly _]/= => /cons_poly_inj0 [-> eq]; rewrite !rm0.
by rewrite /= !cons_poly_def !rm0 => ->; try rewrite eq; rewrite !rm0.
Qed.

Lemma Cmulx_rec_eq L K:
	Poly L = Poly K -> Poly (Cmulx_rec L) = Poly (Cmulx_rec K).
Proof.
elim: L K => [/= K eq | a L ih K]; first by rewrite Cmulx_rec_eq0.
case: K => [eq | a' K]; first by rewrite [Cmulx_rec [::]]/= Cmulx_rec_eq0.
rewrite ![Poly (_ :: _)]/= => /cons_poly_inj [-> eq].
case: L eq ih => [ | b L].
	case: K => // b' K; rewrite ![Poly _]/= => /esym /cons_poly_inj0 [-> eq] ih.
	case: K eq => [ | c' K]; first by rewrite /= !cons_poly_def !rm0.
	rewrite [Poly _]/= => /cons_poly_inj0 [-> /esym eq].
	rewrite Cmulx_recSS !rm0.
	by rewrite !Poly_cons -ih; rewrite /= !cons_poly_def; try rewrite -eq; rewrite !rm0.
case: K.
	rewrite ![Poly _]/= => /cons_poly_inj0 [->].
	case: L => [ | c L]; first by rewrite /= !cons_poly_def !rm0.
	rewrite Poly_cons => /cons_poly_inj0 [-> eq] ih.
	by rewrite Cmulx_recSS Poly_cons (ih nil); try rewrite eq; rewrite /= !cons_poly_def !rm0.
move => b' K.
rewrite !Poly_cons => /cons_poly_inj [->].
case: L => [ | c L].
	case: K => // c' K; rewrite ![Poly _]/= => /esym /cons_poly_inj0 [-> eq] ih.
	by rewrite Cmulx_recSS !rm0 !Poly_cons -ih /=; try rewrite eq; rewrite !cons_poly_def !rm0.
case: K => [ | c' K].
	rewrite ![Poly _]/= => /cons_poly_inj0 [-> ->] ih.
	by rewrite Cmulx_recSS Poly_cons (ih [:: b']) /= !cons_poly_def !rm0.
rewrite Poly_cons Poly_cons => /cons_poly_inj [-> eq] ih.
rewrite !Cmulx_recSS !Poly_cons.
by rewrite (ih [:: b', c' & K]); last by rewrite /= !cons_poly_def eq.
Qed.

Definition Cmulx l :=
  Cmulx_rec (0 :: (if l is a :: l then (a *+ 2 :: l) else l)).

Lemma Cmulx_nil : Cmulx [::] = [:: 0].
Proof. by rewrite /Cmulx /= rm0. Qed.

Lemma size_Cmulx l : size (Cmulx l) = (size l).+1.
Proof. by case: l => // a l; rewrite size_Cmulx_rec. Qed.

Lemma Cmulx_eq L K:
	Poly L = Poly K -> Poly (Cmulx L) = Poly (Cmulx K).
Proof.
rewrite /Cmulx => eq.
apply Cmulx_rec_eq => /=; rewrite !cons_poly_def !rm0; congr (_ * _).
case: L K eq => [ | a L]; case => //=; last first.
		by move => b K /cons_poly_inj [-> ->].
	by move => /cons_poly_inj0 [-> ->]; rewrite !cons_poly_def !rm0.
by move => a L /esym/cons_poly_inj0 [-> ->]; rewrite !cons_poly_def !rm0.
Qed.

Lemma Cmulx_prop (l : seq R) :
  (2%:R : R) \is a GRing.unit -> 
  ('X * \sum_(i < size l) l`_i *: 'T_i)%R =
  \sum_(i < size (Cmulx l)) (Cmulx l)`_i *: 'T_i :> {poly R}.
Proof.
move=> H.
case: l => [|a l].
  by rewrite !(big_ord0, big_ord_recl) /= !rm0.
rewrite [size _]/= big_ord_recl.
rewrite (eq_bigr (fun i : 'I_(size l) => l`_i *: 'T_(1 + i))) => [|i _]; last first.
  by rewrite lift0.
rewrite mulrDr Cmulx_rec_spec // size_Cmulx_rec size_Cmulx //.
case: l => [|b l].
  rewrite !(big_ord0, big_ord_recl) /= !rm0 pT0 pT1.
  rewrite -[a *+ _]mulr_natl -commr_nat mulrK //.
  by rewrite -[RHS]mul_polyC alg_polyC commr_polyX.
rewrite ![size (_ :: _)]/= !(big_ord0, big_ord_recl) !addrA.
congr (_ + _ *: _ + _); last first.
- apply: eq_bigr => i _.
  by rewrite !lift0 !addnS; congr (_ *: _); case: l i.
- by case: l.
rewrite pT1 pT0 addrAC  addrC; congr (_ + _).
  by rewrite /= rm0.
rewrite -commr_polyX alg_polyC  mul_polyC -scalerDl; congr (_ *: _).
case: l => [|c l] /=.
  by rewrite !rm0 -[a *+ _]mulr_natl -commr_nat mulrK.
by rewrite mulrDl -[a *+ _]mulr_natl -commr_nat mulrK.
Qed.

Lemma Cmulx_spec l:
	(2%:R : R) \is a GRing.unit -> (CPoly (Cmulx l)) = 'X * (CPoly l).
Proof.
move=> H.
have H1 := Cmulx_prop l H.
by rewrite /CPoly H1.
Qed.

Definition lpXt i := iter i Cmulx [::1].

Lemma lpXt_step i:
	lpXt (S i) = Cmulx (lpXt i).
Proof.
by rewrite [LHS]iterS.
Qed.

Lemma lpXt_spec i:
	(2%:R : R) \is a GRing.unit -> (CPoly (lpXt i)) = 'X^i.
Proof.
move => u2.
elim: i => [ | i ih]; first by rewrite /CPoly big_ord1 pT0 expr0 /= alg_polyC.
rewrite lpXt_step Cmulx_spec => //.
rewrite [X in _ * X = _ ]ih.
by rewrite exprS.
Qed.

Fixpoint P2CP (l : seq R) :=
  if l is a :: l1 then ladd_poly [:: a] (Cmulx (P2CP l1))
  else [::].

Lemma P2CP_cons a l :
  P2CP (a :: l) = ladd_poly [:: a] (Cmulx (P2CP l)).
Proof. by []. Qed.

Lemma P2CP_spec l :
  (2%:R : R) \is a GRing.unit -> CPoly (P2CP l) = (Poly l).
Proof.
move => I2.
elim l => [ | a k ih]; first by rewrite CPoly_nil.
rewrite P2CP_cons add_Cpoly_spec CPolyC/= cons_poly_def.
by rewrite Cmulx_spec => //; rewrite ih commr_polyX addrC.
Qed.

Fixpoint abs_mul_Cpoly (R : fieldType) n (a : R) acc l := 
 if n is n1.+1 then
   if l is b :: l1 then abs_mul_Cpoly n1 a ((a * b) / 2%:R :: acc) l1
   else (ncons n.+1 0 acc)
 else  add_Cpoly (0 :: acc) [seq (a * i) / 2%:R| i <- l].

Lemma CPoly_rcons (R1 : ringType) (a : R1) l : 
  CPoly (rcons l a) = CPoly l + a *: 'T_(size l).
Proof.
rewrite /CPoly size_rcons big_ord_recr /=.
congr (_ + _).
  apply: eq_bigr => i _.
  by rewrite nth_rcons ltn_ord.
by rewrite nth_rcons ltnn eqxx.
Qed. 

Lemma CPoly_ncons0 (R1 : ringType) n  (a : R1) l : 
  CPoly (ncons n 0 (a :: l)) = CPoly (ncons n.+1 0 l) + a *: 'T_n.
Proof.
rewrite /CPoly !size_ncons addSnnS.
have Li : (n < n + (size l).+1)%nat by rewrite -addSnnS leq_addr.
rewrite [in RHS](bigD1 (Ordinal Li)) //=.
rewrite [_ `_n](_ : _ = 0) ?scale0r ?add0r; last first.
  by rewrite (nth_ncons _ n.+1) leqnn.
rewrite addrC (bigD1 (Ordinal Li)) //=.
congr (_ + _).
  by rewrite nth_ncons ltnn subnn.
apply: eq_bigr => i Hi.
rewrite nth_ncons (nth_ncons _ n.+1).
rewrite [(_ < _.+1)%nat]leq_eqVlt ltnS /=.
rewrite [_ == _](negPf Hi).
case: leqP => //=.
rewrite leq_eqVlt eq_sym  [_ == _](negPf Hi) /= -subn_gt0.
by rewrite subnS; case: subn.
Qed.

Lemma abs_mul_Cpoly_correct (R1 : fieldType) n (a : R1) acc l :
  CPoly (abs_mul_Cpoly n a acc l) =
  CPoly (ncons n.+1 0 acc) +
  \sum_(j < size l) ((a * l`_j) / 2%:R) *: 
      'T_(absn n j)%nat.
Proof.
elim: n acc l => [acc l| n1 IH ac l].
  rewrite /abs_mul_Cpoly add_Cpoly_spec.
  congr (_ + _). 
  rewrite /CPoly size_map //.
  apply: eq_bigr => i _.
  by rewrite (nth_map 0) // abs0n.
rewrite /abs_mul_Cpoly.
case: l => [|b l1].
  by rewrite big_ord0 addr0.
by rewrite IH CPoly_ncons0 -!addrA big_ord_recl absn0.
Qed.
  
Definition add_mul_Cpoly (R : fieldType) n (a : R) l := 
  ncons n 0 [seq (a * i) / 2%:R| i <- l].

Fixpoint mul_rec_Cpoly (R : fieldType) n (l1 l2 : seq R) := 
  if l1 is a :: l3 then
    let v1 := abs_mul_Cpoly n a [::] l2 in
    let v2 := add_mul_Cpoly n a l2 in
    add_Cpoly (add_Cpoly v1 v2) (mul_rec_Cpoly n.+1 l3 l2)
  else [::].

Lemma mul_rec_Cpoly_correct (R1 : fieldType) n (l1 l2 : seq R1) :
  (2%:R != 0 :> R1)%R ->
  CPoly (mul_rec_Cpoly n l1 l2) =  
  CPoly (ncons n 0 l1) * CPoly l2.
Proof.
move=> TNZ.
elim: l1 n => [n|a l1 IH n] /=.
  rewrite [CPoly _]big_ord0 [CPoly _]big1 ?mul0r // => i _.
  by rewrite nth_ncons nth_nil if_same scale0r.
rewrite !add_Cpoly_spec IH abs_mul_Cpoly_correct.
rewrite /add_mul_Cpoly CPoly_ncons0 mulrDl.
rewrite [CPoly _]big1 => [|i _]; last first.
  by rewrite nth_ncons nth_nil if_same scale0r.
rewrite add0r [RHS]addrC.
congr (_ + _).
rewrite [CPoly _](_ : _ = \sum_(j < size l2)
                               (a * l2`_j / 2%:R) *: 'T_(n + j)).
  rewrite -big_split /= mulr_sumr.
  apply: eq_bigr => i _.
  rewrite -scalerDr addrC addnC -mul_pT -!scalerAl -!scalerAr !scalerA.
  by rewrite divfK // ['T_ _ * _]mulrC.
rewrite /CPoly size_ncons size_map.
rewrite big_split_ord /= big1 ?add0r => [|i _]; last first.
  by rewrite nth_ncons ltn_ord scale0r.
apply: eq_bigr => i _.
rewrite nth_ncons ifN; first by rewrite addnC addnK (nth_map 0).
by rewrite -ltnNge ltnS leq_addr.
Qed.

Definition mul_Cpoly (R : fieldType) (l1 l2 : seq R) :=
   mul_rec_Cpoly 0 l1 l2.

Lemma mul_Cpoly_correct (R1 : fieldType) (l1 l2 : seq R1) :
  (2%:R != 0 :> R1)%R ->
  CPoly (mul_Cpoly l1 l2) =  
  CPoly l1 * CPoly l2.
Proof. by move=> TNZ; rewrite [LHS]mul_rec_Cpoly_correct. Qed.

Fixpoint split_Cpoly n (l : seq R) :=
  if n is n1.+1 then 
    if l is a :: l1 then let: (l2,l3) := split_Cpoly n1 l1 in (a :: l2, 0 :: l3)
    else (nseq n 0, [::])
  else ([::], l).

Lemma split_Cpoly_size1 n l : size (split_Cpoly n l).1 = n.
Proof.
elim: n l => //= n IH [|a l] /=; first by rewrite size_nseq.
by case: split_Cpoly (IH l) => /= l1 _ ->.
Qed.

Lemma horner_split_Cpoly n (p : seq R) :
   CPoly p = CPoly (split_Cpoly n p).1 + CPoly (split_Cpoly n p).2.
Proof.
suff /(_ 0%nat) : forall k,
  \sum_(i < size p) p`_i *: 'T_(k + i) =
   \sum_(i < size (split_Cpoly n p).1) (split_Cpoly n p).1`_i *: 'T_(k + i) +
  \sum_(i < size (split_Cpoly n p).2) (split_Cpoly n p).2`_i *: 'T_(k + i).
  by apply.
elim: n p => [p k |n IH [|a p] k] /=; first by rewrite big_ord0 add0r.
  rewrite !big_ord0 big1 ?add0r // => i _.
  by rewrite (@nth_nseq _ _ n.+1) if_same scale0r.
rewrite big_ord_recl /= addn0.
have := IH p k.+1; case: split_Cpoly => p1 p2 /= {IH}IH.
rewrite !big_ord_recl /= scale0r add0r addn0 -addrA.
congr (_ + _).
apply: etrans.
  by apply: eq_bigr => i _; rewrite /bump /= -addSnnS.
by rewrite IH; congr (_ + _);  apply: eq_bigr => i _; rewrite /bump /= -addSnnS.
Qed.


End P2CP.

Lemma horner_CPolyab (R : fieldType) (p : seq R) (a b x : R) :
   (CPolyab a b p).[x] = (CPoly p).[(Tab a b).[x]].
Proof.
rewrite [LHS]horner_sum [RHS]horner_sum.
apply: eq_bigr => i _; rewrite !hornerE horner_pTab.
congr (_ * _.[_]).
rewrite [_ * x]mulrC mulrA -mulrDl opprD addrA.
by rewrite mulr2n mulrDr mulr1.
Qed.



(* T_0(x)	=	1 *)
(* T_1(x)	=	x	 *)
(* T_2(x)	=	2 x^2 - 1 *)
(* T_3(x)	=	4 x^3 - 3 x *)
(* T_4(x)	=	8 x^4 - 8 x^2 + 1	*)
(* T_5(x)	=	16 x^5 - 20 x^3 + 5 x *)
(* T_6(x)	=	32 x^6 - 48 x^4 + 18 x^2 - 1 *)

Definition t0 := [:: ratz (Posz 1)].
Definition t1 := [:: 0; ratz (Posz 1)].
Definition t2 := [:: ratz (-(Posz 1)); 0; ratz (Posz 2)].
Definition t3 := [:: 0; ratz (- (Posz 3)); 0; ratz (Posz 4)].
Definition t4 := [:: ratz (Posz 1); 0; ratz (-(Posz 8)); 0; ratz (Posz 8)].
Definition t5 := [:: 0; ratz (Posz 5); 0; ratz (- (Posz 20)); 0; ratz (Posz 16)].
Definition t6 := [:: ratz (- (Posz 1)); 0; ratz (Posz 18); 0; ratz (- (Posz 48)); 0; ratz (Posz 32)].

Compute P2CP t0.
Compute P2CP t1.
Compute P2CP t2.
Compute P2CP t3.
Compute P2CP t4.
Compute P2CP t5.
Compute P2CP t6.
