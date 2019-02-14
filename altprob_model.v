Require Import FunctionalExtensionality Coq.Program.Tactics ProofIrrelevance.
Require Classical.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple.
From mathcomp Require Import finfun finset bigop.
From mathcomp Require Import boolp classical_sets.
Require Import Reals Lra.
From infotheo Require Import ssrR Reals_ext Rbigop proba convex.
Require Import monad monad_model.

Reserved Notation "mx <.| p |.> my" (format "mx  <.| p |.>  my", at level 50).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip *)

Local Open Scope convex_scope.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Local Open Scope reals_ext_scope.

(* NB: generalization in progress *)
Section convex_set_of_distributions_prop.
Variable A : finType.

Lemma convex_hull (X : set (dist A)) : is_convex_set (hull X).
Proof.
apply/asboolP => x y p; rewrite 2!in_setE.
move=> -[n [g [d [gX ->{x}]]]].
move=> -[m [h [e [hX ->{y}]]]].
rewrite in_setE.
exists (n + m).
exists [ffun i => match fintype.split i with inl a => g a | inr a => h a end].
exists (AddDist.d d e p).
split.
  move=> a -[i _]; rewrite ffunE.
  case: splitP => j _ <-; by [apply gX; exists j | apply hX; exists j].
by rewrite !convn_convdist ConvDist_Add.
Qed.

Lemma hullI (X : set (dist A)) : hull (hull X) = hull X.
Proof.
rewrite predeqE => d; split.
- move=> -[n [g [e [gX ->{d}]]]].
  move: (convex_hull X); rewrite is_convex_setP /is_convex_set_n => /asboolP/(_ _ g e gX).
  by rewrite in_setE.
- by rewrite -in_setE => /hull_mem; rewrite in_setE.
Qed.
End convex_set_of_distributions_prop.

Section CSet_prop.
Import ScaledConvex.
Variable A : finType.

Lemma hull_setU (a : dist A) (x y : {convex_set (dist A)}) :
  x !=set0 -> y !=set0 -> a \in hull (x `|` y) ->
  exists a1, a1 \in x /\ exists a2, a2 \in y /\ exists p : prob, a = a1 <| p |> a2.
Proof.
move=> x0 y0.
rewrite in_setE.
case=> n -[g [e [gX Ha]]].
case: x0 => dx dx_x.
case: y0 => dy dy_y.
move/(f_equal (@S1 _)): Ha; rewrite S1_convn.
rewrite (bigID (fun i => g i \in x)).
set sa1 := \big[_/_]_(i < n | _) _.
set sa2 := \big[_/_]_(i < n | _) _.
move=> Hsa.
have Hpty: forall Ha2: (0 < (weight (dist_convType A)) sa2)%R, point Ha2 \in y.
  move=> Ha2; apply scaled_set_extract.
  rewrite /sa2; apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi. apply scalept_scaled_set.
    rewrite in_setE /= -[_ \in _]orFb -(negbTE Hi) -in_setU in_setE.
    by apply /gX /imageP.
case/boolP: (weight _ sa1 >b 0)%R => /ltRP Ha1; last first.
  exists dx; split.
    by rewrite in_setE.
  have : weight _ (S1 a) = 1%R by [].
  rewrite Hsa weight_addpt (eqR_le_Ngt _ Ha1) ?add0R; last by apply pos_f_ge0.
  move=> Hw2.
  move: Rlt_0_1; rewrite -Hw2 => Hw2'.
  exists (point Hw2'); split => //.
  exists `Pr 0.
  rewrite conv0; apply S1_inj.
  rewrite Hsa (@weight0_Zero _ sa1) /=; last first.
    rewrite -(eqR_le_Ngt _ Ha1) //; by apply pos_f_ge0.
  rewrite -[LHS](Scaled_point Hw2'); congr Scaled.
  by apply val_inj; rewrite /= -Hw2.
exists (point Ha1); split.
  apply scaled_set_extract.
  rewrite /sa1.
  apply big_ind.
  + by rewrite in_setE.
  + apply addpt_scaled_set.
  + move=> i Hi. apply scalept_scaled_set.
    by rewrite in_setE.
case/boolP: (weight _ sa2 >b 0)%R => /ltRP Ha2; last first.
  exists dy; split.
    by rewrite in_setE.
  exists `Pr 1.
  rewrite conv1; apply S1_inj.
  rewrite Hsa (@weight0_Zero _ sa2) /=; last first.
    rewrite -(eqR_le_Ngt _ Ha2) //; by apply pos_f_ge0.
  rewrite addpt0 -[LHS](Scaled_point Ha1); congr Scaled; apply val_inj => /=.
  have <- : weight _ (S1 a) = 1%R by [].
  rewrite Hsa weight_addpt (eqR_le_Ngt _ Ha2) ?addR0 //; by apply pos_f_ge0.
exists (point Ha2); split => //.
exists (Rpos_prob (mkRpos Ha1) (mkRpos Ha2)).
apply S1_inj.
rewrite -(Scaled_point Ha1) -(Scaled_point Ha2) /= in Hsa.
rewrite Hsa; congr Scaled; apply val_inj => /=.
have H1 : weight _ (S1 a) = 1%R by [].
by rewrite -H1 Hsa.
Qed.

End CSet_prop.

Section probabilistic_choice_nondeterministic_choice.
Local Open Scope proba_scope.
Local Open Scope classical_set_scope.
Variable A : finType.

Definition pchoice' (p : prob) (X Y : {convex_set (dist A)}) : set (dist A) :=
  [set d | exists x, x \in X /\ exists y, y \in Y /\ d = x <| p |> y].

Lemma pchoice'_self (p : prob) (X : {convex_set (dist A)}) :
  [set d | exists x, x \in X /\ d = x <| p |> x] `<=` pchoice' p X X.
Proof.
move=> d [x [xX ->{d}]]; rewrite /pchoice'.
exists x; split => //; by exists x; split.
Qed.

Lemma Hpchoice (p : prob) (X Y : {convex_set (dist A)}) : is_convex_set (pchoice' p X Y).
Proof.
apply/asboolP => x y q /=; rewrite in_setE => -[d [dX [d' [d'Y ->]]]].
rewrite in_setE => -[e [eX [e' [e'Y ->]]]]; rewrite in_setE commute.
exists (Conv2Dist.d d e q); split; first exact: (asboolW (CSet.H X)).
exists (Conv2Dist.d d' e' q); split => //; exact: (asboolW (CSet.H Y)).
Qed.

Definition pchoice (p : prob) (X Y : {convex_set (dist A)}) : {convex_set (dist A)} :=
  CSet.mk (@Hpchoice p X Y).

Local Notation "mx <.| p |.> my" := (@pchoice p mx my).

Lemma pchoice_cset0 (x : {convex_set (dist A)}) p : x <.|p|.> cset0 _ = cset0 _.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 [d1x [d2 []]]]; by rewrite in_setE.
Qed.

Lemma cset0_pchoice x p : cset0 _ <.|p|.> x = cset0 _.
Proof.
apply val_inj => /=; rewrite /pchoice'.
rewrite predeqE => d; split => // -[d1 []]; by rewrite in_setE.
Qed.

Lemma pchoice_eq0 p a b :
  a <.| p |.> b == cset0 _ -> (a == cset0 _) || (b == cset0 _).
Proof.
case/boolP : (a == cset0 _) => //= /cset0PN[da Hda].
case/boolP : (b == cset0 _) => //= /cset0PN[db Hdb].
case/eqP; rewrite /pchoice' => H.
suff : set0 (da <| p |> db) by [].
rewrite -H; exists da; split; first by rewrite in_setE.
exists db; split => //; by rewrite in_setE.
Qed.

Lemma pchoice0 (a b : {convex_set (dist A)}) : a !=set0 -> a <.| `Pr 0 |.> b = b.
Proof.
move=> a0; apply/val_inj=> /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv0.
- move=> bd; case: a0 => d' ad'; exists d'; split; first by rewrite in_setE.
  exists d; split; by [rewrite in_setE | rewrite conv0].
Qed.

Lemma pchoice1 (a b : {convex_set (dist A)}) : b !=set0 -> a <.| `Pr 1 |.> b = a.
Proof.
move=> b0; apply/val_inj => /=; rewrite /pchoice' predeqE => d; split.
- move=> [x [xa]] [y [yb ->{d}]]; by rewrite -in_setE conv1.
- move=> ad; case: b0 => d' bd'; exists d; split; first by rewrite in_setE.
  exists d'; split; by [rewrite in_setE | rewrite conv1].
Qed.

Lemma pchoiceC p (x y : {convex_set (dist A)}) : x <.| p |.> y = y <.| `Pr p.~ |.> x.
Proof.
apply/val_inj/classical_sets.eqEsubset => /=; rewrite /pchoice'.
- move=> d [a [aX [b [bY ->{d}]]]].
  by exists b; split => //; exists a; split => //; rewrite convC.
- move=> d [a [aY [b [bX ->{d}]]]].
  exists b; split => //; exists a; split => //; rewrite convC.
  by apply/dist_ext => a0; rewrite !Conv2Dist.dE /= !onemK.
Qed.

Lemma pchoicemm p : idempotent (pchoice p).
Proof.
move=> Y; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[x [Hx [y [Hy ->{d}]]]].
  by rewrite -in_setE (asboolW (CSet.H Y)).
- apply: classical_sets.subset_trans; last exact: pchoice'_self.
  set Y' := (X in _ `<=` X). suff : Y = Y' :> set (dist A) by move=> <-. rewrite {}/Y'.
  transitivity [set y | y \in Y].
    rewrite predeqE => d; split; by rewrite in_setE.
  rewrite predeqE => d; split.
  - move=> dY; exists d; split => //; by rewrite convmm.
  - case=> d' [d'Y ->{d}]; by rewrite (asboolW (CSet.H Y)).
Qed.

Lemma nepchoiceA (p q r s : prob) (x y z : {convex_set (dist A)}) :
  (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
  x <.| p |.> (y <.| q |.> z) = (x <.| r |.> y) <.| s |.> z.
Proof.
move=> [H1 H2]; apply/val_inj/classical_sets.eqEsubset => /=.
- move=> d; rewrite /pchoice' => -[a [xa [b []]]].
  rewrite in_setE /= {1}/pchoice' => -[b1 [b1y [b2 [b2z ->{b} ->{d}]]]].
  exists (a <| r |> b1); split.
    rewrite in_setE /= /pchoice'; exists a; split => //; by exists b1.
  by exists b2; split => //; rewrite (@convA0 _ _ _ r s).
- move=> d; rewrite /pchoice' => -[a []].
  rewrite in_setE /= {1}/pchoice' => -[a1 [a1x [a2 [a2y ->{a}]]]] => -[b] [bz ->{d}].
  exists a1; split => //.
  exists (a2 <| q |> b); split.
    rewrite in_setE /= /pchoice'; exists a2; split => //; by exists b.
  by rewrite (@convA0 _ _ _ r s).
Qed.

Definition nchoice' (X Y : set (dist A)) : set (dist A) := hull (X `|` Y).

Lemma Hnchoice (X Y : {convex_set (dist A)}) : is_convex_set (nchoice' X Y).
Proof.
apply/asboolP => x y p; rewrite /nchoice' => Hx Hy.
have := convex_hull (X `|` Y).
by move/asboolP => /(_ x y p Hx Hy).
Qed.

Definition nchoice (X Y : {convex_set (dist A)}) : {convex_set (dist A)} :=
  CSet.mk (@Hnchoice X Y).

Lemma nchoice0X (X : {convex_set (dist A)}) : nchoice (cset0 _) X = X.
Proof. by apply val_inj => /=; rewrite /nchoice' set0U hull_cset. Qed.

Lemma nchoiceX0 (X : {convex_set (dist A)}) : nchoice X (cset0 _) = X.
Proof. by apply val_inj => /=; rewrite /nchoice' setU0 hull_cset. Qed.

Lemma nchoice_eq0 a b :
  nchoice a b == cset0 _ -> (a == cset0 _) || (b == cset0 _).
Proof.
case/boolP : (a == cset0 _) => // /cset0PN a0.
case/boolP : (b == cset0 _) => //= /cset0PN b0 H.
suff : hull (a `|` b) == set0.
  move/eqP : H => /(congr1 val) /= /eqP.
  rewrite /nchoice' hull_eq0 => /eqP; rewrite setU_eq0 => -[Ha _] _.
  by case: a0 => a0; rewrite Ha.
by move/eqP : H => /(congr1 val) /=; rewrite /nchoice /nchoice' => ->.
Qed.

Lemma nchoiceC : commutative nchoice.
Proof. move=> x y; apply/val_inj => /=; by rewrite /nchoice' setUC. Qed.

Lemma nchoicemm : idempotent nchoice.
Proof.
move=> d; apply/val_inj => /=; rewrite /nchoice' setUid; exact: hull_cset.
Qed.

Lemma nchoiceA : associative nchoice.
Proof.
move=> x y z; apply/val_inj => /=; rewrite /nchoice'; apply eqEsubset.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  case/boolP : (x == cset0 _) => [|/cset0PN H1].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite {}x0 2!set0U hullI /= hull_cset.
  set yz := CSet.mk (convex_hull (y `|` z)).
  case/boolP : (yz == cset0 _) => [|/cset0PN H2].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[y0 z0].
    by move: Ha; rewrite y0 z0 2!setU0 hullI hull0 setU0.
  case: (hull_setU H1 H2 Ha) => d1 [d1x [d [dyz [p Hp]]]]; rewrite Hp.
  case/boolP : (y == cset0 _) => [|/cset0PN H3].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case/boolP : (z == cset0 _) => [|/cset0PN H4].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hullI hull_cset -Hp.
  case: (hull_setU H3 H4 dyz) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := [s_of p, q].
  set r := [r_of p, q].
  rewrite (@convA0 _ _ _ r s); last 2 first.
    exact: p_is_rs.
    by rewrite s_of_pqE onemK.
  apply mem_hull_setU => //; exact/mem_hull_setU.
- move=> a; rewrite -in_setE => Ha; rewrite -in_setE.
  set xy := CSet.mk (convex_hull (x `|` y)).
  case/boolP : (xy == cset0 _) => [|/cset0PN H1].
    rewrite cset0P hull_eq0 => /eqP; rewrite setU_eq0 => -[x0 y0].
    by move: Ha; rewrite x0 y0 3!set0U hull0 set0U hullI.
  case/boolP : (z == cset0 _) => [|/cset0PN H2].
    rewrite cset0P => /eqP z0.
    by move: Ha; rewrite z0 2!setU0 hull_cset hullI.
  case: (hull_setU H1 H2 Ha) => d1 [d1xy [d [dz [p Hp]]]]; rewrite Hp.
  case/boolP : (x == cset0 _) => [|/cset0PN H3].
    rewrite cset0P => /eqP x0.
    by move: Ha; rewrite x0 2!set0U hullI hull_cset -Hp.
  case/boolP : (y == cset0 _) => [|/cset0PN H4].
    rewrite cset0P => /eqP y0.
    by move: Ha; rewrite y0 set0U setU0 2!hull_cset -Hp.
  case: (hull_setU H3 H4 d1xy) => d2 [d2y [d3 [d3z [q Hq]]]]; rewrite Hq.
  set s := [s_of (`Pr p.~), (`Pr q.~)].
  set r := [r_of (`Pr p.~), (`Pr q.~)].
  rewrite -(@convA0 _ (`Pr s.~) (`Pr r.~)); last 2 first.
    transitivity (s.~) => //.
    by rewrite (s_of_pqE (`Pr p.~) (`Pr q.~)) !onemK mulRC.
    by rewrite 2!onemK (p_is_rs (`Pr p.~) (`Pr q.~)) mulRC.
  apply mem_hull_setU => //; exact/mem_hull_setU.
Qed.

Lemma nchoiceDr p :
  right_distributive (fun x y => x <.| p |.> y) (fun x y => nchoice x y).
Proof.
move=> x y z.
case/boolP : (y == cset0 _) => [/eqP|/cset0PN] y0.
  by rewrite {}y0 nchoice0X pchoice_cset0 nchoice0X.
case/boolP : (z == cset0 _) => [/eqP|/cset0PN] z0.
  by rewrite {}z0 nchoiceX0 pchoice_cset0 nchoiceX0.
case/boolP : (x == cset0 _) => [/eqP|/cset0PN] x0.
  by rewrite {}x0 !cset0_pchoice nchoice0X.
have /cset0PN xy0 : (pchoice p x y != cset0 _).
  apply/negP => /pchoice_eq0 /orP[]; exact/negP/cset0PN.
have /cset0PN xz0 : (pchoice p x z != cset0 _).
  apply/negP => /pchoice_eq0 /orP[]; exact/negP/cset0PN.
apply/val_inj => /=; apply eqEsubset.
- move=> a [b [bx [c [xyz ->{a}]]]].
  case: (hull_setU y0 z0 xyz) => c1 [c1y [c2 [c2z [q cq]]]].
  rewrite cq distribute -in_setE; apply mem_hull_setU.
  rewrite in_setE; exists b; split => //.
  exists c1; split => //.
  rewrite in_setE; exists b; split => //.
  by exists c2; split => //.
- move=> a.
  rewrite /nchoice' -in_setE.
  case/(hull_setU xy0 xz0) => b [bxy [c [cxz [q ->{a}]]]].
  rewrite /nchoice /pchoice' /nchoice' /=.
  move: bxy; rewrite in_setE /pchoice /= /pchoice' => -[a' [xa' [b' [b'y] Hb']]].
  move: cxz; rewrite in_setE /pchoice /= /pchoice' => -[a'' [xa'' [b'' [b''y] Hb'']]].
  exists (a' <| q |> a''); split.
    rewrite in_setE.
    rewrite -(hull_cset x).
    rewrite -in_setE.
    rewrite -(setUid x).
    by apply mem_hull_setU.
  exists (b' <| q |> b''); split.
    by apply mem_hull_setU.
  by rewrite Hb' Hb'' commute.
Qed.

End probabilistic_choice_nondeterministic_choice.

(* non-empty convex sets *)
Module NECSet.
Section def.
Local Open Scope classical_set_scope.
Local Open Scope proba_scope.
Variable A : convType.
Record t : Type := mk {
  car : {convex_set A} ;
  H : car != cset0 _ }.
End def.
End NECSet.
Notation necset := NECSet.t.
Coercion NECSet.car : necset >-> convex_set_of.

Section necset_canonical.
Variable (A : convType).

Canonical necset_subType := [subType for @NECSet.car A].
Canonical necset_predType :=
  Eval hnf in mkPredType (fun t : necset A => (fun x => x \in NECSet.car t)).
Definition necset_eqMixin := Eval hnf in [eqMixin of (@necset A) by <:].
Canonical necset_eqType := Eval hnf in EqType (@necset A) necset_eqMixin.

End necset_canonical.

(* non-empty convex sets of distributions *)
Notation "{ 'csdist+' T }" := (necset (dist_convType T)) (format "{ 'csdist+'  T }") : convex_scope.

Section necset_prop.

Lemma pchoice_ne A p (m1 m2 : {csdist+ A}) : pchoice p m1 m2 != cset0 _.
Proof.
move: m1 m2 => -[m1 H1] -[m2 H2] /=.
by apply/negP => /pchoice_eq0; rewrite (negbTE H1) (negbTE H2).
Qed.

Lemma nchoice_ne A (m1 m2 : {csdist+ A}) : nchoice m1 m2 != cset0 _.
Proof.
move: m1 m2 => -[m1 H1] -[m2 H2] /=.
by apply/negP => /nchoice_eq0; rewrite (negbTE H1) (negbTE H2).
Qed.

End necset_prop.

Require Import relmonad.

Module relFunctorLaws.
Section def.
Variable (M : convType -> convType) (f : forall (A B : convType),
  ({affine A -> B}) -> {affine M A -> M B}).
Definition id := forall A, f (@affine_function_id A) = (@affine_function_id (M A)) :> {affine M A -> M A}.
Definition comp := forall (A B C : convType) (h : {affine A -> B}) (g : {affine B -> C}),
  f (affine_function_comp h g) = affine_function_comp (f h) (f g) :> {affine M A -> M C}.
End def.
End relFunctorLaws.

Module relFunctor.
Record class_of (m : convType -> convType) : Type := Class {
  f : forall (A B : convType), ({affine A -> B}) -> {affine m A -> m B} ;
  _ : relFunctorLaws.id f ;
  _ : relFunctorLaws.comp f
}.
Structure t : Type := Pack { m : convType -> convType ; class : class_of m }.
Module Exports.
Definition relFun (F : t) : forall (A B : convType), ({affine A -> B}) -> {affine m F A -> m F B} :=
  let: Pack _ (Class f _ _) := F return forall A B : convType, ({affine A -> B}) -> {affine m F A -> m F B} in f.
Arguments relFun _ [A] [B].
Notation relfunctor := t.
Coercion m : relfunctor >-> Funclass.
End Exports.
End relFunctor.
Export relFunctor.Exports.
Notation "F # f" := (relFun F f) (at level 11).

(* wip *)
Module Functor.

Definition F (A B : finType) (f : {affine {dist A} -> {dist B}}) : {csdist+ A} -> {csdist+ B}.
case=> car car0.
apply: (@NECSet.mk _ (@CSet.mk _ (f @` car) _)).
  rewrite /is_convex_set.
  apply/asboolP => x y p /imsetP[a0 Ha0 ->{x}] /imsetP[a1 Ha1 ->{y}].
  apply/imsetP; exists (a0 <|p|> a1).
  exact/mem_convex_set.
  by rewrite (affine_functionP' f).
move=> H.
case/cset0PN : car0 => a carx.
apply/cset0PN; exists (f a) => /=; by exists a.
Defined.

(* the functor goes through as follows: *)
(* NB: see also Functorslaws.id *)
Lemma map_laws_id A (Z : {csdist+ A}) :
  (F (affine_function_id (dist_convType A))) Z = ssrfun.id Z.
Proof.
apply/val_inj => /=.
case: Z => Z HZ.
apply/val_inj => /=.
rewrite predeqE => x; split.
  by case => y Zy <-.
move=> Zx; by exists x.
Qed.

(* NB: see FunctorLaws.comp *)
Lemma map_laws_comp (A B C : finType) (f : {affine {dist B} -> {dist C}})
  (g : {affine {dist A} -> {dist B}}) (Z : {csdist+ A})
  : (F (affine_function_comp g f)) Z = (F f \o F g) Z.
Proof.
apply/val_inj => /=.
case: Z => Z HZ.
apply/val_inj => /=.
rewrite predeqE => c; split.
  case => a Za <-.
  exists (g a) => //; by exists a.
case => b -[a Za <-{b} <-{c}].
by exists a.
Qed.

Let nepchoice : prob -> forall A, {csdist+ A} -> {csdist+ A} -> {csdist+ A} :=
  fun p A m1 m2 => NECSet.mk (pchoice_ne p m1 m2).

Local Notation "mx <.| p |.> my" := (@nepchoice p _ mx my).

Lemma F_preserves_pchoice (A B : finType) (f : {affine {dist A} -> {dist B}}) (Z Z' : {csdist+ A}) (p : prob) :
  (F f) (Z <.| p |.> Z') = (F f) Z <.| p |.> (F f) Z'.
Proof.
do 2 apply val_inj => /=.
rewrite predeqE => b; split.
- case=> a.
  case=> /= a0 [Za0 [a1 [Z'a1 ->{a}]]] <-{b}.
  rewrite /pchoice'.
  exists (f a0); split.
    rewrite in_setE /= /F /=.
    case: Z Za0 => /= Z HZ a0Z.
    apply/imageP; by rewrite -in_setE.
  exists (f a1); split; last by rewrite (affine_functionP' f).
  rewrite in_setE /= /F /=.
  case: Z' Z'a1 => /= Z' HZ' a1Z'.
  apply/imageP; by rewrite -in_setE.
- case => b0 [].
  rewrite in_setE {1}/F /=.
  case: Z => Z HZ /=.
  case=> a0 Za0 <-{b0}.
  case=> b1 [].
  rewrite in_setE {1}/F /=.
  case: Z' => Z' HZ' /=.
  case=> a1 Z'a1 <-{b1} ->{b}.
  exists (a0 <|p|> a1); last by rewrite (affine_functionP' f).
  rewrite /pchoice'.
  exists a0; split; first by rewrite in_setE.
  exists a1; split => //; by rewrite in_setE.
Qed.

Lemma image_preserves_convex_hull (A B : finType) (f : {affine {dist A} -> {dist B}})
  (Z : set {dist A}) : f @` hull Z = hull (f @` Z).
Proof.
rewrite predeqE => b; split.
  case=> a [n [g [e [Hg]]]] ->{a} <-{b}.
  exists n, (f \o g), e; split.
    move=> b /= [i _] <-{b} /=.
    by exists (g i) => //; apply Hg; exists i.
  by rewrite affine_function_Sum.
case=> n [g [e [Hg]]] ->{b}.
suff [h Hh] : exists h : 'I_n -> dist_convType A, forall i, h i \in Z /\ f (h i) = g i.
  exists (\Sum_e h).
    exists n; exists h; exists e; split => //.
    move=> a [i _] <-.
    move: (Hh i) => [].
    by rewrite in_setE.
  rewrite affine_function_Sum; apply eq_convn => // i /=.
  by case: (Hh i).
apply (@fin_all_exists _ _ (fun i hi => hi \in Z /\ f hi = g i)) => i.
case: (Hg (g i)); first by exists i.
move=> a // HZa Hfa.
exists a; split; by rewrite // in_setE.
Qed.

Let nenchoice : forall A, {csdist+ A} -> {csdist+ A} -> {csdist+ A} :=
  fun A m1 m2 => NECSet.mk (nchoice_ne m1 m2).

Lemma F_preserves_nchoice (A B : finType) (f : {affine {dist A} -> {dist B}}) (Z Z' : {csdist+ A}) :
  (F f) (nenchoice Z Z') = nenchoice (F f Z) (F f Z').
Proof.
do 2 apply val_inj => /=.
rewrite /nchoice' image_preserves_convex_hull; congr hull.
rewrite predeqE => /= b; split.
  case=> a [] Za <-{b}.
    move: Z Z' Za => [Z Z0] [Z' Z'0] /= Za.
    left; by exists a.
  move: Z Z' Za => [Z Z0] [Z' Z'0] /= Za.
  right; by exists a.
move: Z Z' => [Z Z0] [Z' Z'0] /= [[a Za]|[a Z'a]] <-{b}.
exists a => //; by left.
exists a => //; by right.
Qed.


Definition eta (A : finType) (d : dist A) : {csdist+ A} := NECSet.mk (cset1_neq0 d).

Lemma eta_preserves_pchoice (A : finType) (P Q : dist A) (p : prob) :
  eta (P <| p |> Q) = eta P <.| p |.> eta Q.
Proof.
do 2 apply val_inj => /=.
rewrite predeqE => x; rewrite /set1; split.
  move=> ->{x}.
  rewrite /pchoice'.
  exists P; split; first by rewrite in_setE.
  exists Q; split => //; by rewrite in_setE.
case => P' []; rewrite in_setE /= {1}/set1 => ->{P'}.
by case => Q' []; rewrite in_setE /= {1}/set1 => ->{Q'}.
Qed.

(* wip *)
Lemma naturality (A B : finType) (f : {affine {dist A} -> {dist B}}) (x : dist A) :
  F f (eta x) = eta (f x).
Proof.
do 2 apply/val_inj => /=.
rewrite predeqE => b; split.
by case=> a; rewrite /set1 => ->{a}.
by rewrite /set1 => ->{b}; exists x.
Qed.

End Functor.

Module ModelAltProb.
Section modelaltprob.

Local Obligation Tactic := idtac.

Let F := (fun A : finType => necset (dist_convType A)).

Set Bullet Behavior "Strict Subproofs".

Program Definition RET (A : finType) (a : A) : F A :=
@NECSet.mk _ (@CSet.mk _ (set1 (Dist1.d a)) _) _.

Next Obligation.
intros A a.
unfold is_convex_set.
apply asboolT.
intros x y p Hxin Hyin.
rewrite unfold_in.
rewrite unfold_in in Hxin.
rewrite unfold_in in Hyin.
cbn in *.
unfold set1 in *.
apply asboolW in Hxin.
apply asboolW in Hyin.
subst x y.
apply asboolT, convmm.
Qed.

Next Obligation.
intros A a.
cbn.
rewrite set0P.
exists (Dist1.d a).
reflexivity.
Qed.

Definition set_join {A : Type} (m : set (set A)) : set A :=
fun a => exists s, s \in m /\ a \in s.

Definition distribute (A B : Type) (f : A -> set B) : set (A -> B) :=
fun g => forall a, g a \in f a.

Definition bind
  (A B : finType) (m : set (dist A)) (f : A -> set (dist B)) : set (dist B) :=
hull (set_join ((fun d : dist A => DistBind.d d @` distribute f) @` m)).

Program Definition BIND (A B : finType) (m : F A) (f : A -> F B) : F B :=
@NECSet.mk _ (@CSet.mk _ (bind (NECSet.car m) (fun a => NECSet.car (f a))) _) _.

Next Obligation.
intros A B m f.
apply convex_hull.
Qed.

Next Obligation.
intros A B m f.
cbn.
unfold bind.
pose (H := hull_eq0).
cbn in H.
rewrite H.
clear H.
unfold gen_eq.
cbn.
apply (introT (asboolPn _)).
rewrite <- (@subset0 (dist B)).
intro Hincl.
apply subset_empty in Hincl; [ destruct Hincl as [? []] | ].
clear Hincl.
pose (H := NECSet.H m).
apply (cset0PN _) in H.
destruct H as [d Hin].
pose (H := fun a => NECSet.H (f a)).
assert (H': forall a, NECSet.car (f a) !=set0).
{
  intro a.
  apply cset0PN, H.
}
clear H.
destruct (@IndefiniteDescription.functional_choice _ _ _ H') as [g Hg].
eexists.
eexists.
split; cbn; apply asboolT.
- exists d; [ | reflexivity ].
  exact Hin.
- exists g; [ | reflexivity ].
  intro a.
  apply asboolT, Hg.
Qed.

Lemma BINDretf : relBindLaws.left_neutral BIND RET.
Proof.
intros A B a f.
apply val_inj => /=.
apply val_inj => /=.
extensionality d.
rewrite propeqE.
split.
- intros (n & g & d' & Hincl & Heq).
  subst d.
  admit.
- intro Hin.
  apply asboolW, hull_mem, asboolT.
  exists (NECSet.car (f a)).
  split; [ | apply asboolT, Hin ].
  clear Hin.
  apply asboolT.
  exists (Dist1.d a); [ reflexivity | ].
  extensionality d'.
  rewrite propeqE.
  split.
  + intro Hin.
    apply asboolT, (elimT (imsetP _ _ _)) in Hin.
    destruct Hin as (g, Hin, Heq).
    subst d'.
    rewrite DistBind1f.
    apply asboolW in Hin.
    apply asboolW, Hin.
  + intro Hin.
    apply asboolW, (introT (imsetP _ _ _)).
    eexists (fun a => _); [ | rewrite DistBind1f; reflexivity ].
    apply asboolT.
    unfold distribute.
Admitted.

(* we assume the existence of appropriate BIND and RET *)
Axiom BINDmret : relBindLaws.right_neutral BIND RET.
Axiom BINDA : relBindLaws.associative BIND.

Program Definition apmonad : relMonad.t := @relMonad.Pack F
  (@relMonad.Class _ (@RET) BIND _ _ _ ).
Next Obligation. exact: BINDretf. Qed.
Next Obligation. exact: BINDmret. Qed.
Next Obligation. exact: BINDA. Qed.

Let nepchoice : prob -> forall A, F A -> F A -> F A :=
  fun p A m1 m2 => NECSet.mk (pchoice_ne p m1 m2).

Local Notation "mx <.| p |.> my" := (@nepchoice p _ mx my).

Let nepchoice0 A (mx my : F A) : mx <.| `Pr 0 |.> my = my.
Proof. apply val_inj => /=; rewrite pchoice0 //; by case: mx => ? /= /cset0PN. Qed.
Let nepchoice1 A (mx my : F A) : mx <.| `Pr 1 |.> my = mx.
Proof. apply val_inj => /=; rewrite pchoice1 //; by case: my => ? /= /cset0PN. Qed.
Let nepchoiceC A p (mx my : F A) : mx <.| p |.> my = my <.| `Pr p.~ |.> mx.
Proof. apply val_inj => /=; by rewrite pchoiceC. Qed.
Let nepchoicemm A p : idempotent (@nepchoice p A).
Proof. move=> x; apply val_inj => /=; exact: pchoicemm. Qed.
Lemma nepchoiceA A (p q r s : prob) (mx my mz : F A) :
  (p = r * s :> R /\ s.~ = p.~ * q.~)%R ->
  mx <.| p |.> (my <.| q |.> mz) = (mx <.| r |.> my) <.| s |.> mz.
Proof. move=> H; apply val_inj => /=; exact: nepchoiceA. Qed.

Axiom nepchoice_bindDl : forall p, relBindLaws.bind_left_distributive BIND (nepchoice p).

Let nenchoice : forall A, F A -> F A -> F A := fun A m1 m2 => NECSet.mk (nchoice_ne m1 m2).

Let nenchoiceA A : associative (@nenchoice A).
Proof. move=> a b c; apply val_inj => /=; by rewrite nchoiceA. Qed.

Axiom nenchoice_bindDl : relBindLaws.bind_left_distributive BIND nenchoice.

Let nenchoicemm A : idempotent (@nenchoice A).
Proof. move=> a; apply val_inj => /=; by rewrite nchoicemm. Qed.
Let nenchoiceC A : commutative (@nenchoice A).
Proof. move=> a b; apply val_inj => /=; by rewrite nchoiceC. Qed.
Let nenchoiceDr A p : right_distributive (fun x y : F A => x <.| p |.> y) (fun x y => nenchoice x y).
Proof. move=> a b c; apply val_inj => /=; by rewrite nchoiceDr. Qed.

Program Let nepprob_mixin : relMonadProb.mixin_of apmonad :=
  @relMonadProb.Mixin apmonad (fun p (A : finType) (m1 m2 : F A) =>
    (@nepchoice p _ m1 m2 )) _ _ _ _ _ _.
Next Obligation. exact: nepchoice0. Qed.
Next Obligation. exact: nepchoice1. Qed.
Next Obligation. exact: nepchoiceC. Qed.
Next Obligation. exact: nepchoicemm. Qed.
Next Obligation. exact: nepchoiceA. Qed.
Next Obligation. exact: nepchoice_bindDl. Qed.

Let nepprob_class : relMonadProb.class_of F := @relMonadProb.Class _ _ nepprob_mixin.

Definition nepprob : relMonadProb.t := relMonadProb.Pack nepprob_class.

Program Definition nepalt : relaltMonad := @relMonadAlt.Pack _
  (@relMonadAlt.Class _ (relMonad.class apmonad)
    (@relMonadAlt.Mixin apmonad nenchoice _ _)).
Next Obligation. exact: nenchoiceA. Qed.
Next Obligation. exact: nenchoice_bindDl. Qed.

Program Definition apaltci := @relMonadAltCI.Pack _
  (@relMonadAltCI.Class _ (relMonadAlt.class nepalt) (@relMonadAltCI.Mixin _ _ _ _)).
Next Obligation. exact: nenchoicemm. Qed.
Next Obligation. exact: nenchoiceC. Qed.

Program Definition altprob := @relMonadAltProb.Pack F
  (@relMonadAltProb.Class _ (relMonadAltCI.class apaltci) (relMonadProb.mixin (relMonadProb.class nepprob)) (@relMonadAltProb.Mixin _ _ _)).
Next Obligation. exact: nenchoiceDr. Qed.

End modelaltprob.
End ModelAltProb.
