Require Import FunctionalExtensionality Reals.
Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq choice fintype tuple finfun.
From mathcomp Require Import finmap set bigop finset.

From infotheo Require Import Reals_ext ssr_ext dist.
Require Import choicemonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* wip:
  This file provides models:
  - for the nondeterministic-state monad TODO
  - for the probability monad
*)

Section PR.
Local Open Scope fset_scope.
Section ImfsetTh.
Variables (key : unit) (K V : choiceType).
Variable (f : K -> V).
Lemma imfset_set1 x : f @` [fset x] = [fset f x].
Proof.
apply/fsetP => y.
by apply/imfsetP/fset1P=> [[x' /fset1P-> //]| ->]; exists x; rewrite ?fset11.
Qed.
End ImfsetTh.
Section BigOps.
(*
Variables (R : Type) (idx : R).
Variables (op : Monoid.law idx) (aop : Monoid.com_law idx).
Variables I J : finType.
Variable A B : {set I}.
Lemma big_in_fset1 (a : I) (F : I -> R) :
  \big[op/idx]_(i in [fset a]) F i = F a.
Proof. by apply: big_pred1 => i; rewrite inE in_fset1. Qed.
*)
End BigOps.
End PR.

Module ModelBacktrackableState.
Local Open Scope fset_scope.

Section monad.
Variable S : finType.
Local Obligation Tactic := try by [].

Program Definition _monad : choicemonad := @choiceMonad.Pack _
(@choiceMonad.Class (fun A : choiceType => [choiceType of {ffun S -> {fset (A * S)}}])
(fun A (a : A) => [ffun s => [fset (a, s)]]) (* ret *)
(fun A B m (f : A -> {ffun S -> {fset (B * S)}}) =>
     [ffun s => \bigcup_(i <- (fun x => f x.1 x.2) @` (m s)) i]) (* bind *)
_ _ _).
Next Obligation.
by move=> A B /= m f; apply/ffunP=> s;
 rewrite 2!ffunE imfset_set1 /= big_seq_fset1.
Qed.
Next Obligation.
move=> A B /=; apply/ffunP=> s.
apply/bigfcupsP.


bigcupP
   forall (T I : finType) (x : T) (P : pred I) (F : I -> {set T}),
   reflect (exists2 i : I, P i & x \in F i)
     (x \in (\bigcup_(i | P i) F i)%SET)
bigcupsP
   forall (T I : finType) (U : pred T) (P : pred I) (F : I -> {set T}),
   reflect (forall i : I, P i -> F i \subset U)
     ((\bigcup_(i | P i) F i)%SET \subset U)



apply/fsetP => /= x; apply/bigcupP; case: ifPn => xBs.
  exists [set x]; by [apply/imsetP; exists x | rewrite inE].
case => /= SA /imsetP[] /= sa saBs ->{SA}; rewrite inE => /eqP Hx.
move: xBs; rewrite Hx; apply/negP; rewrite negbK; by case: sa saBs Hx.
Qed.
Next Obligation.
move=> A B C /= m f g; extensionality s.
apply/setP => /= x; apply/bigcupP/bigcupP; case => /= CS /imsetP[/=].
- move=> bs /bigcupP[/= BS] /imsetP[/= sa] sams ->{BS} bsfsa ->{CS} xgbs.
  exists (\bigcup_(i in [set g x0.1 x0.2 | x0 in f sa.1 sa.2]) i).
    by apply/imsetP => /=; exists sa.
  apply/bigcupP; exists (g bs.1 bs.2) => //; by apply/imsetP => /=; exists bs.
- move=> sa sams ->{CS} /bigcupP[/= CS] /imsetP[/= bs] bsfsa ->{CS} xgbs.
  exists (g bs.1 bs.2) => //; apply/imsetP => /=; exists bs => //.
  apply/bigcupP => /=; exists (f sa.1 sa.2) => //; by apply/imsetP => /=; exists sa.
Qed.
End monad.

Section state.
Variable S : finType.
Local Obligation Tactic := try by [].

Program Definition _state : relstateMonad S :=
(@relMonadState.Pack _ _
  (@relMonadState.Class _ _ (relMonad.class (_monad S)) (@relMonadState.Mixin _ _
(fun s => [set (s, s)]) (* get *)
(fun s _ => [set (tt, s)]) (* put *)
_ _ _ _))).
Next Obligation.
move=> s s'; extensionality s''.
rewrite /Bind /=; apply/setP => /= x; rewrite inE; apply/bigcupP/eqP.
- by case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP _ ->; rewrite inE => /eqP.
- move=> -> /=; exists [set (tt, s')]; last by rewrite inE.
  by apply/imsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
move=> s; extensionality s'.
rewrite /Bind /=; apply/setP => /= x; apply/bigcupP/bigcupP.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE /= => /eqP ->.
  exists [set (s, s)]; last by rewrite inE.
  apply/imsetP => /=; exists (tt, s) => //; by rewrite inE.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE => /eqP ->.
  exists [set (s ,s)]; last by rewrite inE.
  by apply/imsetP => /=; exists (tt, s) => //; rewrite inE.
Qed.
Next Obligation.
extensionality s.
rewrite /Bind /skip /= /Ret; apply/setP => /= x; apply/bigcupP/idP.
- by case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> ->; rewrite inE.
- rewrite inE => /eqP ->; exists [set (tt, s)]; last by rewrite inE.
  apply/imsetP; exists (s, s) => //; by rewrite inE.
Qed.
Next Obligation.
move=> k; extensionality s; rewrite /Bind /=; apply/setP => x; apply/bigcupP/bigcupP.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> -> /bigcupP[/= x2] /imsetP[/= x3].
  rewrite inE => /eqP -> /= -> xkss.
  exists (k s s s) => //; apply/imsetP; exists (s, s) => //; by rewrite inE.
- case => /= x0 /imsetP[/= x1]; rewrite inE => /eqP -> -> /= xksss.
  exists (\bigcup_(i in [set k (s, s).1 x2.1 x2.2 | x2 in [set ((s, s).2, (s, s).2)]]) i).
    apply/imsetP; exists (s, s) => //; by rewrite inE.
  apply/bigcupP; exists (k s s s) => //; apply/imsetP; exists (s, s) => //=; by rewrite inE.
Qed.

End state.

Section fail.
Variable S : finType.
Program Definition _fail : relfailMonad := @relMonadFail.Pack _
  (@relMonadFail.Class _ (relMonad.class (_monad S))
    (@relMonadFail.Mixin _ (fun (A : finType) (_ : S) => set0) _)).
Next Obligation.
move=> A B g; extensionality s; apply/setP => x; rewrite inE /Bind; apply/negbTE.
apply/bigcupP; case => /= x0 /imsetP[/= sa]; by rewrite inE.
Qed.

End fail.

Section alt.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition _alt : relaltMonad := @relMonadAlt.Pack _
  (@relMonadAlt.Class _ (@relMonad.class (_monad S))
    (@relMonadAlt.Mixin (_monad S)
      (fun (A : finType) (a b : S -> {set A * S}) (s : S) => a s :|: b s) _ _)).
Next Obligation. by move=> A a b c; extensionality s; rewrite setUA. Qed.
Next Obligation.
move=> A B /= m1 m2 k; extensionality s; rewrite /Bind /=.
apply/setP => /= bs; rewrite !inE; apply/bigcupP/orP.
- case => /= BS /imsetP[/= sa]; rewrite inE => /orP[sam1s ->{BS} Hbs|sam2s ->{BS} Hbs].
  + left; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
  + right; apply/bigcupP => /=; exists (k sa.1 sa.2) => //; apply/imsetP; by exists sa.
- case => /bigcupP[/= BS /imsetP[/= sa sams ->{BS} bsksa]].
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams.
  by exists (k sa.1 sa.2) => //; apply/imsetP; exists sa => //; rewrite inE sams orbT.
Qed.

End alt.

Section nondet.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetbase : relnondetMonad :=
  @relMonadNondet.Pack _ (@relMonadNondet.Class _ (@relMonadFail.class (_fail S))
    (@relMonadAlt.mixin (_alt S) _) (@relMonadNondet.Mixin _ _ _ _)).
Next Obligation. move=> A /= m; extensionality s; by rewrite set0U. Qed.
Next Obligation. move=> A /= m; extensionality s; by rewrite setU0. Qed.
End nondet.

Section nondetstate.

Variable S : finType.
Local Obligation Tactic := try by [].
Program Definition nondetstate : relnondetStateMonad S :=
  @relMonadNondetState.Pack _ _
    (@relMonadNondetState.Class _ _ (relMonadNondet.class (nondetbase S))
      (relMonadState.mixin (relMonadState.class (_state S))) (@relMonadNondetState.Mixin _ _ _)).
Next Obligation.
move=> A B /= g; rewrite /Bind /=; extensionality s; apply/setP => /= sa.
apply/bigcupP/idP.
- case => /= SA /imsetP[/= bs bsgs ->{SA}]; by rewrite inE.
- by rewrite inE.
Qed.
Next Obligation.
move=> A B /= m k1 k2; extensionality s; rewrite /Bind /=; apply/setP => /= bs.
apply/bigcupP/idP.
- case => /= BS /imsetP[/= sa sams ->{BS}]; rewrite inE => /orP[bsk1|bsk2].
  + rewrite inE; apply/orP; left; apply/bigcupP; exists (k1 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
  + rewrite inE; apply/orP; right; apply/bigcupP; exists (k2 sa.1 sa.2) => //.
    apply/imsetP; by exists sa.
- rewrite inE => /orP[|] /bigcupP[/= BS] /imsetP[/= sa sams ->{BS}] bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk.
  exists (k1 sa.1 sa.2 :|: k2 sa.1 sa.2).
    apply/imsetP; by exists sa.
  by rewrite inE bsk orbT.
Qed.

End nondetstate.

End ModelBacktrackableState.
*)

From infotheo Require Import convex.

Module choiceMonadProbModel.
Local Obligation Tactic := idtac.

Program Definition monad : choiceMonad.t := @choiceMonad.Pack Dist
  (@choiceMonad.Class _ Dist1.d DistBind.d _ _ _ ).
Next Obligation. move=> ? ? ? ?; exact: DistBind1f. Qed.
Next Obligation. move=> ? ?; exact: DistBindp1. Qed.
Next Obligation. move=> ? ? ? ? ?; exact: DistBindA. Qed.

Program Definition prob_mixin : choiceMonadProb.mixin_of monad :=
  @choiceMonadProb.Mixin monad (fun p (A : choiceType) (m1 m2 : Dist A) =>
    (@Conv2Dist.d A m1 m2 p)) _ _ _ _ _ _.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv0. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.conv1. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convC. Qed.
Next Obligation. move=> ? ? ?; exact: Conv2Dist.convmm. Qed.
Next Obligation. move=> ? ? ? ? ? ? ? ? [? ?] /=; exact: Conv2Dist.convA. Qed.
Next Obligation. move=> ? ? ? ? ? ?; exact: Conv2Dist.bind_left_distr. Qed.

Definition prob_class : choiceMonadProb.class_of Dist :=
  @choiceMonadProb.Class _ _ prob_mixin.

Definition prob : choiceMonadProb.t := choiceMonadProb.Pack prob_class.

End choiceMonadProbModel.
