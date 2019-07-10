Require Import ssreflect ssrmatching ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat seq path div choice fintype tuple.
From mathcomp Require Import finfun bigop.
From mathcomp Require Import boolp.
Require Import monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* mu2019tr2 *)

Section spark_aggregation.
Local Open Scope mu_scope.

Section definitions.
Variable M : altMonad.

Variables (A B : Type).

Definition deterministic A B (f : A -> M B) := exists g : A -> B, f = Ret \o g.

Variables (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Let Partition A := seq A.
Let RDD A := seq (Partition A).

Definition aggregate : RDD A -> M B :=
  foldl add b (o) (perm \o map (foldl mul b)).

End definitions.
Arguments aggregate {M A B}.

Section aggregate_deterministic.

Section foldl_perm_deterministic.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B) (b : B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : seq A),
  (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.

Lemma lemma32 a :
  foldl op b (o) insert a = Ret \o foldl op b \o (rcons^~ a) :> (_ -> M _).
Proof.
rewrite funeqE; elim/last_ind => [/=|xs y IH].
  by rewrite fcompE insertE fmapE bindretf.
rewrite fcompE.
rewrite insert_rcons.
rewrite naturality_nondeter fmapE bindretf.
rewrite -fmap_comp.
have H : forall w, foldl op b \o rcons^~ w = op^~ w \o foldl op b.
  by move=> w; rewrite funeqE => ws /=; rewrite -cats1 foldl_cat.
rewrite (H y).
rewrite fmap_comp.
rewrite fcompE in IH.
rewrite IH.
rewrite -[in X in _ [~] X]bindretf.
rewrite bindretf.
rewrite -{1}compA.
rewrite fmapE bindretf.
rewrite (H a).
rewrite [in X in _ [~] X]/=.
rewrite opP.
rewrite /= -!cats1 -catA /=.
rewrite foldl_cat /=.
by rewrite altmm.
Qed.

End foldl_perm_deterministic.

Section foldl_perm_deterministic_contd.
Variable M : altCIMonad.
Variables (A B : Type) (op : B -> A -> B).
Local Notation "x (.) y" := (op x y) (at level 11).
Hypothesis opP : forall (x y : A) (w : B), (w (.) x) (.) y = (w (.) y) (.) x.

Lemma lemma31 b : foldl op b (o) perm = Ret \o foldl op b :> (_ -> M _).
Proof.
rewrite funeqE => xs; move: xs b; elim => [/=|x xs IH] b.
  by rewrite fcompE fmapE bindretf.
rewrite fcompE fmap_bind.
have opP' : forall (x y : A) (w : seq A), (foldl op b w (.) x) (.) y = (foldl op b w (.) y) (.) x.
  move=> ? ? ?.
  by rewrite opP.
rewrite_ (lemma32 M opP').
transitivity ((Ret \o foldl op (b (.) x)) xs : M _); last by [].
rewrite -IH.
rewrite [in RHS]fcompE.
rewrite fmapE.
bind_ext => ys.
rewrite /= -cats1 foldl_cat /=.
congr (Ret _ : M _).
elim: ys b opP' => // y ys ih /= b opP'.
rewrite ih //=.
rewrite -/(foldl op b [::]).
by rewrite opP'.
Qed.

End foldl_perm_deterministic_contd.

Section theorem43.
Variable M : altCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).
Hypotheses (addA : associative add) (addC : commutative add).

(* theorem 4.3 *)
Lemma aggregateE :
  aggregate b mul add = Ret \o foldl add b \o map (foldl mul b) :> (_ -> M _).
Proof.
(* NB: mu2017 is using perm_map (lemma 3.1) and (7) but that does not seem useful*)
rewrite -lemma31; last by move=> x ??; rewrite -addA (addC x) addA.
by rewrite /aggregate 2!fcomp_def -compA.
Qed.

Lemma deter_aggregate : deterministic (aggregate b mul add : _ -> M _).
Proof. rewrite /deterministic aggregateE //; eexists; reflexivity. Qed.

End theorem43.

Section homomorphism.
Variables (A B : Type) (add : B -> B -> B) (k : A -> B) (z : B).
Hypotheses (addA : associative add) (add0z : left_id z add).
Definition is_hom (h : seq A -> B) :=
  h nil = z /\ (forall x : A, h [:: x] = k x) /\
  (forall xs ys, h (xs ++ ys) = add (h xs) (h ys)).
End homomorphism.

Section theorem47.
Variable M : altCIMonad.
Variables (A B : Type) (b : B) (mul : B -> A -> B) (add : B -> B -> B).

Lemma perm_is_alt_ret xs : exists m : M (seq A), perm xs = Ret xs [~] m.
Proof.
Admitted.

(* TODO(rei): integrate this into a (new?) monad *)
Hypothesis idempotent_converse :
  forall C m1 m2 x, m1 [~] m2 = Ret x :> M C -> m1 = Ret x /\ m2 = Ret x.
Hypothesis injective_return : forall C x1 x2,
  Ret x1 = Ret x2 :> M C -> x1 = x2.

Lemma lemma45 (xss yss : seq (seq A)) (m : M _):
  aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
  perm xss = Ret yss [~] m ->
  let x := foldl add b (map (foldl mul b) xss) in
  foldl mul b (flatten xss) = x /\
  x = foldr add b (map (foldl mul b) yss).
Proof.
move=> H1 H2 x.
have step1 : (Ret \o foldl mul b \o flatten) xss =
  (Ret \o foldl add b \o map (foldl mul b)) yss [~]
  fmap (foldl add b \o map (foldl mul b)) m.
  rewrite -H1 /aggregate perm_o_map -fcomp_comp.
  by rewrite fcompE H2 alt_fmapDl fmapE /= bindretf.
have step2 : (foldl mul b \o flatten) xss =
             (foldl add b \o map (foldl mul b)) yss.
  apply esym, idempotent_converse in step1.
  case: step1 => step11 step12.
  apply injective_return in step11.
  by rewrite compE -step11.
Abort.

Lemma theorem47 :
 aggregate b mul add = Ret \o foldl mul b \o flatten :> (_ -> M _) ->
 is_hom add (mul b) b (foldl mul b).
Proof.
move=> H.
split; first by [].
split; first by [].
move=> xs ys.
rewrite (_ : xs ++ ys = flatten [:: xs; ys]); last by rewrite /= cats0.
Abort.

End theorem47.

End aggregate_deterministic.

End spark_aggregation.
