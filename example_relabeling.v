Require Import ZArith.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.
From infotheo Require Import ssrZ.
Require Import monae_lib monad fail_monad state_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

(* see Sect. 9 of gibbons2011icfp *)

Section Tree.
Variable A : Type.

Inductive Tree := Tip (a : A) | Bin of Tree & Tree.

Fixpoint foldt B (f : A -> B) (g : B * B -> B) (t : Tree) : B :=
  match t with
  | Tip a => f a
  | Bin t u => g (foldt f g t, foldt f g u)
  end.

(* TODO: move? *)
Section foldt_universal.
Variables (B : Type) (h : Tree -> B) (f : A -> B) (g : B * B -> B).
Hypothesis H1 : h \o Tip = f.
Hypothesis H2 : h \o uncurry Bin = g \o (fun x => (h x.1, h x.2)).
Lemma foldt_universal : h = foldt f g.
Proof.
rewrite boolp.funeqE; elim => [a|]; first by rewrite -H1.
by move=> t1 IH1 t2 IH2 /=; rewrite -IH1 -IH2 -(uncurryE Bin) -compE H2.
Qed.
End foldt_universal.

Definition size_Tree (t : Tree) := foldt (const 1) uaddn t.

Lemma size_Tree_Bin :
  size_Tree \o uncurry Bin = uaddn \o size_Tree^`2.
Proof. by rewrite boolp.funeqE; case. Qed.

Fixpoint labels (t : Tree) : seq A :=
  match t with
  | Tip a => [:: a]
  | Bin t u => labels t ++ labels u
  end.

End Tree.
Arguments Tip {A}.
Arguments Bin {A}.

Section tree_relabelling.

Variable Symbol : eqType. (* TODO: ideally, we would like a generic type here with a succ function *)
Variable M : failFreshMonad Symbol.
Variable q : pred (seq Symbol * seq Symbol).
Hypothesis promotable_q : promotable (Distinct M) q.

Local Open Scope mprog.

Definition relabel : Tree Symbol -> M (Tree Symbol) :=
  foldt (M # Tip \o const Fresh) (fmap (uncurry Bin) \o mpair).

Let drTip {A} : A -> M _ := (M # wrap) \o const Fresh.
Let drBin {N : failMonad} : (N _ * N _ -> N _) :=
  (fmap ucat) \o bassert q \o mpair.

(* extracting the distinct symbol list *)
Definition dlabels {N : failMonad} : Tree Symbol -> N (seq Symbol) :=
  foldt (Ret \o wrap) drBin.

Lemma dlabelsC t u (m : _ -> _ -> M (seq Symbol * seq Symbol)%type) :
  (do x <- dlabels t; do x0 <- relabel u; m x0 x =
   do x0 <- relabel u; do x <- dlabels t; m x0 x)%Do.
Proof.
elim: t u m => [a u /= m|t1 H1 t2 H2 u m].
  rewrite /dlabels /= bindretf; bind_ext => u'.
  by rewrite bindretf.
rewrite (_ : dlabels _ = drBin (dlabels t1, dlabels t2)) //.
rewrite [in RHS]/drBin [in RHS]/bassert 2!compE ![in RHS]bindA.
transitivity (do x0 <- relabel u;
  (do x <- dlabels t1;
   do x <- (do x1 <- (do y <- dlabels t2; Ret (x, y));
            (do x <- assert q x1; (Ret \o ucat) x));
   m x0 x))%Do; last first.
  bind_ext => u'; rewrite bind_fmap bindA; bind_ext => sS.
  rewrite 4!bindA; bind_ext => x; rewrite 2!bindretf !bindA.
  by rewrite_ bindretf.
rewrite -H1.
rewrite [in LHS]/drBin bind_fmap [in LHS]/bassert /= ![in LHS]bindA.
bind_ext => s.
rewrite !bindA.
transitivity (do x0 <- relabel u;
  (do x <- dlabels t2; (do x <-
    (do x1 <- Ret (s, x); (do x3 <- assert q x1; Ret (ucat x3)));
    m x0 x)))%Do; last by bind_ext => y2; rewrite bindA.
rewrite -H2.
bind_ext => s'.
rewrite !bindretf.
rewrite assertE.
rewrite bindA.
transitivity (guard (q (s, s')) >>
  (do x1 <- (Ret \o ucat) (s, s'); relabel u >>= (m^~ x1)))%Do.
  bind_ext; case; by rewrite 2!bindretf.
rewrite guardsC; last exact: failfresh_bindmfail.
rewrite !bindA !bindretf !bindA.
bind_ext => u'.
rewrite bindA guardsC; last exact: failfresh_bindmfail.
by rewrite bindA bindretf.
Qed.

(* see gibbons2011icfp Sect. 9.3 *)
Lemma join_and_pairs :
  (Join \o (M #(*TODO: fmap*) mpair) \o mpair) \o ((fmap dlabels) \o relabel)^`2 =
  (mpair \o Join^`2) \o            ((fmap dlabels) \o relabel)^`2.
Proof.
rewrite boolp.funeqE => -[x1 x2].
rewrite 3!compE.
rewrite joinE.
rewrite fmapE.
rewrite 2![in RHS]compE.
rewrite [in RHS]/mpair.
rewrite [in LHS]/mpair.
move H : (fmap dlabels) => h.
rewrite /=.
rewrite 2![in RHS]joinE.
rewrite 3!bindA.
rewrite -H.
rewrite !fmapE.
rewrite 3!bindA.
bind_ext => {}x1.
rewrite 2!bindretf 2!bindA.
do 3 rewrite_ bindretf.
rewrite -dlabelsC.
bind_ext => ?.
rewrite /=.
rewrite bindA.
bind_ext => ?.
by rewrite bindretf.
Qed.

(* first property of Sect. 9.3 *)
Lemma dlabels_relabel_is_fold :
  relabel >=> dlabels = foldt drTip drBin.
Proof.
apply foldt_universal.
  (* relabel >=> dlabels \o Tip = drTip *)
  rewrite /kleisli (* TODO(rei): don't unfold *) -(compA (Join \o _)) -(compA Join).
  rewrite (_ : _ \o Tip = (M # Tip) \o const Fresh) //.
  rewrite (compA (fmap dlabels)) -functor_o (_ : dlabels \o _ = Ret \o wrap) //.
  by rewrite functor_o 2!compA joinMret.
(* relabel >=> dlabels \o Bin = drBin \o _ *)
rewrite /kleisli (* TODO(rei): don't unfold *) -[in LHS](compA (Join \o _)) -[in LHS](compA Join).
rewrite (_ : _ \o _ Bin = (fmap (uncurry Bin)) \o (mpair \o relabel^`2)); last first.
  by rewrite boolp.funeqE; case.
rewrite (compA (fmap dlabels)) -functor_o.
rewrite (_ : _ \o _ Bin = (fmap ucat) \o bassert q \o mpair \o dlabels^`2); last first.
  by rewrite boolp.funeqE; case.
transitivity ((fmap ucat) \o Join \o (fmap (bassert q \o mpair)) \o mpair \o
    (fmap dlabels \o relabel)^`2).
  rewrite -2![in LHS](compA (fmap ucat)) [in LHS]functor_o.
  rewrite -[in LHS](compA (fmap _)) [in LHS](compA (Join \o _) (fmap _)).
  rewrite compfid natural -2![in RHS]compA; congr (_ \o _).
  by rewrite [in LHS]functor_o -[in LHS]compA naturality_mpair.
rewrite functor_o (compA _ (fmap (bassert q))) -(compA _ _ (fmap (bassert q))).
rewrite commutativity_of_assertions. (* first non-trivial step *)
rewrite (compA _ (bassert q)) -(compA _ _ (fmap mpair)) -(compA _ _ mpair) -(compA _ _ (_^`2)).
by rewrite join_and_pairs. (* second non-trivial step *)
Qed.

(* second property of Sect. 9.3 *)
Lemma symbols_size_is_fold :
  Symbols \o (@size_Tree Symbol) = foldt drTip drBin.
Proof.
apply foldt_universal.
  by rewrite -compA (_ : @size_Tree Symbol \o _ = const 1) // Symbols_prop1.
pose p := Distinct M.
transitivity (bassert p \o Symbols \o @size_Tree Symbol \o uncurry Bin
  : (_ -> M _)).
  by rewrite bassert_symbols.
transitivity ((bassert p) \o Symbols \o uaddn \o (@size_Tree Symbol)^`2
  : (_ -> M _)).
  by rewrite -[in LHS]compA -[in RHS]compA size_Tree_Bin.
transitivity (bassert p \o (fmap ucat) \o mpair \o (Symbols \o (@size_Tree Symbol))^`2
  : (_ -> M _)).
  rewrite -2!compA (compA Symbols) Symbols_prop2.
  by rewrite -(compA (_ \o mpair)) (compA (bassert p)).
transitivity ((fmap ucat) \o bassert q \o mpair \o (bassert p \o Symbols \o (@size_Tree Symbol))^`2
  : (_ -> M _)).
  (* assert p distributes over concatenation *)
  by rewrite (promote_assert_sufficient_condition (@failfresh_bindmfail _ M) promotable_q).
transitivity ((fmap ucat) \o bassert q \o mpair \o (Symbols \o (@size_Tree Symbol))^`2
  : (_ -> M _)).
  by rewrite bassert_symbols.
by [].
Qed.

(* main claim *)
Lemma dlabels_relabel_never_fails :
  relabel >=> dlabels = Symbols \o @size_Tree Symbol.
Proof. by rewrite dlabels_relabel_is_fold symbols_size_is_fold. Qed.

End tree_relabelling.
