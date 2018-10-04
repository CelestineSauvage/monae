(*
  Denotation of the imperative language given in terms of the state/trace monad.
  Prove that the small-step semantics is equivalent to the denotation.
*)

Require Import ssreflect ssrfun ssrbool FunctionalExtensionality Eqdep List.
Import ListNotations.
Require Import monad state_monad_product smallstep.

Section DenotationalSemantics.

Variables S T : Type.
Variable M0 : statefulMonad (S * list T).
Variable M1 : stateMonad S.
Variable M2 : traceMonad T.

Program Let M : stateTraceMonad S T :=
  MonadStateTrace.Pack (MonadStateTrace.Class
    (base1 := MonadState.class M1) (base2 := MonadTrace.class M2) (
  MonadStateTrace.Mixin
    _ _ (Sm := M1) (Tm := M2) (st_monad := M0))).

Next Obligation.
intro t.
extensionality sl.
destruct sl as [s l].
set (f := MonadState.Exports.Get).
set (g := MonadTrace.Exports.Mark t).
Admitted.

Next Obligation.
intros s t.
extensionality sl.
set (f := MonadTrace.Exports.Mark t).
set (g := MonadState.Exports.Put s).
Admitted.

Next Obligation.
destruct M1; reflexivity.
Qed.

Next Obligation.
destruct M2; reflexivity.
Qed.

Program Fixpoint denotation {A : Type} (p : program A) : M A :=
  match p with
  | p_ret _ v => Ret v
  | p_bind _ _ m f => do a <- denotation m; denotation (f a)
  | p_cond _ b p1 p2 => if b then denotation p1 else denotation p2
  | p_get => Get _
  | p_put s' => Put _ s'
  | p_mark t => Mark _ t
  end.

Fixpoint denotation_continuation (k : continuation) : M (@continuation T S) :=
  match k with
  | stop A a => Ret (stop A a)
  | p `; f =>
      do a <- denotation p ;
      denotation_continuation (f a)
  end.

(* TODO: Ca serait une équation dans la spec de MonadStateTrace
   où (denotation p) est remplacé par un M de type m a quelconque *)
Lemma denotation_prefix_preserved A (p : program A) : forall s s' l1 l a,
  Run (denotation p) (s, l1) = (a, (s', l)) -> exists l2, l = l1 ++ l2.
Proof.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 | | s0 | t ]; cbn;
 intros s s' l1 l a' Heq.
- exists [].
  rewrite app_nil_r.
  by move: Heq; rewrite runret => -[].
- rewrite runbind in Heq.
  case_eq (Run (denotation p) (s, l1)).
  intros a (s0, l0) Hp.
  rewrite Hp in Heq.
  apply IHp in Hp.
  apply IHg in Heq.
  destruct Hp as [l2 Hp].
  destruct Heq as [l2' Heq].
  exists (l2 ++ l2').
  rewrite app_assoc.
  congruence.
- destruct b; [ eapply IHp1 | eapply IHp2 ]; exact Heq.
- exists [].
  rewrite app_nil_r.
  by move: Heq; rewrite runget => -[].
- exists [].
  rewrite app_nil_r.
  by move: Heq; rewrite runput => -[].
- exists [t].
  by move: Heq; rewrite runmark => -[].
Qed.

(* TODO: Ca serait une équation dans la spec de MonadStateTrace
   où (denotation p) est remplacé par un M de type m a quelconque *)
Lemma denotation_prefix_independent A (p : program A) s l1 l2 :
  Run (denotation p) (s, l1 ++ l2) =
  let res := Run (denotation p) (s, l2) in
  (res.1, (res.2.1, l1 ++ res.2.2)).
Proof.
elim: p s l1 l2 => /= {A} [A a|A B p1 IH1 p2 IH2|A b p1 IH1 p2 IH2||s'|t] s l1 l2.
by rewrite !runret.
rewrite [in LHS]runbind [in LHS]IH1.
rewrite [in RHS]runbind.
case: (Run (denotation p1) (s, l2)) => a' [s' l'] /=.
by rewrite IH2.
by case: ifPn => _; [rewrite IH1|rewrite IH2].
by rewrite !runget.
by rewrite !runput.
by rewrite !runmark !seq.cats1 seq.rcons_cat.
Qed.

(* TODO: Ca serait une équation dans la spec de MonadStateTrace
   où (denotation_continuation k) est remplacé par un M de type m a quelconque *)
Lemma denotation_continuation_prefix_independent k : forall s l1 l2,
  Run (denotation_continuation k) (s, l1 ++ l2) =
  let res := Run (denotation_continuation k) (s, l2) in
  (res.1, (res.2.1, l1 ++ res.2.2)).
Proof.
elim: k => // [A a s l1 l2|A p k IH s l1 l2].
by rewrite !runret.
rewrite /= !runbind.
rewrite denotation_prefix_independent /=.
destruct (Run (denotation p) (s, l2)) as [ a (s', l) ].
by rewrite IH.
Qed.

Lemma step_None_correct s s' k k' l :
  step (s, k) None (s', k') ->
  Run (denotation_continuation k) (s, l) = Run (denotation_continuation k') (s', l).
Proof.
intro Hstep.
remember (s, k) as sk eqn: Heq.
remember None as o eqn: Heqo.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq' Heqo.
induction Hstep as
 [ s A a f | s A B p f g | s A p1 p2 k | s A p1 p2 k | s f | s s' f | s t f ];
 intros s1 s2 k1 k2 l [= Hs1 Hk1] [= Hs2 Hk2] Heqo.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runret.
- subst s1 k1 s2 k2.
  cbn.
  by rewrite bindA.
- subst s1 s2 k1 k2.
  reflexivity.
- subst s1 s2 k1 k2.
  reflexivity.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runget.
- subst s1 k1 s2 k2.
  by rewrite /= runbind runput.
- discriminate Heqo.
Qed.

Lemma step_Some_correct s s' k k' t l :
  step (s, k) (Some t) (s', k') ->
  Run (denotation_continuation k) (s, l) =
  Run (denotation_continuation k') (s', l ++ [t]).
Proof.
intro Hstep.
remember (s, k) as sk eqn: Heq.
remember (Some t) as o eqn: Heqo.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq' Heqo.
induction Hstep as
 [ s A a f | s A B p f g | s A p1 p2 k | s A p1 p2 k | s f | s s' f | s t' f ];
 intros s1 s2 k1 k2 l [= Hs1 Hk1] [= Hs2 Hk2] Heqo; try discriminate Heqo.
subst s1 k1 s2 k2.
injection Heqo; intro; subst t.
by rewrite /= runbind runmark.
Qed.

Lemma step_star_correct_gen s s' k k' l l' :
  step_star (s, k) l' (s', k') ->
  Run (denotation_continuation k) (s, l) = Run (denotation_continuation k') (s', l++l').
Proof.
intro Hstep_star.
remember (s, k) as sk eqn: Heq.
remember (s', k') as sk' eqn: Heq'.
revert s s' k k' l Heq Heq'.
induction Hstep_star as
 [ s |
  (s, k) (s', k') (s'', k'') l' Hstep Hstep_star IH |
  (s, k) (s', k') (s'', k'') t l' Hstep Hstep_star IH ];
 intros s1 s2 k1 k2 l1 Heq1 Heq2.
- rewrite app_nil_r.
  rewrite Heq1 in Heq2.
  injection Heq2; intros; subst; reflexivity.
- injection Heq1; clear Heq1; intros; subst s1 k1.
  injection Heq2; clear Heq2; intros; subst s2 k2.
  apply step_None_correct with (l := l1) in Hstep.
  rewrite Hstep.
  apply IH; reflexivity.
- injection Heq1; clear Heq1; intros; subst s1 k1.
  injection Heq2; clear Heq2; intros; subst s2 k2.
  apply step_Some_correct with (l := []) in Hstep.
  rewrite <- app_nil_r at 1.
  rewrite denotation_continuation_prefix_independent.
  rewrite -> Hstep, (IH _ s'' _ k'');
   [ | reflexivity | reflexivity ].
  cbn.
  by rewrite denotation_continuation_prefix_independent.
Qed.

Proposition step_star_correct
  (s s' : S) (A : Type) (a : A) (p : program A) (l : list T) :
  step_star (s, p `; stop A) l (s', stop A a) ->
  Run (denotation p) (s, []) = (a, (s', l)).
Proof.
intro Hss.
apply step_star_correct_gen with (l := []) in Hss.
move: Hss.
rewrite /= runret runbind.
destruct (Run (denotation p) (s, [])) as [a'' [s'' l'']].
rewrite runret => Hss.
injection Hss; clear Hss; intros Heq1 Heq2 Heq3.
apply inj_pair2 in Heq3.
congruence.
Qed.

Lemma step_star_complete_gen
  (s s' : S) (A : Type) (a : A) (p : program A) (l1 l2 : list T) f :
  Run (denotation p) (s, l1) = (a, (s', l1 ++ l2)) ->
  step_star (s, p `; f) l2 (s', f a).
Proof.
revert s s' a l1 l2 f.
induction p as [ A a | A B p IHp g IHg | A b p1 IHp1 p2 IHp2 | |  aa | t ]; cbn;
 intros s s' a' l1 l2 f Heq.
- rewrite runret in Heq.
  injection Heq; clear Heq; intros; subst a' s'.
  replace l2 with (@nil T) by
   (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
  eapply ss_step_None; [ apply s_ret | apply ss_refl ].
- eapply ss_step_None.
  + apply s_bind.
  + move: Heq.
    rewrite runbind.
    case_eq (Run (denotation p) (s, l1)).
    intros a (s0, l0) Hp Heq.
(*    rewrite Hp in Heq.*)
    specialize (denotation_prefix_preserved _ _ _ _ _ _ _ Hp).
    intros [l3 Hl3].
    rewrite Hl3 in Hp.
    apply IHp with (f := (fun a => g a `; f)) in Hp.
    clear IHp.
    specialize (denotation_prefix_preserved _ _ _ _ _ _ _ Heq).
    intros [l4 Hl4].
    rewrite Hl4 in Heq.
    apply IHg with (f := f) in Heq.
    clear IHg.
    subst l0.
    replace l2 with (l3 ++ l4) by
     (induction l1; cbn in Hl4; [ congruence | injection Hl4; tauto ]).
    eapply step_star_transitive.
    * apply Hp.
    * exact Heq.
- destruct b; [
    eapply ss_step_None; [
      apply s_cond_true
    | apply IHp1 with (l1 := l1); exact Heq ]
  | eapply ss_step_None; [
      apply s_cond_false
    | apply IHp2 with (l1 := l1); exact Heq ]
  ].
- rewrite runget in Heq.
  injection Heq; clear Heq; intros; subst a' s'.
  replace l2 with (@nil T) by
   (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
  eapply ss_step_None; [ apply s_get | apply ss_refl ].
- rewrite runput in Heq.
  injection Heq; clear Heq; intros; subst a' s'.
  replace l2 with (@nil T) by
   (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
  eapply ss_step_None; [ apply s_put | apply ss_refl ].
- rewrite runmark in Heq.
  injection Heq; clear Heq; intros; subst a' s'.
  replace l2 with [t] by
   (revert l2 H; induction l1; [ tauto | intros ? [=]; firstorder ]).
  eapply ss_step_Some; [ apply s_mark | apply ss_refl ].
Qed.

Proposition step_star_complete
  (s s' : S) (A : Type) (a : A) (p : program A) (l : list T) :
  Run (denotation p) (s, []) = (a, (s', l)) ->
  step_star (s, p `; stop A) l (s', stop A a).
Proof.
intro Hp.
apply step_star_complete_gen with (l1 := []).
exact Hp.
Qed.

End DenotationalSemantics.

Arguments denotation [T] [S] _ _.
