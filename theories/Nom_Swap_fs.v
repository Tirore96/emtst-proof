Require Import TLC.LibTactics TLC.LibLogic TLC.LibNat.

Require Import Metalib.Metatheory.


Locate eq_dec. Require Export Coq.Setoids.Setoid.
Require Import SendRec.Atom.


Definition inter := M.inter.
Definition diff := M.diff.
Definition Equal := M.Equal. 

Definition swap_aux (b c a:atom) : atom := if (a == b) then c else if (a == c) then b else a.

Tactic Notation "simpl_swap_aux" :=  unfold swap_aux;
  intros; simpl; repeat (case_if; try nat_math); subst; auto.
Tactic Notation "simpl_swap_aux" "*" := unfold swap_aux in *;
  intros; simpl in *; repeat (case_if; try nat_math); subst; auto.

Lemma swap_aux_invo : forall b c a,
  swap_aux b c (swap_aux b c a) = a.
Proof. simpl_swap_aux. Qed.

Lemma swap_aux_equivariance : forall b c b0 c0 a,
    swap_aux b c (swap_aux b0 c0 a) =
    swap_aux (swap_aux b c b0) (swap_aux b c c0) (swap_aux b c a).
Proof. simpl_swap_aux. Qed.

Lemma swap_aux_inj : forall b c a1 a2,
  a1 <> a2 -> swap_aux b c a1 <> swap_aux b c a2.
Proof. intros. intro. apply H. simpl_swap_aux*. Qed.

Hint Extern 1 (swap_aux ?b ?c ?a1 <> swap_aux ?b ?c ?a2) => apply swap_aux_inj.

Lemma swap_aux_l : forall b c, swap_aux b c b = c.
Proof. simpl_swap_aux. Qed.
Lemma swap_aux_r : forall b c, swap_aux b c c = b.
Proof. simpl_swap_aux. Qed.


Lemma swap_aux_same : forall a b, swap_aux a a b = b.
Proof. simpl_swap_aux. Qed.



Notation "x `in` E" :=
  (M.In x E)
  (at level 70).

Notation "x `notin` E" :=
  (~ M.In x E)
  (at level 70).

Notation "E `union` F" :=
  (M.union E F)
  (at level 65, right associativity, format "E  `union`  '/' F").


Definition swap_fs (b c : atom) (s : atoms) : atoms :=
  if (M.mem b s) then
       (if (M.mem c s) then s else (M.add c (M.remove b s)))
  else if (M.mem c s) then (M.add b (M.remove c s)) else s.

Lemma swap_fs_1 : forall a b c s,
      a `in` s -> (swap_aux b c a) `in` (swap_fs b c s).
Proof. intros. unfold swap_fs. simpl_swap_aux; try fsetdec;
  try apply M.mem_2 in C1; try apply M.mem_2 in C0; auto;
  apply M.mem_1 in H; rewrite H in *; try inversion C0; inversion C2.
Qed.
Check atoms.
Lemma swap_fs_1' : forall a b c s,
      (swap_aux b c a) `in` (swap_fs b c s) -> a `in` s.
Proof. intros.  unfold swap_fs in *. simpl_swap_aux*; try fsetdec;
  try apply M.mem_2 in C1; try apply M.mem_2 in C0;
  try apply M.mem_2 in C2; auto; try fsetdec;
  apply M.mem_1 in H; rewrite H in *; inversion C1.
Qed.

Lemma swap_fs_2 : forall a b c s,
      a `notin` s -> (swap_aux b c a) `notin` (swap_fs b c s).
Proof. intros. intro. apply swap_fs_1' in H0. apply H. auto. Qed.

Lemma swap_fs_2' : forall a b c s,
      (swap_aux b c a) `notin` (swap_fs b c s) -> a `notin` s.
Proof. intros. intro. apply (swap_fs_1 _ b c) in H0. apply H. auto. Qed.


Lemma swap_fs_3 : forall a b c s,
      (swap_aux b c a) `in` s -> a `in` (swap_fs b c s).
Proof. intros. asserts_rewrite (a = swap_aux b c (swap_aux b c a)).
  simpl_swap_aux. apply swap_fs_1. auto. Qed.
Lemma swap_fs_4 : forall a b c s,
      (swap_aux b c a) `notin` s -> a `notin` (swap_fs b c s).
Proof. intros. asserts_rewrite (a = swap_aux b c (swap_aux b c a)).
  simpl_swap_aux. apply swap_fs_2. auto. Qed.

Lemma swap_fs_3' : forall a b c s,
      a `in` (swap_fs b c s) -> (swap_aux b c a) `in` s .
Proof. intros. asserts_rewrite (a = swap_aux b c (swap_aux b c a)) in H.
  simpl_swap_aux. apply swap_fs_1' in H. auto. Qed.
Lemma swap_fs_4' : forall a b c s,
      a `notin` (swap_fs b c s) -> (swap_aux b c a) `notin` s .
Proof. intros. asserts_rewrite (a = swap_aux b c (swap_aux b c a)) in H.
  simpl_swap_aux. apply swap_fs_2' in H. auto. Qed.


Notation "E [=] F" :=
  (M.Equal E F)
  (at level 70, no associativity).

Notation "E [<=] F" :=
  (M.Subset E F)
  (at level 70, no associativity).



Lemma swap_fs_in : forall b c s, b `in` s -> c `in` s ->
  s [=] swap_fs b c s.
Proof. intros. intro. split.
  - intro. apply swap_fs_3. simpl_swap_aux.
  - intro. apply swap_fs_3' in H1. simpl_swap_aux*.
Qed.

Lemma swap_fs_notin : forall b c s, b `notin` s -> c `notin` s ->
  s [=] swap_fs b c s.
Proof. intros. intro. split.
  - intro. apply swap_fs_3. simpl_swap_aux.
  - intro. apply swap_fs_3' in H1. simpl_swap_aux*.
Qed.

Lemma swap_fs_id : forall b s, swap_fs b b s [=] s.
Proof. intros. intro. split.
  - intro. apply swap_fs_3' in H. simpl_swap_aux*.
  - intro. apply swap_fs_3. simpl_swap_aux.
Qed.

Lemma swap_fs_sym : forall b c s,
  swap_fs b c s [=] swap_fs c b s.
Proof. intros. intro. split.
  - replace a with (swap_aux b c (swap_aux c b a)).
    intro. apply swap_fs_1' in H. apply (swap_fs_1 _ c b) in H.
    simpl_swap_aux*. simpl_swap_aux*.
  - replace a with (swap_aux c b (swap_aux b c a)).
    intro. apply swap_fs_1' in H. apply (swap_fs_1 _ b c) in H.
    simpl_swap_aux*. simpl_swap_aux*.
Qed.

Lemma swap_fs_invo : forall b c s,
  swap_fs b c (swap_fs b c s) [=] s.
Proof. intros. intro. split.
  - intro. repeat apply swap_fs_3' in H. simpl_swap_aux*.
  - intro. repeat apply swap_fs_3. simpl_swap_aux.
Qed.

Lemma swap_fs_monotone : forall b c s s',
  s[<=]s' -> swap_fs b c s [<=] swap_fs b c s'.
Proof. intros. intro. destruct (a==b); destruct (a==c); subst;
  intro; apply swap_fs_3' in H0; apply swap_fs_3; simpl_swap_aux*.
Qed.

Lemma swap_fs_monotone' : forall b c s s',
  swap_fs b c s [<=] swap_fs b c s' -> s [<=] s'.
Proof. intros. rewrite <- swap_fs_invo. rewrites <- (>>swap_fs_invo s').
  apply swap_fs_monotone. eauto.
Qed.

Lemma swap_fs_mon_left : forall b c s s',
  swap_fs b c s [<=] s' -> s [<=] (swap_fs b c s').
Proof. intros. rewrites <- (>>swap_fs_invo s). apply swap_fs_monotone. auto. Qed.

Lemma swap_fs_mon_left' : forall b c s s',
  s [<=] (swap_fs b c s') -> swap_fs b c s [<=] s'.
Proof. intros. rewrites <- (>>swap_fs_invo s'). apply swap_fs_monotone. auto. Qed. Check M.add.

Lemma add_swap_fs : forall b c x s,
  M.add (swap_aux b c x) (swap_fs b c s) [=] swap_fs b c (M.add x s).
Proof.
assert (forall b c s, M.add c (swap_fs b c s) [=] swap_fs b c (M.add b s)).
{ intros. intro. destruct (a==c); subst.
    + split. { intros _ . apply swap_fs_3. simpl_swap_aux. fsetdec. fsetdec. } intro. fsetdec.
    + asserts_rewrite (a `in` M.add c (swap_fs b c s) <-> a `in` swap_fs b c s).
      fsetdec. split. { apply swap_fs_monotone; fsetdec. }
      intro. apply swap_fs_3' in H. assert (swap_aux b c a `in` s).
      { simpl_swap_aux*; fsetdec. } apply swap_fs_3. auto.
}
  intros. simpl_swap_aux*.
  - rewrite swap_fs_sym. rewrite (swap_fs_sym b c). auto.
  - intro. destruct(a==x); subst; split; intro.
    + apply swap_fs_3. simpl_swap_aux.
    + fsetdec.
    +  fsetdec. apply (swap_fs_monotone b c s (M.add x s)). fsetdec.

    + assert (a `in` swap_fs b c s) by fsetdec. auto.
    + apply swap_fs_3' in H0. assert (swap_aux b c a `in` s).
        { simpl_swap_aux*; fsetdec. } apply swap_fs_3 in H1. fsetdec.
Qed.

Lemma add_swap_fs_2 : forall b c x s,
  M.add x (swap_fs b c s) [=] swap_fs b c (M.add (swap_aux b c x) s).
Proof. intros. erewrite <- (swap_aux_invo _ _ x) at 1. apply add_swap_fs. Qed.

Lemma empty_swap_fs : forall b c, swap_fs b c M.empty [=] M.empty.
Proof. intros. split.
  + intro. apply swap_fs_3' in H. fsetdec.
  + fsetdec.
Qed.

Lemma remove_swap_fs : forall b c x s,
  M.remove (swap_aux b c x) (swap_fs b c s) [=] swap_fs b c (M.remove x s).
Proof.
assert (forall b c s, M.remove c (swap_fs b c s) [=] swap_fs b c (M.remove b s)).
{ intros. intro. destruct (a==c); subst.
    + split. fsetdec. intro. apply swap_fs_3' in H. simpl_swap_aux*; fsetdec.
    + asserts_rewrite (a `in` M.remove c (swap_fs b c s) <-> a `in` swap_fs b c s).
      fsetdec. split. { intro. apply swap_fs_3' in H.
      assert (swap_aux b c a `in` M.remove b s). {simpl_swap_aux*; fsetdec. }
      apply swap_fs_3. auto. } { apply swap_fs_monotone; fsetdec. }
}
intros. simpl_swap_aux*.
  - rewrite swap_fs_sym. rewrite (swap_fs_sym b c). apply H.
  - intro. split; destruct (a==x); subst; intro.
    + fsetdec.
    + assert (a `in` swap_fs b c s) by fsetdec.
      apply swap_fs_3' in H1. apply swap_fs_3.
      simpl_swap_aux*; fsetdec.
    + apply swap_fs_3' in H0. simpl_swap_aux*; fsetdec.
    + enough (a `in` swap_fs b c s) by fsetdec.
      apply (swap_fs_monotone b c (M.remove x s) s); fsetdec.
Qed.

Lemma remove_swap_fs_2 : forall b c x s,
  M.remove x (swap_fs b c s) [=] swap_fs b c (M.remove (swap_aux b c x) s).
Proof. intros. erewrite <- (swap_aux_invo _ _ x) at 1. apply remove_swap_fs. Qed.

Lemma union_swap_fs : forall b c s s',
  M.union (swap_fs b c s) (swap_fs b c s') [=] swap_fs b c (M.union s s').
Proof. intros. split.
  - intro. destruct (classic (a `in` (swap_fs b c s))).
    + apply swap_fs_3' in H0. apply swap_fs_3. fsetdec.
    + assert (a `in` (swap_fs b c s')) by fsetdec.
      apply swap_fs_3' in H1. apply swap_fs_3. fsetdec.
  - intro. apply swap_fs_3' in H. destruct (classic (swap_aux b c a `in` s)).
    + apply swap_fs_3 in H0. fsetdec.A
    + assert (swap_aux b c a `in` s') by fsetdec.
      apply swap_fs_3 in H1. fsetdec.
Qed.

Lemma diff_swap_fs : forall b c s s',
  diff (swap_fs b c s) (swap_fs b c s') [=]
    swap_fs b c (diff s s').
Proof. intros. split.
  - intro. destruct (classic (a `in` (swap_fs b c s)));
    destruct (classic (a `notin` (swap_fs b c s')));
    try solve [fsetdec].
    apply swap_fs_3' in H0. apply swap_fs_4' in H1.
    apply swap_fs_3. fsetdec.
  - intro. apply swap_fs_3' in H.
    destruct (classic (swap_aux b c a `in` s));
    destruct (classic (swap_aux b c a `in` s'));
    try solve [fsetdec].
    apply swap_fs_3 in H0. apply swap_fs_4 in H1. fsetdec.
Qed.

Lemma inter_swap_fs : forall b c s s',
    inter (swap_fs b c s) (swap_fs b c s')
    [=] swap_fs b c (inter s s').
Proof. intros. split.
  - intro. destruct (classic (a `in` (swap_fs b c s)));
    destruct (classic (a `in` (swap_fs b c s')));
    try solve [fsetdec].
    apply swap_fs_3' in H0. apply swap_fs_3' in H1.
    apply swap_fs_3. fsetdec.
  - intro. apply swap_fs_3' in H.
    destruct (classic (swap_aux b c a `in` s));
    destruct (classic (swap_aux b c a `in` s'));
    try solve [fsetdec].
    apply swap_fs_3 in H0. apply swap_fs_3 in H1. fsetdec.
Qed.

Add Parametric Morphism b c : (swap_fs b c)
    with signature (M.Equal) ==> (Equal)
      as swap_fs_morphism.
Proof. intros. split; apply swap_fs_monotone; fsetdec. Qed.

Lemma swap_fs_morphism' : forall b c s s',
  (swap_fs b c s) [=] (swap_fs b c s') -> s [=] s'.
Proof. intros. rewrite <- swap_fs_invo. rewrites <- (>>swap_fs_invo s').
  apply swap_fs_morphism. eauto.
Qed.

Lemma equal_empty_swap_fs : forall b c s,
  s [=] M.empty -> swap_fs b c s [=] M.empty.
Proof. intros. erewrite <- empty_swap_fs. apply swap_fs_morphism. auto. Qed.

Lemma equal_empty_swap_fs' : forall b c s,
  swap_fs b c s [=] M.empty -> s [=] M.empty.
Proof. intros. eapply swap_fs_morphism'. erewrite H.
  rewrite empty_swap_fs. fsetdec.
Qed.

Lemma remove_diff_add : forall x s s',
    diff s (M.add x s') [=] M.remove x (diff s s').
Proof. intros. fsetdec. Qed.
