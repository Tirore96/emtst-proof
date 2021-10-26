Require Export Nom_Swap_fs.


Inductive incV (V : Set) : Set :=
| VZ : incV V
| VS : V → incV V.

Arguments VZ {V}.
Arguments VS {V} _.

Definition incV_map {V W : Set} (f : V → W) (x : incV V) : incV W :=
  match x with
  | VZ ⇒ VZ
  | VS y ⇒ VS (f y)
  end.


Definition name := atom.
Definition names := atoms.

Inductive proc (V : Set) : Set :=
| pr_var : V → proc V
| pr_inp : name → proc (incV V) → proc V
| pr_snd : name → proc V → proc V → proc V
| pr_par : proc V → proc V → proc V
| pr_nu : name → proc V → proc V
| pr_nil : proc V
.

Arguments pr_var {V} _.
Arguments pr_inp {V} _ _.
Arguments pr_snd {V} _ _ _.
Arguments pr_par {V} _ _.
Arguments pr_nu {V} _ _.
Arguments pr_nil {V}.

Notation "a ? P" := (pr_inp a P) (at level 42, right associativity).
Notation "a '!(' P ')' Q" := (pr_snd a P Q) (at level 42, right associativity).
Notation "P '//' Q" := (pr_par P Q) (at level 40, left associativity).
Notation "'nu' a , P " := (pr_nu a P) (at level 42, no associativity).
Notation PO := pr_nil.

Notation proc0 := (proc Empty_set).
Notation proc1 := (proc (incV Empty_set)).

Fixpoint fn {V:Set} (P : proc V) : names :=
  match P with
  | pr_var x ⇒ {}
  | a ? P' ⇒ add a (fn P')
  | a !(P') Q ⇒ add a (fn P' `union` fn Q)
  | P' // Q ⇒ fn P' `union` fn Q
  | nu a, P' ⇒ remove a (fn P')
  | PO ⇒ {}
  end.

Fixpoint size {V:Set} (P:proc V) :=
  match P with
  | pr_var x ⇒ 1
  | a ? P' ⇒ S(size P')
  | a !(P') Q ⇒ S(size P' + size Q)
  | P' // Q ⇒ S(size P' + size Q)
  | nu a, P' ⇒ S(size P')
  | PO ⇒ 0
  end.


Fixpoint swap {V:Set} (b:name) (c:name) (P:proc V) : proc V:=
  match P with
  | pr_var x ⇒ pr_var x
  | a ? P' ⇒ (swap_aux b c a) ? (swap b c P')
  | a !(P') Q ⇒ (swap_aux b c a) !(swap b c P') (swap b c Q)
  | P' // Q ⇒ (swap b c P') // (swap b c Q)
  | nu a, P' ⇒ nu (swap_aux b c a), ( swap b c P')
  | PO ⇒ PO
  end.

Lemma unsimpl_swap_nu : ∀ {V:Set} a b c (P:proc V),
    nu (swap_aux b c a), swap b c P = swap b c (nu a, P).
Proof. auto. Qed.

Lemma fn_swap_fs : ∀ V (P : proc V) b c,
      fn (swap b c P) [=] swap_fs b c (fn P).
Proof. intro. induction P as [ A x | A a P IHP
                     | A a P IHP Q IHQ | A P IHP Q IHQ | A a P IHP | A ];
  intros; simpl in *; try rewrite IHP; try rewrite IHQ.
  - symmetry. apply empty_swap_fs.
  - apply add_swap_fs.
  - rewrite union_swap_fs. rewrite add_swap_fs. fsetdec.
  - apply union_swap_fs.
  - apply remove_swap_fs.
  - symmetry. apply empty_swap_fs.
Qed.

Lemma swap_id : ∀ V a (P : proc V), swap a a P = P.
Proof. induction P; default_simp; simpl_swap_aux.
Qed.

Lemma swap_sym : ∀ V b c (P : proc V),
  swap b c P = swap c b P.
Proof.
  induction P; default_simp; simpl_swap_aux.
Qed.

Lemma swap_invo : ∀ V b c (P : proc V),
  swap b c (swap b c P) = P.
Proof.
  induction P; default_simp; simpl_swap_aux.
Qed.

Lemma swap_equivariance : ∀ V b c b0 c0 (P : proc V),
    swap b c (swap b0 c0 P) =
    swap (swap_aux b c b0) (swap_aux b c c0) (swap b c P).
Proof.
  induction P; default_simp; try rewrite swap_aux_equivariance; auto.
Qed.

Lemma swap_indep : ∀ V b c b0 c0 (P : proc V),
  b0≠b → b0≠c → c0≠b →c0≠c →
  swap b c (swap b0 c0 P) = swap b0 c0 (swap b c P).
Proof.
  intros. rewrite swap_equivariance. simpl_swap_aux.
Qed.

Lemma shuffle_swap : ∀ V a b c (P : proc V),
  a ≠ c → b ≠ c →
  (swap a b (swap b c P)) = (swap a c (swap a b P)).
Proof.
  intros. rewrite swap_equivariance. simpl_swap_aux.
Qed.

Lemma notin_fn_equivariance : ∀ V a b c (P : proc V),
  a `notin` fn P →
  swap_aux b c a `notin` fn (swap b c P).
Proof. intros. rewrite fn_swap_fs. apply swap_fs_2. auto. Qed.

Lemma swap_fn_indep : ∀ V b c a (P : proc V),
  a≠b → a≠c → a `in` fn P ↔ a `in` (fn (swap b c P)) .
Proof. intros. rewrite fn_swap_fs. split; intro.
  - apply swap_fs_3. simpl_swap_aux.
  - apply swap_fs_3' in H1. simpl_swap_aux×.
Qed.


Inductive aeq {V:Set}: proc V → proc V → Prop :=
  | aeq_var : ∀ x, aeq (pr_var x) (pr_var x)
  | aeq_inp : ∀ a (P Q : proc (incV V)), @aeq (incV V) P Q →
      aeq (a ? P) (a ? Q)
  | aeq_snd : ∀ a P1 P2 Q1 Q2, aeq P1 Q1 → aeq P2 Q2 →
      aeq (a !(P1) P2) (a !(Q1) Q2)
  | aeq_par : ∀ P1 P2 Q1 Q2, aeq P1 Q1 → aeq P2 Q2 →
      aeq (P1 // P2) (Q1 // Q2)
  | aeq_nu_same : ∀ a P Q, aeq P Q →
      aeq (nu a, P) (nu a, Q)
  | aeq_nu_diff : ∀ b c P Q, b≠c → b `notin` fn Q →
      aeq P (swap b c Q) → aeq (nu b, P) (nu c, Q)
  | aeq_nil : aeq PO PO.

Notation "P =A= Q" := (aeq P Q) (at level 70, no associativity).

Lemma aeq_refl : ∀ V (P: proc V), P =A= P.
Proof.
  induction P; constructor; default_simp.
Qed.

Lemma aeq_swap : ∀ V b c (P Q : proc V), P =A= Q →
    (swap b c P) =A= (swap b c Q).
Proof. intros. induction H; simpl; constructor; default_simp.
  - apply notin_fn_equivariance; auto.
  - rewrite <- swap_equivariance; auto.
Qed.

Lemma aeq_fn : ∀ V (P Q : proc V), P =A= Q → fn P [=] fn Q.
Proof. intros. induction H; default_simp; try fsetdec. rewrite IHaeq. intro.
  destruct (a==b); try fsetdec. destruct(a==c); subst.
  - split; try fsetdec. apply (notin_fn_equivariance _ _ b c) in H0.
    simpl_swap_aux×. fsetdec.
  - assert (a `in` fn (swap b c Q) ↔ a `in` fn Q).
    { symmetry. apply swap_fn_indep; auto. }
    fsetdec.
Qed.

Lemma aeq_sym : ∀ V (P Q : proc V), P =A= Q → Q =A= P.
Proof.
  intros. induction H; try solve [constructor; auto].
  apply aeq_nu_diff; auto.
  - apply (notin_fn_equivariance V b b c Q) in H0. simpl_swap_aux×.
    forwards: aeq_fn P; eauto.
    rewrite H2. auto.
  - rewrite <- (swap_invo _ c b Q). apply aeq_swap. rewrite swap_sym. auto.
Qed.

Lemma aeq_swap_indep : ∀ V a b (P : proc V),
  a≠b → b `notin` fn P → a `notin` fn P → (swap a b P) =A= P.
Proof. intros V a b P. gen a b.
  induction P; intros a b neq nb na; simpl in *;
  try solve [constructor]; subst.
  - simpl_swap_aux; try fsetdec. constructor; apply IHP; auto.
  - simpl_swap_aux; try fsetdec. constructor.
    apply IHP1; auto. apply IHP2; auto.
  - constructor. apply IHP1; auto. apply IHP2; auto.
  - simpl_swap_aux; try fsetdec; constructor; auto;
      rewrite swap_sym; apply aeq_refl.
Qed.

Lemma aeq_trans : ∀ V (P Q R : proc V), P =A= Q → Q =A= R → P =A= R.
Proof. intros V P. induction P; intros Q R AEQ1 AEQ2;
  destruct Q; inversion AEQ1; destruct R; inversion AEQ2; subst;
  try solve [constructor; eauto].
  - constructor; auto. rewrite <- (aeq_fn _ _ _ H7). auto.
    apply IHP with (swap n n1 Q). auto. apply aeq_swap. auto.
  - destruct (n==n1).
    + subst. constructor; try fsetdec. apply IHP with (swap n1 n0 Q).
      auto. rewrite <- (swap_invo V n1 n0 R). apply aeq_swap.
      rewrite swap_sym. auto.
    + rewrite (aeq_fn _ _ _ H12) in H4.
      apply (notin_fn_equivariance _ n n0 n1 ) in H4. rewrite swap_invo in H4.
      simpl_swap_aux×. constructor; auto.
      apply IHP with (swap n n0 (swap n0 n1 R)).
      { apply IHP with (swap n n0 Q); auto. apply aeq_swap; auto. }
      rewrite shuffle_swap; auto. apply aeq_swap.
      apply aeq_swap_indep; auto.
Qed.


Add Parametric Relation (V:Set) : (proc V) (@aeq V)
    reflexivity proved by (aeq_refl V)
    symmetry proved by (aeq_sym V)
    transitivity proved by (aeq_trans V)
      as aeq_eq_rel.

Add Parametric Morphism (V:Set) (a:name): (pr_nu a)
    with signature (@aeq V) ==> (@aeq V)
      as nu_morphism.
Proof. intros; constructor; auto. Qed.

Add Parametric Morphism (V:Set) (a:name): (pr_inp a)
    with signature (@aeq (incV V)) ==> (@aeq V)
      as inp_morphism.
Proof. intros; constructor; auto. Qed.

Add Parametric Morphism (V:Set) (a:name): (pr_snd a)
    with signature (@aeq V) ==> (@aeq V) ==> (@aeq V)
      as snd_morphism.
Proof. intros; constructor; auto. Qed.

Add Parametric Morphism (V:Set): (@pr_par V)
    with signature (@aeq V) ==> (@aeq V) ==> (@aeq V)
      as par_morphism.
Proof. intros; constructor; auto. Qed.

Add Parametric Morphism (V:Set): (fn)
    with signature (@aeq V) ==> (Equal)
      as fn_morphism.
Proof. intros. apply aeq_fn; auto. Qed.

Add Parametric Morphism (V:Set) b c : (swap b c)
    with signature (@aeq V) ==> (@aeq V)
      as swap_morphism.
Proof. intros. apply aeq_swap; auto. Qed.

Lemma swap_morphism' : ∀ (V : Set) (b c : name) (P Q : proc V),
    swap b c P =A= swap b c Q → P =A= Q.
Proof. intros. rewrites <- (>>swap_invo). rewrites <- (>>swap_invo Q).
  apply swap_morphism. eauto. Qed.


Lemma size_induction :
  ∀ (P: ∀ V, proc V →Prop),
    (∀ V x, (∀ W (y:proc W), size y < size x → P W y) → P V x) →
    (∀ V x, P V x).
Proof.
  introv IH. intros V x. gen_eq n: (size x). gen V x.
  induction n using peano_induction. introv Eq. subst×.
Qed.

Lemma swap_size_eq : ∀ V b c (P : proc V),
    size (swap b c P) = size P.
Proof. induction P; simpl; auto. Qed.

Add Parametric Morphism (V:Set) : (size)
    with signature (@aeq V) ==> (eq)
      as size_morphism.
Proof. intros. induction H; simpl; try rewrite IHaeq;
  try rewrite IHaeq1; try rewrite IHaeq2; auto.
  rewrite swap_size_eq. auto.
Qed.


Fixpoint mapV {V W : Set} (f : V → W) (P : proc V) : proc W :=
  match P with
  | pr_var x ⇒ pr_var (f x)
  | a ? P' ⇒ a ? (mapV (incV_map f) P')
  | a !(P') Q ⇒ a !(mapV f P') (mapV f Q)
  | P' // Q ⇒ (mapV f P') // (mapV f Q)
  | nu a, P' ⇒ nu a, (mapV f P')
  | PO ⇒ PO
  end.

Notation shiftV := (mapV (@VS _)).
Notation shiftV1 := (mapV (incV_map (@VS _))).

Definition liftV {V W: Set} (f : V → proc W) (x : incV V) : proc (incV W) :=
  match x with
  | VZ ⇒ pr_var VZ
  | VS y ⇒ shiftV (f y)
  end.

Fixpoint bind_rec {V W : Set} (n : nat) (f : V → proc W)
              (N : names) (P : proc V) : proc W :=
  match n with
  | 0 ⇒ PO
  | S m ⇒ match P with
        | pr_var x ⇒ f x
        | a ? P' ⇒ a ? (bind_rec m (liftV f) N P')
        | a !(P') Q ⇒ a !(bind_rec m f N P') (bind_rec m f N Q)
        | P' // Q ⇒ (bind_rec m f N P') // (bind_rec m f N Q)
        | nu a, P' ⇒ let (b,_) := atom_fresh N in
                        nu b, (bind_rec m f (add b N) (swap a b P'))
        | PO ⇒ PO
        end
  end.

Definition bind {V W : Set} (f: V → proc W) (N: names) (P: proc V) : proc W :=
  bind_rec (size P) f N P.

Definition subst_func {V: Set} (P : proc V) (x : incV V) : proc V :=
  match x with
  | VZ ⇒ P
  | VS y ⇒ pr_var y
  end.

Definition subst {V : Set} (P : proc (incV V)) (Q : proc V) : proc V :=
  bind (subst_func Q) (fn P `union` fn Q) P.

Lemma bind_size : ∀ (V W : Set) n (f : V → proc W) (N : names)
    (P : proc V), size P ≤ n → bind_rec n f N P = bind f N P.
Proof. intros V W n. gen V W. apply (lt_wf_ind n). clear n.
  introv IH ineq. unfold bind in ×. destruct n; destruct P;
  try solve [inversion ineq]; simpl in *; try reflexivity.
  - rewrite IH; auto; nat_math.
  - rewrite IH with (m:=n)(P:=P1); auto; try nat_math.
    rewrite IH with (m:=n)(P:=P2); auto; try nat_math.
    rewrite IH with (m:=size P1 + size P2)(P:=P1); auto; try nat_math.
    rewrite IH with (m:=size P1 + size P2)(P:=P2); auto; try nat_math.
  - rewrite (IH n); auto; try nat_math.
    rewrite (IH n); auto; try nat_math.
    rewrite IH with (m:=size P1 + size P2)(P:=P1); auto; try nat_math.
    rewrite IH with (m:=size P1 + size P2)(P:=P2); auto; try nat_math.
  - destruct atom_fresh. rewrite (IH n); auto;
    rewrite swap_size_eq; auto; nat_math.
Qed.

Tactic Notation "foldbind" :=
  repeat (rewrite bind_size; [|repeat rewrite swap_size_eq; subst; nat_math]).
Tactic Notation "foldbind" "in" hyp(H) :=
  repeat (rewrite bind_size in H; [|repeat rewrite swap_size_eq; subst; nat_math]).


Lemma swap_mapV : ∀ (V W : Set) (P : proc V) b c (f : V → W),
  swap b c (mapV f P) = mapV f (swap b c P).
Proof. intros V W P. revert W. induction P; default_simp.
Qed.

Lemma swap_shiftV : ∀ (V : Set) (P : proc V) b c,
  swap b c (shiftV P) = shiftV (swap b c P).
Proof. intros. rewrite swap_mapV. auto. Qed.

Lemma fn_mapV : ∀ (V W : Set) (P : proc V) (f : V → W),
      fn (mapV f P) [=] fn P.
Proof. intros V W P. gen W. induction P; intros; simpl fn;
  try rewrite IHP; try rewrite IHP1; try rewrite IHP2; try fsetdec.
Qed.

Lemma fn_shiftV : ∀ (V : Set) (P : proc V), fn (shiftV P) [=] fn P.
Proof. intros. rewrite fn_mapV. fsetdec. Qed.

Lemma aeq_mapV : ∀ (V W : Set) (P Q : proc V) (f : V → W),
  P =A= Q → (mapV f P) =A= (mapV f Q).
Proof. intros V W P. revert W. induction P; intros; destruct Q; inversion H;
  simpl in *; constructor; subst; auto.
  - rewrite fn_mapV. auto.
  - rewrite swap_mapV. apply IHP. auto.
Qed.

Add Parametric Morphism (V W : Set) (f : V → W) : (mapV f)
    with signature (@aeq V) ==> (@aeq W)
      as mapV_morphism.
Proof. intros; apply aeq_mapV; auto. Qed.

Lemma aeq_shiftV : ∀ V (P Q : proc V), P =A= Q → (shiftV P) =A= (shiftV Q).
Proof. intros; apply aeq_mapV; auto. Qed.

Add Parametric Morphism V : (shiftV)
    with signature (@aeq V) ==> (@aeq (incV V))
      as shiftV_morphism.
Proof. intros; apply aeq_shiftV; auto. Qed.

Lemma mapV_id {V: Set} (P : proc V) :
  mapV (fun x ⇒ x) P = P.
Proof.
  induction P; default_simp.
  asserts_rewrite (incV_map (fun (x:V) ⇒ x) = fun x ⇒ x).
    { extens. intros [ | x ]; simpl; congruence. } rewrite× IHP.
Qed.

Lemma mapV_mapV {A B C : Set} : ∀ (P : proc A)(f : A → B) (g : B → C),
  mapV g (mapV f P) = mapV (fun x ⇒ g (f x)) P.
Proof.
  intros. gen B C. induction P; default_simp.
   rewrite IHP. fequals. extens. intros [ | x]; simpl; try reflexivity.
Qed.


Tactic Notation "tac_eq_empty" :=
  match goal with
    | |- ?s [=] empty ⇒ apply equal_empty_swap_fs
    | |- _ ⇒ fail
  end.
Tactic Notation "tac_swap_fs_2'_4'" "in" hyp(H) :=
  match type of H with
    | (?x `notin` swap_fs ?b ?c ?s) ⇒ apply swap_fs_4' in H
    | (?x `notin` ?s) ⇒ apply swap_fs_2' in H
    | _ ⇒ fail
  end.

Tactic Notation "simpl_swap_fs" := repeat first
[ rewrite swap_aux_l | rewrite swap_aux_r
| rewrite unsimpl_swap_nu
| rewrite fn_shiftV | rewrite fn_mapV
| rewrite fn_swap_fs
| rewrite swap_fs_id | rewrite swap_id
| apply swap_fs_monotone | apply swap_fs_morphism
| apply swap_morphism | apply swap_fs_mon_left
| rewrite add_swap_fs_2 | rewrite remove_swap_fs_2
| rewrite union_swap_fs | rewrite diff_swap_fs
| rewrite inter_swap_fs | tac_eq_empty
| apply swap_fs_1 | apply swap_fs_2
| apply swap_fs_3 | apply swap_fs_4
| rewrite empty_swap_fs | rewrite remove_diff_add
| rewrite swap_fs_invo | rewrite swap_invo
| rewrite swap_aux_invo
| reflexivity | auto
].

Tactic Notation "simpl_swap_fs" "in" hyp(H) := repeat first
[ rewrite swap_aux_l in H | rewrite swap_aux_r in H
| rewrite unsimpl_swap_nu in H
| rewrite fn_shiftV in H | rewrite fn_mapV in H
| rewrite fn_swap_fs in H
| rewrite swap_fs_id in H | rewrite swap_id in H
| apply swap_fs_monotone' in H | apply swap_fs_morphism' in H
| apply swap_morphism' in H | apply swap_fs_mon_left' in H
| rewrite add_swap_fs_2 in H | rewrite remove_swap_fs_2 in H
| rewrite union_swap_fs in H | rewrite diff_swap_fs in H
| rewrite inter_swap_fs in H | apply equal_empty_swap_fs' in H
| tac_swap_fs_2'_4' in H
| apply swap_fs_1' in H | apply swap_fs_3' in H
| rewrite empty_swap_fs in H | rewrite remove_diff_add in H
| rewrite swap_fs_invo in H | rewrite swap_invo in H
| rewrite swap_aux_invo in H
].


Lemma fnsaxp :∀ V a x (P : proc V) M,
      (remove a (fn P) [<=] M) → x `notin` M →
      fn (swap a x P) [<=] add x M.
Proof. intros. destruct (x==a); subst; simpl_swap_fs. fsetdec.
  intros_all. simpl_swap_fs in H1. simpl_swap_aux*; fsetdec.
Qed.

Lemma bind_return : ∀ V (P : proc V) (f : V → proc V) (N : names),
  (∀ x, f x = pr_var x) → fn P [<=] N → (bind f N P) =A= P.
Proof. intros V P'. apply size_induction with (x:=P'). intros V0 P IHP.
  introv H ineq. unfold bind.
  destruct P as [ x | a P | a P Q | P Q | a P | ]; intros;
  simpl; foldbind; try (rewrite (IHP _ P); trivial);
  try (rewrite (IHP _ Q); trivial); simpl in *;
  try nat_math; try reflexivity; try nat_math; try fsetdec.
  + rewrite H. reflexivity.
  + intros [ | x ]; simpl; trivial. rewrite H. auto.
  + destruct atom_fresh; foldbind. destruct (x==a); subst.
    - constructor. simpl_swap_fs. apply IHP. nat_math. auto. fsetdec.
    - constructor; auto. rewrite (swap_sym _ x a).
      apply IHP. rewrite swap_size_eq; nat_math. auto.
      apply fnsaxp; auto.
Qed.

Lemma bind_return' {V: Set} : ∀ N (P : proc V),
  fn P [<=] N → (bind (@pr_var _) N P) =A= P.
Proof.
  intros. apply bind_return; auto.
Qed.

Lemma bind_mapV {A B1 B2 C : Set} : ∀ (P : proc A) N
  (f1 : A → B1) (f2 : B1 → proc C)(g1 : A → proc B2) (g2 : B2 → C),
  (∀ x, f2 (f1 x) = mapV g2 (g1 x)) → fn P [<=] N →
  (bind f2 N (mapV f1 P)) = (mapV g2 (bind g1 N P)).
Proof. intros P'. gen B1 B2 C. apply size_induction with (x:=P').
  intros V P IH. introv H inc1.
  destruct P as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; simpl in *; foldbind.
  + rewrite H. reflexivity.
  + f_equal. apply IH; try fsetdec; try nat_math. intros [|x]; auto.
    simpl. rewrite H. repeat rewrite mapV_mapV. reflexivity.
  + f_equal; apply IH; auto; try fsetdec; nat_math.
  + f_equal; apply IH; auto; try fsetdec; nat_math.
  + destruct atom_fresh. simpl mapV. f_equal. foldbind.
    rewrite swap_mapV. apply IH; auto.
    rewrite swap_size_eq; nat_math. apply fnsaxp; auto.
  + reflexivity.
Qed.

Lemma fn_bind : ∀ V W (P : proc V) N (f : V → proc W),
  fn P [<=] N → (∀ x, fn (f x) [<=] N) →
  fn (bind f N P) [<=] N.
Proof. intros V W P'. revert W. apply size_induction with (x:=P').
  intros V' P IH W N f in1 in2.
  destruct P as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; simpl in *; foldbind; try fsetdec; auto;
  repeat (rewrite IH; auto; try nat_math; try fsetdec).
  - intros [|x]; simpl. fsetdec. simpl_swap_fs.
  - destruct atom_fresh. foldbind.
    simpl. rewrite IH; auto; try (rewrite swap_size_eq; nat_math);
    try (apply fnsaxp; fsetdec). fsetdec. intro x0. rewrite in2. fsetdec.
Qed.

Lemma aeq_swap_cut_notin : ∀ V b c x (P : proc V),
    (x≠b → x≠c → b≠c → x `notin` fn P ∧ b `notin` fn P)
    → swap c b P =A= swap b x (swap c x P).
Proof. intros.
  destruct (b==c); destruct (x==b); destruct (x==c); subst;
  simpl_swap_fs; try reflexivity. rewrite swap_sym; reflexivity.
  forwards: H; auto.
  rewrite (swap_sym _ c x). rewrite swap_sym. rewrite shuffle_swap; auto.
  symmetry. simpl_swap_fs. apply aeq_swap_indep; auto.
Qed.

Lemma aeq_bind_3 : ∀ V W (P Q : proc V) N (f : V → proc W),
  fn Q [<=] N → P =A= Q → (bind f N P) =A= (bind f N Q).
Proof. intros V W P'. revert W. apply size_induction with (x:=P').
  intros V' P IH W Q N f ineq H.
  destruct P as [ x | a P0 | a P0 P1 | P0 P1 | a P0 | ];
  destruct Q as [ x' | a' Q0 | a' Q0 Q1 | Q0 Q1 | a' Q0 | ];
  unfold bind; simpl in *; foldbind; inversion H; subst; try reflexivity;
  try solve [constructor; apply IH; auto; try fsetdec; nat_math];
  destruct atom_fresh; foldbind; constructor; (apply IH;
  [rewrite swap_size_eq; nat_math | apply fnsaxp; auto |]).
    rewrite H1; easy.
  rewrite <- (swap_invo _ a x). simpl_swap_fs. rewrite H6.
  rewrite swap_sym. apply aeq_swap_cut_notin. intros; fsetdec.
Qed.

Lemma aeq_bind_1 : ∀ V W (P : proc V) N (f g : V → proc W),
  (∀ x, (f x) =A= (g x)) → (bind f N P) =A= (bind g N P).
Proof. intros V W P'. revert W. apply size_induction with (x:=P').
  intros V' P IH W N f g aeqfg.
  destruct P as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; simpl; intros; try destruct atom_fresh; foldbind; auto; constructor;
  try rewrite bind_size with (f:=f); try rewrite bind_size with (f:=g);
  try nat_math; try apply IH; auto; try rewrite swap_size_eq; simpl in *;
  try nat_math. intros [|x]; simpl; try rewrite aeqfg; reflexivity.
Qed.

Lemma lemma_swap_bind_and_aeq_bind_2 :
  ∀ V W (P : proc V) N M (f : V → proc W) b c,
  (fn P) [<=] M → (∀ x, fn (f x) [<=] M) → M [<=] N → b ≠ c →
  (swap b c (bind f N P)) =A=
    (bind (fun x ⇒ swap b c (f x)) (swap_fs b c N) (swap b c P))
  ∧ (bind f N P) =A= (bind f M P).
Proof. intros V' W P'. revert W. apply size_induction with (x:=P').
  intros V P IH. introv in1 in2 inMN inbc.

  assert (∀ (W : Set) (y : proc W),
     size y < size P →
     ∀ (W0 : Set) (N : atoms) (f : W → proc W0) (b c : atom),
     fn y [<=] N →
     (∀ x : W, fn (f x) [<=] N) →
     b ≠ c →
     (swap b c (bind f N y)) =A=
     (bind (fun x : W ⇒ swap b c (f x)) (swap_fs b c N) (swap b c y))) as IHL.
  { intros. forwards ident: IH N0; eauto. fsetdec. easy. }
  
  assert (∀ (W : Set) (y : proc W),
     size y < size P →
     ∀ (W0 : Set) (N M : atoms) (f : W → proc W0),
     fn y [<=] M →
     (∀ x : W, fn (f x) [<=] M) →
     M [<=] N →
     (bind f N y) =A= (bind f M y)) as IHR.
  { intros. destruct (atom_fresh M0). destruct (atom_fresh (add x M0)).
      forwards ident: IH x x0; eauto. easy. }
  
  clear IH. split.

  - destruct P as [ x | a P | a P Q | P Q | a P | ]; unfold bind; intros;
  simpl in *; foldbind; try reflexivity; try constructor; try solve
  [apply IHL; auto; [try nat_math | try fsetdec | intro; rewrite in2; auto]].
  + rewrite IHL; auto. apply aeq_bind_1. intros [|x]; simpl.
      reflexivity. rewrite swap_mapV. reflexivity. nat_math. fsetdec.
    intros [|x]; simpl; simpl_swap_fs; try rewrite in2; fsetdec.
  + destruct atom_fresh. simpl. destruct atom_fresh. foldbind. rewrite inMN in in1.
    remember (swap_aux b c x0) as x1.
    replace x0 with (swap_aux b c x1) in *; [|simpl_swap_aux*].
    clears x0 Heqx1. simpl_swap_fs in n0. rewrite <- swap_equivariance.
    assert (∀ y x2, fn (f x2) [<=] add y N) as in3.
      { intros. apply AtomSetProperties.subset_add_2. rewrite in2. auto. }
    rewrites (>> IHR (swap b c (swap a x1 P)) (swap_fs b c (add x1 N)) ).
      repeat rewrite swap_size_eq; nat_math. simpl_swap_fs.
      rewrite <- fn_swap_fs. apply fnsaxp; auto.
      intro; simpl_swap_fs. simpl_swap_fs.
    rewrite <- IHL; auto;
        [ | rewrite swap_size_eq; nat_math | apply fnsaxp; auto ].
    simpl_swap_fs. destruct (x==x1); subst; try reflexivity.
    constructor; auto. rewrite fn_bind; auto. apply fnsaxp; auto.
    symmetry. rewrite IHL; auto;
      [ | rewrite swap_size_eq; nat_math | apply fnsaxp; auto ].
    rewrites (>> aeq_bind_1 (fun x0 : V ⇒ swap x x1 (f x0)) f).
      intro; rewrite aeq_swap_indep; auto; try reflexivity;
         rewrite in2; rewrite inMN; auto.
    rewrite aeq_bind_3; [ | rewrite <- add_swap_fs;
          rewrite <- (swap_fs_notin x x1); auto;
          simpl_swap_aux; apply fnsaxp; auto; apply in1
        | symmetry; apply aeq_swap_cut_notin; intros; split;
          [ clears n n1 H x; fsetdec | clears x1; fsetdec] ].
    apply IHR; auto. repeat rewrite swap_size_eq; nat_math.
      apply fnsaxp; auto. rewrite <- add_swap_fs.
      rewrite <- (swap_fs_notin x x1); auto. simpl_swap_fs.

  - destruct P as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; intros; simpl in *; foldbind; try constructor;
  try (apply IHR; try nat_math; try fsetdec); auto.
  + reflexivity.
  + intros [|x]; simpl. fsetdec. simpl_swap_fs.
  + destruct atom_fresh; foldbind.
    assert (∀ x0 (x1 : V), fn (f x1) [<=] add x0 M)
      by (intros; rewrite in2; apply AtomSetProperties.subset_add_2; reflexivity).
    rewrite IHR;
    [ | rewrite swap_size_eq; nat_math | apply fnsaxp with (M:=M); auto
      | auto | rewrite inMN; reflexivity ].
    destruct atom_fresh; foldbind. destruct (x==x0); subst; try reflexivity.
    constructor; auto. rewrite fn_bind; auto. apply fnsaxp; auto.
    symmetry.
    apply aeq_trans with (bind f (swap_fs x x0 (add x0 M)) (swap a x P)).
    apply aeq_trans with (bind f (swap_fs x x0 (add x0 M)) (swap x x0 (swap a x0 P))).
    apply aeq_trans with (bind (fun z ⇒ swap x x0 (f z))
            (swap_fs x x0 (add x0 M)) (swap x x0 (swap a x0 P))).
    × apply IHL; auto. rewrite swap_size_eq; nat_math.
      apply fnsaxp; auto.
    × apply aeq_bind_1. intro. apply aeq_swap_indep; auto.
      rewrite in2; auto. rewrite in2; rewrite inMN; auto.
    × apply aeq_bind_3. rewrite <- add_swap_fs. simpl_swap_aux.
        rewrite <- swap_fs_notin; auto. apply fnsaxp; auto.
      symmetry. apply aeq_swap_cut_notin; intros; fsetdec.
    × apply IHR; auto. rewrite swap_size_eq; nat_math.
      apply fnsaxp; auto. rewrite <- add_swap_fs. rewrite <- swap_fs_notin; auto.
        simpl_swap_fs.
Qed.

Lemma aeq_bind_2 : ∀ V W (P : proc V) (f : V → proc W) (N M: names),
  (∀ x, fn (f x) [<=] M)-> fn P [<=] M →
  (∀ x, fn (f x) [<=] N)-> fn P [<=] N →
  (bind f N P) =A= (bind f M P).
Proof. intros. destruct (atom_fresh (N `union` M)).
  destruct (atom_fresh (add x (N `union` M))).
  apply aeq_trans with (bind f (N `union` M) P).
  - forwards: lemma_swap_bind_and_aeq_bind_2 (N `union` M) x x0; eauto.
      fsetdec. easy.
  - forwards: lemma_swap_bind_and_aeq_bind_2 (N `union` M) M x x0; eauto.
      fsetdec. easy.
Qed.

Lemma swap_bind : ∀ V W (P : proc V) N (f : V → proc W) b c,
  (fn P) [<=] N → (∀ x, fn (f x) [<=] N) →
  (swap b c (bind f N P)) =A=
  (bind (fun x ⇒ swap b c (f x)) (swap_fs b c N) (swap b c P)).
Proof. intros. destruct (b==c); subst.
  - repeat rewrite swap_id.
    rewrite (aeq_bind_2 _ _ _ _ (swap_fs c c N) N); try intro; simpl_swap_fs.
    apply aeq_bind_1. intro. simpl_swap_fs.
  - forwards: lemma_swap_bind_and_aeq_bind_2 N; eauto. reflexivity. easy.
Qed.

Lemma swap_bind_f_indep : ∀ V W (P : proc V) N (f : V → proc W) b c,
  (fn P) [<=] N → (∀ x, fn (f x) [<=] N) →
  (∀ x, b `notin` fn (f x)) → (∀ x, c `notin` fn (f x)) →
  (swap b c (bind f N P)) =A= (bind f (swap_fs b c N) (swap b c P)).
Proof. intros. destruct (b==c); subst.
  - simpl_swap_fs. apply aeq_bind_2; try intro; simpl_swap_fs.
  - rewrite swap_bind; auto. apply aeq_bind_1; auto.
    intro. apply aeq_swap_indep; auto.
Qed.

Lemma bind_bind {A B C : Set}: ∀ (P : proc A) N (f : A → proc B)
        (g : B → proc C), fn P [<=] N → (∀ x, fn (f x) [<=] N) →
        (∀ x, fn (g x) [<=] N) →
        (bind g N (bind f N P)) =A= (bind (fun x ⇒ bind g N (f x)) N P).
Proof. intros P'. revert B C. apply size_induction with (x:=P').
  introv IH inP inf ing.
  destruct x as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; simpl in *; foldbind;
  try solve [constructor; apply IH; auto; try nat_math; fsetdec].
  + reflexivity.
  + constructor. rewrite IH; auto; try fsetdec. apply aeq_bind_1.
      intros [|x0]; simpl; try reflexivity.
      erewrite bind_mapV; simpl; auto; reflexivity.
      nat_math. all: intros [|x]; simpl; simpl_swap_fs; fsetdec.
  + destruct atom_fresh eqn:?. unfold bind. simpl in ×. rewrite Heqs.
    clear Heqs. foldbind. constructor. simpl_swap_fs.
    rewrite IH. apply aeq_bind_1. intro x0; apply aeq_bind_2; auto.
      3:rewrite swap_size_eq; nat_math. 3:apply fnsaxp; auto.
      all:intro; try rewrite inf; try rewrite ing; fsetdec.
Qed.

Lemma bind_mapV_comp {A B C:Set}: ∀ P N (f:B→proc C)(g:A→B),
  fn P [<=] N → (∀ x, fn (f x) [<=] N) →
  (bind f N (mapV g P)) = (bind (fun x ⇒ f (g x)) N P).
Proof. intros P'. revert B C. apply size_induction with (x:=P').
  intros V P IH B C N f g inP inf.
  destruct P as [ x | a P | a P Q | P Q | a P | ];
  unfold bind; simpl in *; try destruct atom_fresh;
  foldbind; try reflexivity; f_equal;
  try solve [apply IH; auto; try nat_math; fsetdec].
  - rewrite IH. f_equal. extens. intros [|x0]; simpl; reflexivity.
    nat_math. fsetdec. intros [|x0]; simpl; simpl_swap_fs; fsetdec.
  - rewrite swap_mapV. apply IH.
    rewrite swap_size_eq; nat_math. apply fnsaxp; auto.
    intro; rewrite inf; fsetdec.
Qed.

Lemma subst_shift {V: Set} : ∀ (P Q : proc V),
  (subst (shiftV P) Q) =A= P.
Proof.
  intros. unfold subst.
  rewrites (>> (@bind_mapV) V (fun x : V ⇒ pr_var x) (fun x : V ⇒ x)).
    simpl; auto. 2: rewrite mapV_id; apply bind_return'.
    all: simpl_swap_fs; fsetdec.
Qed.

Lemma aeq_subst : ∀ V (P P' : proc (incV V)) (Q Q' : proc V),
  P =A= P' → Q =A= Q' → subst P Q =A= subst P' Q'.
Proof. intros. unfold subst.
  rewrite (aeq_bind_3 _ _ _ P') ; [| rewrite H; fsetdec |exact H].
  rewrite (aeq_bind_2 _ _ _ _ _ (union (fn P') (fn Q')));
    try rewrite H; try fsetdec. apply aeq_bind_1.
  all: intros [|x]; simpl; try rewrite H0; try easy; fsetdec.
Qed.

Add Parametric Morphism (V:Set) : (subst)
    with signature (@aeq (incV V)) ==> (@aeq V) ==> (@aeq V)
      as subst_morphism.
Proof. intros; apply aeq_subst; auto. Qed.

Lemma swap_subst : ∀ V (P : proc (incV V)) (Q : proc V) b c,
  swap b c (subst P Q) =A= subst (swap b c P) (swap b c Q).
Proof. intros. unfold subst. rewrite swap_bind;
    [ | fsetdec | intros [|x]; simpl; fsetdec].
  asserts_rewrite ((fun x : incV V ⇒ swap b c (subst_func Q x))
                    =(subst_func (swap b c Q))).
    { extens. intros [|x]; simpl; reflexivity. }
  apply aeq_bind_2; try intros [|x]; simpl; simpl_swap_fs; fsetdec.
Qed.

Lemma fn_subst : ∀ V (P : proc (incV V)) (Q : proc V),
  fn (subst P Q) [<=] fn P `union` fn Q.
Proof. intros. unfold subst. apply fn_bind. fsetdec.
  intros [|x]; simpl; fsetdec.
Qed.

Lemma subst_nu_indep : ∀ V a (P : proc (incV V)) (Q : proc V), a `notin` fn Q →
    subst (nu a, P) Q =A= nu a, (subst P Q).
Proof. intros. unfold subst. unfold bind. simpl. destruct atom_fresh. foldbind.
  destruct (a==x); subst.
  - constructor. simpl_swap_fs. apply aeq_bind_2. 2,4: fsetdec.
    all:intros [|x0]; simpl; fsetdec.
  - constructor. auto. rewrite fn_bind; try intros [|x0]; simpl; fsetdec.
    rewrite swap_bind_f_indep. 2:fsetdec. 2-4:intros [|x0]; simpl; fsetdec.
    rewrite swap_sym. apply aeq_bind_2.
    + intros [|x0]; simpl. rewrite swap_fs_notin at 1. apply swap_fs_monotone.
      all: fsetdec.
    + simpl_swap_fs. fsetdec.
    + intros [|x0]; simpl; fsetdec.
    + rewrite swap_sym. apply fnsaxp; fsetdec.
Qed.

Lemma subst_par : ∀ V (P P' : proc (incV V)) (Q : proc V),
    subst (P//P') Q =A= (subst P Q)//(subst P' Q).
Proof. intros. unfold subst. unfold bind; simpl; foldbind.
  constructor; apply aeq_bind_2; try intros [|x]; simpl; fsetdec.
Qed.
