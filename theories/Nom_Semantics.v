Require Export Nom_Syntax.


Fixpoint list_to_fs (L:list name) : names :=
  match L with
  | nil ⇒ empty
  | x::q ⇒ add x (list_to_fs q)
  end.

Lemma list_to_fs_1_aux : ∀ x L, InA eq x L ↔ x `in` (list_to_fs L).
Proof. induction L.
  - split; intro; simpl in ×. inversion H. fsetdec.
  - split; intro; simpl in ×.
    + inversion H; subst. fsetdec. rewrite IHL in H1. fsetdec.
    + destruct (x==a); subst. auto. assert (x `in` (list_to_fs L)) by fsetdec.
      rewrite <- IHL in H0. auto.
Qed.

Lemma list_to_fs_2 : ∀ x L, In x L ↔ x `in` (list_to_fs L).
Proof. intros. rewrite <- list_to_fs_1_aux. symmetry. apply InA_iff_In. Qed.


Inductive label : Set :=
| out : name → label
| inp : name → label
| tau : label
.

Definition fn_lab (l:label) : names :=
  match l with
  | tau ⇒ empty
  | out a ⇒ singleton a
  | inp a ⇒ singleton a
  end.

Notation abs := proc1.

Inductive conc : Set :=
| conc_def : list name → proc0 → proc0 → conc
.

Inductive agent :=
| ag_proc : proc0 → agent
| ag_abs : abs → agent
| ag_conc : conc → agent
.

Coercion ag_abs : abs >-> agent. Coercion ag_conc : conc >-> agent.

Print Classes.

Tactic Notation "destructA" constr(A) := destruct A as [| |[]].

Definition conc_wf C := match C with
| conc_def L P Q ⇒ NoDup L ∧ list_to_fs L [<=] fn P
end.

Definition fn_agent A :=
  match A with
  | ag_proc P ⇒ fn P
  | ag_abs F ⇒ fn F
  | ag_conc C ⇒ match C with | conc_def L P Q ⇒
                   diff (union (fn P) (fn Q)) (list_to_fs L) end
  end.



Fixpoint conc_convert_aux L P Q M :=
  match L with
  | nil ⇒ conc_def nil P Q
  | a::q ⇒ match (conc_convert_aux q P Q (add a M)) with
      | conc_def q' P' Q' ⇒
          If a `in` M then let (x,_) := atom_fresh
          (fn P' `union` fn Q' `union` M `union` (list_to_fs q')) in
          conc_def (x::q') (swap x a P') (swap x a Q')
                      else (conc_def (a::q') P' Q')
      end
  end.

Definition conc_convert C M :=
  match C with
  | conc_def L P Q ⇒ conc_convert_aux L P Q M
  end.

Lemma fold_conc_convert : ∀ L P Q M,
    conc_convert_aux L P Q M = conc_convert (conc_def L P Q) M.
Proof. intros. unfold conc_convert. auto. Qed.

Tactic Notation "fold_conc_convert" := repeat rewrite fold_conc_convert in ×.


Definition conc_parl C P : conc :=
  match conc_convert C (fn P) with
  | conc_def L Q R ⇒ conc_def L Q (R // P)
  end.

Definition conc_parr P C : conc :=
  match conc_convert C (fn P) with
  | conc_def L Q R ⇒ conc_def L Q (P // R)
  end.

Definition parl A (P : proc0) : agent :=
  match A with
  | ag_abs F ⇒ ag_abs (F // (shiftV P))
  | ag_proc P' ⇒ ag_proc (P' // P)
  | ag_conc C ⇒ ag_conc (conc_parl C P)
  end.

Definition parr P A : agent :=
  match A with
  | ag_abs F ⇒ ag_abs ((shiftV P) // F)
  | ag_proc P' ⇒ ag_proc (P // P')
  | ag_conc C ⇒ ag_conc (conc_parr P C)
  end.

Definition conc_new (a:name) (C:conc) : conc :=
  match conc_convert C {{a}} with
  | conc_def L P Q ⇒ If a `in` (fn P) then conc_def (a::L) P Q
                                       else conc_def L P (nu a, Q)
  end.

Definition new (a:name) (A: agent) : agent :=
  match A with
  | ag_abs F ⇒ ag_abs (nu a, F)
  | ag_proc P ⇒ ag_proc (nu a, P)
  | ag_conc C ⇒ ag_conc (conc_new a C)
  end.

Fixpoint genNu {V:Set} L (P:proc V) :=
  match L with
  | nil ⇒ P
  | a::q ⇒ nu a, (genNu q P)
  end.

Definition appr (F:abs) C : proc0 :=
  match conc_convert C (fn F) with
  | conc_def L P Q ⇒ genNu L (subst F P // Q)
  end.

Definition appl C (F:abs) : proc0 :=
  match conc_convert C (fn F) with
  | conc_def L P Q ⇒ genNu L (Q // subst F P)
  end.

Inductive lts : proc0 → label → agent → Prop :=
| lts_out : ∀ a P Q, lts (a !(P) Q) (out a) (ag_conc (conc_def nil P Q))
| lts_inp : ∀ a P, lts (a ? P) (inp a) (ag_abs P)
| lts_parl : ∀ P Q l A, lts P l A → lts (P // Q) l (parl A Q)
| lts_parr : ∀ P Q l A, lts P l A → lts (Q // P) l (parr Q A)
| lts_new : ∀ a P l A, a `notin` fn_lab l → lts P l A →
    lts (nu a, P) l (new a A)
| lts_taul : ∀ a P Q F C, lts P (out a) (ag_conc C) →
    lts Q (inp a) (ag_abs F) → lts (P // Q) tau (ag_proc (appl C F))
| lts_taur : ∀ a P Q F C, lts Q (inp a) (ag_abs F) →
    lts P (out a) (ag_conc C) → lts (Q // P) tau (ag_proc (appr F C))
.

Hint Constructors lts:hopi.


*Tactics to generate fresh names
Ltac gather_atoms :=
  let A := gather_atoms_with (fun s : names ⇒ s) in
  let B := gather_atoms_with (fun x : name ⇒ singleton x) in
  let C := gather_atoms_with (fun l : label ⇒ fn_lab l) in
  let D := gather_atoms_with (fun V ⇒ (fun P : proc V ⇒ fn P)) in
  let E := gather_atoms_with (fun Ag : agent ⇒ fn_agent Ag) in
  constr:(A `union` B `union` C `union` D `union` E).

Ltac pick_fresh_aux x := let L := gather_atoms in (pick fresh x for L).

Tactic Notation "pick" "fresh" ident(x) := pick_fresh_aux x.
Tactic Notation "pick_fresh" ident(x) := pick_fresh_aux x.


Lemma fn_conc_convert_0 : ∀ (L L': list name) (M : names) P P' Q Q',
    conc_convert_aux L P Q M = conc_def L' P' Q' →
    ∀ a, a `in` (list_to_fs L') → a `notin` M.
Proof. induction L; intros; simpl in ×.
  - inversion H; subst. fsetdec.
  - destruct conc_convert_aux eqn:?.
    case_if; try solve [inversion H; subst; simpl; fsetdec].
    + destruct atom_fresh. inversion H; subst; simpl in *; clear H.
      destruct (x==a0); subst; auto. assert (a0 `in` (list_to_fs l)) by fsetdec.
      enough (a0 `notin` add a M) by fsetdec.
      eapply IHL. exact Heqc. auto.
    + inversion H; subst; clear H. destruct (a==a0); subst; simpl in *; auto.
      assert (a0 `in` (list_to_fs l)) by fsetdec.
      enough (a0 `notin` add a M) by fsetdec.
      eapply IHL. exact Heqc. auto.
Qed.

Lemma fn_conc_convert_0' : ∀ (L L': list name) (M : names) P P' Q Q',
    conc_convert_aux L P Q M = conc_def L' P' Q' →
    inter (list_to_fs L') M [=] empty.
Proof. intros. intro. split; try fsetdec. intro.
    forwards: AtomSetImpl.inter_1 H0. forwards: AtomSetImpl.inter_2 H0.
    forwards: fn_conc_convert_0 H a H1. contradiction H3.
Qed.

Lemma fn_conc_convert_1 : ∀ (L L': list name) (M : names) P P' Q Q',
    conc_convert_aux L P Q M = conc_def L' P' Q' →
    diff (fn P) (list_to_fs L) [=] diff (fn P') (list_to_fs L').
Proof. induction L; intros; simpl in ×.
  - inversion H. reflexivity.
  - destruct conc_convert_aux eqn:?.
    forwards: IHL. apply Heqc. clear IHL.
    case_if. 2:inversion H; subst; simpl; fsetdec.
    destruct atom_fresh. inversion H; subst; simpl in *; clear H.
    simpl_swap_fs. rewrite H0. clear H0.
    rewrite (swap_fs_notin x a (list_to_fs l)) at 2.
    3:forwards: fn_conc_convert_0' Heqc; fsetdec. 2:fsetdec. simpl_swap_fs.
    apply swap_fs_notin; try fsetdec.
Qed.

Lemma fn_conc_convert_2 : ∀ (L L': list name) (M : names) P P' Q Q',
    conc_convert_aux L P Q M = conc_def L' P' Q' →
    diff (fn Q) (list_to_fs L) [=] diff (fn Q') (list_to_fs L').
Proof. induction L; intros; simpl in ×.
  - inversion H. reflexivity.
  - destruct conc_convert_aux eqn:?.
    forwards: IHL. apply Heqc. clear IHL.
    case_if. 2:inversion H; subst; simpl; fsetdec.
    destruct atom_fresh. inversion H; subst; simpl in *; clear H.
    simpl_swap_fs. rewrite H0. clear H0.
    rewrite (swap_fs_notin x a (list_to_fs l)) at 2.
    3:forwards: fn_conc_convert_0' Heqc; fsetdec. 2:fsetdec. simpl_swap_fs.
    apply swap_fs_notin; try fsetdec.
Qed.

Lemma conc_convert_indep_wf : ∀ L P Q M, conc_wf (conc_def L P Q) →
    inter (list_to_fs L) M [=] empty →
    conc_convert_aux L P Q M = conc_def L P Q.
Proof. induction L; intros; simpl in *; [reflexivity|]. rewrite IHL.
  - destruct (classic (a `in` M)). fsetdec. default_simp.
  - default_simp. split; auto. fsetdec.
  - default_simp. rewrite list_to_fs_2 in H4. clear IHL H2 H5. fsetdec.
Qed.


Lemma lts_parl' : ∀ P Q l A A',
    lts P l A → parl A Q = A' → lts (P // Q) l A'.
Proof.
  intros; subst; eapply lts_parl; eassumption.
Qed.

Lemma lts_parr' : ∀ P Q l A A',
    lts P l A → parr Q A = A' → lts (Q // P) l A'.
Proof.
  intros; subst; eapply lts_parr; eassumption.
Qed.

Lemma lts_taul' : ∀ P A' Q a F C,
    lts P (out a) (ag_conc C) → lts Q (inp a) (ag_abs F) →
    ag_proc (appl C F) = A' → lts (P // Q) tau A'.
Proof.
  intros. subst. eapply lts_taul; eassumption.
Qed.

Lemma lts_taur' : ∀ P A' Q a F C,
    lts P (out a) (ag_conc C) → lts Q (inp a) (ag_abs F) →
    ag_proc (appr F C) = A' → lts (Q // P) tau A'.
Proof.
  intros; subst; eapply lts_taur; eassumption.
Qed.

Lemma lts_new' : ∀ P l a A A',
    a `notin` fn_lab l → lts P l A → (new a A) = A' →
    lts (nu a, P) l (new a A).
Proof.
  intros; subst; eapply lts_new; eassumption.
Qed.

Hint Resolve lts_parl' lts_parr' lts_taul' lts_taur':hopi.

Lemma lts_tau_proc: ∀ P A, lts P tau A → ∃ P', A = ag_proc P'.
Proof.
  introv Hlts. remember tau as l.
  induction Hlts; inverts Heql; eauto;
    try (destruct IHHlts; try reflexivity; subst; eexists; simpl; reflexivity).
Qed.

Lemma lts_inp_abs : ∀ P a A, lts P (inp a) A → ∃ F, A = ag_abs F.
Proof.
  intros P a A Hlts. remember (inp a) as l.
  induction Hlts; inverts Heql; eauto;
    try (destruct IHHlts; try reflexivity; subst; eexists; simpl; auto).
Qed.

Lemma lts_out_conc : ∀ P a A, lts P (out a) A → ∃ C, A = ag_conc C.
Proof.
  intros P a A Hlts. remember (out a) as l.
  induction Hlts; inverts Heql; eauto;
    try (destruct IHHlts; try reflexivity; subst; eexists; simpl; auto).
Qed.

Lemma notin_fn_notin_fnlab : ∀ P l A x,
        lts P l A → x `notin` fn P → x `notin` fn_lab l.
Proof. intros; induction H; simpl in *; fsetdec. Qed.


Lemma fn_genNu : ∀ V (P:proc V) L,
    fn (genNu L P) [=] diff (fn P) (list_to_fs L).
Proof. intros. induction L; simpl in *; simpl_swap_fs; fsetdec. Qed.

Lemma fn_conc_new : ∀ a C, fn_agent (conc_new a C) [=] remove a (fn_agent C).
Proof. intros; destruct C; simpl; unfold conc_new;
  destruct conc_convert eqn:?; case_if; simpls; forwards: fn_conc_convert_1 Heqc;
  forwards: fn_conc_convert_2 Heqc; fsetdec.
Qed.

Lemma fn_new : ∀ A a, fn_agent (new a A) [=] remove a (fn_agent A).
Proof. intros. destructA A; try solve [simpl; reflexivity].
  unfold new. apply fn_conc_new.
Qed.

Lemma fn_appr : ∀ F C, fn (appr F C) [<=] fn F `union` fn_agent C.
Proof. intros. destruct C. simpl.
  unfold appr. destruct conc_convert eqn:?.
  forwards: fn_conc_convert_1 Heqc. forwards: fn_conc_convert_2 Heqc.
  rewrite fn_genNu. simpl. rewrite fn_subst. fsetdec.
Qed.

Lemma fn_appl : ∀ F C, fn (appl C F) [<=] fn_agent C `union` fn F.
Proof. intros. destruct C. simpl.
  unfold appl. destruct conc_convert eqn:?.
  forwards: fn_conc_convert_1 Heqc. forwards: fn_conc_convert_2 Heqc.
  rewrite fn_genNu. simpl. rewrite fn_subst. fsetdec.
Qed.

Lemma fn_parl: ∀ A P, fn_agent (parl A P) [=] fn_agent A `union` fn P.
Proof. intros. destructA A; simpl; simpl_swap_fs.
  unfold conc_parl. destruct conc_convert eqn:?. simpl in ×.
  forwards: fn_conc_convert_1 Heqc.
  forwards: fn_conc_convert_2 Heqc.
  forwards: fn_conc_convert_0' Heqc. fsetdec.
Qed.

Lemma fn_parr: ∀ A P, fn_agent (parr P A) [=] fn P `union` fn_agent A.
Proof. intros. destructA A; simpl; simpl_swap_fs.
  unfold conc_parr. destruct conc_convert eqn:?. simpl in ×.
  forwards: fn_conc_convert_1 Heqc.
  forwards: fn_conc_convert_2 Heqc.
  forwards: fn_conc_convert_0' Heqc. fsetdec.
Qed.

Lemma lts_fn : ∀ P l A, lts P l A → fn_agent A [<=] fn P.
Proof. intros. induction H; simpl in ×. - fsetdec. - fsetdec.
  - rewrite fn_parl. rewrite IHlts. reflexivity.
  - rewrite fn_parr. rewrite IHlts. reflexivity.
  - rewrite fn_new. rewrite IHlts. reflexivity.
  - rewrite fn_appl. destruct C. rewrite IHlts1. rewrite IHlts2. reflexivity.
  - rewrite fn_appr. destruct C. rewrite IHlts1. rewrite IHlts2. reflexivity.
Qed.


Definition swap_lab (b c : name) l :=
  match l with
  | out n ⇒ out (swap_aux b c n)
  | inp n ⇒ inp (swap_aux b c n)
  | _ ⇒ l
  end.


Lemma swap_lab_notin : ∀ b c l,
    b `notin` fn_lab l → c `notin` fn_lab l → swap_lab b c l = l.
Proof. intros b c l; destruct l; simpl; intros;
  simpl_swap_aux; fsetdec. Qed.

Lemma fn_lab_swap_fs : ∀ b c l,
    fn_lab (swap_lab b c l) [=] swap_fs b c (fn_lab l).
Proof. intros. destruct l; simpl; try solve [symmetry; apply empty_swap_fs];
  intro; split; intro.
  + assert (a = swap_aux b c n) by fsetdec; subst.
    apply swap_fs_1. fsetdec.
  + simpl_swap_fs in H. assert (swap_aux b c a = n) by fsetdec; subst.
    simpl_swap_fs.
  + assert (a = swap_aux b c n) by fsetdec; subst. simpl_swap_fs.
  + simpl_swap_fs in H. assert (swap_aux b c a = n) by fsetdec; subst.
    simpl_swap_fs.
Qed.

Lemma swap_lab_in_iff : ∀ b c l x,
    x `in` fn_lab l ↔ swap_aux b c x `in` fn_lab (swap_lab b c l).
Proof. intros. rewrite fn_lab_swap_fs. split; intro;
  simpl_swap_fs in H; simpl_swap_fs. Qed.


Definition swap_list b c L := List.map (swap_aux b c) L.


Lemma swap_list_id : ∀ a L, swap_list a a L = L.
Proof. intros; induction L; simpl;
  simpl_swap_aux; try rewrite IHL; reflexivity. Qed.
Lemma swap_list_invo : ∀ b c L, swap_list b c (swap_list b c L) = L.
Proof. intros; induction L; simpl;
  simpl_swap_aux; try rewrite IHL; reflexivity. Qed.
Lemma swap_list_sym : ∀ b c L, swap_list b c L = swap_list c b L.
Proof. intros; induction L; simpl;
  simpl_swap_aux; try rewrite IHL; reflexivity. Qed.
Lemma swap_list_equivariance : ∀ b c b0 c0 L,
    swap_list b c (swap_list b0 c0 L) =
    swap_list (swap_aux b c b0) (swap_aux b c c0) (swap_list b c L).
Proof. intros; induction L; simpl; try rewrite IHL;
  simpl_swap_aux; try reflexivity. Qed.
Lemma swap_list_indep : ∀ b c b0 c0 L,
    b0 ≠ b → b0 ≠ c → c0 ≠ b → c0 ≠ c →
    swap_list b c (swap_list b0 c0 L) = swap_list b0 c0 (swap_list b c L).
Proof. intros; rewrite swap_list_equivariance.
    simpl_swap_aux. Qed.
Lemma shuffle_swap_list : ∀ (a b c : name) L, a ≠ c → b ≠ c →
    swap_list a b (swap_list b c L) = swap_list a c (swap_list a b L).
Proof. intros; induction L; simpl in *; try rewrite IHL; simpl_swap_aux. Qed.


Lemma swap_list_notin : ∀ b c L,
    ¬ In b L → ¬ In c L → swap_list b c L = L.
Proof. intros b c L. gen b c. induction L; intros; simpl; auto.
  rewrite IHL; auto.
  - simpl_swap_aux.
    + destruct H; constructor; auto.
    + destruct H0; constructor; auto.
  - intro. destruct H. constructor 2. auto.
  - intro. destruct H0. constructor 2. auto.
Qed.

Lemma swap_list_to_fs : ∀ b c L,
    list_to_fs (swap_list b c L) [=] swap_fs b c (list_to_fs L).
Proof. intros. induction L; simpl in *; try rewrite IHL; simpl_swap_fs. Qed.


Definition swap_c b c C := match C with
  | conc_def L P Q ⇒ conc_def (swap_list b c L) (swap b c P) (swap b c Q)
  end.


Lemma swap_c_invo : ∀ b c C, swap_c b c (swap_c b c C) = C.
Proof. intros; destruct C; simpl; repeat rewrite swap_invo;
  try rewrite swap_list_invo; reflexivity. Qed.


Lemma fold_swap_c : ∀ b c L P Q,
    (conc_def (swap_list b c L) (swap b c P) (swap b c Q))
    = swap_c b c (conc_def L P Q).
Proof. intros. simpl. reflexivity. Qed.

Tactic Notation "fold_swap_c" := repeat rewrite fold_swap_c in ×.


Definition swap_ag b c A := match A with
  | ag_proc P ⇒ ag_proc (swap b c P)
  | ag_abs F ⇒ ag_abs (swap b c F)
  | ag_conc C ⇒ ag_conc (swap_c b c C)
  end.


Lemma swap_ag_id : ∀ a A, swap_ag a a A = A.
Proof. intros; destructA A; simpl; repeat rewrite swap_id;
  try rewrite swap_list_id; reflexivity. Qed.
Lemma swap_ag_invo : ∀ b c A, swap_ag b c (swap_ag b c A) = A.
Proof. intros; destructA A; simpl; repeat rewrite swap_invo;
  try rewrite swap_list_invo; reflexivity. Qed.
Lemma swap_ag_sym : ∀ b c A, swap_ag b c A = swap_ag c b A.
Proof. intros; destructA A; simpl; repeat rewrite (swap_sym _ b c);
  try rewrite swap_list_sym; reflexivity. Qed.
Lemma swap_ag_equivariance : ∀ b c b0 c0 A,
    swap_ag b c (swap_ag b0 c0 A) =
    swap_ag (swap_aux b c b0) (swap_aux b c c0) (swap_ag b c A).
Proof. intros; destructA A; simpl; f_equal.
    - apply swap_equivariance; auto.
    - apply swap_equivariance; auto.
    - f_equal; try apply swap_list_equivariance; try apply swap_equivariance; auto.
Qed.
Lemma swap_ag_indep : ∀ b c b0 c0 A,
    b0 ≠ b → b0 ≠ c → c0 ≠ b → c0 ≠ c →
    swap_ag b c (swap_ag b0 c0 A) = swap_ag b0 c0 (swap_ag b c A).
Proof. intros; rewrite swap_ag_equivariance. simpl_swap_aux. Qed.


Lemma fn_ag_swap_fs : ∀ b c A,
    fn_agent (swap_ag b c A) [=] swap_fs b c (fn_agent A).
Proof. intros; destructA A; simpl; try rewrite swap_list_to_fs; simpl_swap_fs. Qed.

Lemma fn_ag_conc_swap_fs : ∀ b c C,
    fn_agent (swap_c b c C) [=] swap_fs b c (fn_agent C).
Proof. intros. destruct C; simpl; try rewrite swap_list_to_fs; simpl_swap_fs. Qed.

Lemma swap_genNu : ∀ V L (P:proc V) b c,
    swap b c (genNu L P) =A= genNu (swap_list b c L) (swap b c P).
Proof. intros V L. gen V. induction L; intros; simpl in ×.
  reflexivity. constructor. apply IHL. Qed.


Tactic Notation "simpl_swap" := repeat first
[ rewrite fold_swap_c | rewrite fn_ag_conc_swap_fs | rewrite fn_ag_swap_fs
| rewrite fn_lab_swap_fs | rewrite swap_list_to_fs | rewrite swap_list_id
| rewrite swap_ag_id | rewrite swap_list_invo | rewrite swap_c_invo
| rewrite swap_ag_invo | simpl_swap_fs
].

Tactic Notation "simpl_swap" "in" hyp(H) := repeat first
[ rewrite fold_swap_c in H | rewrite fn_ag_conc_swap_fs in H
| rewrite fn_ag_swap_fs in H | rewrite fn_lab_swap_fs in H
| rewrite swap_list_to_fs in H | rewrite swap_list_id in H
| rewrite swap_ag_id in H | rewrite swap_list_invo in H
| rewrite swap_c_invo in H | rewrite swap_ag_invo in H
| simpl_swap_fs in H
].

Tactic Notation "simpl_swap" "in" hyp(H0) hyp(H1) :=
  simpl_swap in H0; simpl_swap in H1.
Tactic Notation "simpl_swap" "in" hyp(H0) hyp(H1) hyp(H2) :=
  simpl_swap in H0; simpl_swap in H1; simpl_swap in H2.


Inductive aeq_conc : conc → conc → Prop :=
  | aeq_conc_nil : ∀ P P' Q Q', P =A= P' →
      Q =A= Q' → aeq_conc (conc_def nil P Q) (conc_def nil P' Q')
  | aeq_conc_cons_1 : ∀ L L' P P' Q Q' a,
      aeq_conc (conc_def L P Q) (conc_def L' P' Q') →
      aeq_conc (conc_def (a::L) P Q) (conc_def (a::L') P' Q')
  | aeq_conc_cons_2 : ∀ L L' P P' Q Q' b c, b≠c →
      b `notin` fn_agent (ag_conc (conc_def L' P' Q')) →
      aeq_conc (conc_def L P Q)
        (conc_def (swap_list b c L') (swap b c P') (swap b c Q')) →
      aeq_conc (conc_def (b::L) P Q) (conc_def (c::L') P' Q')
.

Notation "C =Ac= C'" := (aeq_conc C C') (at level 70, no associativity).

Lemma aeq_conc_refl : ∀ C, C =Ac= C.
Proof. intros; destruct C as [L P Q]. gen P Q. induction L; intros.
  - constructor; reflexivity.
  - constructor. apply IHL.
Qed.

Lemma aeq_conc_swap : ∀ b c C C',
    C =Ac= C' → (swap_c b c C) =Ac= (swap_c b c C').
Proof. intros. gen b c; induction H; intros; simpl in *; constructor; simpl_swap.
  - apply IHaeq_conc.
  - simpl. repeat rewrite <- swap_equivariance. rewrite <- swap_list_equivariance. auto.
Qed.

Lemma fn_aeq_conc_1 : ∀ L L' P P' Q Q',
    conc_def L P Q =Ac= conc_def L' P' Q' →
    diff (fn P) (list_to_fs L) [=] diff (fn P') (list_to_fs L').
Proof. intros. remember (conc_def L P Q) as C. remember (conc_def L' P' Q') as C'.
  gen L L' P P' Q Q'.
  induction H; intros; inversion HeqC; inversion HeqC'; subst; simpl in ×.
  - rewrite H. reflexivity.
  - forwards: IHaeq_conc; try reflexivity. simpl_swap.
  - forwards: IHaeq_conc; try reflexivity. simpl_swap.
    rewrite H2. simpl_swap. symmetry. apply swap_fs_notin; fsetdec.
Qed.

Lemma fn_aeq_conc_2 : ∀ L L' P P' Q Q',
    conc_def L P Q =Ac= conc_def L' P' Q' →
    diff (fn Q) (list_to_fs L) [=] diff (fn Q') (list_to_fs L').
Proof. intros. remember (conc_def L P Q) as C. remember (conc_def L' P' Q') as C'.
  gen L L' P P' Q Q'.
  induction H; intros; inversion HeqC; inversion HeqC'; subst; simpl in ×.
  - rewrite H0. reflexivity.
  - forwards: IHaeq_conc; try reflexivity. simpl_swap.
  - forwards: IHaeq_conc; try reflexivity. simpl_swap.
    rewrite H2. simpl_swap. symmetry. apply swap_fs_notin; fsetdec.
Qed.

Lemma fn_aeq_conc_3 : ∀ C C', C =Ac= C' →
    fn_agent C [=] fn_agent C'.
Proof. intros. destruct C. destruct C'. forwards: fn_aeq_conc_1 H.
  forwards: fn_aeq_conc_2 H. simpl. fsetdec.
Qed.

Lemma aeq_conc_sym : ∀ C C', C =Ac= C' → C' =Ac= C.
Proof. intros. induction H.
  - constructor; symmetry; auto.
  - constructor. auto.
  - forwards: fn_aeq_conc_3 H1. simpl_swap in H2.
    rewrite <- (swap_fs_invo b c) in H0. rewrite <- H2 in H0. simpl_swap in H0.
    constructor; auto. simpl_swap. rewrite <- (swap_c_invo c b (conc_def L' P' Q')).
    apply aeq_conc_swap. simpl. rewrite swap_list_sym.
    repeat rewrite (swap_sym _ c b). auto.
Qed.

Lemma aeq_conc_swap_indep : ∀ a b C, a≠b →
  b `notin` fn_agent (ag_conc C) → a `notin` fn_agent (ag_conc C) →
  (swap_c a b C) =Ac= C.
Proof. intros. destruct C as [L P Q]. simpl. gen a b P Q. induction L; intros.
  - simpl. constructor; simpl in *; apply aeq_swap_indep; fsetdec.
  - simpl. simpl_swap_aux; try fsetdec.
    + constructor; auto. simpl in *; fsetdec.
      rewrite swap_list_sym. repeat rewrite (swap_sym _ a0 b). simpl_swap.
      apply aeq_conc_refl.
    + constructor; auto. simpl in *; fsetdec. apply aeq_conc_refl.
    + constructor; auto. apply IHL; auto; simpl in *; fsetdec.
Qed.

Lemma aeq_conc_trans : ∀ C0 C1 C2,
    C0 =Ac= C1 → C1 =Ac= C2 → C0 =Ac= C2.
Proof. intros C0 C1 C2. destruct C0 as [L0 P0 Q0]. destruct C1 as [L1 P1 Q1].
  destruct C2 as [L2 P2 Q2]. gen P0 Q0 L1 P1 Q1 L2 P2 Q2.
  induction L0; intros.
  - inversion H; subst. inversion H0; subst. constructor.
    rewrite H4; auto. rewrite H7; auto.
  - inversion H; subst; inversion H0; subst;
    try solve [constructor; auto; apply IHL0 with L' P1 Q1; auto].
    + constructor; auto. forwards: fn_aeq_conc_3 H2. rewrite <- H1. auto.
      apply IHL0 with (swap_list a c L') (swap a c P1) (swap a c Q1); auto.
      fold_swap_c. apply aeq_conc_swap. auto.
    + destruct (a==c0); subst.
      × constructor.
        apply IHL0 with (swap_list c c0 L') (swap c c0 P1) (swap c c0 Q1).
        rewrite swap_list_sym. repeat rewrite (swap_sym _ c c0). auto.
        rewrite <- (swap_c_invo c c0 (conc_def L'0 P2 Q2)).
        fold_swap_c. apply aeq_conc_swap. auto.
      × forwards: fn_aeq_conc_3 H13. fold_swap_c. rewrite fn_ag_conc_swap_fs in H1.
        rewrite H1 in H9. simpl_swap in H9. simpl_swap_aux×.
        constructor; auto.
        apply IHL0 with (swap_list a c (swap_list c c0 L'0))
            (swap a c (swap c c0 P2)) (swap a c (swap c c0 Q2)).
          { apply IHL0 with (swap_list a c L') (swap a c P1) (swap a c Q1); auto.
            fold_swap_c. apply aeq_conc_swap. auto. }
        repeat rewrite (shuffle_swap _ a c); auto.
        rewrite shuffle_swap_list; auto. fold_swap_c.
        apply aeq_conc_swap. apply aeq_conc_swap_indep; auto.
Qed.

Lemma NoDup_swap_fs : ∀ b c L, NoDup (swap_list b c L) → NoDup L.
Proof. intros b c L. gen b c. induction L; intros; simpl in *; auto.
  default_simp. constructor. intro. rewrite list_to_fs_2 in H.
  apply (swap_fs_1 _ b c) in H. rewrite <- swap_list_to_fs in H.
  rewrite <- list_to_fs_2 in H. contradiction. apply IHL with b c. auto.
Qed.


Add Parametric Relation : conc aeq_conc
    reflexivity proved by (aeq_conc_refl)
    symmetry proved by (aeq_conc_sym)
    transitivity proved by (aeq_conc_trans)
      as aeq_conc_eq_rel.

Add Parametric Morphism b c : (swap_c b c)
    with signature (aeq_conc) ==> (aeq_conc)
      as swap_conc_morphism.
Proof. intros. apply aeq_conc_swap; auto. Qed.

Add Parametric Morphism (L:list name): (conc_def L)
    with signature (aeq) ==> (aeq) ==> (aeq_conc)
      as aeq_conc_nil_morphism.
Proof. induction L; intros; simpl; constructor; try apply IHL; auto. Qed.


Lemma aeq_conc_convert : ∀ C M, C =Ac= conc_convert C M.
Proof. destruct C as [L P Q]. gen P Q.
  induction L; intros; simpl; try reflexivity.
  destruct conc_convert_aux eqn:?. default_simp.
  - assert (x≠a) by fsetdec. symmetry. constructor; auto.
    + simpl. forwards: fn_conc_convert_1 Heqc. forwards: fn_conc_convert_2 Heqc.
      fsetdec.
    + rewrite <- (swap_list_notin x a l). fold_swap_c.
      rewrite <- Heqc. symmetry. rewrite IHL. reflexivity.
      { intro. rewrite list_to_fs_2 in H0. clears Heqc a. fsetdec. }
      { intro. rewrite list_to_fs_2 in H0.
        forwards: fn_conc_convert_0' Heqc. clears x Heqc i. fsetdec. }
  - constructor. forwards: IHL P Q (add a M).
    rewrite H. rewrite Heqc. reflexivity.
Qed.

Lemma aeq_genNu : ∀ V L (P P':proc V),
    P =A= P' → genNu L P =A= genNu L P'.
Proof. intros V L. gen V. induction L; intros; simpl; auto.
  constructor. apply IHL. auto. Qed.

Add Parametric Morphism V L : (genNu L)
    with signature (@aeq V) ==> (aeq)
      as genNu_morphism.
Proof. intros. apply aeq_genNu. auto. Qed.


Inductive aeq_agent : agent → agent → Prop :=
  | aeq_agent_proc : ∀ P Q, P =A= Q →
      aeq_agent (ag_proc P) (ag_proc Q)
  | aeq_agent_abs : ∀ P Q, P =A= Q →
      aeq_agent (ag_abs P) (ag_abs Q)
  | aeq_agent_conc : ∀ C C', C =Ac= C' →
      aeq_agent (ag_conc C) (ag_conc C').

Notation "A =Ag= A'" := (aeq_agent A A') (at level 70, no associativity).

Lemma aeq_agent_refl : ∀ A, A =Ag= A.
Proof. intros; destructA A; constructor; reflexivity. Qed.

Lemma aeq_agent_swap : ∀ b c A A',
    A =Ag= A' → (swap_ag b c A) =Ag= (swap_ag b c A').
Proof. intros; destructA A; destructA A'; inversion H; simpl;
    constructor; fold_swap_c; rewrite H2; reflexivity. Qed.

Lemma aeq_agent_fn : ∀ A A', A =Ag= A' →
    fn_agent A [=] fn_agent A'.
Proof. intros; destructA A; destructA A'; inversion H;
    try solve [simpl; rewrite H2; reflexivity].
    rewrite <- H0 in ×. rewrite <- H1 in ×. subst.
    apply fn_aeq_conc_3. auto. Qed.

Lemma aeq_agent_sym : ∀ A A', A =Ag= A' → A' =Ag= A.
Proof. intros. intros; destructA A; destructA A'; inversion H;
    constructor; rewrite H2; reflexivity. Qed.

Lemma aeq_agent_swap_indep : ∀ a b A, a≠b →
  b `notin` fn_agent A → a `notin` fn_agent A →
  (swap_ag a b A) =Ag= A.
Proof. intros; destructA A; simpl in *; constructor;
    try apply aeq_swap_indep; auto. fold_swap_c.
    apply aeq_conc_swap_indep; auto. Qed.

Lemma aeq_agent_trans : ∀ A0 A1 A2,
    A0 =Ag= A1 → A1 =Ag= A2 → A0 =Ag= A2.
Proof. intros; destructA A0; destructA A1; destructA A2;
    inversion H; inversion H0; constructor; rewrite H3; auto. Qed.


Add Parametric Relation : agent aeq_agent
    reflexivity proved by (aeq_agent_refl)
    symmetry proved by (aeq_agent_sym)
    transitivity proved by (aeq_agent_trans)
      as aeq_agent_eq_rel.

Add Parametric Morphism : (fn_agent)
    with signature (aeq_agent) ==> (Equal)
      as fn_agent_morphism.
Proof. intros. apply aeq_agent_fn; auto. Qed.

Add Parametric Morphism b c : (swap_ag b c)
    with signature (aeq_agent) ==> (aeq_agent)
      as swap_agent_morphism.
Proof. intros. apply aeq_agent_swap; auto. Qed.

Add Parametric Morphism : (ag_proc)
    with signature (aeq) ==> (aeq_agent)
      as ag_proc_morphism.
Proof. intros. constructor; auto. Qed.

Add Parametric Morphism : (ag_abs)
    with signature (aeq) ==> (aeq_agent)
      as ag_abs_morphism.
Proof. intros. constructor; auto. Qed.

Add Parametric Morphism : (ag_conc)
    with signature (aeq_conc) ==> (aeq_agent)
      as ag_conc_morphism.
Proof. intros. constructor; auto. Qed.


Lemma conc_convert_wf : ∀ C M, conc_wf C → conc_wf (conc_convert C M).
Proof. intros. destruct C as [L P Q]. unfold conc_wf in *; simpl in ×.
  destruct H. gen L M P Q. induction L; intros; simpl in *; auto.
  assert (a `in` fn P) by fsetdec. inversion H; subst.
  assert (list_to_fs L [<=] fn P) by fsetdec.
  destruct conc_convert_aux eqn:?. forwards: IHL H5 H2. rewrite Heqc in H3.
  destruct H3. case_if.
  - destruct atom_fresh. simpl. split.
    + constructor; auto. intro. rewrite list_to_fs_2 in H7. fsetdec.
    + assert (a `notin` list_to_fs l). { forwards: fn_conc_convert_0' Heqc. fsetdec. }
      rewrite fn_swap_fs. intro. destruct(a0==x); destruct (a0==a); subst;
      [ fsetdec | | fsetdec | ].
    × intros _. simpl_swap_fs. forwards: fn_conc_convert_1 Heqc.
      rewrite list_to_fs_2 in H4. clears x p0 H0 H2 H3 H6. fsetdec.
    × intro. assert (a0 `in` list_to_fs l) by fsetdec.
      simpl_swap_fs. simpl_swap_aux.
  - split.
    + constructor; auto. intro. rewrite list_to_fs_2 in H7.
      forwards: fn_conc_convert_0 Heqc a; auto.
    + simpl. enough (a `in` fn p) by fsetdec.
      enough (a `in` diff (fn p) (list_to_fs l)) by fsetdec.
      rewrites <- (>>fn_conc_convert_1 Heqc).
      rewrite list_to_fs_2 in H4. fsetdec.
Qed.

Lemma swap_conc_wf : ∀ b c C, conc_wf C → conc_wf (swap_c b c C).
Proof. intros. destruct C as [L P Q]. induction L.
  - simpl. intuition. constructor.
  - simpl in ×. destruct H. inversion H; subst. split; simpl_swap.
    constructor. rewrite list_to_fs_2. rewrite list_to_fs_2 in H3. simpl_swap.
    apply (NoDup_swap_fs b c). simpl_swap.
Qed.

Lemma aeq_conc_wf : ∀ C C', C =Ac= C' → conc_wf C → conc_wf C'.
Proof. intros. destruct C as [L P Q]; destruct C' as [L' P' Q'].
  induction H; default_simp.
  - split; [constructor|fsetdec].
  - forwards: IHaeq_conc. split; auto; fsetdec. default_simp.
    rewrite list_to_fs_2 in H4. forwards: fn_aeq_conc_1 H.
    split; try fsetdec. constructor; auto.
    intro. rewrite list_to_fs_2 in H6. fsetdec.
  - forwards: IHaeq_conc. split; auto; fsetdec. clear IHaeq_conc. default_simp.
    forwards: fn_aeq_conc_1 H2. apply NoDup_swap_fs in H3.
    assert (b `in` fn P0) by fsetdec. rewrite list_to_fs_2 in H6.
    simpl_swap in H0 H5. assert (b `in` swap_fs b c
    (diff (fn P'0) (list_to_fs L'0))) by fsetdec. simpl_swap in H9. split.
    + constructor; auto. rewrite list_to_fs_2. clears b. fsetdec.
    + clears b. fsetdec.
Qed.

Lemma conc_new_wf : ∀ x C, conc_wf C → conc_wf (conc_new x C).
Proof. intros. unfold conc_new. destruct conc_convert eqn:?.
  assert (conc_wf (conc_def l p p0)). { rewrite <- Heqc. apply conc_convert_wf; auto. }
  case_if.
  - destruct C as [L P Q]. simpls. unfold conc_wf in *; intuition. constructor.
    forwards: fn_conc_convert_0' Heqc. rewrite list_to_fs_2. fsetdec. auto.
  - unfold conc_wf in *; intuition.
Qed.

Lemma conc_parl_wf : ∀ C P, conc_wf C → conc_wf (conc_parl C P).
Proof. intros. unfold conc_parl. destruct conc_convert eqn:?.
  assert (conc_wf (conc_def l p p0)).
    { rewrite <- Heqc. apply conc_convert_wf; auto. }
  unfold conc_wf in *; intuition.
Qed.

Lemma conc_parr_wf : ∀ C P, conc_wf C → conc_wf (conc_parr P C).
Proof. intros. unfold conc_parr. destruct conc_convert eqn:?.
  assert (conc_wf (conc_def l p p0)).
    { rewrite <- Heqc. apply conc_convert_wf; auto. }
  unfold conc_wf in *; intuition.
Qed.

Hint Extern 1 (conc_wf (conc_new ?x ?C)) ⇒ apply conc_new_wf.
Hint Extern 1 (conc_wf (conc_parl ?C ?P)) ⇒ apply conc_parl_wf.
Hint Extern 1 (conc_wf (conc_parr ?P ?C)) ⇒ apply conc_parr_wf.
Hint Extern 1 (conc_wf (swap_c ?b ?c ?C)) ⇒ apply swap_conc_wf.
Hint Extern 2 (conc_wf (conc_def (swap_list ?b ?c ?L) (swap ?b ?c ?P) (swap ?b ?c ?Q)))
    ⇒ fold_swap_c; apply swap_conc_wf.
Hint Extern 1 (conc_wf (conc_convert ?C ?M)) ⇒ apply conc_convert_wf.

Lemma lts_conc_wf : ∀ P l (C:conc), lts P l C → conc_wf C.
Proof. intros. gen_eq: (ag_conc C) as A. gen C.
  induction H; introv HC; try destructA A; inverts HC; auto.
  unfold conc_wf. split. constructor. fsetdec.
Qed.

Hint Extern 3 (conc_wf ?C) ⇒ eapply lts_conc_wf; eauto.
Hint Extern 4 (conc_wf ?C) ⇒
  match goal with
  | H : ?C1 =Ac= ?C |- _ ⇒ apply (aeq_conc_wf C1 C)
  | H : ?C =Ac= ?C1 |- _ ⇒ symmetry in H; apply (aeq_conc_wf C1 C)
  end.



Lemma morphism_aeq_conc_parl_indep : ∀ L L' P P' Q Q' R R',
  R =A= R' → conc_def L P Q =Ac= conc_def L' P' Q' →
  inter (list_to_fs L) (fn R) [=] empty →
  inter (list_to_fs L') (fn R) [=] empty →
  conc_def L P (Q//R) =Ac= conc_def L' P' (Q'//R').
Proof. induction L; intros; simpl; inversion H0; subst; simpl in ×.
  - constructor. auto. rewrite H9. rewrite H. reflexivity.
  - constructor. apply IHL; auto; fsetdec.
  - constructor. auto. simpl. clear H0 H2 H6 H12. rewrite <- H. fsetdec.
    assert (R =A= swap a c R). { symmetry. apply aeq_swap_indep. auto.
        clears a. fsetdec. clears c. fsetdec. } rewrite H3.
    simpl. apply IHL; auto.
    + simpl_swap.
    + rewrite <- H3. clears c H11; fsetdec.
    + simpl_swap. clears a; fsetdec.
Qed.

Lemma aeq_conc_parl : ∀ C C' R R', C =Ac= C' → R =A= R' →
    conc_parl C R =Ac= conc_parl C' R'.
Proof. intros. unfold conc_parl.
  destruct conc_convert eqn:?. destruct (conc_convert C') eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. destruct C' as [L' P' Q'].
  forwards: fn_conc_convert_0'. exact Heqc.
  forwards: fn_conc_convert_0'. exact Heqc0.
  rewrite fold_conc_convert in ×.
  apply morphism_aeq_conc_parl_indep; auto.
  + rewrite <- Heqc. rewrite <- Heqc0.
  repeat rewrite <- aeq_conc_convert. auto.
  + rewrite (aeq_fn _ R R'); auto.
Qed.

Lemma swap_conc_parl : ∀ b c C R,
    swap_c b c (conc_parl C R) =Ac= conc_parl (swap_c b c C) (swap b c R).
Proof. intros. unfold conc_parl.
  destruct conc_convert eqn:?. destruct (conc_convert (swap_c b c C)) eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. simpls.
  forwards: fn_conc_convert_0'. exact Heqc0.
  forwards: fn_conc_convert_0'. exact Heqc1.
  rewrite fold_conc_convert in ×. fold_swap_c.
  apply morphism_aeq_conc_parl_indep; auto; simpl_swap.
  rewrite <- Heqc0. rewrite <- Heqc1.
  repeat rewrite <- aeq_conc_convert. reflexivity.
Qed.

Add Parametric Morphism : (conc_parl)
    with signature (aeq_conc) ==> (aeq) ==> (aeq_conc)
      as conc_parl_morphism.
Proof. intros. apply aeq_conc_parl; auto. Qed.


Lemma morphism_aeq_conc_parr_indep : ∀ L L' P P' Q Q' R R',
  R =A= R' → conc_def L P Q =Ac= conc_def L' P' Q' →
  inter (list_to_fs L) (fn R) [=] empty →
  inter (list_to_fs L') (fn R) [=] empty →
  conc_def L P (R//Q) =Ac= conc_def L' P' (R'//Q').
Proof. induction L; intros; simpl; inversion H0; subst; simpl in ×.
  - constructor. auto. rewrite H9. rewrite H. reflexivity.
  - constructor. apply IHL; auto; fsetdec.
  - constructor. auto. simpl. clear H0 H2 H6 H12. rewrite <- H. fsetdec.
    assert (R =A= swap a c R). { symmetry. apply aeq_swap_indep. auto.
        clears a. fsetdec. clears c. fsetdec. } rewrite H3.
    simpl. apply IHL; auto.
    + simpl_swap.
    + rewrite <- H3. clears c H11. fsetdec.
    + simpl_swap. clears a; fsetdec.
Qed.

Lemma aeq_conc_parr : ∀ C C' R R', C =Ac= C' → R =A= R' →
    conc_parr R C =Ac= conc_parr R' C'.
Proof. intros. unfold conc_parr.
  destruct conc_convert eqn:?. destruct (conc_convert C') eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. destruct C' as [L' P' Q'].
  forwards: fn_conc_convert_0'. exact Heqc.
  forwards: fn_conc_convert_0'. exact Heqc0.
  rewrite fold_conc_convert in ×.
  apply morphism_aeq_conc_parr_indep; auto.
  + rewrite <- Heqc. rewrite <- Heqc0.
  repeat rewrite <- aeq_conc_convert. auto.
  + rewrite (aeq_fn _ R R'); auto.
Qed.

Lemma swap_conc_parr : ∀ b c C R,
    swap_c b c (conc_parr R C) =Ac= conc_parr (swap b c R) (swap_c b c C).
Proof. intros. unfold conc_parr.
  destruct conc_convert eqn:?. destruct (conc_convert (swap_c b c C)) eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. simpls.
  forwards: fn_conc_convert_0'. exact Heqc0.
  forwards: fn_conc_convert_0'. exact Heqc1.
  rewrite fold_conc_convert in ×. fold_swap_c.
  apply morphism_aeq_conc_parr_indep; auto; simpl_swap.
  rewrite <- Heqc0. rewrite <- Heqc1.
  repeat rewrite <- aeq_conc_convert. reflexivity.
Qed.

Add Parametric Morphism : (conc_parr)
    with signature (aeq) ==> (aeq_conc) ==> (aeq_conc)
      as conc_parr_morphism.
Proof. intros. apply aeq_conc_parr; auto. Qed.


Lemma morphism_aeq_appr_indep : ∀ L L' P P' Q Q' (F F':proc1),
  F =A= F' → conc_def L P Q =Ac= conc_def L' P' Q' →
  inter (list_to_fs L) (fn F) [=] empty →
  inter (list_to_fs L') (fn F) [=] empty →
  genNu L (subst F P// Q) =A= genNu L' (subst F' P'// Q').
Proof. induction L; intros; simpl; inversion H0; subst; simpl in ×.
  - rewrite H9. rewrite H. rewrite H6. reflexivity.
  - constructor. apply IHL; auto; fsetdec.
  - constructor. auto. rewrite fn_genNu. simpl. clear H0 H2 H6 H12.
    rewrite fn_subst. rewrite <- H. fsetdec.
    assert (F =A= swap a c F). { symmetry. apply aeq_swap_indep. auto.
        clears a; fsetdec. clears c; fsetdec. } rewrite H3.
    rewrite swap_genNu. simpl. rewrite swap_subst. apply IHL; auto.
    + simpl_swap.
    + rewrite <- H3. clears c H11; fsetdec.
    + simpl_swap. clears a; fsetdec.
Qed.

Lemma aeq_appr : ∀ F F' C C', F =A= F' → C =Ac= C' →
    appr F C =A= appr F' C'.
Proof. intros. unfold appr.
  destruct conc_convert eqn:?. destruct (conc_convert C') eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. destruct C' as [L' P' Q'].
  forwards: fn_conc_convert_0'. exact Heqc.
  forwards: fn_conc_convert_0'. exact Heqc0.
  rewrite fold_conc_convert in ×.
  apply morphism_aeq_appr_indep; auto.
  + rewrite <- Heqc. rewrite <- Heqc0.
    repeat rewrite <- aeq_conc_convert. auto.
  + rewrite H. auto.
Qed.

Add Parametric Morphism : (appr)
    with signature (aeq) ==> (aeq_conc) ==> (aeq)
      as appr_morphism.
Proof. intros. apply aeq_appr; auto. Qed.

Lemma swap_appr : ∀ F C b c,
    swap b c (appr F C) =A= appr (swap b c F) (swap_c b c C).
Proof. intros. unfold appr.
  destruct conc_convert eqn:?. destruct (conc_convert (swap_c b c C)) eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. simpls.
  forwards: fn_conc_convert_0'. exact Heqc0.
  forwards: fn_conc_convert_0'. exact Heqc1.
  rewrite fold_conc_convert in ×. fold_swap_c.
  rewrite swap_genNu. simpl. rewrite swap_subst.
  apply morphism_aeq_appr_indep; auto; simpl_swap.
  rewrite <- Heqc0. rewrite <- Heqc1.
  repeat rewrite <- aeq_conc_convert. reflexivity.
Qed.


Lemma morphism_aeq_appl_indep : ∀ L L' P P' Q Q' (F F':proc1),
  F =A= F' → conc_def L P Q =Ac= conc_def L' P' Q' →
  inter (list_to_fs L) (fn F) [=] empty →
  inter (list_to_fs L') (fn F) [=] empty →
  genNu L (Q // subst F P) =A= genNu L' (Q' // subst F' P').
Proof. induction L; intros; simpl; inversion H0; subst; simpl in ×.
  - rewrite H9. rewrite H. rewrite H6. reflexivity.
  - constructor. apply IHL; auto; fsetdec.
  - constructor. auto. rewrite fn_genNu. simpl. clear H0 H2 H6 H12.
    rewrite fn_subst. rewrite <- H. fsetdec.
    assert (F =A= swap a c F). { symmetry. apply aeq_swap_indep. auto.
        clears a. fsetdec. clears c. fsetdec. } rewrite H3.
    rewrite swap_genNu. simpl. rewrite swap_subst. apply IHL; auto.
    + simpl_swap.
    + rewrite <- H3. clears c H11. fsetdec.
    + simpl_swap. clears a; fsetdec.
Qed.

Lemma aeq_appl : ∀ F F' C C', F =A= F' → C =Ac= C' →
    appl C F =A= appl C' F'.
Proof. intros. unfold appl.
  destruct conc_convert eqn:?. destruct (conc_convert C') eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. destruct C' as [L' P' Q'].
  forwards: fn_conc_convert_0'. exact Heqc.
  forwards: fn_conc_convert_0'. exact Heqc0.
  rewrite fold_conc_convert in ×.
  apply morphism_aeq_appl_indep; auto.
  + rewrite <- Heqc. rewrite <- Heqc0.
    repeat rewrite <- aeq_conc_convert. auto.
  + rewrite H. auto.
Qed.

Add Parametric Morphism : (appl)
    with signature (aeq_conc) ==> (aeq) ==> (aeq)
      as appl_morphism.
Proof. intros. apply aeq_appl; auto. Qed.

Lemma swap_appl : ∀ F C b c,
    swap b c (appl C F) =A= appl (swap_c b c C) (swap b c F).
Proof. intros. unfold appl.
  destruct conc_convert eqn:?. destruct (conc_convert (swap_c b c C)) eqn:?.
  unfold conc_convert in ×. destruct C as [L P Q]. simpls.
  forwards: fn_conc_convert_0'. exact Heqc0.
  forwards: fn_conc_convert_0'. exact Heqc1.
  rewrite fold_conc_convert in ×. fold_swap_c.
  rewrite swap_genNu. simpl. rewrite swap_subst.
  apply morphism_aeq_appl_indep; auto; simpl_swap.
  rewrite <- Heqc0. rewrite <- Heqc1.
  repeat rewrite <- aeq_conc_convert. reflexivity.
Qed.


Lemma aeq_swap_new_aux : ∀ L P Q L' P' Q' a,
    a `notin` (list_to_fs L) → a `notin` (list_to_fs L') →
    conc_def L P Q =Ac= conc_def L' P' Q' →
    conc_def L P (nu a, Q) =Ac= conc_def L' P' (nu a, Q').
Proof. induction L; introv n1 n2 H; inversion H; subst; simpl in ×.
  - constructor. auto. constructor; auto.
  - constructor. apply IHL; auto.
  - constructor. auto. simpl. fsetdec.
    simpl. assert (a≠a0) by fsetdec. assert (c≠a0) by fsetdec.
    rewrites (>>IHL H9); simpl_swap; simpl; simpl_swap_aux. reflexivity.
Qed.

Lemma swap_conc_new : ∀ C a b c,
    swap_c b c (conc_new a C) =Ac= conc_new (swap_aux b c a) (swap_c b c C).
Proof. intros. unfold conc_new. destruct conc_convert eqn:?.
  destruct (conc_convert _ {{(swap_aux b c a)}}) eqn:?.
  forwards*: aeq_conc_convert (swap_c b c C) (singleton (swap_aux b c a)).
  rewrite Heqc1 in H. destruct C as [L P Q]; simpls.
  assert (a `notin` list_to_fs l). { forwards: fn_conc_convert_0' Heqc0. fsetdec. }
  assert (swap_aux b c a `notin` list_to_fs l0). { forwards: fn_conc_convert_0' Heqc1.
  fsetdec. } forwards: fn_conc_convert_1 Heqc1. simpl_swap in H2.
  rewrites (>> fn_conc_convert_1 Heqc0) in H2.
  assert (a `in` fn p ↔ swap_aux b c a `in` fn p1).
  { split; intros.
    - assert (a `in` diff (fn p) (list_to_fs l)) by fsetdec.
      apply (swap_fs_1 _ b c) in H4. rewrite H2 in H4. fsetdec.
    - enough (a `in` diff (fn p) (list_to_fs l)) by fsetdec.
      apply (swap_fs_1' _ b c). rewrite H2. fsetdec. } clear H2.
  repeat case_if; try solve [rewrite H3 in C; contradiction].
  - default_simp. constructor. fold_swap_c. rewrite <- Heqc0.
    fold_conc_convert. repeat rewrite <- aeq_conc_convert. auto.
  - forwards: aeq_conc_convert (conc_def L P Q) {{a}}. simpl in H2. rewrite Heqc0 in H2.
    fold_swap_c. rewrite H2 in H. simpl in ×. apply aeq_swap_new_aux; auto; simpl_swap.
Qed.

Lemma swap_new : ∀ A a b c,
    swap_ag b c (new a A) =Ag= new (swap_aux b c a) (swap_ag b c A).
Proof. intros. destructA A; try reflexivity. constructor. apply swap_conc_new. Qed.

Lemma aeq_conc_new : ∀ C C' a, C =Ac= C' → conc_new a C =Ac= conc_new a C'.
Proof. intros. destruct C; destruct C'. unfold conc_new.
  destruct conc_convert eqn:?. destruct (conc_convert (conc_def l0 p1 p2)) eqn:?.
  forwards: aeq_conc_convert. rewrite Heqc in H0.
  forwards: aeq_conc_convert. rewrite Heqc0 in H1.
  rewrite H in H0. rewrite H0 in H1.
  forwards: fn_conc_convert_0' Heqc. forwards: fn_conc_convert_0' Heqc0.
  clears l l0. assert (a `in` fn p3 ↔ a `in` fn p5).
  { forwards: fn_aeq_conc_1 H1. fsetdec. }
  repeat case_if; try solve [rewrite H in C; contradiction].
    2:apply aeq_swap_new_aux; try fsetdec. constructor. all:auto.
Qed.

Add Parametric Morphism a : (conc_new a)
    with signature (aeq_conc) ==> (aeq_conc)
      as conc_new_morphism.
Proof. intros. apply aeq_conc_new; auto. Qed.

Lemma aeq_new : ∀ A A' a, A =Ag= A' → new a A =Ag= new a A'.
Proof. intros. destructA A; destructA A'; inversion H; simpl; constructor;
  rewrite H2; reflexivity. Qed.

Add Parametric Morphism a : (new a)
    with signature (aeq_agent) ==> (aeq_agent)
      as new_morphism.
Proof. intros. apply aeq_new; auto. Qed.

Lemma aeq_conc_new_2 : ∀ (C:conc) a c,
    c `notin` fn_agent (C) → a≠c →
    conc_new a C =Ac= conc_new c (swap_c a c C).
Proof. intros. rewrite <- (swap_aux_l a c) at 1. rewrite <- swap_conc_new.
  symmetry. apply aeq_conc_swap_indep; auto; rewrite fn_conc_new; fsetdec. Qed.

Lemma aeq_new_2 : ∀ A A' a c, A =Ag= A' →
    c `notin` fn_agent A' → a≠c →
    new a A =Ag= new c (swap_ag a c A').
Proof. intros. rewrite H. clears A. destructA A'; simpl in *;
  constructor; try solve [constructor; auto; simpl_swap].
  apply aeq_conc_new_2; auto.
Qed.


Lemma aeq_parl : ∀ A A' Q Q', A =Ag=A' → Q =A= Q' →
    parl A Q =Ag= parl A' Q'.
Proof. intros. destructA A; destructA A'; inversion H; simpl;
  try solve [constructor; rewrite H0; rewrite H3; reflexivity].
Qed.

Add Parametric Morphism : (parl)
    with signature (aeq_agent) ==> (@aeq Empty_set) ==> (aeq_agent)
      as parl_morphism.
Proof. intros. apply aeq_parl; auto. Qed.

Lemma swap_parl : ∀ A Q b c,
    swap_ag b c (parl A Q) =Ag= parl (swap_ag b c A) (swap b c Q).
Proof. intros. destructA A; unfold parl; simpl in ×.
  - reflexivity.
  - rewrite swap_shiftV. reflexivity.
  - fold_swap_c. apply ag_conc_morphism. apply swap_conc_parl.
Qed.

Lemma aeq_parr : ∀ A A' Q Q', A =Ag=A' → Q =A= Q' →
    parr Q A =Ag= parr Q' A'.
Proof. intros. destructA A; destructA A'; inversion H; simpl;
  try solve [constructor; rewrite H0; rewrite H3; reflexivity].
Qed.

Add Parametric Morphism : (parr)
    with signature (@aeq Empty_set) ==> (aeq_agent) ==> (aeq_agent)
      as parr_morphism.
Proof. intros. apply aeq_parr; auto. Qed.

Lemma swap_parr : ∀ A Q b c,
    swap_ag b c (parr Q A) =Ag= parr (swap b c Q) (swap_ag b c A).
Proof. intros. destructA A; unfold parl; simpl in ×.
  - reflexivity.
  - rewrite swap_shiftV. reflexivity.
  - fold_swap_c. constructor. apply swap_conc_parr.
Qed.


Lemma swap_lts : ∀ P l A b c, lts P l A →
    ∃ A', A' =Ag= (swap_ag b c A) ∧ lts (swap b c P) (swap_lab b c l) A'.
Proof. introv Hlts. induction Hlts;
  try solve [eexists; split; [reflexivity| simpl; constructor]].
  - destruct IHHlts as [A0 []]. ∃ (parl A0 (swap b c Q)).
    rewrite swap_parl. simpl. split.
    + rewrite H. reflexivity.
    + constructor. auto.
  - destruct IHHlts as [A0 []]. ∃ (parr (swap b c Q) A0).
    rewrite swap_parr. simpl. split.
    + rewrite H. reflexivity.
    + constructor. auto.
  - destruct IHHlts as [A0 []]. simpl. ∃ (new (swap_aux b c a) A0). split.
    + rewrite swap_new. rewrite H0. reflexivity.
    + constructor. simpl_swap. auto.
  - destruct IHHlts1 as [A0 []]. destruct IHHlts2 as [A1 []]. simpl.
    inversion H. subst A0. inversion H1. subst A1. subst.
    ∃ (ag_proc (appl C0 P0)). split.
    + rewrite swap_appl. rewrite H5. rewrite H7. reflexivity.
    + simpl in ×. constructor 6 with (swap_aux b c a); auto.
  - destruct IHHlts1 as [A0 []]. destruct IHHlts2 as [A1 []]. simpl.
    inversion H1. subst A1. inversion H. subst A0. subst.
    ∃ (ag_proc (appr P0 C0)). split.
    + rewrite swap_appr. rewrite H5. rewrite H7. reflexivity.
    + simpl in ×. constructor 7 with (swap_aux b c a); auto.
Qed.

Lemma aeq_lts : ∀ V (P P' : proc V) (f : V → Empty_set) l A,
    P =A= P' → lts (mapV f P) l A →
    ∃ A', A =Ag= A' ∧ lts (mapV f P') l A'.
Proof. intros V' P''. apply size_induction with (x:=P''). intros V P.
  introv IH aeq Hlts. inversion aeq; subst; inversion Hlts; subst; simpls.
  - eexists. split. constructor. rewrite H. reflexivity. constructor.
  - eexists. split. constructor. rewrite H. rewrite H0. reflexivity. constructor.
  - forwards: IH P1 H H5. nat_math. destruct H1 as [A7 []].
    ∃ (parl A7 (mapV f Q2)). split.
    + rewrite H0. rewrite H1. reflexivity.
    + constructor. auto.
  - forwards: IH P2 H0 H5. nat_math. destruct H1 as [A7 []].
    ∃ (parr (mapV f Q1) A7). split.
    + rewrite H. rewrite H1. reflexivity.
    + constructor 4. auto.
  - forwards: IH P1 H H3. nat_math. destruct H1 as [C7 []].
    forwards: IH P2 H0 H6. nat_math. destruct H4 as [Q7 []].
    inversion H1; inversion H4; subst.
    ∃ (ag_proc (appl C' Q)). split.
    + rewrite H8. rewrite H11. reflexivity.
    + constructor 6 with a; auto.
  - forwards: IH P1 H H3. nat_math. destruct H1 as [C7 []].
    forwards: IH P2 H0 H6. nat_math. destruct H4 as [Q7 []].
    inversion H1; inversion H4; subst.
    ∃ (ag_proc (appr Q C')). split.
    + rewrite H8. rewrite H11. reflexivity.
    + constructor 7 with a; auto.
  - forwards: IH P0 H H5. nat_math. destruct H0 as [A7 []].
    ∃ (new a A7). split.
    + rewrite H0. reflexivity.
    + constructor; auto.
  - forwards: swap_lts b c H7. destruct H2 as [A6 []].
    apply (aeq_swap _ b c) in H1. rewrite swap_invo in H1.
    forwards: IH (swap b c P0) H1. rewrite swap_size_eq. nat_math.
    rewrite swap_mapV in H3. exact H3. destruct H5 as [A7 []].
    ∃ (new c A7). split.
    + assert (b `notin` fn_agent A7). { rewrites (>>lts_fn H6). simpl_swap. }
      rewrite (aeq_new_2 A7 A7 c b); auto; try reflexivity.
      rewrite <- H5. rewrite H2. rewrite swap_ag_sym. simpl_swap.
    + asserts_rewrite (l = swap_lab b c l).
        { symmetry. apply swap_lab_notin; auto. rewrite (swap_lab_in_iff b c).
          apply notin_fn_notin_fnlab with (mapV f Q) A7; auto. simpl_swap. }
      constructor; simpl_swap.
Qed.

Lemma aeq_lts_2 : ∀ (P P' : proc0) l A,
    P =A= P' → lts P l A → ∃ A', A =Ag= A' ∧ lts P' l A'.
Proof. intros.
  asserts_rewrite (P = mapV (fun x ⇒ x) P) in H0. symmetry; apply mapV_id.
  asserts_rewrite (P' = mapV (fun x ⇒ x) P'). symmetry; apply mapV_id.
  forwards: aeq_lts H H0. destruct H1. ∃ x; intuition.
Qed.
