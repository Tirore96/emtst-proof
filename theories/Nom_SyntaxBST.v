(* The Send Receive System. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Equations.Equations.
From SendRec Require  Nom_Swap_fs.
Require Import Coq.ssr.ssreflect.
Require Import Lia.
Require Import PP.Ppsimplmathcomp.
Require Import Equations.Equations.
Require Import SendRec.Atom.

Inductive sort : Set :=
  | boole : sort (* boolean expression *)
  | end_points : tp -> tp -> sort
with tp : Set :=
  | input : sort -> tp -> tp
  | output : sort -> tp -> tp
  | ch_input : tp -> tp -> tp
  | ch_output : tp -> tp -> tp
  | offer_branch : tp -> tp -> tp
  | take_branch : tp -> tp -> tp
  | ended : tp
  | bot : tp
.

Scheme tp_sort := Induction for tp Sort Prop
  with sort_tp := Induction for sort Sort Prop. (* Minimality *)
Combined Scheme tp_sort_mutind from tp_sort, sort_tp.

Fixpoint dual (T : tp) : tp :=
  match T with
  | input s T => output s (dual T)
  | output s T => input s (dual T)
  | ch_input T T' => ch_output T (dual T')
  | ch_output T T' => ch_input T (dual T')
  | offer_branch T T' => take_branch (dual T) (dual T')
  | take_branch T T' => offer_branch (dual T) (dual T')
  | ended => ended
  | bot => bot
  end
.

Lemma dual_is_dual t : dual (dual t) = t.
  elim t=>// ; rewrite/dual ; move=>//; rewrite-/dual ;
    do ? (move=> s t0 =>->) ;
    do ? (move=> t0 R' t1 =>->) ;
    rewrite ?R' ;
   easy.
Qed.

Lemma double_dual t: t = dual(dual t).
Proof.
  elim t=>//; rewrite/dual=>//; rewrite-/dual ; congruence.
Qed.

Fixpoint eq_tp (T T': tp) : bool :=
  match T, T' with
  | input s T, input s' T' => eq_sort s s' && eq_tp T T'
  | output s T, output s' T' => eq_sort s s' && eq_tp T T'
  | ch_input T1 T2, ch_input T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ch_output T1 T2, ch_output T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'

  | offer_branch T1 T2, offer_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | take_branch T1 T2, take_branch T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | ended, ended => true
  | bot, bot => true
  | _, _ => false
  end
with eq_sort (s s' : sort) : bool :=
  match s, s' with
  | boole, boole => true
  | end_points T1 T2, end_points T1' T2' => eq_tp T1 T1' && eq_tp T2 T2'
  | _, _ => false
  end.

Lemma eq_imp_eq : (forall x y, eq_tp x y -> x = y) /\ forall s s', eq_sort s s' -> s = s'.
Proof.
  apply tp_sort_mutind ; intros; try destruct y  ; try destruct s'; try easy ;
  inversion H1 ; apply Bool.andb_true_iff in H3 ; destruct H3 ;
  try(move:H3 ; move/H0=>H3 ; move:H2 ; move/H=>H4 ; by rewrite H3 H4).
Qed.

Lemma eq_tp_refl x : eq_tp x x.
Proof.
  by elim x using tp_sort with (P:=fun x=>eq_tp x x) (P0:= fun s=>eq_sort s s)=>//;
     move=>s H t H0; simpl; rewrite H H0.
Qed.

Lemma eq_sort_refl s : eq_sort s s.
Proof.
  by elim s using sort_tp with (P:=fun x=> eq_tp x x)=>//;
     move=>x H t H0; simpl; rewrite H H0.
Qed.

Lemma eq_tpP : Equality.axiom eq_tp.
Proof.
  move=>x y.
  apply: (iffP idP)=>[|<-].
  apply eq_imp_eq.
  apply eq_tp_refl.
Qed.

Lemma eq_sortP : Equality.axiom eq_sort.
Proof.
  move=>x y.
  apply: (iffP idP)=>[|<-].
  apply eq_imp_eq.
  apply eq_sort_refl.
Qed.

Canonical tp_eqMixin := EqMixin eq_tpP.
Canonical tp_eqType := Eval hnf in EqType tp tp_eqMixin.

Canonical sort_eqMixin := EqMixin eq_sortP.
Canonical sort_eqType := Eval hnf in EqType sort sort_eqMixin.

Inductive exp : Set :=
  | tt
  | ff
  | var : atom -> exp
.

Definition eq_atom := Atom.eq_atom.
Definition exp_eqb e0 e1 : bool :=
match (e0,e1) with
| (tt,tt) => true
| (ff,ff) => true
| (var nm0,var nm1) => eq_atom nm0 nm1
| _ => false
end.


Inductive proc : Set :=
| send : atom -> exp -> proc -> proc
| receive : atom -> atom -> proc -> proc


| throw : atom -> atom -> proc -> proc
| catch : atom -> atom  -> proc -> proc

| par : proc -> proc -> proc
| inact : proc
| nu_ch : atom -> proc -> proc
.

Notation "k ![ e ] ; p0" := (send k e p0)(at level 70) .
Notation "k ? ( x ) 'in' p0" := (receive k x p0)(at level 70) .


Notation "p0 |||| p1" := (par p0 p1)(at level 81, left associativity) .

Fixpoint proc_eqb p0 p1 := 
match p0,p1 with
| (send a0 e0 p0'),(send a1 e1 p1') => eq_atom a0 a1 && exp_eqb e0 e1 && proc_eqb p0' p1'
| (receive a0 a0' p0'),(receive a1 a1' p1') => eq_atom a0 a1 && eq_atom a0' a1' && proc_eqb p0' p1'
| (throw a0 a0' p0'),(throw a1 a1' p1') => eq_atom a0 a1 && eq_atom a0' a1' && proc_eqb p0' p1'
| (catch a0 a0' p0'),(catch a1 a1' p1') => eq_atom a0 a1 && eq_atom a0' a1' && proc_eqb p0' p1'
| (par p0' p0''),(par p1' p1'') => proc_eqb p0' p1' && proc_eqb p0'' p1''
| inact,inact => true
| nu_ch nm0 p0', nu_ch nm1 p1' => eq_atom nm0 nm1 && proc_eqb p0' p1'
| _,_ => false 
end.

Definition fv_exp (e : exp) : seq atom  :=
  match e with
    | tt => [::]
    | ff => [::]
    | var a =>  [::a]
  end.

Fixpoint fv (P : proc) : seq atom :=
  match P with
  | send nm e P0 => [::nm] ++ (fv_exp e) ++ (fv P0)
  | receive nm0 nm1 P0 => [::nm0] ++ (filter (predC1 nm1) (fv P0))
  | throw nm0 nm1 P0 => [::nm0; nm1] ++ (fv P0) 
  | catch nm0 nm1 P0 => [::nm0] ++ (filter (predC1 nm1) (fv P0))
  | par P0 P1 => (fv P0) ++ (fv P1)
  | inact => [::]
  | nu_ch nm P0 => filter (predC1 nm) (fv P0)
end.          

Definition swap_aux (b c a : atom) := 
  if (a == b) then c else if (a == c) then b else a.

          
Fixpoint swap_exp (b c : atom) (e: exp) : exp :=
  match e with
  | var nm => var (swap_aux b c nm)
  | t => t
  end.

Fixpoint swap (b c: atom) (P : proc) : proc :=
  match P with
  | send nm e P0 => send (swap_aux b c nm) (swap_exp b c e) (swap b c P0)
  | receive nm0 nm1 P0 => receive (swap_aux b c nm0) (swap_aux b c nm1) (swap b c P0)
  | throw nm0 nm1 P0 => throw (swap_aux b c nm0) (swap_aux b c nm1) (swap b c P0)
  | catch nm0 nm1 P0 => catch (swap_aux b c nm0) (swap_aux b c nm1) (swap b c P0)
  | par P0 P1 => par (swap b c P0) (swap b c P1)
  | inact => inact
  | nu_ch nm P0 => nu_ch (swap_aux b c nm) (swap b c P0)
  end.
Print mem. Locate mem. Check mem_seq.
Definition binder_eq f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if eq_atom nm0 nm1 then f P0 P1
                               else if mem_seq (fv P1) nm0 then false 
                               else f P0 (swap nm0 nm1 P1).


Fixpoint aeq (P0 P1 : proc) : bool :=
let binder_eq := binder_eq aeq in
match P0,P1 with
| (send nm0 e0 P0'), (send nm1 e1 P1') => (eq_atom nm0 nm1) && (exp_eqb e0 e1) && (aeq P0' P1')
| (receive nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (eq_atom nm0 nm1) && (binder_eq (nmb0, P0') (nmb1, P1'))
| (throw nm0 nm0' P0'), (throw nm1 nm1' P1') => (eq_atom nm0 nm1) && (eq_atom nm0' nm1') && (aeq P0' P1')
| (catch nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (eq_atom nm0 nm1) && (binder_eq (nmb0, P0') (nmb1, P1'))
| (nu_ch nm0 P0), (nu_ch nm1 P1) => binder_eq (nm0, P0) (nm1, P1)
| _, _ => false
end.


Reserved Notation "P === Q" (at level 70).
Inductive congruent : proc -> proc -> Prop :=
| c_refl P : P === P
| c_alpha P Q (H: aeq P Q): P === P 
| c_inact P : (par inact P) === P
| c_comm P Q: (par P Q) === (par Q P)
| c_asoc P Q R: (par (par P Q) R) === (par P (par Q R))
| c_nu_ch P Q nm (H: nm \notin (fv Q)) : (par (nu_ch nm P) Q) === (nu_ch nm (par P Q))
| c_nu_ch_inact nm : nu_ch nm inact === inact
where "P === Q" := (congruent P Q).


Fixpoint congruent_fun P Q :=
if proc_eqb P Q then true
else if aeq P Q then true
else match P, Q with
     | (par inact P'),_ => proc_eqb P' Q
     | (par (par P' P'') P'''),(par Q' (par Q'' Q''')) => proc_eqb P' Q' && proc_eqb P'' Q'' && proc_eqb P''' Q''' 
     | (par P' P''),(par Q' Q'') => proc_eqb P' Q'' && proc_eqb P'' Q'
     | (par (nu_ch nm P') P''), (nu_ch nm' (par Q' Q'')) => eq_atom nm nm' && proc_eqb P' Q' && proc_eqb P'' Q'' && (negb (mem_seq (fv P'') nm)) 
     | (nu_ch m inact), inact => true 
     | _, _ => false 
     end.



Definition subst_exp (e : exp) (x : atom) (e_body : exp) : exp :=
  match e_body with
  | var nm => if eq_atom nm x then e else var nm
  | t => t
  end.

Fixpoint proc_size (P : proc) : nat :=
match P with
| send _ _ P0 => 1 + (proc_size P0)
| receive _ _ P0 => 1 + (proc_size P0)
| throw _ _ P0 => 1 + (proc_size P0)
| catch _ _ P0 => 1 + (proc_size P0)
| par P0 P1 => 1 + (proc_size P0) + (proc_size P1)
| inact => 1
| nu_ch _ P0 => 1 + (proc_size P0)
end.

Lemma swap_size : forall a b P, proc_size (swap a b P) = proc_size P.
Proof. 
move=> a b P. elim P;
do ? (move=> a0 e p H0/=//; rewrite H0//).
rewrite e/=//. rewrite /=//.
move => a0 p/= =>->//. 
Qed.

Obligation Tactic := move => *;do ? ((do ? rewrite swap_size); apply : leP; rewrite /=; ppsimpl;lia).

Equations subst_proc_exp (e : exp) (x : atom) (P : proc) : proc by wf (proc_size P)  :=
subst_proc_exp e x (send nm e0 P0) := send nm (subst_exp e x e0) (subst_proc_exp e x P0);
subst_proc_exp e x (receive nm0 nm1 P0) := if eq_atom x nm1 then  (receive nm0 nm1 P0) 
                                                        else receive nm0 (fresh (fv P0 ++ fv_exp e)) (subst_proc_exp e x (swap nm1 (fresh (fv P0 ++ fv_exp e)) P0));
subst_proc_exp e x (throw nm0 nm1 P0) := throw nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (catch nm0 nm1 P0) := catch nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (par P0 P1) := par (subst_proc_exp e x P0) ( subst_proc_exp e x P1);
subst_proc_exp e x inact := inact;
 subst_proc_exp e x (nu_ch nm P0) := nu_ch nm (subst_proc_exp e x P0).


Definition subst_nm (a x nm : atom) : atom :=
if eq_atom x nm then a else nm.


Equations subst_proc_nm (a x: atom)  (P : proc) : proc by wf (proc_size P)  :=
subst_proc_nm a x (send nm e P0) := send (subst_nm a x nm) e (subst_proc_nm a x P0);
subst_proc_nm a x (receive nm0 nm1 P0) := receive (subst_nm a x nm0) nm1 (subst_proc_nm a x P0);
subst_proc_nm a x (throw nm0 nm1 P0) := throw (subst_nm a x nm0) (subst_nm a x nm1) (subst_proc_nm a x P0);
subst_proc_nm a x (catch nm0 nm1 P0) := if eq_atom x nm1 then catch (subst_nm a x nm0) nm1 P0 
                                                         else catch (subst_nm a x nm0) (fresh ([:: a]++ (fv P0))) (subst_proc_nm a x (swap nm1 (fresh ([:: a]++ (fv P0))) P0));
subst_proc_nm a x (par P0 P1) := par (subst_proc_nm a x P0) ( subst_proc_nm a x P1);
subst_proc_nm a x inact := inact;
subst_proc_nm a x (nu_ch nm P0) := if eq_atom x nm then nu_ch nm P0 
                                                   else nu_ch (fresh ([:: a] ++  (fv P0))) (subst_proc_nm a x (swap nm (fresh ([:: a] ++  (fv P0))) P0)).

Reserved Notation "P --> Q" (at level 70).
Inductive red : proc -> proc -> Prop :=
| r_com k e nm P Q:
    (par (send k e P) (receive k nm Q)) --> (par P (subst_proc_exp e nm Q))

| r_pass k k' k'' P Q (H: k' \notin (fv Q)) :
    (par (throw k k' P) (catch k k'' Q)) --> (par P (subst_proc_nm k' k'' Q))

| r_cong P P' Q Q' :
    congruent_fun P P' ->
    P' --> Q' ->
    congruent_fun Q' Q ->
    P --> Q

| r_scop_ch P P' nm (H: P --> P') : nu_ch nm P --> nu_ch nm P'

| r_par P P' Q (H: P --> P') : par P Q --> par P' Q

where "P --> Q" := (red P Q).

(*
Ltac atom_destruct :=
  repeat match goal with
         | [ |- context[Atom.eq_dec ?e ?e0] ] 
                => destruct (Atom.eq_dec e e0);try contradiction
         | [ _ : context[Atom.eq_dec ?e ?e0]  |- _ ] 
                => destruct (Atom.eq_dec e e0);try contradiction
         end.

Ltac atom_unf := rewrite /eqb ; atom_destruct.*)

Definition k0 := fresh [::].
Definition k1 := fresh [::k0].
(*A very simple example*)
Lemma ex1 : (k0![tt];inact |||| k0? (k1) in inact) --> (inact |||| inact).
Proof. eapply r_com. Qed. 

Lemma eq_atom_refl : forall a, eq_atom a a. 
Proof.
move=>a. apply/Atom.eq_reflect. auto. 
Qed.

(*Building on the simple example, instead of P -> inact |||| inact, we now have inact |||| P -> inact.
  Congruence rules must be used on both initial and reduced process before applying r_com.  *)
Lemma ex_cong_comp : (inact |||| (k0![tt]; inact |||| k0? (k1) in inact)) --> inact.
Proof. apply : r_cong. 2: { apply : ex1. } do ? rewrite /= eq_atom_refl //. rewrite /= //. 
Qed.

(*The inductive definition is useful when processes are to be manipulated (eg. change P to inact |||| P),
  the function definition is useful if we are done manipulating and simply want to verify that two
  processes are congruent, given if congruent_fun returns true *)
Lemma congruent_iff : forall P Q, P === Q <-> congruent_fun P Q.
Proof. Admitted.

(*The counter example that breaks subject reduction*)
Lemma counter_ex : forall k0 k1 k2 k3, k1 != k3 -> k1 != k2 -> ((throw k0 k1 inact) |||| (catch k0 k2 (k2? (k3) in (k1![tt]; inact)))) -->
                                    (k1? (k3) in (k1![tt]; inact)).
Proof.
move => k0 k1 k2 k3 H H2. apply : r_cong. rewrite -congruent_iff. apply : c_refl. 2: { rewrite -congruent_iff. apply : c_inact. } apply : r_cong. rewrite -congruent_iff. apply c_refl. apply : r_pass. rewrite /=.  rewrite H. simpl. rewrite inE /=. rewrite /negb /=. rewrite unfold_in. rewrite /=. Search _ (_ ||  false). rewrite Bool.orb_false_r. inversion H2. Search _ ( _ = true -> _ = false). destruct (eqVneq k1 k2). move : H1. rewrite /=. move=>H3. inversion H3. rewrite /=. rewrite eq_refl. 
(*
We are stuck
*)
Abort. 


(*We replace k1 with k2 in the receiving process, that way it does not end up with both sides of the channel*)
Lemma counter_ex_fixed : forall k0 k1 k2 k3, k1!= k2  -> k2 != k3 ->
  ((throw k0 k1 inact) |||| (catch k0 k2 (k2? (k3) in (k2![tt]; inact)))) -->
                                    (k1? (k3) in (k1![tt]; inact)).
Proof.
move => k0 k1 k2 k3 H H2. apply : r_cong. rewrite -congruent_iff. apply : c_refl. 2: { rewrite -congruent_iff. apply : c_inact. } apply : r_cong. rewrite -congruent_iff. apply c_refl. apply : r_pass. rewrite /=. rewrite inE.  
rewrite unfold_in. destruct (eqVneq k1 k2). move : H=> /=. auto. rewrite /=. rewrite H2. rewrite /=. rewrite Bool.orb_false_r. auto.
simp subst_proc_nm. rewrite /=. rewrite /subst_nm. do ? rewrite eq_atom_refl. rewrite /=//. 
Qed.

