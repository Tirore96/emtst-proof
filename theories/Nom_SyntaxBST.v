(* The Send Receive System. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Equations.Equations.
From SendRec Require  Nom_Swap_fs.
Require Import Metalib.Metatheory.
Require Import Coq.ssr.ssreflect.
Require Import Lia.
Require Import PP.Ppsimplmathcomp.
Require Import Equations.Equations.

Definition mem := AtomSetImpl.mem.
Inductive exp : Set :=
  | tt
  | ff
  | var : atom -> exp
.
Definition exp_eqb e0 e1 : bool :=
match (e0,e1) with
| (tt,tt) => true
| (ff,ff) => false 
| (var nm0,var nm1) => eqb nm0 nm1
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
| (send a0 e0 p0'),(send a1 e1 p1') => eqb a0 a1 && exp_eqb e0 e1 && proc_eqb p0' p1'
| (receive a0 a0' p0'),(receive a1 a1' p1') => eqb a0 a1 && eqb a0' a1' && proc_eqb p0' p1'
| (throw a0 a0' p0'),(throw a1 a1' p1') => eqb a0 a1 && eqb a0' a1' && proc_eqb p0' p1'
| (catch a0 a0' p0'),(catch a1 a1' p1') => eqb a0 a1 && eqb a0' a1' && proc_eqb p0' p1'
| (par p0' p0''),(par p1' p1'') => proc_eqb p0' p1' && proc_eqb p0'' p1''
| inact,inact => true
| nu_ch nm0 p0', nu_ch nm1 p1' => eqb nm0 nm1 && proc_eqb p0' p1'
| _,_ => false 
end.

Definition fv_exp (e : exp) : atoms  :=
  match e with
    | tt => {}
    | ff => {}
    | var a =>  {{ a }}
  end.

Fixpoint fv (P : proc) : atoms :=
  match P with
  | send nm e P0 => {{ nm }} `union` (fv_exp e) `union` (fv P0)
  | receive nm0 nm1 P0 => {{ nm0 }} `union` (remove nm1 (fv P0))
  | throw nm0 nm1 P0 => {{ nm0 }} `union` {{ nm1 }} `union` (fv P0)
  | catch nm0 nm1 P0 => {{ nm0 }} `union` (remove nm1 (fv P0))
  | par P0 P1 => (fv P0) `union` (fv P1)
  | inact => {}
  | nu_ch nm P0 => remove nm (fv P0)
end.          

Definition swap_aux := Nom_Swap_fs.swap_aux.
          
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

Definition binder_eq f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if eqb nm0 nm1 then f P0 P1
                               else if AtomSetImpl.mem nm0 (fv P1) then false 
                               else f P0 (swap nm0 nm1 P1).


Fixpoint aeq (P0 P1 : proc) : bool :=
let binder_eq := binder_eq aeq in
match P0,P1 with
| (send nm0 e0 P0'), (send nm1 e1 P1') => (eqb nm0 nm1) && (exp_eqb e0 e1) && (aeq P0' P1')
| (receive nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (eqb nm0 nm1) && (binder_eq (nmb0, P0') (nmb1, P1'))
| (throw nm0 nm0' P0'), (throw nm1 nm1' P1') => (eqb nm0 nm1) && (eqb nm0' nm1') && (aeq P0' P1')
| (catch nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (eqb nm0 nm1) && (binder_eq (nmb0, P0') (nmb1, P1'))
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
     | (par (nu_ch nm P') P''), (nu_ch nm' (par Q' Q'')) => eqb nm nm' && proc_eqb P' Q' && proc_eqb P'' Q'' && (negb (AtomSetImpl.mem nm (fv P''))) 
     | (nu_ch m inact), inact => true 
     | _, _ => false 
     end.



Definition subst_exp (e : exp) (x : atom) (e_body : exp) : exp :=
  match e_body with
  | var nm => if eq_dec nm x then e else var nm
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
subst_proc_exp e x (receive nm0 nm1 P0) := if eqb x nm1 then  (receive nm0 nm1 P0) 
                                                        else let (z,_) := atom_fresh (fv P0 `union`fv_exp e) in
                                                             receive nm0 z (subst_proc_exp e x (swap nm1 z P0));
subst_proc_exp e x (throw nm0 nm1 P0) := throw nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (catch nm0 nm1 P0) := catch nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (par P0 P1) := par (subst_proc_exp e x P0) ( subst_proc_exp e x P1);
subst_proc_exp e x inact := inact;
subst_proc_exp e x (nu_ch nm P0) := nu_ch nm (subst_proc_exp e x P0).



Definition subst_nm (a x nm : atom) : atom :=
if eqb x nm then a else nm.


Equations subst_proc_nm (a x: atom)  (P : proc) : proc by wf (proc_size P)  :=
subst_proc_nm a x (send nm e P0) := send (subst_nm a x nm) e (subst_proc_nm a x P0);
subst_proc_nm a x (receive nm0 nm1 P0) := receive (subst_nm a x nm0) nm1 (subst_proc_nm a x P0);
subst_proc_nm a x (throw nm0 nm1 P0) := throw (subst_nm a x nm0) (subst_nm a x nm1) (subst_proc_nm a x P0);
subst_proc_nm a x (catch nm0 nm1 P0) := if eqb x nm1 then catch (subst_nm a x nm0) nm1 P0 
                                                      else let (z,_) := atom_fresh (add a (fv P0) ) in 
                                                              catch (subst_nm a x nm0) z (subst_proc_nm a x (swap nm1 z P0));
subst_proc_nm a x (par P0 P1) := par (subst_proc_nm a x P0) ( subst_proc_nm a x P1);
subst_proc_nm a x inact := inact;
subst_proc_nm a x (nu_ch nm P0) := if eqb x nm then nu_ch nm P0 
                                                else let (z,_) := atom_fresh (add a (fv P0)) in 
                                                     nu_ch z (subst_proc_nm a x (swap nm z P0)).

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

Ltac atom_destruct :=
  repeat match goal with
         | [ |- context[Atom.eq_dec ?e ?e0] ] 
                => destruct (Atom.eq_dec e e0);try contradiction
         | [ _ : context[Atom.eq_dec ?e ?e0]  |- _ ] 
                => destruct (Atom.eq_dec e e0);try contradiction
         end.

Ltac atom_unf := rewrite /eqb ; atom_destruct.

Definition k0 := fresh [::].
Definition k1 := fresh [::k0].
(*A very simple example*)
Lemma ex1 : (k0![tt];inact |||| k0? (k1) in inact) --> (inact |||| inact).
Proof. eapply r_com. Qed. 

(*Building on the simple example, instead of P -> inact |||| inact, we now have inact |||| P -> inact.
  Congruence rules must be used on both initial and reduced process before applying r_com.  *)
Lemma ex_cong_comp : (inact |||| (k0![tt]; inact |||| k0? (k1) in inact)) --> inact.
Proof. apply : r_cong. 2: { apply : ex1. } rewrite /=. atom_unf. rewrite /=//. rewrite /=//. 
Qed.

(*The inductive definition is useful when processes are to be manipulated (eg. change P to inact |||| P),
  the function definition is useful if we are done manipulating and simply want to verify that two
  processes are congruent, given if congruent_fun returns true *)
Lemma congruent_iff : forall P Q, P === Q <-> congruent_fun P Q.
Proof. Admitted.

(*The counter example that breaks subject reduction*)
Lemma counter_ex : forall k0 k1 k2 k3, ((throw k0 k1 inact) |||| (catch k0 k2 (k2? (k3) in (k1![tt]; inact)))) -->
                                    (k1? (k3) in (k1![tt]; inact)).
Proof.
move => k0 k1 k2 k3. apply : r_cong. rewrite -congruent_iff. apply : c_refl. 2: { rewrite -congruent_iff. apply : c_inact. } apply : r_cong. rewrite -congruent_iff. apply c_refl. apply : r_pass. destruct_notin. rewrite /fv. 
(*
We are stuck on the goal 
k1
  `notin` union (singleton k2)
            (remove k3 (union (singleton k1) (union (fv_exp tt) empty)))
Since k1 is in the set
*)
Abort. 

Lemma eqb_refl : forall k, eqb k k.
Proof. move=>k. atom_unf. done. Qed.

(*We replace k1 with k2 in the receiving process, that way it does not end up with both sides of the channel*)
Lemma counter_ex_fixed : forall k0 k1 k2 k3, k1 `notin` (singleton k1) -> 
  ((throw k0 k1 inact) |||| (catch k0 k2 (k2? (k3) in (k2![tt]; inact)))) -->
                                    (k1? (k3) in (k1![tt]; inact)).
Proof.
move => k0 k1 k2 k3 H. apply : r_cong. rewrite -congruent_iff. apply : c_refl. 2: { rewrite -congruent_iff. apply : c_inact. } apply : r_cong. rewrite -congruent_iff. apply c_refl. apply : r_pass. solve_notin. (*metalib tactic*)
simp subst_proc_nm. rewrite /=. rewrite /subst_nm. do ? rewrite eqb_refl. rewrite /=//. 
Qed.
