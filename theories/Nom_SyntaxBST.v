(* The Send Receive System. *)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Equations.Equations.
From SendRec Require Export  Nom_Swap_fs.
Require Import Coq.ssr.ssreflect.
Require Import Lia.
Require Import PP.Ppsimplmathcomp.
Require Import Equations.Equations.

Require Import SendRec.Atom.


Notation "E `union` F" :=
  (M.union E F)
  (at level 65, right associativity, format "E  `union`  '/' F").

Notation singleton := M.singleton.
Notation remove := M.remove.
Notation add := M.add.
Notation empty := M.empty.

Inductive exp : Set :=
  | tt
  | ff
  | var : atom -> exp
.

Locate atom.

Definition exp_eqb e0 e1 : bool :=
match (e0,e1) with
| (tt,tt) => true
| (ff,ff) => true
| (var nm0,var nm1) => nm0 == nm1
| _ => false
end.

Lemma exp_eqb_reflect : forall a b, ssrbool.reflect (a = b) (exp_eqb a b).
Proof.
elim. 
- elim; rewrite /exp_eqb; try ((constructor + constructor 2);done). 
- elim; rewrite /exp_eqb; try ((constructor + constructor 2);done). 
- move => t. elim. 
 *  rewrite /exp_eqb; try ((constructor + constructor 2);done). 
 *  rewrite /exp_eqb; try ((constructor + constructor 2);done). 
 * move => t1. rewrite /exp_eqb. case : (Atom.eq_reflect t t1).
  ** move=>->. rewrite eq_refl. constructor. done. 
  **  move => x; have copy := x; move: copy x. rewrite /eq_op.   rewrite /=. move/ Atom.eq_atom_neq=>->. constructor. intro H.  inversion H. done. 
Qed.


Definition exp_eqMixin := EqMixin exp_eqb_reflect.
Canonical atom_eqType := EqType exp exp_eqMixin.

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
| (send a0 e0 p0'),(send a1 e1 p1') => (a0 == a1) && (e0 == e1) && proc_eqb p0' p1'
| (receive a0 a0' p0'),(receive a1 a1' p1') => (a0 == a1) && (a0' == a1') && proc_eqb p0' p1'
| (throw a0 a0' p0'),(throw a1 a1' p1') => (a0 == a1) && (a0' == a1') && proc_eqb p0' p1'
| (catch a0 a0' p0'),(catch a1 a1' p1') => (a0 == a1) && (a0' == a1') && proc_eqb p0' p1'
| (par p0' p0''),(par p1' p1'') => proc_eqb p0' p1' && proc_eqb p0'' p1''
| inact,inact => true
| nu_ch nm0 p0', nu_ch nm1 p1' => (nm0 == nm1) && proc_eqb p0' p1'
| _,_ => false 
end. 

(*add proc to the equality type class later*)


Fixpoint fv_nm (P : proc) : atoms :=
  match P with
  | send nm e P0 => (singleton nm) `union` (fv_nm P0)
  | receive nm0 nm1 P0 => (singleton nm0) `union` (fv_nm P0)
  | throw nm0 nm1 P0 => ((singleton nm0) `union` (singleton nm1)) `union` (fv_nm P0) 
  | catch nm0 nm1 P0 => (singleton nm0) `union` (remove nm1 (fv_nm P0))
  | par P0 P1 => (fv_nm P0) `union` (fv_nm P1)
  | inact => empty
  | nu_ch nm P0 => remove nm (fv_nm P0)
end.   


Definition fv_exp_aux (e : exp) : atoms  :=
  match e with
    | tt => M.empty
    | ff => M.empty
    | var a =>  M.singleton a
  end.


Fixpoint fv_exp (P : proc) : atoms :=
  match P with
  | send nm e P0 => (fv_exp_aux e) `union` (fv_exp P0)
  | receive nm0 nm1 P0 => remove nm1 (fv_exp P0)
  | throw nm0 nm1 P0 => (fv_exp P0) 
  | catch nm0 nm1 P0 => fv_exp P0
  | par P0 P1 => (fv_exp P0) `union` (fv_exp P1)
  | inact => empty
  | nu_ch nm P0 => (fv_exp P0)
end.          


Definition swap_exp (b c : atom) (e: exp)  : exp :=
  match e with
  | var nm => var (swap_aux b c nm)
  | _ => e
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


(*
Definition binder_eq_nm f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
                               else if M.mem nm0 (fv_nm P1) then false 
                               else f P0 (swap nm0 nm1 P1).


Definition binder_eq_exp f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
                               else if M.mem nm0 (fv_exp P1) then false 
                               else f P0 (swap nm0 nm1 P1).

*)

Definition set_fresh (s :atoms) : atom := 
  match atom_fresh s with
  (exist x _) => x
end. 
(*
Definition binder_eq_nm f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
else let z := set_fresh (M.union (fv_nm P0) (fv_nm P1)) 
      in f (swap nm0 z P0) (swap nm1 z P1).




Definition binder_eq_exp f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
else let z := set_fresh (M.union (fv_exp P0) (fv_exp P1)) 
      in f (swap nm0 z P0) (swap nm1 z P1).*)

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
(*
Equations aeq (P0 P1 : proc) : bool by wf (proc_size P0)  :=
aeq (send nm0 e0 P0') (send nm1 e1 P1') :=  (nm0 == nm1) && (e0 == e1) && (aeq P0' P1');
aeq (receive nm0 nmb0 P0')  (receive nm1 nmb1 P1') :=  (nm0 == nm1) && if (nmb0 == nmb1) then aeq P0' P1' else aeq (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1');
aeq (throw nm0 nm0' P0') (throw nm1 nm1' P1') := (nm0 == nm1) && (nm0' == nm1') && (aeq P0' P1');
aeq (catch nm0 nmb0 P0') (catch nm1 nmb1 P1') := (nm0 == nm1) && if nmb0 == nmb1 then aeq P0' P1' else aeq (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1');
aeq (nu_ch nm0 P0') (nu_ch nm1 P1') := if nm0 == nm1 then aeq P0' P1' else aeq (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1');
aeq (par P0' P0'') (par P1' P1'') := (aeq P0' P1') && (aeq P0'' P1'');

aeq inact inact := true;
aeq _ _ := false.

Fixpoint aeq_aux (n : nat) (P0 P1 : proc)  :=
match n with 
| 0 => false 
| S n' => match P0, P1 with 
         | (send nm0 e0 P0'),(send nm1 e1 P1') =>  (nm0 == nm1) && (e0 == e1) && (aeq_aux n' P0' P1')
         | (receive nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (nm0 == nm1) && if nmb0 == nmb1 then aeq_aux n' P0' P1' else aeq_aux n' (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1')
         | (throw nm0 nm0' P0'), (throw nm1 nm1' P1') => (nm0 == nm1) && (nm0' == nm1') && (aeq_aux n' P0' P1')
         | (catch nm0 nmb0 P0'), (catch nm1 nmb1 P1') => (nm0 == nm1) && if nmb0 == nmb1 then aeq_aux n' P0' P1' else aeq_aux n' (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1')
         | (nu_ch nm0 P0'), (nu_ch nm1 P1') => if nm0 == nm1 then aeq_aux n' P0' P1' else aeq_aux n' (swap nm0 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P0') 
                                                                                                               (swap nm1 (set_fresh (M.union (fv_exp P0') (fv_exp P1'))) P1')
         | (par P0' P0''),(par P1' P1'') => (aeq P0' P1') && (aeq P0'' P1'')

         | inact, inact => true
         |  _, _ => false
         end
end.

Definition aeq2 p0 p1 := aeq_aux (proc_size p0) p0 p1.

(*An alternative way to define functions whose termination is not immediate
  I will try to experiment with this and the equations approach, to see which is nicest*)
Lemma aeq2_size : forall p0 p1 n , aeq_aux (proc_size p0) p0 p1 = aeq_aux ((proc_size p0) + n) p0 p1.
Proof. Admitted. *)

(*
Fixpoint aeq (P0 P1 : proc) {struct P0} : bool :=
let binder_eq_nm := binder_eq_nm aeq in
let binder_eq_exp := binder_eq_exp aeq in

match P0,P1 with
| (send nm0 e0 P0'), (send nm1 e1 P1') => (nm0 == nm1) && (e0 == e1) && (aeq P0' P1')
| (receive nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (nm0 == nm1) && (binder_eq_exp (nmb0, P0') (nmb1, P1'))
| (throw nm0 nm0' P0'), (throw nm1 nm1' P1') => (nm0 == nm1) && (nm0' == nm1') && (aeq P0' P1')
| (catch nm0 nmb0 P0'), (catch nm1 nmb1 P1') => (nm0 == nm1) && (binder_eq_nm (nmb0, P0') (nmb1, P1'))
| (nu_ch nm0 P0), (nu_ch nm1 P1) => binder_eq_nm (nm0, P0) (nm1, P1)
| (par P0' P0''),(par P1' P1'') => (aeq P0' P1') && (aeq P0'' P1'')
| inact, inact => true
| _, _ => false
end.
*)

Definition binder_eq_nm f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
                               else if M.mem nm0 (fv_nm P1) then false 
                               else f P0 (swap nm0 nm1 P1).

Definition binder_eq_exp f (p0 p1 : (atom * proc)) : bool :=
let (nm0,P0) := p0 in let (nm1,P1) := p1 in
if (nm0 == nm1) then f P0 P1
                               else if M.mem nm0 (fv_exp P1) then false 
                               else f P0 (swap nm0 nm1 P1).


Fixpoint aeq (P0 P1 : proc) {struct P0} : bool :=
let binder_eq_nm := binder_eq_nm aeq in
let binder_eq_exp := binder_eq_exp aeq in

match P0,P1 with
| (send nm0 e0 P0'), (send nm1 e1 P1') => (nm0 == nm1) && (e0 == e1) && (aeq P0' P1')
| (receive nm0 nmb0 P0'), (receive nm1 nmb1 P1') => (nm0 == nm1) && (binder_eq_exp (nmb0, P0') (nmb1, P1'))
| (throw nm0 nm0' P0'), (throw nm1 nm1' P1') => (nm0 == nm1) && (nm0' == nm1') && (aeq P0' P1')
| (catch nm0 nmb0 P0'), (catch nm1 nmb1 P1') => (nm0 == nm1) && (binder_eq_nm (nmb0, P0') (nmb1, P1'))
| (nu_ch nm0 P0), (nu_ch nm1 P1) => binder_eq_nm (nm0, P0) (nm1, P1)
| (par P0' P0''),(par P1' P1'') => (aeq P0' P1') && (aeq P0'' P1'')
| inact, inact => true
| _, _ => false
end.



Notation "P =A= Q" := (aeq P Q)(at level 70). 


Reserved Notation "P === Q" (at level 70).
Inductive congruent : proc -> proc -> Prop :=
| c_refl P : P === P
| c_alpha P Q (H: aeq P Q): P === Q 
| c_inact P : (par inact P) === P
| c_comm P Q: (par P Q) === (par Q P)
| c_asoc P Q R: (par (par P Q) R) === (par P (par Q R))
| c_nu_ch P Q nm (H: ~ M.In nm (fv_nm Q)) : (par (nu_ch nm P) Q) === (nu_ch nm (par P Q))
| c_nu_ch_inact nm : nu_ch nm inact === inact
where "P === Q" := (congruent P Q).

(*broken, can capture variables*)
Fixpoint swap_weak (b c: atom) (P : proc) : proc :=
  match P with
  | send nm e P0 => send nm e (swap_weak b c P0)
  | receive nm0 nm1 P0 => receive nm0 (swap_aux b c nm1) (swap_weak b c P0)
  | throw nm0 nm1 P0 => throw nm0 nm1 (swap_weak b c P0)
  | catch nm0 nm1 P0 => catch nm0 (swap_aux b c nm1) (swap_weak b c P0)
  | par P0 P1 => par (swap_weak b c P0) (swap_weak b c P1)
  | inact => inact
  | nu_ch nm P0 => nu_ch (swap_aux b c nm) (swap_weak b c P0)
  end.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => M.singleton x) in
  let C := gather_atoms_with (fun p : proc => fv_nm p) in

  constr:(M.union A (M.union B C)).

Definition alpha_variant (P : proc -> Prop) := forall p b c, P (swap_weak b c p) -> P p.

(*
Check proc_ind.
Section PROC. 

Variable Avoid : atoms.


Variable  P : proc -> Prop.
Hypothesis P_H : forall p b c, P (swap_weak b c p) <-> P p.
Hypothesis (H :  (forall (t : atom) (e : exp) (p : proc), P p -> P (send t e p))).
Hypothesis H1 :  (forall (t t0 : atom) (p : proc), ~ M.In t0 Avoid -> P p -> P (receive t t0 p)).
Hypothesis H2 :  (forall (t t0 : atom) (p : proc), P p -> P (throw t t0 p)).
Hypothesis H3 : (forall (t t0 : atom) (p : proc), ~ M.In t0 Avoid -> P p -> P (catch t t0 p)).
Hypothesis H4 : (forall p : proc, P p -> forall p0 : proc, P p0 -> P (par p p0)).
Hypothesis H5 : P inact.
Hypothesis H6 : (forall (t : atom) (p : proc), P p -> P (nu_ch t p)).

Lemma ind : forall p : proc, P p.
Proof.  apply proc_ind.
- apply H. 
- move => t t0 p HP.  destruct (atom_fresh Avoid). apply (@P_H _ t0 x).  rewrite /=. 
  rewrite /swap_aux eq_refl . apply H1. apply n. apply P_H. done. 
- apply H2. 
- move => t t0 p HP.  destruct (atom_fresh Avoid). apply (@P_H _ t0 x).  rewrite /=. 
  rewrite /swap_aux eq_refl . apply H3. apply n. apply P_H. done. 
- apply H4. 
- apply H5. 
- move => t p HP.  destruct (atom_fresh Avoid). apply (@P_H _ t x).  rewrite /=. 
  rewrite /swap_aux eq_refl . apply H6. apply P_H. done. 
Qed.

End PROC.

Check ind.*)



Definition subst_exp (e : exp) (x : atom) (e_body : exp) : exp :=
  match e_body with
  | var nm => if nm == x then e else var nm
  | t => t
  end.



Check (fresh nil).
Check (atom_fresh empty).  Check atom_fresh. 
Check atom_fresh.


Equations subst_proc_exp (e : exp) (x : atom) (P : proc) : proc by wf (proc_size P)  :=
subst_proc_exp e x (send nm e0 P0) := send nm (subst_exp e x e0) (subst_proc_exp e x P0);
subst_proc_exp e x (receive nm0 nm1 P0) := if x == nm1 then  (receive nm0 nm1 P0) 
                                           else receive nm0 (set_fresh (fv_exp P0 `union` fv_exp_aux e)) 
                                                            (subst_proc_exp e x (swap nm1 (set_fresh (fv_exp P0 `union` fv_exp_aux e)) P0));
subst_proc_exp e x (throw nm0 nm1 P0) := throw nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (catch nm0 nm1 P0) := catch nm0 nm1 (subst_proc_exp e x P0);
subst_proc_exp e x (par P0 P1) := par (subst_proc_exp e x P0) ( subst_proc_exp e x P1);
subst_proc_exp e x inact := inact;
 subst_proc_exp e x (nu_ch nm P0) := nu_ch nm (subst_proc_exp e x P0).


Definition subst_nm (a x nm : atom) : atom :=
if x == nm then a else nm.

(*parameterize this over some free variablesx*)

(*added x in the catch case to see if forget proof becomes easier*)
Equations subst_proc_nm (a x: atom)  (P : proc) : proc by wf (proc_size P)  :=
subst_proc_nm a x (send nm e P0) := send (subst_nm a x nm) e (subst_proc_nm a x P0);
subst_proc_nm a x (receive nm0 nm1 P0) := receive (subst_nm a x nm0) nm1 (subst_proc_nm a x P0);
subst_proc_nm a x (throw nm0 nm1 P0) := throw (subst_nm a x nm0) (subst_nm a x nm1) (subst_proc_nm a x P0);
subst_proc_nm a x (catch nm0 nm1 P0) := if x == nm1 then catch (subst_nm a x nm0) nm1 P0 
                                                         else catch (subst_nm a x nm0) (set_fresh ((add a (add x(fv_nm (P0)))))) (subst_proc_nm a x (swap nm1 (set_fresh (add a (add x(fv_nm (P0))))) P0));
subst_proc_nm a x (par P0 P1) := par (subst_proc_nm a x P0) ( subst_proc_nm a x P1);
subst_proc_nm a x inact := inact;
subst_proc_nm a x (nu_ch nm P0) := if x == nm then nu_ch nm P0 
                                                   else nu_ch (set_fresh (add a (fv_nm (P0)))) (subst_proc_nm a x (swap nm (set_fresh (add a (add x (fv_nm (P0))))) P0)).

Notation "nm{ x ::= a } t" := (subst_nm a x t) (at level 70).

Notation "p{ x ::= a } t" := (subst_proc_nm a x t) (at level 70).



Ltac destruct_bool := match goal with
                      | [  |- is_true (_ && _) -> _ ] =>  move=> /andP []
                      | [  |- is_true (~~ (_ && _)) -> _ ] => rewrite negb_and; move=> /orP []

                      end.


Ltac reduce_in := rewrite /=  ?inE negb_or; destruct_bool.

Lemma predC1_iff :  forall (a0 a1 : atom), (~~ predC1 a0 a1) <-> a0 == a1.
Proof.
move=> a0 a1. rewrite /predC1 /= Bool.negb_involutive. split; move/eqP=>->//=. 
Qed.

(*
Lemma swap_aux_refl : forall a b, swap_aux a a b = b.
Proof.
move=> a b. rewrite /swap_aux. case : (eqVneq b a); done.
Qed.*)

Lemma swap_exp_same : forall e a, swap_exp a a e = e.
Proof.
elim. 
- move=> a. done. 
- move=> a. done. 
- move=> a a0. rewrite /swap_exp. rewrite swap_aux_same.  done. 
Qed.

Lemma swap_same : forall p a, swap a a p = p.
Proof.
elim.
- move=> a e p IH a0. rewrite /swap -/swap swap_aux_same. rewrite swap_exp_same. f_equal. done. 
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_same. rewrite swap_aux_same. f_equal. done. 
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_same. rewrite swap_aux_same. f_equal. done.  
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_same. rewrite swap_aux_same. f_equal. done.  
- move=> p IHp p0 IHp0 a.  rewrite /swap -/swap. rewrite IHp. rewrite IHp0. done. 
- move => a. rewrite /=. done.
- move=> a p IH a0.  rewrite /swap -/swap. rewrite IH. rewrite swap_aux_same. done. 
Qed.

Ltac name_case a0 a1 := case : (eqVneq a0 a1).


(*
Lemma in_swap_set : forall a bs bs' s, M.In a (swap_set bs bs' s) <-> exists a', M.In a' s /\ swap_aux bs bs' a' = a.
Proof. 
move => a bs bs' s. split;rewrite /swap_set; rewrite MapFunction.map_In //=; move=> x y-> //=.
Qed.
*)


(*Some tactics*)
Ltac contra := intros; subst; match goal with
                    | [ H:  (is_true (negb (@eq_op nat_eqType ?a ?a)))  |- _ ] => by move : H=> /eqP

                    | [ H: ?a <> ?a  |- _ ] => by move : H 

                      end.

Ltac ifN_tac :=  intro ; rewrite ifN_eq; [ | done ].
Ltac ifNC_tac :=  intro ; rewrite ifN_eqC; [ | done ].

Ltac get_eqs := try (match goal with
                | [ H:  (is_true (_ (@eq_op nat_eqType _ _)))  |- _ ] => move : H
                end).

Ltac if_destruct := (try rewrite eq_refl) ; match goal with
                    | [ |- context[if ?a == ?b then _ else _] ] => get_eqs; name_case a b; [move =>-> ; try rewrite eq_refl | try (ifN_tac + ifNC_tac) ]
                    end ; try solve [contra | done ].

Ltac if_destruct_r := repeat if_destruct.


(*
Lemma in_eqvt : forall a s bs bs', M.In a s <-> M.In (swap_aux bs bs' a) (swap_set bs bs' s).
Proof. 
move => a s bs bs'. split. 
- rewrite in_swap_set. rewrite /swap_aux. if_destruct.  
 * exists bs. rewrite eq_refl. split; done. 
 * exists a. split. done. if_destruct. 
- rewrite in_swap_set.  rewrite /swap_aux. 
 * move => [] x [].  if_destruct.  
  **  if_destruct. if_destruct_r. 
  ** if_destruct_r. by move => + + + + <-.
Qed.
*)

(*
Lemma fv_nm_eqvt : forall P bs bs', M.Equal (swap_set bs bs' (fv_nm P)) (fv_nm (swap bs bs' P)).
Proof. Admitted.


Lemma in_fv_eqvt : forall P a bs bs', M.In a (fv_nm P) <-> M.In (swap_aux bs bs' a) (fv_nm (swap bs bs' P)).
Proof.
move => P a bs bs'. split. move/(in_eqvt _ _ bs bs'). rewrite fv_nm_eqvt. done.
move => H.  rewrite (in_eqvt _ _ bs bs'). rewrite fv_nm_eqvt. done. 
Qed.

Lemma not_in_fv_equiv : forall P a bs bs', ~ M.In a (fv_nm P) <-> ~ M.In (swap_aux bs bs' a) (fv_nm (swap bs bs' P)).
Proof.
move => P a bs bs'. split. move => H2 H3. apply H2. rewrite in_eqvt.  rewrite fv_nm_eqvt. apply H3.   
 move => H2 H3. apply H2. rewrite -in_fv_eqvt.  done. 
Qed.

Lemma swap_set_involutive : forall p bs bs', swap_set bs bs' (swap_set bs bs' p) = p.
Proof. Admitted.*)

Lemma swap_fs_singleton : forall a bs bs', swap_fs bs bs' (singleton a) [=] singleton (swap_aux bs bs' a).
Proof.
move => a bs bs'. rewrite /swap_fs !singleton_b. Print MF. rewrite /eqb. simpl_swap_aux. done. fsetdec.  fsetdec. fsetdec. 
Qed.

Lemma fv_nm_eqvt : forall P bs bs', (fv_nm (swap bs bs' P)) [=] (swap_fs bs bs' (fv_nm P)).
Proof. 
elim; try solve [intros; rewrite /=; (do ? rewrite -union_swap_fs); rewrite H; rewrite !swap_fs_singleton;  done].
- intros. rewrite /=.
  rewrite -union_swap_fs. rewrite H. rewrite swap_fs_singleton. rewrite -remove_swap_fs. fsetdec. 
- intros. rewrite /=.
  rewrite -union_swap_fs. rewrite H H0. done. 
- move => bs bs'. rewrite /=. fsetdec. 
- intros. rewrite /=. rewrite -remove_swap_fs. rewrite H. done.
Qed.


Ltac forget_tac IH :=  
(*  move => a b; *)rewrite /fv_nm -/fv_nm; simp subst_proc_nm;
  rewrite /subst_nm; if_destruct; (try fsetdec);
  let H := fresh "H__in" in move=> H; simp aeq; rewrite /= ?eq_refl /=; apply IH; fsetdec.

(*
Lemma aeq_refl : forall P , P =A= P.
Proof. 
elim.
- move => k e p H. simp aeq. by rewrite /= 2!eq_refl. 
- move => k ep H. simp aeq. rewrite !eqxx. done . 
- move => k e p H. simp aeq. rewrite !eqxx. done. 
- move => k k' p H. simp aeq. rewrite !eqxx. done. 
- move => k k' p H.  simp aeq. rewrite /= ?eq_refl. apply/andP. split; done.  
- rewrite /=. done. 
- move => k p H. simp aeq. by rewrite /= ?eq_refl. 
Qed.*)
Lemma aeq_refl : forall P , P =A= P.
Proof. 
elim.
- move => k e p H. by rewrite /= 2!eq_refl. 
- move => k ep H. by rewrite /= 2!eq_refl. 
- move => k e p H. by rewrite /= 2!eq_refl. 
- move => k k' p H. by rewrite /= ?eq_refl. 
- move => k k' p H. rewrite /= ?eq_refl. apply/andP. split; done.  
- rewrite /=. done. 
- move => k p H. by rewrite /= ?eq_refl. 
Qed.





(*Used by fresh Metalib tactic*)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => M.singleton x) in
  let C := gather_atoms_with (fun p : proc => fv_nm p) in

  constr:(M.union A (M.union B C)).


(*substitution lemmas*)
Lemma subst_nm_refl : forall a b, nm{ a::=a} b = b.
Proof. 
move => a b. rewrite /subst_nm. if_destruct. 
Qed. 

Lemma subst_nm_refl2 : forall a b, nm{ a::=b} b = b.
Proof. 
move => a b. rewrite /subst_nm. name_case a b; done. 
Qed. 

Lemma subst_nm_match : forall a b, nm{ a::=b} a = b.
Proof. 
move => a b. rewrite /subst_nm. rewrite eq_refl. done. 
Qed. 


(*Don't prove this lemma, it won't be needed later*)
Lemma swap_aeq : forall p p' bs bs', p =A= p' -> swap bs bs' p =A= swap bs bs' p'.
Proof. Admitted.

Lemma swap_exp_comm : forall p bs bs', swap_exp bs bs' p = swap_exp bs' bs p.
Proof. move => p bs bs'. rewrite /swap_exp. destruct p. done. done. simpl_swap_aux. 
Qed.

(*A variantion of  this lemma will be needed later*)
Lemma swap_comm : forall p bs bs', swap bs bs' p = swap bs' bs p.
Proof. Admitted.


Require Import Wellfounded. 
Check (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                        PeanoNat.Nat.lt_wf_0)).

(*By size induction*)

Lemma subst_eqvt : forall P a b bs bs',  swap bs bs' (p{a::= b} P) =A= p{ (swap_aux bs bs' a) ::= (swap_aux bs bs' b)} swap bs bs' P.
Proof. Admitted.

Lemma aeq_trans : forall P0 P1 P2, P0 =A= P1 -> P1 =A= P2 -> P0 =A= P2.
Proof. Admitted.

Lemma swap_involutive : forall P bs bs', swap bs bs' (swap bs bs' P) = P.
Proof. Admitted.

Lemma swap_exp_eqvt : forall e bs0 bs1 bs2 bs3, swap_exp bs0 bs1 (swap_exp bs2 bs3 e) = swap_exp (swap_aux bs0 bs1 bs2) (swap_aux bs0 bs1 bs3) (swap_exp bs0 bs1 e).
Proof.
intros. rewrite /swap_exp. destruct e. done. done. f_equal. apply swap_aux_equivariance. 
Qed.



Lemma swap_eqvt : forall P bs0 bs1 bs2 bs3, swap bs0 bs1 (swap bs2 bs3 P) = swap (swap_aux bs0 bs1 bs2) (swap_aux bs0 bs1 bs3) (swap bs0 bs1 P).
Proof. Locate lt_wf. Check  Wf_nat.lt_wf.
induction P using (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                       Wf_nat.lt_wf )).
move => bs0 bs1 bs2 bs3.
destruct P.
- rewrite /swap -/swap. f_equal. apply swap_aux_equivariance. apply swap_exp_eqvt. apply H. done. 
- rewrite /swap -/swap. f_equal. all : try apply swap_aux_equivariance.  apply H. done. 
- rewrite /swap -/swap. f_equal. all : try apply swap_aux_equivariance.  apply H. done. 
- rewrite /swap -/swap. f_equal. all : try apply swap_aux_equivariance.  apply H.  done. 
- rewrite /swap -/swap. f_equal. apply H. auto. apply / leP. rewrite /=.  ppsimpl. lia.  
  apply H. auto. apply / leP. rewrite /=.  ppsimpl. lia.  
- rewrite /swap -/swap. done. 
- rewrite /swap -/swap. f_equal. apply swap_aux_equivariance. apply H. done. 
Qed.

Lemma forget : forall  P a b, ~ M.In a (fv_nm P) ->  (p{a::= b} P) =A= P.
Proof.
move => + a b. induction P using (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                        PeanoNat.Nat.lt_wf_0)).
destruct P. 
-  forget_tac H.
-  forget_tac H.
-  rewrite /fv_nm -/fv_nm; simp subst_proc_nm. Print exp.
  rewrite /subst_nm.  if_destruct_r; (try fsetdec).
  move => neq H__in. rewrite /= ?eq_refl /=. apply H. fsetdec. fsetdec. 
- rewrite /fv_nm -/fv_nm. 
  simp  subst_proc_nm.  
  if_destruct. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   ** by rewrite aeq_refl. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   **  move => H2 H3. rewrite /aeq -/aeq eq_refl /=. 
       rewrite /set_fresh. destruct (atom_fresh ((add b (add a(fv_nm P))))). if_destruct. 
    *** rewrite swap_same. move => H5. apply H.  auto. move : H5=> /eqP => H4. have H__in: ~ M.In t0 ((singleton a)).  fsetdec. fsetdec. 
    *** have: M.mem x (fv_nm P) = false. rewrite <- F.not_mem_iff. fsetdec. move=>->. move => H4 H5. rewrite swap_comm. 
        apply H;auto. 
     **** rewrite swap_size. auto.
     **** rewrite fv_nm_eqvt. apply swap_fs_4. simpl_swap_aux; fsetdec. 
Admitted.

Lemma forget : forall  P a b, ~ M.In a (fv_nm P) ->  (p{a::= b} P) =A= P.
Proof.
induction P using (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                        PeanoNat.Nat.lt_wf_0)).
destruct P. 
-  forget_tac H. 
-  forget_tac H. 
-  move => a b. rewrite /fv_nm -/fv_nm; simp subst_proc_nm. Print exp.
  rewrite /subst_nm.  if_destruct_r; (try fsetdec).
  move => neq H__in. simp aeq; rewrite /= ?eq_refl /=. apply H. fsetdec. fsetdec. 
- move => a b.  rewrite /fv_nm -/fv_nm. 
  simp  subst_proc_nm.  
  if_destruct. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   ** by rewrite aeq_refl. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   **  move => H2 H3. simp aeq. rewrite eq_refl /=. 
       rewrite /set_fresh. destruct ( atom_fresh (add b (add a(fv_nm P)))). if_destruct.
    *** rewrite swap_same. move => H5. apply H.  auto. move : H5=> /eqP => H4. fsetdec. 
    ***(* have: M.mem x (fv_nm P) = false. rewrite <- F.not_mem_iff. fsetdec. move=>->.*) move => H4 H5. destruct (atom_fresh (fv_exp (p{ a ::= b} swap t0 x P) `union` fv_exp P)). 
         apply: aeq_trans. apply : subst_eqvt. rewrite swap_eqvt. simpl_swap_aux; try fsetdec. 
     **** auto. apply H. auto. 
     **** rewrite swap_size. auto.
     **** rewrite fv_nm_eqvt. apply swap_fs_4. simpl_swap_aux. (*Need stronger freshness assumption for generated variable here*) fsetdec. fsetdec. fsetdec. 
Admitted.



Lemma renaming : forall P a b c, ~ M.In c (fv_nm P) -> p{ c ::= b} (swap c a P) =A= p{ a ::= b} P.
Proof.
move => + a b. induction P using (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                        PeanoNat.Nat.lt_wf_0)).
destruct P.
- admit. 
- admit.
- admit. 
rewrite /swap -/swap /fv_nm -/fv_nm. simpl_swap_aux; try fsetdec. 
 * simp subst_proc_nm. move : C.  if_destruct. if_destruct. move => H1 H2 H3. rewrite /set_fresh. 
    destruct (atom_fresh (add b (add c (fv_nm (swap c a P))))). 
    destruct (atom_fresh (add b (add a (fv_nm P)))). rewrite /=. if_destruct. 
  ** rewrite /subst_nm !eqxx. move => _. rewrite /=. rewrite swap_eqvt. simpl_swap_aux.
   *** rewrite swap_involutive swap_same. rewrite /=. apply aeq_refl.
Set Printing All. if_destruct. rewrite (eq_sym a c). if_destruct. if_destruct. move => _ + H. rewrite /set_fresh.
    destruct (atom_fresh (add b (add c (fv_nm (swap c a P))))). 
    destruct (atom_fresh (add b (add a (fv_nm P)))). rewrite /subst_nm !eqxx.
    rewrite /aeq -/aeq eqxx /=. move : n n0. if_destruct. 
   *** rewrite swap_swap /swap_aux. if_destruct. if_destruct. fsetdec. rewrite swap_swap. rewrite /swap_aux. if_destruct. if_destruct. fsetdec.  if_destruct. move => H1 H2 H3 H4 H5 H6 H7 H8 H9 H10. rewrite swap_comm. aplpy H. rewrite swap_size. auto. rewrite -fv_nm_eqvt. 
  rewrite (in_eqvt _ _ c x0). rewrite swap_set_involutive. rewrite /swap_aux eqxx. fsetdec. 
   *** move => H1 H2 H3 H4 H5 H6. have: M.mem x (fv_nm P) = false. rewrite <- F.not_mem_iff. have: ~M.In x (fv_nm (swap c a P)). fsetdec. rewrite -fv_nm_eqvt. rewrite (in_eqvt _ _ c a). rewrite swap_set_involutive. rewrite /swap_aux. move : H3. if_destruct. fsetdec. move : H4. if_destruct. fsetdec. move=>->. move => H4 H5. rewrite swap_comm. 
        apply H;auto. 

move : n. if_destruct. (*Need stronger freshness assumption for generated variable here*)fsetdec. 
          if_destruct. move : i0=> /eqP => H5. fsetdec. 
Admitted.

rewrmove/eq_sym.

Ltac forget_tac2 IH :=  
  rewrite /fv_nm -/fv_nm; simp subst_proc_nm;
  rewrite /subst_nm; if_destruct; (try fsetdec);
  let H := fresh "H__in" in move=> H; rewrite /= ?eq_refl /=; move=>H2; apply H; fsetdec.

Lemma forget3 : forall  P a b, ~ M.In a (fv_nm P) ->  (p{a::= b} P) =A= P.
Proof.
move => P a b. funelim  (p{ a ::= b} P).
-  rewrite /fv_nm -/fv_nm; simp subst_proc_nm.
  rewrite /subst_nm; if_destruct; (try fsetdec).
  let H := fresh "H__in" in move=> H. rewrite /= ?eq_refl /=. move=>H2.  apply H. fsetdec.

-   rewrite /fv_nm -/fv_nm; simp subst_proc_nm.
  rewrite /subst_nm; if_destruct; (try fsetdec).
  let H := fresh "H__in" in move=> H. rewrite /= ?eq_refl /=. move=>H2.  apply H. fsetdec.
-
  rewrite /fv_nm -/fv_nm; simp subst_proc_nm.
  rewrite /subst_nm.  if_destruct_r; (try fsetdec).
  move => neq H__in. rewrite /= ?eq_refl /=. move => H2. apply H. fsetdec. 
- rewrite /fv_nm -/fv_nm. 
  simp  subst_proc_nm. move : Heqcall.  
  if_destruct. 
  * rewrite /subst_nm. if_destruct. 
   ** move => H2. fsetdec. 
   ** rewrite aeq_refl. done. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   **  move => H2 H3. (* rewrite /aeq -/aeq eq_refl -/fv_nm /= -/fv_nm.  *)
    *** move : H. rewrite /set_fresh.  destruct (atom_fresh (add a (add x (fv_nm p2)))). move=> H H4 H5.   apply H. move => + ->.  
        simp subst_proc_nm. move : H3. if_destruct.  rewrite /subst_nm. move : H2. if_destruct. rewrite /set_fresh.
        destruct (atom_fresh (add a (add x (fv_nm p2)))).
    *** rewrite swap_refl. move => H5. apply H. fsetdec. 
    ***  rewrite /set_fresh. destruct (atom_fresh ((add b (add a(fv_nm p))))). have: M.mem x0 (fv_nm p) = false. rewrite <- F.not_mem_iff. fsetdec. move =>->. move => H H2.
         rewrite -subst_fresh.  
     **** f_equal. admit. 
     **** fsetdec. 
     **** fsetdec. 
admit.     
admit.
admit.
admit.





(*The rest is unchanged, probably doesn't even run anymore*)

 
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



Definition k := fresh [::].

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
Qed

