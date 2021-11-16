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

Definition swap_aux (b c a : atom) := 
  if (a == b) then c else if (a == c) then b else a.

          
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

Check ind.



Definition subst_exp (e : exp) (x : atom) (e_body : exp) : exp :=
  match e_body with
  | var nm => if nm == x then e else var nm
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
Check (fresh nil).
Check (atom_fresh empty).  Check atom_fresh. 
Check atom_fresh.
Definition set_fresh (s :atoms) : atom := 
  match atom_fresh s with
  (exist x _) => x
end. 


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
                                                         else catch (subst_nm a x nm0) (set_fresh (add a (add x (fv_nm P0)))) (subst_proc_nm a x (swap nm1 (set_fresh (add a (add x (fv_nm P0)))) P0));
subst_proc_nm a x (par P0 P1) := par (subst_proc_nm a x P0) ( subst_proc_nm a x P1);
subst_proc_nm a x inact := inact;
subst_proc_nm a x (nu_ch nm P0) := if x == nm then nu_ch nm P0 
                                                   else nu_ch (set_fresh (add a (fv_nm P0))) (subst_proc_nm a x (swap nm (set_fresh (add a (fv_nm P0))) P0)).

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

Lemma swap_aux_refl : forall a b, swap_aux a a b = b.
Proof.
move=> a b. rewrite /swap_aux. case : (eqVneq b a); done.
Qed.

Lemma swap_exp_refl : forall e a, swap_exp a a e = e.
Proof.
elim. 
- move=> a. done. 
- move=> a. done. 
- move=> a a0. rewrite /swap_exp. rewrite swap_aux_refl. done. 
Qed.

Lemma swap_refl : forall p a, swap a a p = p.
Proof.
elim.
- move=> a e p IH a0. rewrite /swap -/swap swap_aux_refl. rewrite swap_exp_refl. f_equal. done. 
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_refl. rewrite swap_aux_refl. f_equal. done. 
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_refl. rewrite swap_aux_refl. f_equal. done.  
- move=> a a0 p IH a1.  rewrite /swap -/swap swap_aux_refl. rewrite swap_aux_refl. f_equal. done.  
- move=> p IHp p0 IHp0 a.  rewrite /swap -/swap. rewrite IHp. rewrite IHp0. done. 
- move => a. rewrite /=. done.
- move=> a p IH a0.  rewrite /swap -/swap. rewrite IH. rewrite swap_aux_refl. done. 
Qed.

Ltac name_case a0 a1 := case : (eqVneq a0 a1).

Lemma swap_inject : forall a a' bs bs', swap_aux bs bs' a = swap_aux bs bs' a' -> a  = a'.
Proof.
move => a a' bs bs'. rewrite /swap_aux.
name_case a bs. 
- move=>->. name_case a' bs.
 + move=>->. done.
 + name_case a' bs'. 
  * move=>->. done.
  * move=> /eqP H. move : (not_eq_sym H). done.
- name_case a bs'.
 + move=>->.  name_case a' bs.
  * move=>->. done.
  * name_case a' bs'. 
   ** move=>->. done.
   ** move=> H1 H2 H3 H4. move : H4 H1 H2 H3=>->. move => _. move/eqP. done.
 + name_case a' bs.
  * move=>->. move=> /eqP H _. done. 
  * name_case a' bs'. 
   ** move=>->. move => H1 H2 H3 H4. move : H4 H1 H2 H3=>->. move => _ _ /eqP. done.
   ** done.
Qed. 

Definition swap_set bs bs' s := MapFunction.map (swap_aux bs bs') s. 


Lemma in_swap_set : forall a bs bs' s, M.In a (swap_set bs bs' s) <-> exists a', M.In a' s /\ swap_aux bs bs' a' = a.
Proof. 
move => a bs bs' s. split;rewrite /swap_set; rewrite MapFunction.map_In //=; move=> x y-> //=.
Qed.

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
Proof. Admitted.


Ltac forget_tac IH :=  
  rewrite /fv_nm -/fv_nm; simp subst_proc_nm;
  rewrite /subst_nm; if_destruct; (try fsetdec);
  let H := fresh "H__in" in move=> H; rewrite /= ?eq_refl /=; apply IH; fsetdec.

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



Check ind.
(*This lemma is used in forget*)
Lemma subst_fresh : forall p a b x x0, ~ M.In x (M.union (singleton a) (singleton b)) -> 
                                  ~ M.In x0 (M.union (singleton a) (singleton b)) -> swap x x0 (p{ a ::= b } p) = (p{ a ::= b} swap x x0 p).
Proof. Admitted.
Lemma swap_aeq : forall p p' bs bs', p =A= p' -> swap bs bs' p =A= swap bs bs' p'.
Proof. Admitted.

Lemma swap_comm : forall p bs bs', swap bs bs' p = swap bs' bs p.
Proof. Admitted.
Require Import Wellfounded. 
Check (well_founded_induction
                     (wf_inverse_image _ nat _ (@proc_size)
                        PeanoNat.Nat.lt_wf_0)).

(*By size induction*)
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
    *** rewrite swap_refl. move => H5. apply H.  auto. move : H5=> /eqP => H4. have H__in: ~ M.In t0 ((singleton a)).  fsetdec. fsetdec. 
    *** have: M.mem x (fv_nm P) = false. rewrite <- F.not_mem_iff. fsetdec. move=>->. move => H4 H5. rewrite swap_comm. 
        apply H;auto. 
     **** rewrite swap_size. auto.
     **** rewrite -fv_nm_eqvt. rewrite (in_eqvt _ _ x t0). rewrite swap_set_involutive. rewrite /swap_aux. move : n.  if_destruct.
      ***** fsetdec. 
      ***** if_destruct. move : i0=> /eqP => H5. have : ~ M.In a (singleton t0) by fsetdec. fsetdec.
Admitted.

Lemma forget : forall  P a b, ~ M.In a (fv_nm P) ->  (p{a::= b} P) =A= P.
Proof.
move => + a b. apply  (@ind (M.union (M.singleton a) (M.singleton b)) (fun P => ~ M.In a (fv_nm P) -> (p{ a ::= b} P) =A= P)). 
- admit. 
- move => t e p IH. forget_tac IH. 
- move => k x p H__nin IH. forget_tac IH.
- move => k x p IH. 
  rewrite /fv_nm -/fv_nm; simp subst_proc_nm. Print exp.
  rewrite /subst_nm.  if_destruct_r; (try fsetdec).
  move => neq H__in. rewrite /= ?eq_refl /=. apply IH. fsetdec. 
- move => k x p _ IH. rewrite /fv_nm -/fv_nm. 
  simp  subst_proc_nm.  
  if_destruct. 
  * rewrite /subst_nm. if_destruct. 
   ** move => H2. fsetdec. 
   ** rewrite aeq_refl. done. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   **  move => H2 H3. rewrite /aeq -/aeq eq_refl /=. 
       rewrite /set_fresh. destruct (atom_fresh ((add b (add a(fv_nm p))))). name_case x0 x. 
    *** move=>->.   rewrite swap_refl. apply IH.  move : H2=> /eqP => H4. have H__in: ~ M.In x ((singleton a)).  fsetdec. fsetdec. 
    *** have: M.mem x0 (fv_nm p) = false. rewrite <- F.not_mem_iff. fsetdec. move=>->.
  
      apply singleton_iff.        Locate "!=". fsetdec.
        if_destruct.
    *** rewrite swap_refl. move => H5. apply IH. fsetdec. (*freshness of x is needed here*)
    *** have: M.mem x0 (fv_nm p) = false. rewrite <- F.not_mem_iff. fsetdec. 
        move =>->. move => H H2. rewrite swap_comm. rewrite -subst_fresh.  
     **** apply swap_aeq. apply IH. fsetdec. 
     **** fsetdec. 
     **** fsetdec.      
- admit. 
- admit.
-admit. 
Admitted.

Ltac forget_tac2 IH :=  
  rewrite /fv_nm -/fv_nm; simp subst_proc_nm;
  rewrite /subst_nm; if_destruct; (try fsetdec);
  let H := fresh "H__in" in move=> H; rewrite /= ?eq_refl /=; move=>H2; apply H; fsetdec.

Lemma forget2 : forall  P a b, ~ M.In a (fv_nm P) ->  (p{a::= b} P) =A= P.
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
  simp  subst_proc_nm.  
  if_destruct. 
  * rewrite /subst_nm. if_destruct. 
   ** move => H2. fsetdec. 
   ** rewrite aeq_refl. done. 
  * rewrite /subst_nm. if_destruct. 
   ** fsetdec. 
   **  move => H2 H3 H4. rewrite /aeq -/aeq eq_refl /=. 
    *** rewrite /set_fresh.  destruct (atom_fresh (add a (add x (fv_nm p2)))). 
        if_destruct.  
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

