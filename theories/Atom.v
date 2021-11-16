(* Atoms for locally nameless *)

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq path.

Require Import FinMap.ordtype.

Require Import Omega.
Require Import Coq.Structures.Equalities.

 Require Import Lia.
Require Import PP.Ppsimplmathcomp. 
(* Require Import Coq.Arith.Max.
Require Metalib.Metatheory.*)
Require Coq.Lists.List.
Require Import Metalib.CoqListFacts.
Require Metalib.LibTactics.


(* Require Import Metalib.LibTactics. *)

(* Require Import Structures.Orders. *)
(*Notation In := Lists.List.In.*)
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Require Import FSets.

Require Import Structures.OrderedType.
Print Nat_as_OT.

Locate In. 

Require Import SendRec.MapFunction.


Module Atom <: OrderedType.
 Include Nat_as_OT. Print Nat_as_OT.
 Definition eq_atom (a b : t) : bool := ssrnat.eqn a b.  
 Lemma eq_reflect a b :  ssrbool.reflect (a = b) (eq_atom a b).
  Proof. by apply: ssrnat.eqnP. Qed.


  Lemma eq_atom_refl : forall (a : t), eq_atom a a.
  Proof. Search "nat_refl". Check ssrnat.eqnP. rewrite /eq_atom. elim. done. done. 
  Qed.

  Scheme Equality for nat.
  
  Lemma eq_atom_neq : forall a b, a<> b -> eq_atom a b = false.
  Proof. move => a b /eqP. case (eq_reflect a b).  move => H /eqP. done. done.  Qed. 

  Definition atom_eqMixin := EqMixin Atom.eq_reflect.
  Canonical atom_eqType := EqType t atom_eqMixin.

 Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y. auto with arith.
      simpl. induction z; ppsimpl;lia. 
  Qed.


 Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
   induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
    - subst. ppsimpl. lia.  auto using max_lt_r. 
Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ In n xs }.
  Proof.
   intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). ppsimpl. lia. trivial.
  Qed.

Check exist.
  Definition fresh (l : list t) :=
    match atom_fresh_for_list l with
      (exist x _) => x
    end.

  Lemma fresh_not_in : forall l, ~ In (fresh l)  l.
  Proof.
    intro l. unfold fresh.
    destruct atom_fresh_for_list. auto.
  Qed.

 (* Fixpoint fresh' a (l : seq atom) :=
    match l with
    | [::] => a +1
    | x::xs => fresh' (maxn x a) xs
    end.

  Definition fresh l := fresh' 0 l.

  Lemma fresh_not_head a a' l : a <= a' -> fresh' a' l != a.
  Proof.
    elim: l a' => [|  a'' l IHl] a' Le_a_a'.
      by rewrite /fresh' neq_ltn addn1 ltnS orb_idl.
    by rewrite /fresh' maxnC; apply IHl; rewrite leq_max orb_idr.
  Qed.

  Lemma fresh_not_in l : fresh l \notin l.
  Proof.
    suff fresh'_not_in a : fresh' a l \notin l by apply fresh'_not_in.
    elim: l a =>  // a' l IHl a.
      by rewrite /fresh/fresh' in_cons Bool.negb_orb fresh_not_head ?(IHl (maxn a' a)) ?leq_maxl.
  Qed.*)

  Definition nat_of (x : t) := x.
  (* end hide *)

End Atom.

Definition nat_beq := Atom.nat_beq.
Definition nat_eq_dec := Atom.nat_eq_dec.

Canonical atom_eqType := EqType Atom.t Atom.atom_eqMixin.

Module M := FSetAVL.Make(Atom).

Module MapFunction := MapFunction M.

Locate In.

Notation atom := Atom.t. 
Notation atoms := M.t.
Notation fresh := Atom.fresh.
Notation fresh_not_in := Atom.fresh_not_in.
Notation atom_fresh_for_list := Atom.atom_fresh_for_list.


(** The [AtomSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)

Module Export AtomSetDecide := Coq.FSets.FSetDecide.WDecide_fun Atom M.

(** The [AtomSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    atoms, as well as a variety of lemmas about non-membership. *)

(* Module Export AtomSetNotin := FSetWeakNotin.Notin_fun Atom AtomSetImpl. *)

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module MF := FSetFacts.Facts M.

Module MP := FSetProperties.Properties M.


Export MF.

Export MP.
(* ********************************************************************** *)
(** * Properties *)

(** For any given finite set of atoms, we can generate an atom fresh
    for it. *)
(*
Lemma test : forall (l : seq atom) a ,a \in (elements l) <-> In a l.
Proof.
move=> l.
elim : elements l. - move => l a. H. 
*)




Lemma atom_fresh : forall L : atoms, { x : atom | ~ M.In x L }.
Proof.
  intros L. destruct (atom_fresh_for_list (M.elements L)) as [a H].
  exists a. intros J. contradiction H. Search "InA".  Search "InA_iff_In". Search _ (M.elements _). Print InA.  Search "In_InA". 
  rewrite <- CoqListFacts.InA_iff_In. auto using M.elements_1.
Qed.



(* ********************************************************************** *)
(** * Tactic support for picking fresh atoms *)

(* begin hide *)

(** The auxiliary tactic [simplify_list_of_atom_sets] takes a list of
    finite sets of atoms and unions everything together, returning the
    resulting single finite set. *)

Locate empty.
Locate Ltac ltac_remove_dups. 
Ltac simplify_list_of_atom_sets L :=
  let L := eval simpl in L in
  let L := LibTactics.ltac_remove_dups L in
  let L := eval simpl in (List.fold_right M.union M.empty L) in
  match L with
    | context C [M.union ?E M.empty] => context C [ E ]
  end.

(* end hide *)

(** [gather_atoms_with F] returns the union of all the finite sets
    [F x] where [x] is a variable from the context such that [F x]
    type checks. *)

Ltac gather_atoms_with F :=
  let apply_arg x :=
    match type of F with
      | _ -> _ -> _ -> _ => constr:(@F _ _ x)
      | _ -> _ -> _ => constr:(@F _ x)
      | _ -> _ => constr:(@F x)
    end in
  let rec gather V :=
    match goal with
      | H : _ |- _ =>
        let FH := apply_arg H in
        match V with
          | context [FH] => fail 1
          | _ => gather (M.union FH V)
        end
      | _ => V
    end in
  let L := gather M.empty in eval simpl in L.

(** [beautify_fset V] assumes that [V] is built as a union of finite
    sets and returns the same set cleaned up: empty sets are removed
    and items are laid out in a nicely parenthesized way. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | M.union ?E1 ?E2 => let Acc2 := go Acc E2 in go Acc2 E1
     | M.empty => Acc
     | ?E1 => match Acc with
                | M.empty => E1
                | _ => constr:(M.union E1 Acc)
              end
     end
  in go M.empty V.

(** The tactic [pick fresh Y for L] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [~ In Y L], i.e., that [Y] is fresh for [L].
    The tactic will fail if [Y] is already declared in the context.
    The variant [pick fresh Y] is similar, except that [Y] is fresh
    for "all atoms in the context."  This version depends on the
    tactic [gather_atoms], which is responsible for returning the set
    of "all atoms in the context."  By default, it returns the empty
    set, but users are free (and expected) to redefine it. *)

Ltac gather_atoms :=
  constr:(M.empty).

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (atom_fresh L) as [Y Fr]).

Tactic Notation "pick" "fresh" ident(Y) :=
  let L := gather_atoms in
  pick fresh Y for L.

Ltac pick_fresh y :=
  pick fresh y.

(** Example: We can redefine [gather_atoms] to return all the
    "obvious" atoms in the context using the [gather_atoms_with] thus
    giving us a "useful" version of the "[pick fresh]" tactic. *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => M.singleton x) in
  constr:(M.union A B).

Lemma example_pick_fresh_use : forall (x y z : atom) (L1 L2 L3: atoms), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3.
  pick fresh k.

  (** At this point in the proof, we have a new atom [k] and a
      hypothesis [Fr] that [k] is fresh for [x], [y], [z], [L1], [L2],
      and [L3]. *)

  trivial.
Qed.
(* end show *)

