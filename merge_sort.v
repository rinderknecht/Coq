Require Import List.

Notation "[]"    := nil.
Notation "[ z ]" := (cons z []) (z at level 200).

(* Total order *)

Definition antisymmetric (A : Set) (rel : A -> A -> bool) :=
  forall (x y : A),
  (rel x y = true /\ rel y x = true) -> x = y.

Definition transitive (A : Set) (rel : A -> A -> bool) :=
  forall (x y z : A),
  (rel x y = true /\ rel y z = true) -> rel x z = true.

Definition connex (A : Set) (rel : A -> A -> bool) :=
  forall (x y : A), rel x y = true \/ rel y x = true.

Definition total_order (A : Set) : Set := {
  cmp : A -> A -> bool |
  antisymmetric A cmp /\ transitive A cmp /\ connex A cmp
}.

(* Permutations by transpositions *)

Inductive perm (a : Set)
             : list a -> list a -> Prop :=
  perm_nil   : perm a [] []
| perm_cons  : forall (x : a) (s t : list a),
               perm a s t -> perm a (x::s) (x::t)
| perm_swap  : forall (x y : a) (s : list a),
               perm a (x::y::s) (y::x::s)
| perm_trans : forall (s t u : list a),
               perm a s t -> perm a t u -> perm a s u.

Notation "s ~~ t" := (perm _ s t) (at level 70, no associativity).

Theorem perm_refl :
  forall (a : Set) (s : list a), s ~~ s.
Proof.
intros.
induction s as [| x s].
  - apply perm_nil.
  - apply perm_cons.
    apply IHs.
Defined.

Theorem perm_symm : 
  forall (a : Set) (s t : list a), s ~~ t -> t ~~ s.
Proof.
intros.
induction H.
  - apply perm_nil.
  - apply perm_cons.
    apply IHperm.
  - apply perm_swap.
  - apply (perm_trans a u t s).
    * apply IHperm2.
    * apply IHperm1.
Defined.

(* Totally ordered lists *)

Inductive ord_list (a : Set) (cmp : total_order a)
                 : list a -> Prop :=
  ord_nil  : ord_list a cmp []
| ord_one  : forall x : a, ord_list a cmp [x]
| ord_more : forall (x y : a) (s : list a),
                proj1_sig cmp x y = true  (* x <= y in mind *)
             -> ord_list a cmp (y::s)
             -> ord_list a cmp (x::y::s).

(* Merging two sorted lists *)

Fixpoint merge (A : Set) (cmp : total_order A)
               (s t : list A) : list A :=
  let fix merge' t :=
    match s, t with
      [], _ => t
    | _, [] => s
    | x::s', y::t' =>
        if proj1_sig cmp x y
        then x :: merge A cmp s' t
        else y :: merge' t'
    end
  in merge' t.

(* Stable online bottom-up merge sort *)

Inductive bit (A : Set) : Set :=
  Zero : bit A
| One  : list A -> bit A.

Fixpoint unb (A : Set) (cmp : total_order A)
             (s : list (bit A)) (u : list A) :=
  match s with
               [] => u
  | Zero _  :: s' => unb A cmp s' u
  | One _ t :: s' => unb A cmp s' (merge A cmp t u)
  end.

Fixpoint add (A : Set) (cmp : total_order A)
             (s : list A) (t : list (bit A)) :=
  match t with
               [] => [One A s]
  | Zero _  :: t' => One A s :: t'
  | One _ u :: t' => Zero A :: add A cmp (merge A cmp s u) t'
  end.

Fixpoint sum (A : Set) (cmp : total_order A) 
             (s : list A) (t : list (bit A)) :=
  match s with
       [] => t
  | x::s' => sum A cmp s' (add A cmp [x] t)
  end.

Definition oms (A : Set) (cmp : total_order A) (s : list A) :=
  unb A cmp (sum A cmp s []) [].

(* Merge sort is indeed a sorting algorithm *)

Theorem is_sorted :
  forall (a : Set) (cmp: total_order a) (s : list a),
  ord_list a cmp (oms a cmp s) /\ perm a (oms a cmp s) s.

(*
(* Stable bottom-up merge sort *)

Fixpoint next (A : Set) (cmp : total_order A)
              (u : list (list A)) : list (list A) :=
  match u with
    s::t::u' => merge A cmp s t :: next A cmp u'
  |        _ => u
  end.

(* Require Import Omega. *)
Search (forall x y, S x < S y -> x < y).
Search (forall x y, x < y -> S x < S y).

Lemma next_level :
  forall (A : Set) (cmp : total_order A)
         (u s : list (list A)) (a b : list A),
  a::b::s = u -> length (next A cmp u) < length u.
Proof.
intros.
induction u.
  - discriminate H.
  - unfold next.
    fold next.
    case_eq u.
      * intro uempty.
        rewrite uempty in H. (* contradiction.? *)
        inversion H.
      * intros.
        simpl.
        apply Lt.lt_n_S.
        apply IHu.
        

Fixpoint solo (A : Set) (cmp : total_order A)
              (s : list A) : list (list A) :=
  match s with
       [] => []
  | x::s' => [x] :: solo A cmp s'
  end.

Fixpoint all (A : Set) (cmp : total_order A)
             (s : list (list A)) : list A :=
  match s with
    [s'] => s'
  |    _ => all A cmp (next A cmp s)
  end.
*)

(*
(* Unstable top-down merge sort *)

Fixpoint cut (A : Set) (s t u : list A) :=
  match t, u with
    y::t', _::_::u' => cut A (y::s) t' u'
  | _, _            => (s, t)
  end.

Print cut.

Definition split (A : Set) (s : list A) :=
  cut A [] s s.

Require Import FunInd Arith Recdef Wf_nat.

Function tms (A : Set) (cmp : total_order A)
         (s : list A) {measure length s} : list A :=
  match s with
    [] | [_] => s
  | _  =>
      let (rpre, suff) := split A s
      in merge A cmp (tms A cmp rpre) (tms A cmp suff)
  end.
Proof.
  - intros.

    unfold split in teq1.
 (*   rewrite <- teq in *.
    rewrite <- teq0 in *.
*)    unfold cut in teq1.
    simpl.

    rewrite <- teq in *.
    rewrite <- teq0 in *.

      -

    induction l0.
    rewrite <- teq in *.
    rewrite <- teq0 in *.
*)
*)

(*Fixpoint rev_append (A : Set) (s t : list A) :=
  match s with
       [] => t
  | x::s' => rev_append A s' (x::t)
  end.

Lemma split_undone :
  forall (A : Set) (s : list A),
  let (rpre, suff) := split A s
  in rev_append A rpre suff = s.
Admitted. (* TODO *)

Lemma rpre_suff :
  forall (A : Set) (s t u : list A),
  rev_append A s t = u -> length s + length t = length u.
Admitted. (* TODO *)
*)

(*
Definition pair_order (a b : Set)
  (ord_a : total_order a) (ord_b : total_order b) :=
    forall (p1 p2 : a * b), (* p1 <= p2 in mind *)
       proj1_sig ord_a (fst p1) (fst p2) = true
    \/ proj1_sig ord_b (snd p1) (snd p2) = true.

(*
Lemma pair_order_is_total :
  forall (a b : Set) (ord_a : total_order a) (ord_b : total_order b),
   pair_order a b ord_a ord_b -> total_order (a*b). (* Wrong. *)
Proof.
intros.
*)

(* Partial order *)

Lemma partial_order : forall (a : Set) (cmp : total_order a) (x y : a),
  proj1_sig cmp x y = false -> proj1_sig cmp y x = true /\ x <> y.
Proof.
  destruct cmp as (rel, (antisym, (trans, conn))).
  simpl.
  intros.
  case (conn x y).
  - rewrite H. intro. discriminate. (* or "congruence" *)
  - intro Hyx.
    split.
    + assumption.
    + intro Heq. (* x <> y is x = y -> False *)
      rewrite Heq in *.
      rewrite H in Hyx.
      discriminate.
Qed.
*)
