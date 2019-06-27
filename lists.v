Inductive seq (a : Set) :=
  Nil  : seq a
| Cons : a -> seq a -> seq a.

Notation "[]" := (Nil _).
Notation "[ x | s ]" := 
  (Cons _ x s) (x at level 0, s at level 200).
Notation "[ x ]" := (Cons _ x (Nil _)) (x at level 0).

Print Grammar constr.

Fixpoint len (a : Set) (s : seq a) : nat :=
  match s with
         [] => 0
  | [x | s] => 1 + len a s
  end.

Fixpoint cat (a : Set) (s t : seq a) : seq a :=
  match s with
         [] => t               (* alpha *)
  | [x | s] => [x | cat a s t] (* beta  *)
  end.

(* Page 13 *)

Theorem cat_assoc : forall (a : Set) (s t u : seq a),
  cat a s (cat a t u) = cat a (cat a s t) u.

Proof.
induction s as [| x s].
  - intros t u.
    change (cat a [] (cat a t u)) with (cat a t u).
    change (cat a (cat a [] t) u) with (cat a t u).
    reflexivity.
  - intros t u.
    unfold cat at 1.
    fold cat.
    rewrite (IHs t u).
    unfold cat at -1. (* What? *)
    fold cat.
    reflexivity.
Qed.

(*
    let f replace :=
      match goal with
        [|- ?l = ?r] => 
          change l with replace
      end 
    in f (cat t u).
*)
(*
    match goal with
      [H: ?toto |- ?l = ?r] => 
        idtac "tutu" "l:" l "r:" r;
        match H with
          t => idtac "Found"
        end
    end.
*)

Theorem cat_len : forall (a : Set) (s : seq a) (t : seq a),
  len a (cat a s t) = len a s + len a t. 

Require Import Omega.

Proof.
induction s.
  - intros.
    unfold cat.
    unfold len at 2.
    omega.
  - intro t.
    unfold cat.
    fold cat.
    unfold len at 1.
    fold len.
    unfold len at 2.
    fold len.
    apply eq_S.
    apply IHs.
Qed.

Fixpoint rev0 (a : Set) (s : seq a) : seq a :=
  match s with
         [] => []                    (* gamma *)
  | [x | s] => cat a (rev0 a s) [x]  (* delta *)
  end.

Theorem rev0_len : forall (a : Set) (s : seq a),
  len a (rev0 a s) = len a s.

Require Import Nat.

Proof.
intros.
induction s.
  - unfold rev0.
    reflexivity.
  - unfold rev0.
    fold rev0.
    rewrite cat_len.
    unfold len at 2.
    unfold Nat.add at 2.
    rewrite Nat.add_comm.
    apply eq_S.
    apply IHs.
Qed.

Lemma cat_nil : forall (a : Set) (s : seq a),
  cat a s (Nil a) = s.

Proof.
intros.
induction s.
  - unfold cat.
    reflexivity.
  - unfold cat.
    fold cat.
    rewrite IHs.
    reflexivity.
Qed.

Lemma cat_rev : forall (a : Set) (s t : seq a),
  cat a (rev0 a t) (rev0 a s) = rev0 a (cat a s t).

Proof.
intros.
induction s.
  -rewrite cat_nil.
   unfold cat.
   reflexivity.
 - unfold rev0 at 2.
   fold rev0.
   rewrite cat_assoc.
   rewrite IHs.
   unfold cat at 3.
   fold cat.
   unfold rev0 at 2.
   fold rev0.
   reflexivity.
Qed.
  

Theorem idempotent : forall (a : Set) (s : seq a),
  rev0 a (rev0 a s) = s.

Proof.
intros.
induction s.
  - unfold rev0 at 2.
    reflexivity.
  - unfold rev0 at 2.
    fold rev0.
    rewrite <- cat_rev.
    rewrite IHs.
    unfold rev0.
    unfold cat.
    reflexivity.
Qed.

Fixpoint rcat (a : Set) (l acc : seq a) :=
  match l with
           Nil _ => acc
  | Cons _ hd tl => rcat a tl (Cons a hd acc)
  end.

Definition rev (a : Set) (l : seq a) :=
  rcat a l (Nil a).

Lemma rev_cat : forall a (s t : seq a),
  rcat a s t = cat a (rev a s) t.

Proof.
intros a s.
induction s as [|x s IH].
  - unfold rcat.
    unfold rev.
    unfold rcat.
    unfold cat.
    reflexivity.
  - intro t.
    unfold rcat.
    fold rcat.
    rewrite -> (IH (Cons a x t)).
    change t at 1 with (cat a (Nil a) t).
    change (Cons a x (cat a (Nil a) t)) with
           (cat a (Cons a x (Nil a)) t).
    rewrite cat_assoc.
    rewrite <- (IH (Cons a x (Nil a))).
    unfold rev.
    unfold rcat at 2.
    fold rcat.
    reflexivity.
Qed.

Theorem eq_rev : forall a (s : seq a),
  rev0 a s = rev a s.

Proof.
intros.
induction s as [| x s IH].
  - unfold rev0.
    unfold rev.
    unfold rcat.
    reflexivity.
  - unfold rev0.
    fold rev0.
    rewrite IH.
    rewrite <- rev_cat. 
    unfold rev.
    unfold rcat at 2.
    fold rcat.
    reflexivity.
Qed.

Fixpoint sfst1 (a : Set) (eq : a -> a -> bool) (s : seq a) (x : a) :=
  match s with
         Nil _ => s
  | Cons _ y t => if eq x y then t 
                  else Cons a y (sfst1 a eq t x)
  end.


Fixpoint sfst3 (a : Set) (eq : a -> a -> bool) (s : seq a) (x : a)
               (t u : seq a) :=
  match s with
         Nil _ => u
  | Cons _ y s => if eq x y then rcat a t s 
                  else sfst3 a eq s x (Cons a y t) u
  end. 

Definition sfst2 (a : Set) (eq : a -> a -> bool) 
           (s : seq a) (x : a ) :=
  sfst3 a eq s x s.

Definition compose (a b c : Set) (g : b -> c) (f : a -> b) : a -> c :=
   fun x => g (f x).

Fixpoint map (a b : Set) (f : a -> b) (s : seq a) : seq b :=
  match s with
    Nil _ => Nil b
  | Cons _ hd tl => Cons b (f hd) (map a b f tl)
  end.

Theorem map_comp_comm :
  forall (a b c : Set) (f : a -> b) (g : b -> c) (s : seq a),
  map a c (compose a b c g f) s 
= compose (seq a) (seq b) (seq c) (map b c g) (map a b f) s.

Proof.
intros.
induction s as [| x t].
  - unfold map at 1.
    unfold compose.
    unfold map.
    reflexivity.
  - unfold map at 1.
    fold map.
    rewrite IHt.
    unfold compose.
    unfold map.
    fold map.
    reflexivity.
Qed.

Definition total_order (a : Set) : Set := { 
  cmp : a -> a -> bool | 
  forall x y, x = y \/ cmp x y = true \/ cmp y x = true 
}.

Require Import List.

Fixpoint ins (a : Set) (cmp : total_order a) 
             (s : list a) (x : a) :=
  match s with
    y::s' => 
      match cmp with 
        exist _ cmp' _ =>
          if   cmp' x y
          then x::s 
          else y :: ins a cmp s' x 
      end
  | nil => x::s
  end.

Fixpoint isrt (a : Set) (cmp : total_order a)
              (s : list a) :=
  match s with
     nil => nil
  | x::s => ins a cmp (isrt a cmp s) x
  end.

(* Set Implicit Arguments.*)

Inductive ord_list (a : Set) (cmp : total_order a)
                 : list a -> Prop :=
  ord_nil  : ord_list a cmp nil
| ord_one  : forall x : a, ord_list a cmp (x::nil)
| ord_more : forall (x y : a) (s : list a),
             (let 'exist _ cmp' _ := cmp in
                cmp' x y = true)
             -> ord_list a cmp (y::s)
             -> ord_list a cmp (x::y::s).

(*
(* Unmark View/Display notations for the following: *)
Print exist.
Locate "{ _ : _ | _ }".
{ x : nat | x < 10 }
*)

(* Arguments ord_nil [a]. *)

Print ord_list.

Set Implicit Arguments.

(* (* Three ways: *)
Inductive mylist a :=
  my_nil
| my_cons (hd: a) (tl: mylist a).

| my_cons : a -> mylist a -> mylist a

| my_cons : forall (hd : a) (tl : mylist a), mylist a.
*)

(*
Lemma len_ins : forall (a : Set) (gt : a -> a -> bool)
                       (s : seq a) (x : a),
  len a (Cons a x s) = len a (ins a gt s x).

intros.
induction s as [| y t IH].
  - unfold len at 1.
    unfold ins.
    unfold len.
    reflexivity.
  - unfold len.
    fold len.
    unfold ins.
    fold ins.
    case_eq (gt x y).
    unfold len at 2.
    fold len.
    auto.
    unfold len at 2.
    fold len.
*)
