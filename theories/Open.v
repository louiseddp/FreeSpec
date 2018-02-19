Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import FreeSpec.Control.Either.
Require Import Coq.Program.Equality.

Import ListNotations.
Local Open Scope list_scope.

(** If you use polymorphic definition, do no use function from the
    standard library. Define your own.
 *)

Polymorphic Fixpoint cardinal
            {a:  Type}
            (l:  list a)
  : nat :=
  match l with
  | _ :: rst
    => S (cardinal rst)
  | nil
    => O
  end.

Inductive inhabited
  : Type.

Polymorphic Fixpoint get
            (set:  list Type)
            (n:    nat)
            {struct n}
  : Type :=
  match n, set with
  | 0, t :: _
    => t
  | S n, _ :: set'
    => get set' n
  | _, _
    => inhabited
  end.

Polymorphic Inductive union
            (set:  list Type)
  : Type :=
| OneOf {t:   Type}
        (n:   nat)
        (H:   get set n = t)
        (H':  n < cardinal set)
        (x:   t)
  : union set.

Arguments OneOf [set t] (n H H' x).

Polymorphic Inductive product
  : list Type -> Type :=
| Acons (a:    Type)
        (x:    a)
        (set:  list Type)
        (rst:  product set)
  : product (a :: set)
| Anil
  : product [].

Arguments Acons [a] (x) [set] (rst).

Polymorphic Fixpoint fetch
            {set:  list Type}
            (x:    product set)
            (n:    nat)
            (H:    n < cardinal set)
  : get set n.
case_eq set.
+ intros Heq.
  subst.
  cbn in H.
  omega.
+ intros T l Heq.
  subst.
  dependent induction x.
  induction n.
  exact x.
  cbn.
  apply fetch.
  ++ exact x0.
  ++ cbn in H.
     omega.
Defined.

Polymorphic Fixpoint swap
            {set:  list Type}
            (x:    product set)
            (n:    nat)
            (H:    n < cardinal set)
            (v:    get set n)
            {struct x}
  : product set.
case_eq set.
+ intros Heq.
  subst.
  cbn in H.
  omega.
+ intros T l Heq.
  subst.
  dependent induction x.
  induction n.
  ++ exact (Acons v x0).
  ++ refine (Acons x _).
     apply (swap l x0 n).
     +++ cbn in H.
         omega.
     +++ exact v.
Defined.

Polymorphic Class Contains
            (t:    Type)
            (set:  list Type)
  := { rank:            nat
     ; rank_get_t:      get set rank = t
     ; rank_bound:      rank < cardinal set
     }.

Arguments rank (t set) [_].
Arguments rank_get_t (t set) [_].
Arguments rank_bound (t set) [_].

Polymorphic Fixpoint remove
            (set:  list Type)
            (n:    nat)
  : list Type :=
  match set, n with
  | _ :: rst, 0
    => rst
  | x :: rst, S n
    => x :: remove rst n
  | _, _
    => []
  end.

Polymorphic Instance Contains_nat
            (set:  list Type)
            (n:    nat)
            (H:    n < cardinal set)
  : Contains (get set n) set :=
  { rank        := n
  ; rank_get_t  := eq_refl
  ; rank_bound  := H
  }.

Polymorphic Instance Contains_head
            (t:    Type)
            (set:  list Type)
  : Contains t (cons t set) :=
  { rank        := 0
  ; rank_get_t  := eq_refl
  }.
+ apply Nat.lt_0_succ.
Defined.

Polymorphic Instance Contains_tail
            (t any:  Type)
            (set:    list Type)
            (H:      Contains t set)
  : Contains t (cons any set) :=
  { rank       := S (rank t set)
  }.
+ apply rank_get_t.
+ cbn.
  apply lt_n_S.
  apply rank_bound.
Defined.

Polymorphic Definition inj
            {t:    Type}
            {set:  list Type} `{Contains t set}
            (x:    t)
  : union set :=
  OneOf (rank t set) (rank_get_t t set) (rank_bound t set) x.

Ltac evaluate_exact v :=
  let x := fresh "x" in
  let Heqx := fresh "Heqx" in
  remember v as x eqn:Heqx;
  vm_compute in Heqx;
  match type of Heqx with
  | x = ?ev => exact ev
  end.

Ltac inj v :=
  match goal with
  | [ |- union ?set]
    => evaluate_exact (@inj _ set _ v)
  end.

Section DoesItWork.
  Definition test_bool
    : union [bool; nat] :=
    inj true.

  Definition test_nat
    : union [bool; nat] :=
    inj 0.
End DoesItWork.

Definition visit
           {t:    Type}
           {set:  list Type} `{Contains t set}
           {a:    Type}
           (x:    product set)
           (f:    t -> a * t)
  : a * product set.
  refine (
  match fetch x (rank t set) (rank_bound t set)
        return get set (rank t set) = t -> a * product set
  with
  | v
    => fun (H: get set (rank t set) = t)
       => _
  end (rank_get_t t set)
    ).
  remember (f (eq_rect (get set (rank t set)) (fun X => X) v t H)) as p.
  induction p as [v' u].
  refine (v', swap x (rank t set) (rank_bound t set) _).
  refine (eq_rect t (fun X => X) u (get set (rank t set)) _).
  symmetry.
  exact H.
Defined.