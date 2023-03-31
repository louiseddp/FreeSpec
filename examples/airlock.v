(* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. *)

(* Copyright (C) 2018–2020 ANSSI *)

From Coq Require Import Arith.
From FreeSpec.Core Require Import Core CoreFacts.
Add Rec LoadPath "/home/louise/github.com/louiseddp/sniper" as Sniper.
From Sniper Require Import Sniper.
From Hammer Require Import Hammer.

#[local] Open Scope nat_scope.

Create HintDb airlock.

(** * Specifying *)

(** ** Doors *)

Inductive door : Type := left | right.

Definition door_eq_dec (d d' : door) : { d = d' } + { ~ d = d' } :=
  ltac:(decide equality).

Inductive DOORS : interface :=
| IsOpen : door -> DOORS bool
| Toggle : door -> DOORS unit.

Inductive bool_tag := 
bool_tag0.

Inductive unit_tag :=
unit_tag0.

Inductive DOORS' : Type :=
| IsOpen' (t : bool_tag) (d : door) : DOORS'
| Toggle' (t : unit_tag) (d : door) : DOORS'.

Inductive DOORS'' : bool -> Type :=
| IsOpen'' (d : door) : DOORS'' true
| Toggle'' (d : door) : DOORS'' false.

Generalizable All Variables. (* Permet de ne pas introduire les variables
dont Coq peut deviner le type *)



Definition is_open `{Provide ix DOORS} (d : door) : impure ix bool :=
  request (IsOpen d).

Print is_open. (*ix est un implicite *)

Definition toggle `{Provide ix DOORS} (d : door) : impure ix unit :=
  request (Toggle d).


(* let* = sucre syntaxique pour le bind *)
Definition open_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when (negb open) (toggle d).

Definition close_door `{Provide ix DOORS} (d : door) : impure ix unit :=
  let* open := is_open d in
  when open (toggle d).

(** ** Controller *)

Inductive CONTROLLER : interface :=
| Tick : CONTROLLER unit
| RequestOpen (d : door) : CONTROLLER unit.

Print request.

Definition tick `{Provide ix CONTROLLER} : impure ix unit :=
  request Tick.

Definition request_open `{Provide ix CONTROLLER} (d : door) : impure ix unit :=
  request (RequestOpen d).

Definition co (d : door) : door :=
  match d with
  | left => right
  | right => left
  end.

Definition controller `{Provide ix DOORS, Provide ix (STORE nat)}
  : component CONTROLLER ix :=
  fun _ op =>
    match op with
    | Tick =>
      let* cpt := get in
      when (15 <? cpt) begin
        close_door left;;
        close_door right;;
        put 0
      end
    | RequestOpen d =>
        close_door (co d);;
        open_door d;;
        put 0
    end.
Print "+".

(** * Verifying the Airlock Controller *)

(** ** Doors Specification *)

(** *** Witness States *)

Definition Ω : Type := bool * bool.

Definition sel (d : door) : Ω -> bool :=
  match d with
  | left => fst
  | right => snd
  end.

Definition tog (d : door) (ω : Ω) : Ω :=
  match d with
  | left => (negb (fst ω), snd ω)
  | right => (fst ω, negb (snd ω))
  end.

Lemma tog_equ_1 (d : door) (ω : Ω)
  : sel d (tog d ω) = negb (sel d ω).

Proof.
  destruct d; reflexivity.
Qed.

Lemma tog_equ_2 (d : door) (ω : Ω)
  : sel (co d) (tog d ω) = sel (co d) ω.

Proof.
  destruct d; reflexivity.
Qed.

(** From now on, we will reason about [tog] using [tog_equ_1] and [tog_equ_2].
    FreeSpec tactics rely heavily on [cbn] to simplify certain terms, so we use
    the <<simpl never>> options of the [Arguments] vernacular command to prevent
    [cbn] from unfolding [tog].

    This pattern is common in FreeSpec.  Later in this example, we will use this
    trick to prevent [cbn] to unfold impure computations covered by intermediary
    theorems. *)

#[local] Opaque tog.

Definition step (ω : Ω) (a : Type) (e : DOORS a) (x : a) :=
  match e with
  | Toggle d => tog d ω
  | _ => ω
  end.

(** *** Requirements *)

Inductive doors_o_caller : Ω -> forall (a : Type), DOORS a -> Prop :=

(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)

| req_is_open (d : door) (ω : Ω)
  : doors_o_caller ω bool (IsOpen d)

(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed too for a request to toggle [d] to be valid. *)

| req_toggle (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : doors_o_caller ω unit (Toggle d).

Inductive doors_o_caller' : Ω -> DOORS' -> Prop :=

(** - Given the door [d] of o system [ω], it is always possible to ask for the
      state of [d]. *)

| req_is_open' (d : door) (ω : Ω)
  : doors_o_caller' ω (IsOpen' bool_tag0 d)

(** - Given the door [d] of o system [ω], if [d] is closed, then the second door
      [co d] has to be closed too for a request to toggle [d] to be valid. *)

| req_toggle' (d : door) (ω : Ω) (H : sel d ω = false -> sel (co d) ω = false)
  : doors_o_caller' ω (Toggle' unit_tag0 d).

Print implb.

Definition doors_o_caller_dec (ω : Ω) (d : DOORS') : bool := 
match d with
| IsOpen' _ d => true
| Toggle' _ d =>  if negb (sel d ω) then (negb (sel (co d) ω)) else true
end.

Definition transfo {A : Type} (t: DOORS A) :=
match t with
| IsOpen d => IsOpen' bool_tag0 d
| Toggle d => Toggle' unit_tag0 d
end.

Lemma equivalence A (ω : Ω) (d : DOORS A) :
doors_o_caller ω A d <-> doors_o_caller' ω (transfo d).
Proof. split.
  + intro H. destruct d.
      - simpl. constructor.
      - simpl. constructor. inversion H. apply H2.
  + intro H. destruct d.
      - simpl in H. constructor.
      - simpl in H. constructor. inversion H. apply H2. Qed.

Lemma caller_dec ω d : doors_o_caller' ω d <-> doors_o_caller_dec ω d = true.
Proof.
split; intro H; destruct d.
  - simpl. reflexivity.
  - simpl. inversion H. destruct (sel d ω) eqn:E.
simpl. reflexivity. simpl. destruct ((sel (co d) ω)). firstorder. firstorder.
  - subst. destruct t; econstructor.
  - subst. destruct t; constructor. simpl in H.  intros. destruct (negb (sel d ω)) eqn:E.
    + rewrite <- Bool.negb_involutive in H. simpl in H. 
generalize dependent (sel (co d) ω). intros. sauto lq:on.
    + generalize dependent (sel d ω). intros. sauto lq:on. Qed.

Lemma doors_o_caller_inversion : 
forall ω (a : Type) (d: DOORS a) (H : doors_o_caller ω a d), 
(exists (d0 : door) (ω0 : Ω),  
ω0 = ω /\ @eq Type bool a /\ 
existT (fun x : Type => DOORS x) bool (IsOpen d0)
= existT (fun x : Type => DOORS x) a d)
\/ (exists (d0 : door) (ω0 : Ω) (H : sel d0 ω0 = false -> sel (co d0) ω0 = false),  
ω0 = ω /\ @eq Type unit a /\
existT (fun x : Type => DOORS x) unit (Toggle d0)
= existT (fun x : Type => DOORS x) a d).
Proof. intros. inversion H. left.
exists d0. exists ω0. split. assumption. split. reflexivity.
reflexivity. right.
exists d0. exists ω. exists H3. split. reflexivity. split. reflexivity.
reflexivity. Qed.

#[global] Hint Constructors doors_o_caller : airlock.

(** *** Promises *)

Inductive doors_o_callee : Ω -> forall (a : Type), DOORS a -> a -> Prop :=

(** - When a system in a state [ω] reports the state of the door [d], it shall
      reflect the true state of [d]. *)

| doors_o_callee_is_open (d : door) (ω : Ω) (x : bool) (equ : sel d ω = x)
  : doors_o_callee ω bool (IsOpen d) x

(** - There is no particular doors_o_calleeises on the result [x] of a request for [ω] to
      close the door [d]. *)

| doors_o_callee_toggle (d : door) (ω : Ω) (x : unit)
  : doors_o_callee ω unit (Toggle d) x.

Inductive doors_o_callee' : Ω -> DOORS' -> (bool*unit) -> Prop :=
| doors_o_callee_is_open' (d : door) (ω : Ω) (y : bool*unit) (equ : sel d ω = fst y)
  : doors_o_callee' ω (IsOpen' bool_tag0 d) y
| doors_o_callee_toggle' (d : door) (ω : Ω) (y : bool*unit)
  : doors_o_callee' ω (Toggle' unit_tag0 d) y. 


Definition doors_o_callee'_dec (ω : Ω) (d : DOORS') (p : bool*unit) : bool := 
match d with
| IsOpen' b d => fst p <---> sel d ω
| Toggle' b d => true
end.

Lemma callee_dec ω d p : doors_o_callee' ω d p <-> doors_o_callee'_dec ω d p = true.
Proof.
split; intro H; destruct d.
  - simpl. inversion H. subst. generalize dependent (fst p). generalize dependent (sel d ω).
sauto lq:on.
  -  subst.  subst. generalize dependent (fst p). generalize dependent (sel d ω).
sauto lq:on.
  - subst. sauto lq:on. 
  - subst. sauto lq:on. Qed.

Lemma two_elem : ~ (@eq Type unit bool).
Proof.
intro Helim.
assert (H : forall (x : unit), x = tt).
intro. destruct x. reflexivity.
assert (H1 : forall (x : bool), x = true \/ x = false).
intro. destruct x; auto.
assert (H2 : true <> false).
intro Helim2. inversion Helim2.
assert (H3 : forall (x y : bool), x = y).
intros x y. Admitted. 


Require Import Coq.Program.Equality.

Lemma equivalence' (b : bool) (c: unit) (ω : Ω) :
(forall (d : DOORS bool), doors_o_callee ω bool d b <-> doors_o_callee' ω (transfo d) (b, c))
/\ 
(forall (d : DOORS unit), doors_o_callee ω unit d c <-> doors_o_callee' ω (transfo d) (b, c)).
Proof. split. split.
  + dependent destruction d.
      - simpl. intros. inversion H. econstructor 1. ssubst.
apply Eqdep.EqdepTheory.inj_pair2 in H2. simpl; assumption.
      - intros. inversion H. assert (Hfalse : False). apply two_elem. assumption.  inversion Hfalse.
assert (Hfalse : False). apply two_elem. assumption.  inversion Hfalse.
  +  dependent destruction d.
    - intro H. inversion H. subst. constructor. simpl in equ. assumption.
    - assert (Hfalse : False). apply two_elem. assumption. inversion Hfalse.
  + split. dependent destruction d; intro H; simpl in *.
    * 
assert (Hfalse : False). apply two_elem. symmetry. assumption. inversion Hfalse.
    * econstructor.  
    * intro H. dependent destruction d. assert (Hfalse : False). apply two_elem. symmetry. assumption. inversion Hfalse.
    simpl in H. inversion H. subst. constructor. 
  Qed.

Lemma doors_o_callee_inversion : 
forall ω (a : Type) (d: DOORS a) (x : a) (H : doors_o_callee ω a d x), 
(exists (d0 : door) (ω0 : Ω) (x: bool) (equ : sel d0 ω0 = x),  
ω0 = ω /\ @eq Type bool a /\ 
existT (fun x : Type => DOORS x) bool (IsOpen d0)
= existT (fun x : Type => DOORS x) a d) 
\/ (exists (d0 : door) (ω0 : Ω) (x : unit),  
ω0 = ω /\ @eq Type unit a /\
existT (fun x : Type => DOORS x) unit (Toggle d0)
= existT (fun x : Type => DOORS x) a d).
Proof. intros. inversion H. left.
exists d0. exists ω. exists x0. exists equ. split. reflexivity. split. 
assumption. assumption.
right.
exists d0. exists ω. exists x0. split. reflexivity. split. assumption. assumption. Qed.

#[global] Hint Constructors doors_o_callee : airlock.

Definition doors_contract : contract DOORS Ω :=
  make_contract step doors_o_caller doors_o_callee.

(** ** Intermediary Lemmas *)

(** Closing a door [d] in any system [ω] is always a respectful operation. *)

Definition foo := (prod_types, MayProvide, Provide, interface).

Lemma close_door_respectful `{Provide ix DOORS} (ω : Ω) (d : door)
  : pre (to_hoare doors_contract (close_door d)) ω.

Proof.
  (* We use the [prove_program] tactics to erase the program monad *)
prove impure.
sauto. apply equivalence. 
apply equivalence in o_caller. pose proof (p := equivalence').
edestruct p.  rewrite H1 in o_caller0. sauto.

(* apply equivalence; simpl.
apply caller_dec. scope. destruct x3 ; destruct x4; auto.
destruct x ; destruct x0; auto. destruct x ; destruct x0; auto.
- clear H3 H4 H H0 gen_MayProvide0 gen_MayProvide4 gen_MayProvide6 gen_MayProvide5 gen_MayProvide3 gen_MayProvide2 gen_MayProvide1 proj_MayProvide
H8 H5 H6 H11 H9. 
snipe. *)
Qed.


#[global] Hint Resolve close_door_respectful : airlock.

Lemma open_door_respectful `{Provide ix DOORS} (ω : Ω)
    (d : door) (safe : sel (co d) ω = false)
  : pre (to_hoare doors_contract (open_door (ix := ix) d)) ω.

Proof.
  prove impure. 
  - sauto.
  - sauto.
Qed.

#[global] Hint Resolve open_door_respectful : airlock.

Lemma close_door_run `{Provide ix DOORS} (ω : Ω) (d : door) (ω' : Ω) (x : unit)
  (run : post (to_hoare doors_contract (close_door d)) ω x ω')
  : sel d ω' = false.

Proof.
  unroll_post run. (* unroll_post -> tous les chemins d'exécution possibles pour arriver à la conclusion
et retrouve les callee obligations que l'on a à ce moment *)
  + (* sauto dep:on. *) rewrite tog_equ_1. pose proof (p := equivalence'). edestruct p.
  rewrite H3 in H1. rewrite H4 in H2. sauto.
  +  pose proof (p := equivalence'). edestruct p. rewrite H2 in H1.
sauto.

 (* note: ici on peut faire clear H0. clear H. *)
Qed.

#[global] Hint Resolve close_door_run : airlock.

#[local] Opaque close_door.
#[local] Opaque open_door.
#[local] Opaque Nat.ltb.

Remark one_door_safe_all_doors_safe (ω : Ω) (d : door)
    (safe : sel d ω = false \/ sel (co d) ω = false)
  : forall (d' : door), sel d' ω = false \/ sel (co d') ω = false.

Proof.
  intros d'.
  destruct d; destruct d'; auto.
  + cbn -[sel].
    now rewrite or_comm.
  + cbn -[sel].
    fold (co right).
    now rewrite or_comm.
Qed.

(** The objective of this lemma is to prove that, if either the right door or
    the left door is closed, then after any respectful run of a computation
    [p] that interacts with doors, this fact remains true. *)

#[local] Opaque sel.

Lemma respectful_run_inv `{Provide ix DOORS} {a} (p : impure ix a)
    (ω : Ω) (safe : sel left ω = false \/ sel right ω = false)
    (x : a) (ω' : Ω) (hpre : pre (to_hoare doors_contract p) ω)
    (hpost : post (to_hoare doors_contract p) ω x ω')
  : sel left ω' = false \/ sel right ω' = false.

(** We reason by induction on the impure computation [p]:

    - Either [p] is a local, pure computation; in such a case, the doors state
      does not change, hence the proof is trivial.

    - Or [p] consists in a request to the doors interface, and a continuation
      whose domain satisfies the theorem, i.e. it preserves the invariant that
      either the left or the right door is closed.  Due to this hypothesis, we
      only have to prove that the first request made by [p] does not break the
      invariant. We consider two cases.

      - Either the computation asks for the state of a given door ([IsOpen]),
        then again the doors state does not change and the proof is trivial.
      - Or the computation wants to toggle a door [d].  We know by hypothesis
        that either [d] is closed or [d] is open (thanks to the
        [one_door_safe_all_doors_safe] result and the [safe] hypothesis).
        Again, we consider both cases.

         - If [d] is closed —and therefore will be opened—, then because we
           consider a respectful run, [co d] is necessarily closed too (it is a
           requirements of [door_contract]). Once [d] is opened, [co d] is still
           closed.
         - Otherwise, [co d] is closed, which means once [d] is toggled (no
           matter its initial state), then [co d] is still closed.

         That is, we prove that, when [p] toggles [d], [co d] is necessarily
         closed after the request has been handled.  Because there is at least
         one door closed ([co d]), we can conclude that either the right or the
         left door is closed thanks to [one_door_safe_all_doors_safe]. *)

Proof.
  fold (co left) in *.
  revert ω hpre hpost safe.
  induction p; intros ω hpre run safe.
  + now unroll_post run.
  + unroll_post run.
    assert (hpost : post (interface_to_hoare doors_contract β e) ω x0 ω0). {
      split; [apply H2|now rewrite H3].
    }
    apply H1 with (ω:=ω0) (β:=x0); auto; [now apply hpre|].
    cbn in *.
    unfold gen_caller_obligation, gen_callee_obligation, gen_witness_update in *.
    destruct (proj_p e) as [e'|].
    ++ destruct hpost as [o_callee equω].
       destruct e' as [d|d].
       +++ rewrite H3.
           apply safe.
       +++ apply one_door_safe_all_doors_safe with (d := d);
             apply one_door_safe_all_doors_safe with (d' := d) in safe;
             subst.
           destruct hpre as [hbefore hafter].
           inversion hbefore; ssubst.
           cbn.
           destruct safe as [safe|safe].
           all: right; rewrite tog_equ_2; auto.
    ++ destruct hpost as [_ equω].
       subst.
       exact safe.
Qed.

(** ** Main Theorem *)

Print MayProvide.
Check StrictProvide2.
Check Distinguish.
Print STORE.
Print interface.
Check contract.
Print correct_component.
Print component.
Check no_contract.
Check doors_contract.
Print CONTROLLER.
Set Printing All.
Check controller.

Print Scopes.
Print iplus.

Print pre.
Print impure.
Print hoare.
Print to_hoare.
Print impure.
Print open_door.

Set Printing All.

Lemma controller_correct `{StrictProvide2 ix DOORS (STORE nat)}
  : correct_component controller
                      (no_contract CONTROLLER)
                      doors_contract
                      (fun _ ω => sel left ω = false \/ sel right ω = false).

Proof.
  intros ωc ωd pred a e req.
  assert (hpre : pre (to_hoare doors_contract (controller a e)) ωd).
    (destruct e; prove impure)


Focus 5.  Set Printing All. Check @controller. Check component. Check @to_hoare.
 Check caller_obligation.
with airlock). (* TODO *)
  split; auto.
  intros x ωj' run.
  cbn.
  split.
  + auto with freespec.
  + apply respectful_run_inv in run; auto.
Qed.

Check @controller_correct.
