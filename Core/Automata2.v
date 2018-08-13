From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac impl_e P P_implies_Q :=
  apply P_implies_Q in P.
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).

(* A semantics of contracts with decidable deterministic transitions *)
Section State.

Definition value := nat.
Definition address := nat.
Definition tag := nat.
Definition payload := (seq (nat * seq nat)).

(* Message with a payload *)
Record message := Msg {
      val    : value;
      sender : address;
      to     : address;
      method : tag;
      body   :  payload
}.

(* Augmented state of a contract *)
Record cstate (T : Type) := CState {
      my_id : address;
      balance : value;
      state : T
}.

(* Global blockchain state *)
Record bstate := BState {
      block_num : nat;
}.

End State.

Section Protocol.
  
Section Transitions.

(* State type *)
Variable S: Type.

(* A response from a transition *)
Definition resp_type := (address * value * tag * payload)%type.
Definition msg_bal (rt : resp_type) : value := rt.1.1.2.

(* Transitions are functions *)
Definition trans_fun_type :=
  address -> value -> S -> message -> bstate -> (S * option message).
  
(* Contract transition in the spirit of I/O automata *)
Record ctransition :=
  CTrans {
      (* Unique tag of a transition in the protocol *)
      ttag : tag;
      
      (* Function (bstate, state, msg) :-> (state', option msg') *)
      tfun : trans_fun_type;
  }.

Definition idle_fun : trans_fun_type := fun _ _ s _ _ => (s, None).
Definition idle := CTrans 0 idle_fun.

End Transitions.

Record Protocol (S : Type) :=
  CProt {
      (*Account id *)
      acc : address;
      (* Initial balance *)
      init_bal : nat;
      (* Initial state of a protocol *)
      init_state : S;      
      (* Protocol comes with a set of transitions *)
      transitions : seq (ctransition S);
      (* All transitions have unique tags *)
      _ : uniq (map (@ttag _) transitions)
    }.

Definition tags {S : Type} (p : Protocol S) :=
  map (@ttag _) (transitions p).

End Protocol.

Section Semantics.

Variables (S : Type) (p : Protocol S).

(* Blockchain schedules *)
Definition schedule := seq (bstate * message).

(* In a well-formed schedule block numbers only grow *)
Fixpoint wf_sched (sch : schedule) :=
  if sch is s :: sch'
  then let bnum := block_num s.1 in
       all [pred s' | bnum <= block_num s'.1] sch' && wf_sched sch'
  else true.

Definition step_state pre bc m : cstate S :=
  let: CState id bal s := pre in
  let: n := seq.find (fun t => ttag t == method m) (transitions p) in
  let: tr := nth (idle S) (transitions p) n in
  let: (s', out) := (tfun tr) id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  CState id bal' s'.

Definition state0 := CState (acc p) (init_bal p) (init_state p).

(*****************************************************)
(*            Some modal connectives                 *)
(*****************************************************)
(* A temporal CTL semantics *)
Definition pred := cstate S -> Prop.
Definition reachability : cstate S -> cstate S -> Prop := fun s1 s2 =>
                                                          exists (bc : bstate) (m : message),
                                                            step_state s1 bc m = s2.
Definition path := nat -> cstate S.
Definition first (p : path) : cstate S := p 0. 

(* A good path is a path that begins with the initial state and satisfies the reachability relation *)
Definition path_predicate (p : path) := (* p 0 = state0 /\ *) forall n, reachability (p n) (p (n + 1)).
Definition gpath : Type := {p : path & path_predicate p }.
Definition gpath_proj1 : gpath -> (nat -> cstate S) := fun gp =>  match gp with | existT a _ => a end.
Coercion gpath_proj1 : gpath >-> Funclass.

(* State satisfaction *)
Definition forces (s : cstate S) (p : pred) : Prop :=
  p s.
Notation "w '|=' P" := (forces w P) (at level 80, no associativity).

(* Stuff in Prop *)
Axiom LEM : forall P : Prop, P \/ ~ P.
Definition entails P Q : Prop :=
  forall w,  (w |= P) -> (w |= Q).
Definition equiv P Q : Prop :=
  entails P Q /\ entails Q P.

(* Stuff in pred *)
Parameter Top : pred.
Parameter Bottom : pred.
Definition Neg P : pred := fun w =>
                             ~(w |= P).
Definition Conj P Q : pred := fun w =>
                                (w |= P) /\ (w |= Q).
Definition Disj P Q : pred := fun w =>
                                (w |= P) \/ (w |= Q).
Definition Impl P Q : pred := fun w =>
                                ~(w |= P) \/ (w |= Q).

Delimit Scope temporal_logic with temporal_logic.
Open Scope temporal_logic.

Notation "P <=> Q" := (equiv P Q) (at level 35, no associativity).
Notation "~~ P" := (Neg P) : temporal_logic.
Notation "P & Q" := (Conj P Q) (at level 65, left associativity) : temporal_logic.
Notation "P || Q" := (Disj P Q) : temporal_logic.
Notation "P --> Q" := (Impl P Q) (at level 35, no associativity) : temporal_logic.

(* Temporal operator definitions *)
Definition AllNext (P : pred) : pred := fun w =>  
  forall p, first p = w ->
            p 1 |= P.
Definition ExistsNext (P : pred) : pred := fun w =>  
  exists p, first p = w ->
            p 1 |= P.
Definition AllBox P : pred := fun w =>  
  forall p, first p = w ->
            forall n, p n |= P.
Definition ExistsBox P : pred := fun w =>  
  exists p, first p = w ->
            forall n, p n |= P.
Definition AllFuture P : pred := fun w =>  
  forall p, first p = w ->
            exists n, p n |= P.
Definition ExistsFuture P : pred := fun w =>  
  exists p, first p = w ->
            exists n, p n |= P.
Definition AllUntil P Q : pred := fun w =>  
  forall p, first p = w ->
            exists n, p n |= Q /\
                      forall m, m < n -> p m |= P.
Definition ExistsUntil P Q : pred := fun w =>  
  exists p, first p = w ->
            exists n, p n |= Q /\
                      forall m, m < n -> p m |= P.

(* Temporal operator extensions *)
Definition AllRelease P Q : pred := 
  ~~ (ExistsUntil (~~ P) (~~ Q)).
Definition ExistsRelease P Q : pred :=
  ~~ (AllUntil (~~ P) (~~ Q)).
Definition AllWait P Q : pred :=
  AllRelease P (P || Q).
Definition ExistsWait P Q : pred :=
  ExistsRelease P (P || Q).

Close Scope temporal_logic.

(* Given the sigma-type gpath, we can safely say this
because gpath will handle the proof of reachability *)
Definition reachable (st st' : cstate S) :=
  exists (p : gpath),
  exists (n m : nat),
    p n = st /\ p m = st.

(* A stronger safety property *)
(* The former safety property said that all states in a viable execution path
hold a certain property *)
(* If we assume that "path" already comes with a viability *)
Definition safe (P : pred) (p : gpath) :=
  forall n : nat, P (p n).

Lemma safe_ind :
  forall (P : pred) (p : gpath),
  P (p 0) ->
  (forall n : nat, P (p n) -> P (p (n.+1))) ->
                  forall n : nat, P (p n).
Proof.
  intros P path.
  intros H_0 HI m. 
  elim m.
  exact H_0.
  apply HI.
Qed. 

End Semantics.