From mathcomp.ssreflect 
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
From Contracts
Require Import Automata2 CTL.
  
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Encoding of the Crowdfunding contract from the Scilla whitepaper *)
(* Extended with a branching-time temporal logic *)

Section Crowdfunding.

Record crowdState := CS {
   owner_mb_goal : address * nat * value;
   backers : seq (address * value);
   funded : bool;
}.

(* Administrative setters/getters *)
Definition get_owner cs : address := (owner_mb_goal cs).1.1.
Definition get_goal cs : value := (owner_mb_goal cs).2.
Definition get_max_block cs : nat := (owner_mb_goal cs).1.2.

Definition set_backers cs bs : crowdState :=
  CS (owner_mb_goal cs) bs (funded cs).

Definition set_funded cs f : crowdState :=
  CS (owner_mb_goal cs) (backers cs) f.

(* Parameters *)
Variable init_owner : address.
Variable init_max_block : nat.
Variable init_goal : value.

(* Initial state *)
Definition init_state := CS (init_owner, init_max_block, init_goal) [::] false.

(*********************************************************)
(********************* Transitions ***********************)

(***********************************************************)
(**         **TEMPORAL** Correctness properties           **)
(***********************************************************)

(************************************************************************
1. Until the funded flag has been flipped, meaning that the owner got the
funds, the contract will have enough funds to reimburse every backer.
 ************************************************************************)
(* Important reminder: supply pred S with crowdState and not world crowdState *)

Definition notfunded_pred : pred crowdState :=
  fun w => funded (state (st w)) = false.
Definition balance_sufficient_pred : pred crowdState :=
  fun s => sumn (map snd (backers (state (st s)))) <= balance (st s).
(*
Lemma temporal_balance_backed :
  forall (w : world crowdState),
    AllBox crowd_prot (notfunded_pred --> balance_sufficient_pred) w.


Proof.
  intro w.
  unfold AllBox.
  intros p H_fst n.
  unfold forces.
  unfold notfunded_pred.
  unfold balance_sufficient_pred.
  unfold Impl.
  unfold not. 
  unfold forces.
  destruct p as [path path_fact].
  unfold path_predicate in path_fact.
  unfold reachability in path_fact.
  (* Study Ilya's original proof *)
Admitted. *)

(************************************************************************
2. Until the backer claims his donation back, the contract doesn't drop
the records of each backer's donations.
 ************************************************************************)
                                                                        

(* Definition step_world (w : world) : world :=
  let: CState id bal s := st w in
  let: bc := b w in
  let: m := inFlight w in
  let: n := seq.find (fun t => ttag t == method m) (transitions p) in
  let: tr := nth (idle S) (transitions p) n in
  let: (s', out) := (tfun tr) id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  mkW m (CState id bal' s') bc out. *)

(* Definition step_claim_world (w : world crowdState) : world crowdState :=
  let: CState id bal s := st w in
  let: bc := b w in
  let: m := inFlight w in
  let: (s', out) := claim_fun id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  mkW m (CState id bal' s') bc out. *)
  
(* Definition step_claim_state pre bc m : cstate crowdState :=
  let: CState id bal s := pre in
  let: (s', out) := claim_fun id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  CState id bal' s'. *)

(* Definition reachable_via_message_sender (cs1 cs2 : cstate crowdState) : address -> Prop := fun n => 
  exists (bc : bstate) (m : message),
    step_state P cs1 bc m = cs2 /\ sender m = n. *)

  (* This can't be defined solely in pred because the statement is about messages *)
  (*
Definition claim_from_pred (n : address) : pred crowdState :=
  fun w => sender (inFlight w) = n.
Definition donated_pred (b : address) (d : value) : pred crowdState :=
  fun s => (filter [pred e | e.1 == b] (backers (state (st s)))) == [::(b, d)].
       
Lemma temporal_donation_preserved (b : address) (d : value) :
  forall (w : world crowdState),
    (donated_pred b d w) -> AllWait crowd_prot (donated_pred b d) (claim_from_pred b) w.


Proof.
  intros w H_donated.
  unfold AllWait.
  unfold AllRelease.
  unfold ExistsUntil.
  unfold Neg.
  unfold satisfies.
  intros. destruct H.
  destruct x as [path path_fact].
  simpl in *.
  destruct H.
  destruct H0 as [spot ?].
  destruct H0.
  unfold first in H.
  rewrite <- H in H_donated.
  assert (forall j, donated_pred b d (path j)).
  { induction j.
    - exact H_donated.
    - unfold path_predicate in path_fact.
    specialize (path_fact j).
    unfold reachability in path_fact.
    unfold step_world in *.
    
    unfold first in H.
  

  Print path_predicate.
  Abort. *)
    
(************************************************************************
3. The final property: if the campaign has failed, every registered backer 
can get its donation back.
 *************************************************************************)
(*
Definition balance_exceeded_pred : pred crowdState := fun w => balance (st w) < (get_goal (state (st w))).
Definition block_exceeded (bc : bstate) : pred crowdState := fun w => get_max_block (state (st w)) < block_num bc.

Definition campaign_failed (b : address) (d : value) (bc : bstate) : pred crowdState := fun w => 
    (block_exceeded bc & balance_exceeded_pred & notfunded_pred & donated_pred b d) w.


Lemma can_claim_back (n : address) (d : value) (bc : bstate) :
  forall w : world crowdState,
    AllWait crowd_prot (campaign_failed n d bc) (claim_from_pred n) w.
Proof. Abort.
*)
(************************************************************************
4. The additional property: if the campaign has succeeded, the owner can 
get funds to kickstart the campaign.
 *************************************************************************)
(*
Definition owner_gets_funds_pred : pred crowdState := fun w =>
                                                        sender (inFlight w) = get_owner (state (st w)).
                                              
Lemma can_get_funds :
  forall w : world crowdState,
    AllBox crowd_prot (balance_exceeded_pred --> owner_gets_funds_pred) w.
Proof.

Abort. 
*)
End Crowdfunding. 
