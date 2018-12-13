From mathcomp.ssreflect 
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
From Contracts
Require Import Automata2 Temporal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(************************************************************************
1. Until the funded flag has been flipped, meaning that the owner got the
funds, the contract will have enough funds to reimburse every backer.
 ************************************************************************)
(* Important reminder: supply pred S with crowdState and not world crowdState *)

Definition notfunded : pred :=
  fun w => funded (state (st w)) = false.
Definition balance_sufficient : pred :=
  fun s => sumn (map snd (backers (state (st s)))) <= balance (st s).

Lemma temporal_balance_backed :
  forall (w : world crowdState),
    w |= (AG (notfunded --> balance_sufficient)).
Proof. Admitted.


(************************************************************************
2. Until the backer claims his donation back, the contract doesn't drop
the records of each backer's donations.
 ************************************************************************)

Definition claim_from (n : address) : pred :=
  fun w => sender (inFlight w) = n.
Definition donated (b : address) (d : value) : pred :=
  fun s => (filter [pred e | e.1 == b] (backers (state (st s)))) == [::(b, d)].
       
Lemma temporal_donation_preserved (b : address) (d : value) :
  forall (w : world crowdState),
    (donated b d w) -> w |= (A [(donated b d) W (claim_from b)]).
Proof. Admitted.
    
(************************************************************************
3. The final property: if the campaign has failed, every registered backer 
can get its donation back.
 *************************************************************************)

Definition balance_exceeded : pred := fun w => balance (st w) < (get_goal (state (st w))).
Definition block_exceeded (bc : bstate) : pred := fun w => get_max_block (state (st w)) < block_num bc.

Definition campaign_failed (b : address) (d : value) (bc : bstate) : pred := fun w => 
    (block_exceeded bc && balance_exceeded && notfunded && donated b d) w.

Lemma can_claim_back (n : address) (d : value) (bc : bstate) :
  forall w : world crowdState,
    w |= A [(campaign_failed n d bc) W (claim_from n)].
Proof. Admitted.

(************************************************************************
4. The additional property: if the campaign has succeeded, the owner can 
get funds to kickstart the campaign.
 *************************************************************************)

Definition owner_gets_funds : pred := fun w =>
  sender (inFlight w) = get_owner (state (st w)).
                                              
Lemma can_get_funds :
  forall w : world crowdState,
    w |= (AG (balance_exceeded --> owner_gets_funds)).
Proof. Admitted.
