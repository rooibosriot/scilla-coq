From mathcomp.ssreflect 
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp
Require Import path.
Require Import Eqdep.
From Heaps
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap coding. 
From Contracts
Require Import Automata2. 

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
(*********************************************************)

(* Transition 1 *)
Variable crowd_addr : address.

Notation tft := (trans_fun_type crowdState).
Definition ok_msg := [:: (0, [:: 1])].
Definition no_msg := [:: (0, [:: 0])].

Definition donate_tag := 1.
Definition donate_fun : tft := fun id bal s m bc =>
  if method m == donate_tag then
    let bs := backers s in
    let nxt_block := block_num bc + 1 in
    let from := sender m in
    if get_max_block s <= nxt_block 
    then (s, Some (Msg 0 crowd_addr from 0 no_msg)) (* (3) *)
    else if all [pred e | e.1 != from] bs
                (* new backer *)
                (* Herein lies the bug: change val m to 0 *)
         then let bs' := (from, val m) :: bs in
              let s'  := set_backers s bs' in
              (s', Some (Msg 0 crowd_addr from 0 ok_msg)) (* (2) *)
         else (s, Some (Msg 0 crowd_addr from 0 no_msg)) (* (1) *)
  else (s, None).

Definition donate := CTrans donate_tag donate_fun.

(* Transition 2: Sending the funds to the owner *)
(* Only the owner can request funds *)
(* The owner flips the funded boolean to indicate that the funds have been
collected by him, backers are allowed to donate regardless of whether
the goal has been met. *)

(* Sender should not be able to self-specify *)
Definition getfunds_tag := 2.
Definition getfunds_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if (method m == getfunds_tag) && (from == (get_owner s)) then
    let blk := block_num bc + 1 in
    if (get_max_block s < blk)
         (* The goal should be less than the balance *)
         (* If this branch is never true, the contract state never updates *)
         (* But nothing breaks *)
    then if get_goal s <= bal
         then let s' := set_funded s true in
              (s', Some (Msg bal crowd_addr from 0 ok_msg))
         else (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else (s, Some (Msg 0 crowd_addr from 0 no_msg))
  else (s, None).

Definition get_funds := CTrans getfunds_tag getfunds_fun.

(* Transition 3: Reclaim funds by a backer *)
Definition claim_tag := 3.
Definition claim_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if method m == claim_tag then
    let blk := block_num bc in
    if blk <= get_max_block s
    then
      (* Too early! *)
      (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else let bs := backers s in
         (* Relationship between these two variables? *)
         (* This part is very weird *)
         (* If funded faithfully represents the RHS, redundancy *)
         if [|| funded s | get_goal s <= bal]
         (* Cannot reimburse: campaign succeeded *)
         then (s, Some (Msg 0 crowd_addr from 0 no_msg))
         else let n := seq.find [pred e | e.1 == from] bs in
              if n < size bs 
              then let v := nth 0 (map snd bs) n in
                   (* Demo: change != to == so Lemma 2 breaks *)
                   let bs' := filter [pred e | e.1 != from] bs in
                   let s'  := set_backers s bs' in
                   (* Demo: change v to 0 so Lemma 3 breaks *)
                   (s', Some (Msg v crowd_addr from 0 ok_msg))
              else
                (* Didn't back or already claimed *)
                (s, None)
  else (s, None).

Definition claim := CTrans claim_tag claim_fun.
(** What is the Program Definition here? **)
Program Definition crowd_prot : Protocol crowdState :=
  @CProt _ crowd_addr 0 init_state [:: donate; get_funds; claim] _.

Lemma crowd_tags : tags crowd_prot = [:: 1; 2; 3].
Proof. by []. Qed.

(* Added an ssrbool prefix here to avoid confusion with temporal pred *)
Lemma find_leq {A : eqType} (p : ssrbool.pred (A * nat)) (bs : seq (A * nat)) :
  nth 0 [seq i.2 | i <- bs] (seq.find p bs) <= sumn [seq i.2 | i <- bs].
Proof.
elim: bs=>//[[a w]]bs/=Gi; case:ifP=>_/=; first by rewrite leq_addr.
by rewrite (leq_trans Gi (leq_addl w _)).
Qed.

(***********************************************************)
(**             Correctness properties                    **)
(***********************************************************)

(************************************************************************

1. The contract always has sufficient balance to reimburse everyone,
unless it's successfully finished its campaign:

The "funded" flag is set only if the campaign goals were reached, then
all money goes to owner. Otherwise, the contract keeps all its money
intact.

Perhaps, we should make it stronger, adding a temporal property that
one's reimbursement doesn't change.

************************************************************************)

(************************************************************************)
Definition balance_backed (st: cstate crowdState) : Prop :=
  (* If the campaign not funded... *)
  ~~ (funded (state st)) ->
  (* the contract has enough funds to reimburse everyone. *)
  sumn (map snd (backers (state st))) <= balance st.
Print path.

Lemma sufficient_funds_safe :
  forall p : (path crowdState),
  forall n : nat,
    balance_backed (p n).
Proof.
Abort.

(***********************************************************************)
(******           Proving temporal properties                     ******)
(***********************************************************************)

(* Contribution of backer b is d is recorded in the `backers` *)
Definition donated b (d : value) st :=
  (filter [pred e | e.1 == b] (backers (state st))) == [:: (b, d)].

(* b doesn't claim its funding back *)
Definition no_claims_from b (q : bstate * message) := sender q.2 != b.

(************************************************************************
2. The following lemma shows that the donation record is going to be
preserved by the protocol since the moment it's been contributed, as
long, as no messages from the corresponding backer b is sent to the
contract. This guarantees that the contract doesn't "drop" the record
about someone's donations.

In conjunctions with sufficient_funds_safe (proved above) this
guarantees that, if the campaign isn't funded, there is always a
necessary amount on the balance to reimburse each backer, in the case
of failure of the campaign.
************************************************************************)

(* This one is a little bit trickier to translate into modal logic *)
(* Lemma donation_preserved (b : address) (d : value):
  since_as_long crowd_prot (donated b d)
                (fun _ s' => donated b d s') (no_claims_from b). *)


(************************************************************************
3. The final property: if the campaign has failed (goal hasn't been
reached and the deadline has passed), every registered backer can get
its donation back.
TODO: formulate and prove it.
************************************************************************)

Lemma can_claim_back b d st bc:
  (* We have donated, so the contract holds that state *)
  donated b d st ->
  (* Not funded *)
  ~~(funded (state st)) ->
  (* Balance is small: not reached the goal *)
  balance st < (get_goal (state st)) ->
  (* Block number exceeds the set number *)
  get_max_block (state st) < block_num bc ->
  (* Can emit message from b *)
  exists (m : message),
    sender m == b /\
    out (step_prot crowd_prot st bc m) = Some (Msg d crowd_addr b 0 ok_msg).
Proof.
move=>D Nf Nb Nm.
exists (Msg 0 b crowd_addr claim_tag [::]); split=>//.
rewrite /step_prot.
case: st D Nf Nb Nm =>id bal s/= D Nf Nb Nm.
rewrite /apply_prot/=/claim_fun/=leqNgt Nm/= leqNgt Nb/=.
rewrite /donated/= in D.
move/negbTE: Nf=>->/=; rewrite -(has_find [pred e | e.1 == b]) has_filter.
move/eqP: D=>D; rewrite D/=.
congr (Some _); congr (Msg _ _ _ _ _). 
elim: (backers s) D=>//[[a w]]bs/=; case:ifP; first by move/eqP=>->{a}/=_; case. 
by move=>X Hi H; move/Hi: H=><-. 
Qed.

End Crowdfunding.
