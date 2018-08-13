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
Lemma temporal_balance_backed : forall (st : cstate crowdState), AllBox balance_backed st.
Proof. Abort.

(***********************************************************************)
(******           Proving temporal properties                     ******)
(***********************************************************************)

(* Contribution of backer b is d is recorded in the `backers` *)
Definition donated b (d : value) st :=
  (filter [pred e | e.1 == b] (backers (state st))) == [:: (b, d)].

(* b doesn't claim its funding back *)
(* Definition no_claims_from b (q : bstate * message) := sender q.2 != b. *)
(* This lemma needs to be reformulated to be state-based *)
(* The previous formulation is slightly problematic and temporally unsound *)
(* I want to say something along the lines of 
a state transition occurred by virtue of a claim funds message from b *)
Check step_state.
(* There doesn't exist a state whereby a previous state reached it via a send 
claim message transition *)
Print message.
Definition no_claims_from (n : address) : pred crowdState := fun cs1 =>
                                                               ~ (exists (cs2 : cstate crowdState)
                                                                         (bs : bstate)
                                                                         (m : message),
                                                                     step_state crowd_prot cs1 bs m = cs2 /\ sender m = n).

(************************************************************************
2. The following lemma guarantees that the contract doesn't "drop" the record
about someone's donations.
************************************************************************)

(* This one is a little bit trickier to translate into modal logic *)
Lemma temporal_donation_preserved (b : address) (d : value) :
  forall (cs : cstate crowdState),
    AllWait (donated b d) (no_claims_from b) cs.
Proof. Abort.
(* Lemma donation_preserved (b : address) (d : value):
  since_as_long crowd_prot (donated b d)
                (fun _ s' => donated b d s') (no_claims_from b). *)


(************************************************************************
3. The final property: if the campaign has failed, every registered backer can get
its donation back.
 *************************************************************************)

Definition notfunded_pred : pred crowdState := fun cs => funded (state cs) = false.
Definition donated_pred (b : address) (d : value) : pred crowdState := fun cs => donated b d cs.
Definition balance_exceeded_pred : pred crowdState := fun cs => balance cs < (get_goal (state cs)).
Definition block_exceeded (bc : bstate) : pred crowdState := fun cs => get_max_block (state cs) < block_num bc.

Definition campaign_failed (b : address) (d : value) (bc : bstate) : pred crowdState := fun cs => 
    Conj (block_exceeded bc) (Conj balance_exceeded_pred (Conj notfunded_pred (donated_pred b d))) cs.

Definition claim_from (n : address) : pred crowdState := fun cs =>
                                                           exists (cs' : cstate crowdState)
                                                                  (bs : bstate)
                                                                  (m : message),
                                                             step_state crowd_prot cs bs m = cs' /\ sender m = n.
(* This is a more expressive "claim_from" pred *)
Definition step_get_funds_state pre bc m : cstate crowdState :=
  let: CState id bal s := pre in
  let: (s', out) := getfunds_fun id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  CState id bal' s'.
Definition get_funds_from_pred (n : address) : pred crowdState := fun cs =>
                                                      exists (cs' : cstate crowdState)
                                                             (bc : bstate)
                                                             (m : message),
                                                        cs = step_get_funds_state cs bc m
                                                                                  /\ sender m = n.
Lemma can_claim_back (n : address) (d : value) (bc : bstate) :
  forall cs : cstate crowdState,
    AllWait (campaign_failed n d bc) (get_funds_from_pred n) cs.
  Proof. Abort.

(* 
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
 *)
  
End Crowdfunding.
