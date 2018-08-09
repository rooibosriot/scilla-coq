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

Section Crowdfunding.
(* Encoding of the Crowdfunding contract from the Scilla whitepaper *)

(******************************************************
contract Crowdfunding
 (owner     : address,
  max_block : uint,
  goal      : uint)

(* Mutable state description *)
{
  backers : address => uint = [];
  funded  : boolean = false;
}

(* Transition 1: Donating money *)
transition Donate
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number;
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)

(* Transition 2: Sending the funds to the owner *)
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block >= blk
  then if goal <= bal
       then funded := true;
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)

(* Transition 3: Reclaim funds by a backer *)
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main",
              msg -> "here_is_your_money">, MT)

 *******************************************************)

Record crowdState := CS {
   owner_mb_goal : address * nat * value;
   backers : seq (address * value);
   funded : bool;
}.

(* Administrative setters/getters *)
(** E :  Why have tupled types when you can avoid this with separate types? **)
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
(** Typo here in the original branch **)
Definition init_state := CS (init_owner, init_max_block, init_goal) [::] false.

(*********************************************************)
(********************* Transitions ***********************)
(*********************************************************)

(* Transition 1 *)
(*
transition Donate
  (sender : address, value : uint, tag : string)
  (* Simple filter identifying this transition *)
  if tag == "donate" =>

  bs <- & backers;
  blk <- && block_number; 
  let nxt_block = blk + 1 in
  if max_block <= nxt_block
  then send (<to -> sender, amount -> 0,
	      tag -> main,
	      msg -> "deadline_passed">, MT)
  else
    if not (contains(bs, sender))
    then let bs1 = put(sbs, ender, value) in
         backers := bs1;
         send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "ok">, MT)
    else send (<to -> sender,
                amount -> 0,
	        tag -> "main",
	        msg -> "already_donated">, MT)
 *)

(* Definition of the protocol *)
Variable crowd_addr : address.

Notation tft := (trans_fun_type crowdState).
Definition ok_msg := [:: (0, [:: 1])].
Definition no_msg := [:: (0, [:: 0])].

(* The donate function doesn't actually change the balance *)
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

(* Donate merely appends the backer and his value *)
(* So what does the contract state's balance keep track of? *)

Definition donate := CTrans donate_tag donate_fun.

(* Transition 2: Sending the funds to the owner *)
(*
transition GetFunds
  (sender : address, value : uint, tag : string)
  (* Only the owner can get the money back *)
  if (tag == "getfunds") && (sender == owner) =>
  blk <- && block_number;
  bal <- & balance;
  if max_block < blk
  then if goal <= bal
       then funded := true;   
            send (<to -> owner, amount -> bal,
                   tag -> "main", msg -> "funded">, MT)
       else send (<to -> owner, amount -> 0,
                   tag -> "main", msg -> "failed">, MT)
  else send (<to -> owner, amount -> 0, tag -> "main",
   	      msg -> "too_early_to_claim_funds">, MT)
 *)

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
(*
transition Claim
  (sender : address, value : uint, tag : string)
  if tag == "claim" =>
  blk <- && block_number;
  if blk <= max_block
  then send (<to -> sender, amount -> 0, tag -> "main",
              msg -> "too_early_to_reclaim">, MT)
  else bs <- & backers;
       bal <- & balance;
       if (not (contains(bs, sender))) || funded ||
          goal <= bal
       then send (<to -> sender, amount -> 0,
                   tag -> "main",
	           msg -> "cannot_refund">, MT)
       else
       let v = get(bs, sender) in
       backers := remove(bs, sender);
       send (<to -> sender, amount -> v, tag -> "main",
              msg -> "here_is_your_money">, MT)
*)

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

(*
Lemma find_leq {A : eqType} (p : pred (A * nat)) (bs : seq (A * nat)) :
  nth 0 [seq i.2 | i <- bs] (seq.find p bs) <= sumn [seq i.2 | i <- bs].
Proof.
elim: bs=>//[[a w]]bs/=Gi; case:ifP=>_/=; first by rewrite leq_addr.
by rewrite (leq_trans Gi (leq_addl w _)).
Qed.
*)

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

Lemma sufficient_funds_safe : safe balance_backed.
  
End Crowdfunding.
