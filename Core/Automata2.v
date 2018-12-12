From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun ssrbool eqtype seq. 
From VST.msl
Require Import seplog Extensionality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
      body   : payload
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

  (* A response from a transition *)
  Definition resp_type := (address * value * tag * payload)%type.
  Definition msg_bal (rt : resp_type) : value := rt.1.1.2.

  Variable (S : Type).
  Definition trans_fun_type :=
    address -> value -> S -> message -> bstate -> (S * option message).
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

(* Blockchain schedules *)
Definition schedule := seq (bstate * message).

(* In a well-formed schedule block numbers only grow *)
Fixpoint wf_sched (sch : schedule) :=
  if sch is s :: sch'
  then let bnum := block_num s.1 in
       all [pred s' | bnum <= block_num s'.1] sch' && wf_sched sch'
  else true.

Variables (S : Type) (p : Protocol S).

Definition step_state pre bc m : cstate S :=
  let: CState id bal s := pre in
  let: n := seq.find (fun t => ttag t == method m) (transitions p) in
  let: tr := nth (idle S) (transitions p) n in
  let: (s', out) := (tfun tr) id bal s m bc in
  let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
  CState id bal' s'.

Definition state0 := CState (acc p) (init_bal p) (init_state p).

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
Definition init_crowdstate := CS (init_owner, init_max_block, init_goal) [::] false.

(* Definition of the protocol *)
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
    then (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else if all [pred e | e.1 != from] bs
         (* new backer *)
         then let bs' := (from, val m) :: bs in
              let s'  := set_backers s bs' in
              (s', Some (Msg 0 crowd_addr from 0 ok_msg))
         else (s, Some (Msg 0 crowd_addr from 0 no_msg))
  else (s, None).

Definition donate := CTrans donate_tag donate_fun.

Definition getfunds_tag := 2.
Definition getfunds_fun : tft := fun id bal s m bc =>
  let: from := sender m in
  if (method m == getfunds_tag) && (from == (get_owner s)) then
    let blk := block_num bc + 1 in
    if (get_max_block s < blk)
    then if get_goal s <= bal
         then let s' := set_funded s true in
              (s', Some (Msg bal crowd_addr from 0 ok_msg))
         else (s, Some (Msg 0 crowd_addr from 0 no_msg))
    else (s, Some (Msg 0 crowd_addr from 0 no_msg))
  else (s, None).

Definition get_funds := CTrans getfunds_tag getfunds_fun.

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
         if [|| funded s | get_goal s <= bal]
         (* Cannot reimburse: campaign suceeded *)
         then (s, Some (Msg 0 crowd_addr from 0 no_msg))
         else let n := seq.find [pred e | e.1 == from] bs in
              if n < size bs
              then let v := nth 0 (map snd bs) n in
                   let bs' := filter [pred e | e.1 != from] bs in
                   let s'  := set_backers s bs' in
                   (s', Some (Msg v crowd_addr from 0 ok_msg))
              else
                (* Didn't back or already claimed *)
                (s, None)
  else (s, None).

Definition claim := CTrans claim_tag claim_fun.

Program Definition crowd_prot : Protocol crowdState :=
  @CProt _ crowd_addr 0 init_crowdstate [:: donate; get_funds; claim] _.

Lemma crowd_tags : tags crowd_prot = [:: 1; 2; 3].
Proof. by []. Qed.

(* 
Lemma find_leq {T : eqType} (p : pred (T * nat)) (bs : seq (T * nat)) :
  nth 0 [seq i.2 | i <- bs] (seq.find p bs) <= sumn [seq i.2 | i <- bs].
Proof.
elim: bs=>//[[a w]]bs/=Gi; case:ifP=>_/=; first by rewrite leq_addr.
by rewrite (leq_trans Gi (leq_addl w _)).
Qed.
 *)

End Crowdfunding.

End Protocol.


Record world T := mkW
    {
      inFlight : message;
      st : cstate T;
      b : bstate;
      outFlight : option message
    }. 


Parameter emptymsg: message.
Parameter b0 : bstate.
Definition world0 (T : Type) (prot : Protocol T) := mkW emptymsg (state0 prot) b0 None.
Definition step_world (T : Type) (prot : Protocol T) (w : world T) : world T :=
     let: CState id bal s := st w in
     let: bc := b w in
     let: m := inFlight w in
     let: n := seq.find (fun t => ttag t == method m) (transitions prot) in
     let: tr := nth (idle T) (transitions prot) n in
     let: (s', out) := (tfun tr) id bal s m bc in
     let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
     mkW m (CState id bal' s') bc out.
  

