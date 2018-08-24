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
         if [|| funded s | get_goal s <= bal]
         (* Cannot reimburse: campaign succeeded *)
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
(**         **TEMPORAL** Correctness properties           **)
(***********************************************************)

(************************************************************************
1. Until the funded flag has been flipped, meaning that the owner got the
funds, the contract will have enough funds to reimburse every backer.
 ************************************************************************)
(* Important reminder: supply pred S with crowdState and not world crowdState *)
Definition notfunded_pred : pred crowdState := fun w =>
                                                 funded (state (st w)) = false.
Definition balance_sufficient_pred : pred crowdState := fun s =>
                                                          sumn (map snd (backers (state (st s)))) <= balance (st s).

Open Scope temporal_logic.
Lemma temporal_balance_backed :
  forall (w : world crowdState),
    AllBox crowd_prot (notfunded_pred --> balance_sufficient_pred) w.
Proof.
  intro s.
  unfold AllBox.
  intros p H_fst n.
  unfold forces.
  unfold notfunded_pred. unfold balance_sufficient_pred.
  unfold Impl.
  unfold not.
  unfold forces.
  destruct p.
  unfold path_predicate in p.
  unfold reachability in p.
  unfold step_state in p.
  (* Study Ilya's original proof *)
Admitted.

(************************************************************************
2. Until the backer claims his donation back, the contract doesn't drop
the records of each backer's donations.
 ************************************************************************)
Definition donated_pred (b : address) (d : value) : pred crowdState := fun s =>
                                                                         (filter [pred e | e.1 == b] (backers (state (st s)))) == [::(b, d)].
                                                                               

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
Definition claim_from_pred (n : address) : pred crowdState := fun w =>
                                                                sender (inFlight w) = n.

Lemma temporal_donation_preserved (b : address) (d : value) :
  forall (w : world crowdState),
    (donated_pred b d w) -> AllWait crowd_prot (donated_pred b d) (claim_from_pred b) w.
Proof. Abort.

(************************************************************************
3. The final property: if the campaign has failed, every registered backer 
can get its donation back.
 *************************************************************************)
Definition balance_exceeded_pred : pred crowdState := fun w => balance (st w) < (get_goal (state (st w))).
Definition block_exceeded (bc : bstate) : pred crowdState := fun w => get_max_block (state (st w)) < block_num bc.

Definition campaign_failed (b : address) (d : value) (bc : bstate) : pred crowdState := fun w => 
    (block_exceeded bc & balance_exceeded_pred & notfunded_pred & donated_pred b d) w.

Lemma can_claim_back (n : address) (d : value) (bc : bstate) :
  forall w : world crowdState,
    AllWait crowd_prot (campaign_failed n d bc) (claim_from_pred n) w.
Proof. Abort.

(************************************************************************
4. The additional property: if the campaign has succeeded, the owner can 
get funds to kickstart the campaign.
 *************************************************************************)
Definition owner_gets_funds_pred : pred crowdState := fun w =>
                                                        sender (inFlight w) = get_owner (state (st w)).
                                                     
Lemma can_get_funds :
  forall w : world crowdState,
    AllBox crowd_prot (balance_exceeded_pred --> owner_gets_funds_pred) w.
Proof. Abort.

End Crowdfunding.
