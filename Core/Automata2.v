From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun ssrbool eqtype seq. 
From VST.msl
Require Import seplog Extensionality.
(* Require Import ctl. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).

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


Section World.
(* World type *)
  Variables (T : Type) (prot : Protocol T).
 
  Record world T := mkW
      {
        inFlight : message;
        st : cstate T;
        b : bstate;
        outFlight : option message
      }.

    Parameter emptymsg: message.
    Parameter b0 : bstate.
    Definition world0 := mkW emptymsg (state0 prot) b0 None. (* First world *)
    Definition step_world (w : world T) : world T :=
     let: CState id bal s := st w in
     let: bc := b w in
     let: m := inFlight w in
     let: n := seq.find (fun t => ttag t == method m) (transitions prot) in
     let: tr := nth (idle T) (transitions prot) n in
     let: (s', out) := (tfun tr) id bal s m bc in
     let: bal' := if out is Some m' then (bal + val m) - val m' else bal in
     mkW m (CState id bal' s') bc out.
  
    Definition pred := world T -> Prop.
  
    Definition reachability : world T -> world T -> Prop :=
    fun w1 w2 => step_world w1 = w2.

    Lemma reachability_trans :
      forall (w1 w2 w3 : world T),
        reachability w1 w2 -> reachability w2 w3 -> reachability w1 w3.
    Proof. Abort. (* This is the exactly not what we want *)

    (* Path definitions *)
    Definition path := nat -> world T.
    Definition first (p : path) : world T := p 0.
    Definition path_predicate (p : path) := forall n, reachability (p n) (p (n.+1)).
    (** Contention : paths can't all start with world0 **) 
    (* Good path sigma-type definitions *)
    Definition gpath : Type := {p : path & path_predicate p}.
    (* Projection functions for sigma type good paths *)
    Definition gpath_proj1 : gpath -> (nat -> world T) := fun gp => 
        match gp with
        | existT a _ => a
        end.
    Coercion gpath_proj1 : gpath >-> Funclass. 
    Definition gpath_proj2 (gp : gpath) : (path_predicate (gpath_proj1 gp)) :=
        match gp with
        | existT _ b => b
        end.    

    (* A cacophany of path constructions *)
    (* Constructing a random path *) 
    Fixpoint step_n_times (w : world T) (n : nat) :=
      match n with
      | 0 => w
      | S n' => step_world (step_n_times w n')
      end.
    
    Definition make_path (w : world T) : path := step_n_times w.

    Lemma rewrite_step_world_S :
      forall (n : nat) (w : world T),
        step_n_times w (n.+1) = step_world (step_n_times w n).
      Proof. reflexivity. Qed.

    Lemma step_world_swap_helper :
      forall (n : nat) (w : world T),
        step_world (step_n_times w n) =
        step_n_times (step_world w) n.
    Proof.
      intros n w.
      induction n.
      - reflexivity.
      - rewrite rewrite_step_world_S.
        rewrite IHn.
        rewrite rewrite_step_world_S.
        reflexivity.
    Qed.

    Lemma step_world_swap :
      forall n : nat,
        step_world (step_n_times (step_world world0) n) =
        step_n_times (step_world (step_world world0)) n.
    Proof.
      induction n.
      - reflexivity.
      - rewrite step_world_swap_helper.
        reflexivity.
    Qed.
    
    Lemma step_world_ind :
      forall n : nat,
        step_world (step_n_times world0 n) = step_n_times world0 n.+1.
    Proof.
      induction n.
      - simpl; reflexivity.
      - simpl. reflexivity.
    Qed.

    Lemma about_p : path_predicate (make_path world0).
    Proof.
      unfold path_predicate.
      induction n.
      - simpl. unfold reachability. reflexivity.
      - unfold reachability in *.
        unfold make_path in *.
        rewrite <- IHn.
        simpl. reflexivity.
    Qed.

    Lemma about_p_hole :
      forall w : world T,
        path_predicate (make_path w).
    Proof.
      unfold path_predicate.
      induction n.
      - simpl. unfold reachability. reflexivity.
      - unfold reachability in *.
        unfold make_path in *.
        rewrite <- IHn.
        simpl. reflexivity.
    Qed.

    Definition gp : gpath := (existT _ (make_path world0) about_p).
    (* Can you make a sigma type with a dependent type? *)
    Parameter generic_world : world T.
    Check (about_p_hole generic_world).
    Definition gp_hole (w : world T) : gpath := (existT _ (make_path w) (about_p_hole w)).
    (* The answer is yes *)

    (* Constructing an offset path *)
    Definition make_offset_path (p : path) : path := fun n => p n.+1.
    Definition make_offset_path' (gp : gpath) : path := fun n => gpath_proj1 gp n.+1.
    Lemma about_offset_path :
      forall p : path,
        path_predicate p ->
        path_predicate (make_offset_path p).
    Proof.
      intros p H_p.
      unfold make_offset_path.
      unfold path_predicate in *.
      intro n. 
      exact (H_p n.+1).
    Qed.
    Lemma about_offset_path' :
      forall gp : gpath,
        path_predicate (make_offset_path' gp). 
    Proof.
      intro gp.
      destruct gp. unfold path_predicate in p.
      unfold make_offset_path'.
      unfold gpath_proj1.
      unfold path_predicate.
      intros n.
      exact (p n.+1).
    Qed.
    Definition gp_offset (p : path) (pred : path_predicate p) : gpath :=
      (existT _ (make_offset_path p) (about_offset_path pred)).
    Definition gp_offset' (gp : gpath) : gpath :=
      (existT _ (make_offset_path' gp) (about_offset_path' gp)).

    (* Constructing a backwards offset path *)
    Definition make_backwards_offset_path (w0 : world T) (p : path) : path :=
      fun n => if eqn n 0 then w0 else (p n.-1).
    Definition make_backwards_offset_path' (w0 : world T) (gp : gpath) : path :=
      fun n => if eqn n 0 then w0 else gpath_proj1 gp n.-1.
    Lemma about_backwards_offset_path :
      forall (p : path) (w0 : world T),
        path_predicate p ->
        reachability w0 (p 0) -> 
        path_predicate (make_backwards_offset_path w0 p).
    Proof.
      intros p w0 H_p.
      unfold make_backwards_offset_path.
      unfold path_predicate in *.
      destruct n.
      simpl. exact H.
      simpl. apply (H_p n).
    Qed.
    Lemma about_backwards_offset_path' :
      forall (gp : gpath) (w0 : world T),
        reachability w0 (gpath_proj1 gp 0) -> 
        path_predicate (make_backwards_offset_path' w0 gp). 
    Proof.
      intros gp w0 H_0.
      destruct gp. unfold path_predicate in p.
      unfold make_backwards_offset_path'.
      unfold gpath_proj1.
      unfold path_predicate.
      destruct n.
      simpl. exact H_0.
      simpl. apply (p n).
    Qed.
    Definition gp_backwards_offset
               (w0 : world T) (p : path)
               (pred : path_predicate p)
               (r : reachability w0 (p 0)) : gpath :=
      (existT _ (make_backwards_offset_path w0 p) (about_backwards_offset_path pred r)).
    Definition gp_backwards_offset'
               (w0 : world T) (gp : gpath)
               (r : reachability w0 (gpath_proj1 gp 0)) : gpath :=
      (existT _ (make_backwards_offset_path' w0 gp) (about_backwards_offset_path' r)).    

    (* Satisfaction definition *)
    Definition satisfies (w : world T) (p : pred) : Prop := p w.
    (* I'm not sure that the following metalogic entail is necessary *)
    Definition entails (p q : pred) : Prop :=
      forall w, (satisfies w p) -> (satisfies w q).
    Definition equiv (p q : pred) : Prop := entails p q /\ entails q p.
    
  End World. 

Axiom LEM : forall P : Prop, P \/ ~ P.
Notation "w '|=' p" := (satisfies w p) (at level 80, no associativity).

Section CTL.
  Variables (S : Type) (prot : Protocol S).  
Local Open Scope logic.

(* NatDed in Prop  *) 
Instance natded_prop : NatDed Prop :=
  { andp p q := p /\ q;
    orp p q := p \/ q;
    exp t p := exists t, p t;
    allp t p := forall t, p t;
    imp p q := p -> q;
    prop p := p;
    derives p q := p -> q;
  }.
- intros. apply prop_ext. split. exact H. exact H0.
- intros. apply H.
- intros. apply H0; apply H. exact H1.
- intros. split.  apply H; exact H1. apply H0; exact H1. 
- intros. destruct H0. apply H; exact H0.
- intros. apply H. destruct H0. exact H1. 
- intros. destruct H1. apply H; exact H1. apply H0; exact H1.
- intros. left. apply H; exact H0.
- intros. right. apply H. exact H0. 
- intros. exists x. apply H. exact H0. 
- intros. destruct H0. apply (H x). exact H0. 
- intros. apply H.  exact (H0 x).
- intros. apply (H t). exact H0. 
- intros. split. intros. apply H. split. apply H0. apply H1.
- intros. apply H. destruct H0. exact H0. destruct H0.  exact H1. 
- intros. apply H. exact H0. trivial. 
- intros. exact H.
- intros. apply H; exact H0.
- intros. exact (H b1).
Defined.

(* NatDed in pred *)
Instance natded_pred (S : Type) : NatDed (pred S) :=
  {
    andp p q := fun w => (w |= p) /\ (w |= q);
    orp p q := fun w => (w |= p) \/ (w |= q);
    exp t p := fun w => exists n, (w |= p n);
    allp t p := fun w => forall n, (w |= p n);
    imp p q := fun w => (w |= p) -> (w |= q);
    prop p := fun w => p;
    derives p q := forall w, (w |= p) -> (w |= q);
  }.

- intros.
  apply extensionality. intros x.
  apply prop_ext. split.
  apply H. apply H0.
- intros; trivial.
- intros. apply H0. apply H. exact H1.
- intros. split. 
  assert (H_copy := H1).
  apply H in H1. exact H1.
  apply H0 in H1. exact H1. 
- intros. apply H. unfold satisfies in H0.
  destruct H0. exact H0. 
- intros. apply H. apply H0.
- intros. unfold satisfies in H1. destruct H1.
  apply H in H1. exact H1. apply H0 in H1. exact H1.
- intros. apply H in H0. unfold satisfies in *. left. exact H0.
- intros. unfold satisfies in *. right. apply H. exact H0.
- intros. unfold satisfies in *. spec H w. exists x. apply H. exact H0. 
- intros. unfold satisfies in *. destruct H0. spec H x. apply H. exact H0.
- intros. apply H.  unfold satisfies in *. spec H0 x. exact H0.
- intros. unfold satisfies in *. intro n. spec H n w. apply H. exact H0.
- intros. split. intros. unfold satisfies in *.
  assert (Q w \/ ~ Q w). apply LEM. destruct H1. intro. apply H. split. exact H0.
  exact H1. intro. contradiction.
- intros. unfold satisfies in *. apply H; auto.
- intros. unfold satisfies in *. destruct H0. exact H0. destruct H0. exact H1. 
- intros. unfold satisfies in *. apply H. exact H0. auto. 
- intros. unfold satisfies in *. exact H.
- intros. apply H.
- intros. apply H.
Defined.

(* CTL class *)
Class CTL (T : Type) {ND: NatDed T} : Type := mkCTL {
  all_next : T -> T ;
  exists_next : T -> T ;
  all_future : T -> T ;
  exists_future : T -> T;
  all_box : T -> T;
  exists_box : T -> T;
  all_until : T -> T -> T;
  exists_until : T -> T -> T;  
  ctl_1 : forall (P : T), all_box P |-- (P && all_next (all_box P));
  ctl_2 : forall (P : T), (P && all_next (all_box P)) |-- all_box P;
  ctl_3 : forall (P : T), exists_box P |-- (P && (exists_next (exists_box P)));
  ctl_4 : forall (P : T), (P && exists_next (exists_box P)) |-- exists_box P;
  (* The following equivalences suffice to prove the adequate connectives result *)
  equiv_1 : forall (P : T), all_next P |-- (exists_next (P --> FF) --> FF);
  equiv_2 : forall (P : T), all_future P |-- (exists_box (P --> FF) --> FF);
  equiv_3 : forall (P : T), all_box P |-- (exists_future (P --> FF) --> FF);
  equiv_4 : forall (P : T), all_future P |-- all_until TT P;
  equiv_5 : forall (P : T), exists_future P |-- exists_until TT P;
  equiv_6 : forall (P Q : T), all_until P Q |-- (exists_until (P --> FF)
                                                              ((P --> FF) && (Q --> FF))
                                                              --> FF) && all_future Q; 
                                                }.

Instance lift_ctl_modal : (@CTL _ (natded_pred S)) :=
  { all_next p := fun w =>
                    forall gp : gpath prot,
                      first gp = w -> gp 1 |= p;
    exists_next p := fun w =>
                       exists gp : gpath prot,
                         first gp = w /\ gp 1 |= p;
    all_future p := fun w =>
                      forall gp : gpath prot,
                        first gp = w -> exists n, gp n |= p;
    exists_future p := fun w =>
                         forall gp : gpath prot,
                           first gp = w -> exists n, gp n |= p;
    all_box p := fun w =>
                   forall gp : gpath prot,
                     first gp = w -> forall n, gp n |= p;
    exists_box p := fun w =>
                      exists gp : gpath prot,
                        first gp = w /\ forall n, gp n |= p;
    all_until p q := fun w =>
                       forall gp : gpath prot,
                         first gp = w ->
                         exists n, gp n |= q
                                   /\ forall m, m < n -> gp m |= p;
    exists_until p q := fun w =>
                          exists gp : gpath prot,
                            first gp = w
                            /\ exists n, gp n |= q
                                         /\ forall m, m < n -> gp m |= p;
  }.
(* Proving ctl_1 : forall (P : T), all_box P |-- (P && all_next (all_box P)) *)
intros P.
unfold derives. simpl. unfold satisfies in *. 
intros w H_AG.
split.
spec H_AG (gp_hole prot w).
unfold first in H_AG.
assert ((gp_hole prot w) 0 = w).
simpl. reflexivity.
exact (H_AG H 0).
intros gp H_first gp' H_first' n.
assert (exists m, gp m = gp' n).
exists n.+1.
unfold gpath in gp, gp'.
destruct gp, gp'.
unfold path_predicate in p, p0.
simpl in H_first'.
unfold first in H_first'.
simpl in H_first, H_first'. simpl.
assert (p_copy := p).
assert (p0_copy := p0).
unfold reachability in p, p0.
induction n.
symmetry; exact H_first'.
rewrite <- (p n.+1).
rewrite <- (p0 n). rewrite <- IHn. 
reflexivity.
destruct H.
rewrite <- H. 
spec H_AG gp.
apply H_AG. exact H_first.
(* Proving ctl_2 : forall (P : T), (P && all_next (all_box P)) |-- all_box P *)
intros P.
unfold derives. simpl. unfold derives in *.
intros w H gp H_first n. unfold satisfies in *.
destruct H as [H_P H_AXAG].
spec H_AXAG gp.
(* The following series of bookkeeping moves is annoying but necessary to 
circumvent the high demands of automation from apply tactic *)
assert (forall gp' : gpath prot, first gp' = gp 1 -> forall n : nat, P (gp' n)).
apply H_AXAG; exact H_first.
clear H_AXAG.
rename H into H_AXAG.
spec H_AXAG (gp_offset' gp).
simpl in H_AXAG.
assert (first (make_offset_path' gp) = gp 1).
unfold make_offset_path'.
unfold first. reflexivity.
(* Another series of redundant bookkeeping moves *)
assert (forall n : nat, P (make_offset_path' gp n)).
apply H_AXAG; exact H.
clear H_AXAG H.
unfold make_offset_path' in H0.
case n.
unfold first in H_first; rewrite H_first; exact H_P. 
exact H0.
(* Proving ctl_3 : forall (P : T), exists_box P |-- (P && (exists_next (exists_box P))) *)
intros P.
unfold derives. simpl. unfold satisfies in *. 
intros w H_EG.
split.
destruct H_EG. destruct H. 
spec H0 0.
unfold first in H; rewrite H in H0; exact H0.
destruct H_EG. destruct H.
exists x. split.
exact H. exists (gp_offset' x).
split.
simpl. unfold make_offset_path'. unfold first. reflexivity.
intro n.
spec H0 n.+1.
unfold gp_offset'.
unfold make_offset_path'. simpl.
exact H0.
(* Proving ctl_4 : forall (P : T), (P && (exists_next (exists_box P))) |-- exists_box P *)
intro P.
unfold derives. simpl. unfold satisfies in *.
intros. destruct H.
repeat destruct H0.
destruct H1. destruct H0.
assert (reachability prot (x 0) (x 1)).
unfold gpath in x. 
destruct x.
unfold path_predicate in p.
simpl.
exact (p 0).
assert (reachability prot (x 0) (x0 0)).
unfold first in H0; rewrite H0; exact H2.
clear H2.
exists (gp_backwards_offset' H3).
split.
simpl. unfold make_backwards_offset_path'.
unfold first. reflexivity.
unfold gp_backwards_offset'.
destruct n.
simpl. exact H.
simpl.
unfold make_backwards_offset_path'.
simpl. exact (H1 n).
(* Proving equiv_1 : AX P == ~ EX (~P) *)
intro P.
unfold derives. simpl. unfold satisfies in *.
intros w H_1 H.
repeat destruct H.
spec H_1 x.
assert (first x = first x) by reflexivity.
apply H_1 in H.
apply H0.
exact H.
(* Proving equiv_2 : AF P == ~ EG (~P) *)
intro P. 
unfold derives. simpl. unfold satisfies in *.
intros w H_AG H_EG.
destruct H_EG.
destruct H.
spec H_AG x.
apply H_AG in H.
destruct H.
spec H0 x0.
apply H0. exact H.
(* Proving equiv_3 : AG p == ~ EF (~P) *)
intro P. 
unfold derives. simpl. unfold satisfies in *.
intros w H_AG H_EF.
spec H_AG (gp_hole prot w).
assert (first (gp_hole prot w) = w).
unfold first. unfold gp_hole. simpl; reflexivity.
assert (forall n : nat, P ((gp_hole prot w) n)).
apply H_AG. exact H.
clear H_AG.
spec H_EF (gp_hole prot w).
assert (exists n : nat, P ((gp_hole prot w) n) -> False).
apply H_EF; exact H.
destruct H1.
apply H1.
spec H0 x. exact H0.
(* Proving equiv_4 : AF P == A[T U P] *)
intro P. 
unfold derives. simpl. unfold satisfies in *.
intros w H_AF gp H_first.
spec H_AF gp.
assert (exists n : nat, P (gp n)).
apply H_AF.
exact H_first.
destruct H. exists x. split. exact H.
intros. reflexivity.
(* Proving equiv_5 : EF P == E[T U P] *)
intro P.
unfold derives. simpl. unfold satisfies in *.
intros w H_EF.
spec H_EF (gp_hole prot w).
assert (first (gp_hole prot w) = w) by reflexivity.
apply H_EF in H.
clear H_EF.
destruct H. 
exists (gp_hole prot w).
split.
reflexivity.
exists x. 
split.
exact H.
intros; reflexivity.
(* Proving ind : P -> AN P == AG P 
intro P.
unfold derives. simpl. unfold satisfies in *.
intros w H_AN gp H_first n.
induction n.
unfold first in H_first; rewrite H_first.
apply H_AN.
intros gp' H_first'.
 This seems unprovable *)
(* Proving equiv_6 : A[P U Q] == ~E[~P U (~P /\ ~Q)] /\ (AF Q) *)
intros P Q. 
unfold derives. simpl. unfold satisfies in *.
intros w H_AU.
split.
intros H_EU.
destruct H_EU.
repeat destruct H.
destruct H0. repeat destruct H.
spec H_AU x.
assert (first x = first x) by reflexivity. 
apply H_AU in H.
clear H_AU.
(* Clearly this needs to be proven via contradiction *)
rename H into H_EU. rename x into gp.
destruct H_EU.
destruct H.
assert (x < x0 \/ ~ x < x0).
apply LEM.
destruct H3.
spec H0 x. 
apply H0 in H3.
inversion H3.
Abort.

End CTL.

(* Next we need to deal with the notions of induction and safety *) 
(* A stronger safety property *)
Definition safe  (S : Type) (P : Protocol S) (pr : pred S) (pth : gpath P) :=
  forall n : nat, pr (pth n).

Lemma safe_ind :
  forall  (S : Type) (P : Protocol S) (pr : pred S) (p : gpath P),
  pr (p 0) ->
  (forall n : nat, pr (p n) -> pr (p (n.+1))) ->
                  forall n : nat,  pr(p n).
Proof.
  intros P path.
  intros H_0 HI m.
  intro.
  induction n.
  exact m.
  apply H. exact IHn.
Qed.

