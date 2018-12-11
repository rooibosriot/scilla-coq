From mathcomp.ssreflect
Require Import ssreflect ssrnat ssrfun ssrbool eqtype seq. 
From VST.msl
Require Import seplog Extensionality.
From Contracts
Require Import Automata2.
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


Section World.
(* World type *)
  Variables (T : Type) (prot : Protocol T).

  (* In order to transition to Kripke models, we augment world with 
     predetermined outFlight message, similar to FSM in NuSMV *)
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

(* Next: induction principle for CTL? Proof theory? *) 
