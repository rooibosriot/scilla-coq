From mathcomp.ssreflect
Require Import ssreflect eqtype.
Require Import Eqdep.
From Contracts
Require Import Automata2.
Require Import Arith Bool Omega.

(* Tacticals *)
Ltac impl_e P P_implies_Q :=
  apply P_implies_Q in P.
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 

(* No more sections and types *)
Definition pred := world crowdState -> Prop.
Variable prot : Protocol crowdState.
Definition world0_here : world crowdState := world0 prot.

Definition reachability : world crowdState -> world crowdState -> Prop := fun w1 w2 => step_world prot w1 = w2.

(* Path definitions *)
Definition path := nat -> world crowdState.
Definition first (p : path) : world crowdState := p 0.
Definition path_predicate (p : path) := forall n, reachability (p n) (p (S n)).
(* Good path sigma-type definitions *)
Definition gpath : Type := {p : path & path_predicate p}.
(* Projection functions for sigma type good paths *)
Definition gpath_proj1 : gpath -> (nat -> world crowdState) :=
  fun gp => match gp with
            | existT a _ => a
            end.
Coercion gpath_proj1 : gpath >-> Funclass. 
Definition gpath_proj2 (gp : gpath) : (path_predicate (gpath_proj1 gp)) :=
  match gp with
  | existT _ b => b
  end.    
(* A cacophany of path constructions *)
(* Constructing a random path *) 
Fixpoint step_n_times (w : world crowdState) (n : nat) :=
  match n with
  | 0 => w
  | S n' => step_world prot (step_n_times w n')
  end.

Definition make_path (w : world crowdState) : path := step_n_times w.

Lemma rewrite_step_world_S :
  forall (n : nat) (w : world crowdState),
    step_n_times w (S n) = step_world prot (step_n_times w n).
Proof. reflexivity. Qed.

Lemma step_world_swap_helper :
  forall (n : nat) (w : world crowdState),
    step_world prot (step_n_times w n) =
    step_n_times (step_world prot w) n.
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
    step_world prot (step_n_times (step_world prot world0_here) n) =
    step_n_times (step_world prot (step_world prot world0_here)) n.
Proof.
  induction n.
  - reflexivity.
  - rewrite step_world_swap_helper.
    reflexivity.
Qed.

Lemma step_world_ind :
  forall n : nat,
    step_world prot (step_n_times world0_here n) = step_n_times world0_here (S n).
Proof.
  induction n.
  - simpl; reflexivity.
  - simpl. reflexivity.
Qed.

Lemma about_p : path_predicate (make_path world0_here).
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
  forall w : world crowdState,
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

Definition gp : gpath := (existT _ (make_path world0_here) about_p).
(* Can you make a sigma type with a dependent type? *)
Parameter generic_world : world crowdState.
Check (about_p_hole generic_world).
Definition gp_hole (w : world crowdState) : gpath := (existT _ (make_path w) (about_p_hole w)).
(* The answer is yes *)

(* Constructing an offset path *)
Definition make_offset_path (p : path) : path := fun n => p (S n).
Definition make_offset_path' (gp : gpath) : path := fun n => gpath_proj1 gp (S n).
Lemma about_offset_path :
  forall p : path,
    path_predicate p ->
    path_predicate (make_offset_path p).
Proof.
  intros p H_p.
  unfold make_offset_path.
  unfold path_predicate in *.
  intro n. 
  exact (H_p (S n)).
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
  exact (p (S n)).
Qed.

Definition gp_offset (p : path) (pred : path_predicate p) : gpath :=
  (existT _ (make_offset_path p) (about_offset_path p pred)).
Definition gp_offset' (gp : gpath) : gpath :=
  (existT _ (make_offset_path' gp) (about_offset_path' gp)).

(* Constructing a backwards offset path *)
Definition make_backwards_offset_path (w0 : world crowdState) (p : path) : path :=
  fun n => match n with 0 => w0 | _ => (p (n-1)) end.
Definition make_backwards_offset_path' (w0 : world crowdState) (gp : gpath) : path :=
  fun n => match n with 0 => w0 | _ => (gpath_proj1 gp (n-1)) end.
Lemma about_backwards_offset_path :
  forall (p : path) (w0 : world crowdState),
    path_predicate p ->
    reachability w0 (p 0) -> 
    path_predicate (make_backwards_offset_path w0 p).
Proof.
  intros p w0 H_p.
  unfold make_backwards_offset_path.
  unfold path_predicate in *.
  destruct n.
  simpl. exact H.
  simpl. replace (n-0) with n. Focus 2. rewrite Nat.sub_0_r. reflexivity. apply (H_p n).
Qed.
Lemma about_backwards_offset_path' :
  forall (gp : gpath) (w0 : world crowdState),
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
  simpl. replace (n-0) with n. Focus 2. omega. apply (p n).
Qed.
Definition gp_backwards_offset
           (w0 : world crowdState) (p : path)
           (pred : path_predicate p)
           (r : reachability w0 (p 0)) : gpath :=
  (existT _ (make_backwards_offset_path w0 p) (about_backwards_offset_path p w0 pred r)).
Definition gp_backwards_offset'
           (w0 : world crowdState) (gp : gpath)
           (r : reachability w0 (gpath_proj1 gp 0)) : gpath :=
  (existT _ (make_backwards_offset_path' w0 gp) (about_backwards_offset_path' gp w0 r)).    
(* Satisfaction definition *)
Definition satisfies (w : world crowdState) (p : pred) : Prop := p w.
(* I'm not sure that the following metalogic entail is necessary *)
Definition entails (p q : pred) : Prop :=
  forall w, (satisfies w p) -> (satisfies w q).
Definition equiv (p q : pred) : Prop := entails p q /\ entails q p.
 
Axiom LEM : forall P : Prop, P \/ ~ P.
Notation "w '|=' p" := (satisfies w p) (at level 80, no associativity).

(* Temporal operator definitions *)
Parameter Top : pred.
Parameter Bottom : pred.
Axiom about_top : forall w, Top w.
Axiom about_bottom : forall w, Bottom w -> False.
Definition Neg p : pred := fun w => (w |= p) -> False.
Definition Conj p q : pred := fun w => (w |= p) /\ (w |= q).
Definition Disj p q : pred := fun w => (w |= p) \/ (w |= q).
Definition Impl p q : pred := fun w => ~ (w |= p) \/ (w |= q).

(* Temporal operator definitions *)
(* AX says 'in every next state', all gpaths beginning with w next satisfy p. *)
Definition AllNext (p : pred) := fun w =>  
  forall gp : path, first gp = w -> gp 1 |= p.
(* EX says 'in some next state', all gpaths beginning with w next satisfy p. *)
Definition ExistsNext (p : pred) := fun w =>  
  exists gp : path, first gp = w /\ gp 1 |= p.
(* AG says all states along all paths beginning with  w satisfy p, including w. *)
Definition AllBox (p : pred) := fun w =>  
  forall gp : path, first gp = w -> forall n, gp n |= p.
(* EG says that there exists a path beginning with w along which all states satisfy p. *)
Definition ExistsBox (p : pred) := fun w =>  
  exists gp : path, first gp = w /\ forall n, gp n |= p.
(* AF says all paths beginning with w contain a future state which satisfies p. *)
Definition AllFuture (p : pred) := fun w =>  
  forall gp : path, first gp = w -> exists n, gp n |= p.
(* EF says that there exists a path beginning with a future state which satisfies p. *)
Definition ExistsFuture (p : pred) := fun w =>  
  exists gp : path, first gp = w /\  exists n, gp n |= p.
(* AU says that all paths beginning with w satisfy p Until q. *)
Definition AllUntil (p q : pred) := fun w =>  
  forall gp : path, first gp = w -> exists n, gp n |= q /\ forall m, m < n -> gp m |= p.
(* EU says that there exists a path beginning with w that satifies p Until q. *)
Definition ExistsUntil (p q : pred) := fun w =>  
  exists gp : path, first gp = w /\ exists n, gp n |= q /\ forall m, m < n -> gp m |= p.

(* Extended temporal operator definitions *)
Definition AllRelease (p q : pred) := fun w => 
  Neg (ExistsUntil (Neg p) (Neg q)) w.
Definition ExistsRelease (p q : pred) := fun w => 
  Neg (AllUntil (Neg p) (Neg q)) w.
Definition AllWait (p q : pred) := fun w => 
  AllRelease q (Disj p q) w.
Definition ExistsWait (p q : pred) := fun w =>
  ExistsRelease q (Disj p q) w.

(* Notation definitions *)
Notation "p <=> q" := (equiv p q) (at level 35, no associativity).
Notation "! p" := (Neg p) (at level 60, right associativity).
Notation "p && q" := (Conj p q) (at level 40, left associativity).
Notation "p || q" := (Disj p q).
Notation "p --> q" := (Impl p q) (at level 35, no associativity).
Notation "'AG' p" := (AllBox p) (at level 35, no associativity).
Notation "'EG' p" := (ExistsBox p) (at level 35, no associativity).
Notation "'AX' p" := (AllNext p) (at level 35, no associativity).
Notation "'EX' p" := (ExistsNext p) (at level 35, no associativity).
Notation "'AF' p" := (AllFuture p) (at level 35, no associativity).
Notation "'EF' p" := (ExistsFuture p) (at level 35, no associativity). 
Notation "'A' '[' p 'U' q ']'" := (AllUntil p q) (at level 35, no associativity).
Notation "'E' '[' p 'U' q ']'" := (ExistsUntil p q) (at level 35, no associativity).
Notation "'A' '[' p 'R' q ']'" := (AllRelease p q) (at level 35, no associativity).
Notation "'E' '[' p 'R' q ']'" := (ExistsRelease p q) (at level 35, no associativity).
Notation "'A' '[' p 'W' q ']'" := (AllWait p q) (at level 35, no associativity).
Notation "'E' '[' p 'W' q ']'" := (ExistsWait p q) (at level 35, no associativity).

Theorem ctl_1 : forall (P : pred),
    AG P <=> (P && AX (AG P)).
Proof.
  intro P. unfold equiv. unfold entails. unfold satisfies. Admitted.
Theorem ctl_2 : forall (P : pred),
    (P && AX (AG P)) <=> AG P.
Proof. Admitted.
Theorem ctl_3 : forall (P : pred),
    EG P <=> (P && EX (EG P)).
Proof. Admitted.      

Theorem ctl_4 : forall (P : pred),
    (P && EX (EG P)) <=> EG P.
Proof. Admitted.
Theorem equiv_1 : forall (P : pred),
    AX P <=> ! (EX (! P)).
Proof. Admitted.
Theorem equiv_2 : forall (P : pred),
    AF P <=> ! (EG (! P)).
Proof. Admitted.
Theorem equiv_3 : forall (P : pred),
    AG P <=> ! (EF (!P)).
Proof. Admitted.
Theorem equiv_4 : forall (P : pred),
    AF P <=> A [Top U P]. 
Proof. Admitted.
Theorem equiv_5 : forall (P : pred),
    EF P <=> E [Top U P].
Proof. Admitted.
Theorem equiv_6 : forall (P Q : pred),
    A [P U Q] <=> E [!P U (!P && !Q)] && AF Q.
Proof. Admitted.


