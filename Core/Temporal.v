From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype.
Require Import Eqdep.

(* Type definitions *)
Variable state : Type.
Definition pred := state -> Prop.
(* How do I make a dependent type of pred? *)
Parameter R : state -> state -> Prop.
Definition path := nat -> state.
Definition first (p : path) := p 0.
Parameter p : path.
Definition path_reachability := forall (n : nat), R (p n) (p (S n)).
Definition safe (P : pred) (p : path) :=
  forall n : nat, P (p n).
Definition forces (s : state) (p : pred) : Prop :=
  p s.

Parameter Top : pred.
Parameter Bottom : pred.

(* Notation *)
Notation "w '|=' P" := (forces w P) (at level 80, no associativity).
Ltac impl_e P P_implies_Q :=
  apply P_implies_Q in P.
Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H). 
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).

(* Stuff in Prop *)
Axiom LEM : forall P : Prop, P \/ ~ P.
Definition entails P Q : Prop :=
  forall w,  (w |= P) -> (w |= Q).
Definition equiv P Q : Prop :=
  entails P Q /\ entails Q P.

(* Stuff in pred *)
Definition Neg P : pred := fun w =>
                             ~(w |= P).
Definition Conj P Q : pred := fun w =>
                                (w |= P) /\ (w |= Q).
Definition Disj P Q : pred := fun w =>
                                (w |= P) \/ (w |= Q).
Definition Impl P Q : pred := fun w =>
                                ~(w |= P) \/ (w |= Q).


Delimit Scope temporal_logic with temporal_logic.
Local Open Scope temporal_logic.

Notation "P <=> Q" := (equiv P Q) (at level 35, no associativity).

(* Metalogic semantics *)
(* Definition Top : pred := fun w =>
                           ~ (w |= Bottom). *)                        

Notation "~~ P" := (Neg P) : temporal_logic.
Notation "P & Q" := (Conj P Q) (at level 35, no associativity) : temporal_logic.
Notation "P || Q" := (Disj P Q) : temporal_logic.
Notation "P --> Q" := (Impl P Q) (at level 35, no associativity) : temporal_logic.

(* Temporal operator definitions *)
Definition AllNext (P : pred) : pred := fun w =>  
  forall p, first p = w ->
            p 1 |= P.

Definition ExistsNext (P : pred) : pred := fun w =>  
  exists p, first p = w ->
            p 1 |= P.

Definition AllBox P : pred := fun w =>  
  forall p, first p = w ->
            forall n, p n |= P.

Definition ExistsBox P : pred := fun w =>  
  exists p, first p = w ->
            forall n, p n |= P.

Definition AllFuture P : pred := fun w =>  
  forall p, first p = w ->
            exists n, p n |= P.

Definition ExistsFuture P : pred := fun w =>  
  exists p, first p = w ->
            exists n, p n |= P.

Definition AllUntil P Q : pred := fun w =>  
  forall p, first p = w ->
            exists n, p n |= Q /\
                      forall m, m < n -> p m |= P.

Definition ExistsUntil P Q : pred := fun w =>  
  exists p, first p = w ->
            exists n, p n |= Q /\
                      forall m, m < n -> p m |= P.

(* Temporal operator extensions *)
Definition AllRelease P Q : pred := 
  ~~ (ExistsUntil (~~ P) (~~ Q)).

Definition ExistsRelease P Q : pred :=
  ~~ (AllUntil (~~ P) (~~ Q)).

Definition AllWait P Q : pred :=
  AllRelease P (P || Q).

Definition ExistsWait P Q : pred :=
  ExistsRelease P (P || Q).

(* Other fun equivalences to prove *)
Section FunProofs.

  Variables P Q : pred.

  Proposition fun1 :  (AllBox P) <=> (P & (AllNext (AllBox P))).
  Proof. Abort.

  Proposition fun2 : (ExistsBox P) <=> (P & (ExistsNext (ExistsBox P))).
  Proof. Abort.

  Proposition fun3 : (AllFuture P) <=> (P || (AllNext (AllFuture P))).
  Proof. Abort.

  Proposition fun4 : (ExistsFuture P) <=> (P || (ExistsNext (ExistsFuture P))).
  Proof. Abort.

  Proposition fun5 : (AllUntil P Q) <=> (Q || (P & (AllNext (AllUntil P Q)))).
  Proof. Abort.

  Proposition fun6 : (ExistsUntil P Q) <=> (Q || (P & (ExistsNext (ExistsUntil P Q)))).
  Proof. Abort.

End FunProofs.

Section deMorgan.

  Variables P Q : pred.

  Proposition deMorgan1 : (~~ (AllFuture P)) <=> (ExistsBox (~~ P)).
  Proof. Abort.

  Proposition deMorgan2 : (~~ (ExistsFuture P))<=> (AllBox (~~ P)).
  Proof. Abort.

  Proposition deMorgan3 : (~~ (AllNext P)) <=> (ExistsNext (~~ P)).
  Proof. Abort.

End deMorgan.

Section OtherEquivalences.
  Variables P Q : pred.

  Proposition equiv1 : (AllFuture P) <=> (AllUntil Top P).
  Proof. Abort.

  Proposition equiv2 : (ExistsFuture P) <=> (ExistsUntil Top P).
  Proof. Abort.

End OtherEquivalences.

(* I forgot exactly what this weird equivalence was 
Proposition weirdequiv : forall P Q : Prop,
    equiv (AllUntil P Q) (Neg ((ExistsUntil (Neg P) (Conj (Neg P) Disj (Neg Q))) ExistsBox (Neg Q)).
Proof.
  intros P Q.
  split.
  - intro H.
    unfold AllUntil in H.
    (* What in the world happens next *)
Abort. *)


(* Investigations 
Definition AllWaits P Q : pred := fun w => 
  forall p, first p = w ->
            (forall n, p n |= P) \/
                      (exists n, p n |= Q /\
                                forall m, m < n -> p m |= P).

Definition Option1 P Q : pred :=
  AllBox P \_/ AllUntil P Q.

Definition Option2 P Q : pred :=
  ExistsBox P \_/ AllUntil P Q.

Section Exploration.
Variables P Q : pred.

Lemma hypothesis1 : AllWaits P Q -=- Option1 P Q.
Proof.
  unfold AllWaits. 
  unfold Option1.
  unfold equiv.
  split.
  left. unfold AllBox.
  intros p fst n.
Abort.

Lemma hypothesis2 : Option1 P Q -=- AllWaits P Q.
Proof.
  unfold equiv. split.
  intro H; unfold Option1 in H. unfold AllWaits. intros p fst.
  unfold AllBox in H.
  (*
  destruct H. left.
  spec H p.
  apply H.
  exact fst.
  unfold AllUntil in H.
  spec H p.
  right.
  apply H. exact fst.
Qed. *)
  Abort.

Lemma LEM_injection : forall P w, (exists p, first p = w -> forall n, p n |= P) \/
                                  ~ (exists p, first p = w -> forall n, p n |= P).
Proof.
  intros.
  apply LEM.
Qed.

Lemma hypothesis3 : AllWaits P Q -=- Option2 P Q.
  Proof.
    unfold equiv. split.
    intro H_AllWaits; unfold AllWaits in H_AllWaits.
    unfold Option2. (* 
    assert ((exists p, first p = w -> forall n, p n |= P) \/
            ~ (exists p, first p = w -> forall n, p n |= P)).
    apply LEM.
    destruct H as [H_left | H_right].
    left.
    unfold ExistsBox. exact H_left.
    right; unfold AllUntil.
    intros p fst.
    spec H_AllWaits p.
    apply H_AllWaits in fst.
    destruct fst.
    Focus 2.
    exact H.  
    assert (forall p, first p = w /\ exists n, p n |= P -> False).
    admit. (* Let me deMorgan this away please *)
    rename H0 into sacrilege.
    spec sacrilege p.
    destruct sacrilege as [fst sacriligious].
    destruct sacriligious.
    spec H x.
    contradiction. *)
Admitted.
    
Lemma hypothesis4 : Option2 P Q -> AllWaits P Q.
Proof.
  intro H; unfold Option2 in H.
  unfold AllWaits.
  intros p fst.
  destruct H.
  - unfold ExistsBox in H. destruct H. left. 
Abort.

End Exploration.

(* Desirable properties *)
Definition AllBox' P :=
  forall p, first p = w ->
            forall w', R w w' -> w' |= P.

Lemma AllBox_equiv P : AllBox P <-> AllBox' P.
Proof.
  split.
  - intro. unfold AllBox in H. unfold AllBox'.
    intro p. intro fst.
Abort.
*)

