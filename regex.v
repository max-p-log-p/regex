(* CS6301: Assignment 6

   Name: Brandon Luo
   Email: bxl190001@utdallas.edu

 *)

Require Import Bool.
Require Import List.

Inductive rexp {S : Set} : Type :=
  | Empty
  | Epsilon
  | Sym (A : S)
  | Cat (r1 r2 : rexp)
  | Plus (r1 r2 : rexp)
  | Star (r : rexp).

Definition myrexp : rexp :=
  (* Empty Star ((Sym(false) + Sym(true)) + Epsilon) *)
  (Cat (Star Empty) ((Plus (Plus (Sym false) (Sym true)) Epsilon))).

Fixpoint matches_nil {A : Set} (r : @rexp A) : bool :=
  match r with
  | Empty => false
  | Epsilon => true
  | Sym b => false
  | Cat r1 r2 => (matches_nil r1) && (matches_nil r2)
  | Plus r1 r2 => (matches_nil r1) || (matches_nil r2)
  | Star r => true
  end.

Example myrexp_matches_nil:
  matches_nil myrexp = true.
Proof.
  Proof. simpl. reflexivity.
Qed.

Lemma matches_nil_cat2:
  forall r, @matches_nil bool (Cat r r) = @matches_nil bool r.
Proof.
  intros r.
  simpl.
  destruct (matches_nil r).
  - reflexivity.
  - reflexivity.
Qed.

Definition bool_eq (b1 b2 : bool) :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Theorem b1_eq_b2 : forall b1 b2 : bool, 
  bool_eq b1 b2 = eqb b1 b2.  Proof.  reflexivity.
Qed.

Definition eqdec (A : Set) := forall (a1 a2 : A), {a1 = a2} + {a1 <> a2}.

Fixpoint rem {A : Set} (eq : eqdec A) (r : rexp) (b : bool) : rexp :=
  match r with
  | Empty => Empty
  | Epsilon => Empty
  | Sym b1 => if (bool_eq b1 b) then Epsilon else Empty
  | Cat r1 r2 => match (matches_nil r1) with
		 | true => Plus (rem eq r2 b) (Cat (rem eq r1 b) r2) 
		 | false => Cat (rem eq r1 b) r2
		 end
  | Plus r1 r2 => Plus (rem eq r1 b) (rem eq r2 b)
  | Star r => Cat (rem eq r b) (Star r)
  end.

Theorem rem_cat_nil_sym:
  forall b r eq, matches_nil r = true ->
    matches_nil (@rem bool eq (Cat r (Sym b)) b) = true.
Proof.
  intros b r eq H.
  simpl.
  rewrite -> H.
  rewrite b1_eq_b2.
  rewrite eqb_reflx.
  reflexivity.
Qed.

(* 1. Define "matches" here. *)
Fixpoint matches {A : Set} (eq : eqdec A) (r : rexp) (s : list bool) : bool :=
  match s with
  | nil => matches_nil r
  | h :: t => matches eq (rem eq r h) t
  end.

Theorem matches_plus_or:
  forall s r1 r2 eq, 
  @matches bool eq (Plus r1 r2) s = @matches bool eq r1 s || @matches bool eq r2 s.  
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. rewrite IHs. reflexivity.
Qed.

Theorem matches_app:
  forall s1 s2 r1 r2 eq, 
  @matches bool eq r1 s1 = true -> @matches bool eq r2 s2 = true ->
  @matches bool eq (Cat r1 r2) (s1++s2) = true.
Proof.
  induction s1; intros.
  - destruct s2; simpl in *; rewrite H, ?matches_plus_or, H0, ?orb_true_r; reflexivity.
  - simpl. destruct (matches_nil r1); 
  rewrite ?matches_plus_or, IHs1, ?orb_true_r; (reflexivity || assumption).
Qed.

Inductive Matches {A:Set} : @rexp A -> list A -> Prop :=
| MEpsilon: Matches Epsilon nil | MSym (a:A): Matches (Sym a) (a::nil)
| MCat r1 r2 s1 s2 (M1: Matches r1 s1) (M2: Matches r2 s2):
Matches (Cat r1 r2) (s1++s2)
| MPlus1 r1 r2 s (M: Matches r1 s): Matches (Plus r1 r2) s
| MPlus2 r1 r2 s (M: Matches r2 s): Matches (Plus r1 r2) s
| MStar0 r: Matches (Star r) nil
| MStar r (a:A) s1 s2 (M0: Matches r (a::s1)) (M: Matches (Star r) s2):
Matches (Star r) (a::s1++s2).

Theorem Matches_nil:
  forall (A:Set) (r:@rexp A), matches_nil r = true <-> Matches r nil.
Proof.
  intros.
  split; intros.
  - induction r.
  + discriminate.
  + apply MEpsilon.
  + discriminate.
  + simpl in H. apply andb_prop in H. destruct H. apply (MCat r1 r2 nil nil). 
  * apply IHr1. apply H.
  * apply IHr2. apply H0.
  + simpl in H. apply orb_prop in H. destruct H. 
  * apply MPlus1. apply IHr1. apply H.
  * apply MPlus2. apply IHr2. apply H.
  + apply MStar0.
  - induction r.
  + inversion H.
  + reflexivity. 
  + inversion H. 
  + simpl. inversion H. apply app_eq_nil in H3. destruct H3. rewrite H0 in M1. 
  rewrite H3 in M2. apply andb_true_intro. split.
  * apply IHr1. apply M1.
  * apply IHr2. apply M2.
  + simpl. apply orb_true_intro. inversion H. 
  * left. apply IHr1. apply M.
  * right. apply IHr2. apply M.
  + reflexivity.
Qed.

Theorem Matches_rem:
  forall (A:Set) (eq:eqdec A) a r s, Matches r (a::s) <-> Matches (rem eq r a) s.
Proof.
  intros.
  split.
  - generalize dependent s. induction r; intros.
  + inversion H.
  + inversion H.
  + simpl. rewrite b1_eq_b2. inversion H. rewrite eqb_reflx. apply MEpsilon.

  + simpl. inversion H. destruct s1. rewrite <- Matches_nil in M1. rewrite M1. simpl in *. apply MPlus1. apply IHr2. rewrite <- H3. apply M2.
  * destruct (matches_nil r1) eqn:e. 
  apply MPlus2. inversion H3. apply (MCat (rem eq r1 a) r2 s1 s2). apply IHr1. rewrite H4 in M1. apply M1.
  apply M2.
  inversion H3. apply (MCat (rem eq r1 a) r2 s1 s2). apply IHr1. rewrite H4 in M1. apply M1. apply M2.

  + simpl in *. inversion H. 
  * apply MPlus1. apply IHr1. apply M.
  * apply MPlus2. apply IHr2. apply M.

  + simpl in *. inversion H. apply (MCat (rem eq r a) (Star r) s1 s2).
  * apply IHr. apply M0.
  * apply M.

  - generalize dependent s. induction r; intros.
  + inversion H.
  + inversion H.
  + simpl in *. rewrite b1_eq_b2 in H. destruct (eqb A0 a) eqn:e. inversion H.   * rewrite eqb_true_iff in e. rewrite e. apply MSym.
  * inversion H.
  + simpl in *. destruct (matches_nil r1) eqn:e in H. inversion H. apply (MCat r1 r2 nil (a :: s)). 
  * rewrite <- Matches_nil. apply e.
  * apply IHr2. apply M.
  * inversion M. apply IHr1 in M1. apply (MCat r1 r2 (a :: s1) s2). apply M1. apply M2.
  * inversion H. apply IHr1 in M1. apply (MCat r1 r2 (a :: s1) s2). apply M1. apply M2.
  + simpl in *. inversion H. apply IHr1 in M. apply MPlus1. apply M. apply IHr2 in M. apply MPlus2. apply M.
  + simpl in *. inversion H. apply MStar. 
  * apply IHr in M1. apply M1.
  * apply M2.
Qed.

Theorem Matches_matches:
  forall (A:Set) (eq:eqdec A) s r, matches eq r s = true <-> Matches r s.
Proof.
  split.
  - generalize dependent r. induction s; intros.
  + rewrite <- Matches_nil. apply H.
  + simpl in *. rewrite (@Matches_rem A eq). apply IHs. apply H.
  - generalize dependent r. induction s; intros.
  + simpl. rewrite Matches_nil. apply H.
  + simpl in *. apply IHs. rewrite <- Matches_rem. apply H.
Qed.
