(** * Redblack: Red-Black Trees *)

(** Red-black trees are a kind of _balanced_ binary search tree (BST).
    Keeping the tree balanced ensures that the worst-case running
    time of operations is logarithmic rather than linear. *)

(** This chapter uses Okasaki's algorithms for red-black trees.
    If you don't recall those or haven't seem them in a while, read one
    of the following:

    - Red-Black Trees in a Functional Setting, by Chris Okasaki.
      _Journal of Functional Programming_, 9(4):471-477, July 1999.
      Available from {https://doi.org/10.1017/S0956796899003494}.
      Archived at
      {https://web.archive.org/web/20070926220746/http://www.eecs.usma.edu/webs/people/okasaki/jfp99.ps}.

    - _Purely Functional Data Structures_, by Chris Okasaki. Section
      3.3.  Cambridge University Press, 1998.

    You can also consult Wikipedia or other standard textbooks, though
    they are likely to use different, imperative implementations. *)

(** This chapter is based on the Coq standard library module
    [MSetRBT], which can be found at
    [https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetRBT.html].
    The design decisions for that module are described in the
    following paper:

    - Efficient Verified Red-Black Trees, by Andrew W. Appel,
      September 2011.  Available from
      {http://www.cs.princeton.edu/~appel/papers/redblack.pdf}.  *)

Set Warnings "-undo-batch-mode".
From Coq Require Import String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import ZArith.
From VFA Require Import Perm.
From VFA Require Import Extract.
Open Scope Z_scope.

(* ################################################################# *)
(** * Implementation *)

(** We use the [int] type axiomatized in [Extract] as the
    key type. *)
Definition key := int.

Inductive color := Red | Black.

Inductive tree (V : Type) : Type :=
| E : tree V
| T : color -> tree V -> key -> V -> tree V -> tree V.

Arguments E {V}.
Arguments T {V}.

Definition empty_tree (V : Type) : tree V :=
  E.

(** The [lookup] implementation for red-black trees is exactly
    the same as the [lookup] for BSTs, except that the [T] constructor
    carries a [color] component that is ignored. *)

Fixpoint lookup {V : Type} (d : V) (x: key) (t : tree V) : V :=
  match t with
  | E => d
  | T _ tl k v tr => if ltb x k then lookup d x tl
                    else if ltb k x then lookup d x tr
                         else v
  end.

(** We won't explain the [insert] algorithm here; read Okasaki's
    work if you want to understand it.  In fact, you'll need very
    little understanding of it to follow along with the verification
    below. It uses [balance] and [ins] as helpers:

    - [ins] recurses down the tree to find where to insert, and is
      mostly the same as the BST [insert] algorithm.

    - [balance] takes care of rebalancing the tree on the way back
      up. *)

Definition balance
           {V : Type} (c : color) (t1 : tree V) (k : key) (vk : V)
           (t2 : tree V) : tree V :=
  match c with
  | Red => T Red t1 k vk t2
  | _ => match t1 with
        | T Red (T Red a x vx b) y vy c =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | T Red a x vx (T Red b y vy c) =>
            T Red (T Black a x vx b) y vy (T Black c k vk t2)
        | _ => match t2 with
              | T Red (T Red b y vy c) z vz d =>
	          T Red (T Black t1 k vk b) y vy (T Black c z vz d)
              | T Red b y vy (T Red c z vz d)  =>
	          T Red (T Black t1 k vk b) y vy (T Black c z vz d)
              | _ => T Black t1 k vk t2
              end
        end
  end.

Inductive red_node {V : Type} : tree V -> Prop :=
  | rn_red : forall l k v r, red_node (T Red l k v r).

Inductive black_node {V : Type} : tree V -> Prop :=
  | bn_empty : black_node E
  | bn_black : forall l k v r, black_node (T Black l k v r).

Lemma red_or_black {V : Type} (t : tree V) : red_node t \/ black_node t.
Proof.
  exact (match t with
         | E => or_intror bn_empty
         | T Red l k v r => or_introl (rn_red l k v r)
         | T Black l k v r => or_intror (bn_black l k v r)
         end).
Qed.

Inductive need_balance {V : Type} : tree V -> Prop :=
  | need_bal_l : forall a x vx b y vy c,
      need_balance (T Red (T Red a x vx b) y vy c)
  | need_bal_r : forall a x vx b y vy c,
      black_node a ->
      need_balance (T Red a x vx (T Red b y vy c)).
  
Inductive no_balance {V : Type} : tree V -> Prop :=
  | no_bal_r_none : forall l k v r,
      black_node l ->
      black_node r ->
      no_balance  (T Red l k v r)
  | no_bal_b : forall l k v r,
      no_balance (T Black l k v r)
  | no_bal_E : no_balance E.

Theorem bal_tree_spec {V : Type} : forall (t : tree V), need_balance t \/ no_balance t.
Proof.
  intros t.
  refine (match t return need_balance t \/ no_balance t with
          | E => or_intror (no_bal_E)
          | T Black l k v r => or_intror (no_bal_b l k v r)
          | T Red l k v r =>
              match red_or_black l with
              | or_introl Hl => or_introl _
              | or_intror Hl =>
                  match red_or_black r with
                  | or_introl Hr => or_introl _
                  | or_intror Hr =>
                      or_intror (no_bal_r_none l k v r Hl Hr)
                  end
              end
          end).
  - destruct Hl. apply need_bal_l; assumption.
  - destruct Hr. apply need_bal_r; assumption.
Qed.

Inductive balance_cases {V : Type} : color -> tree V -> tree V -> Prop :=
  | bc_red : forall t1 t2, balance_cases Red t1 t2
  | bc_t1 : forall t1 t2,
      need_balance t1 ->
      balance_cases Black t1 t2
  | bc_t2 : forall t1 t2,
      no_balance t1 ->
      need_balance t2 ->
      balance_cases Black t1 t2
  | bc_none : forall t1 t2,
      no_balance t1 ->
      no_balance t2 ->
      balance_cases Black t1 t2.

Theorem balance_spec {V : Type} c (t1 t2 : tree V) : balance_cases c t1 t2.
Proof.
  exact (match c with
          | Red => bc_red t1 t2
          | Black =>
              match bal_tree_spec t1 with
              | or_introl Hl => bc_t1 t1 t2 Hl
              | or_intror Hl =>
                  match bal_tree_spec t2 with
                  | or_introl Hr => bc_t2 t1 t2 Hl Hr
                  | or_intror Hr => bc_none t1 t2 Hl Hr
                  end
              end
          end).
Qed.

Fixpoint ins {V : Type} (x : key) (vx : V) (t : tree V) : tree V :=
  match t with
  | E => T Red E x vx E
  | T c a y vy b => if ltb x y then balance c (ins x vx a) y vy b
                   else if ltb y x then balance c a y vy (ins x vx b)
                        else T c a x vx b
  end.

Definition make_black {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T _ a x vx b => T Black a x vx b
  end.

Definition insert {V : Type} (x : key) (vx : V) (t : tree V) :=
  make_black (ins x vx t).

(** The [elements] implementation is the same as for BSTs,
    except that it ignores colors. *)

Fixpoint elements_aux {V : Type} (t : tree V) (acc: list (key * V))
  : list (key * V) :=
  match t with
  | E => acc
  | T _ l k v r => elements_aux l ((k, v) :: elements_aux r acc)
  end.

Definition elements {V : Type} (t : tree V) : list (key * V) :=
  elements_aux t [].

(** Sedgewick has proposed _left-leaning red-black trees_, which
    have a simpler [balance] function but a more complicated
    representation invariant. He does this in order to make the proof
    of correctness easier: there are fewer cases in the [balance]
    function, and therefore fewer cases in the case-analysis of the
    proof of correctness of [balance]. But as you will see, our proofs
    about [balance] will have automated case analyses, so we don't
    care how many cases there are! *)

(* ################################################################# *)
(** * Case-Analysis Automation *)

(** Before verifying the correctness of our red-black tree
    implementation, let's warm up by proving that the result of any
    [insert] is a nonempty tree. *)

Lemma ins_not_E : forall (V : Type) (x : key) (vx : V) (t : tree V),
    ins x vx t <> E.
Proof.
  intros. destruct t; simpl.
  discriminate.

  (* Let's [destruct] on the topmost case, [ltb x k]. We can use
     [destruct] instead of [bdestruct] because we don't need to know
     whether [x < k] or [x >= k]. *)

  destruct (ltb x k).
  unfold balance.

  (* A huge goal!  The proof of this goal begins by matching
     against a color. *)

  destruct c.
  discriminate.

  (* Another [match], this time against a tree. *)

  destruct (ins x vx t1).

  (* Another [match] against a tree. *)

  destruct t2.
  discriminate.

  (* Yet another [match]. This pattern deserves automation.  The
     following tactic applies [destruct] whenever the current goal is
     a [match] against a color or a tree. *)

  
  match goal with
  | |- match ?c with Red => _ | Black => _  end <> _ => destruct c
  | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
  end.

  (* Let's apply that tactic repeatedly. *)

  repeat
    match goal with
    | |- match ?c with Red => _ | Black => _  end <> _ => destruct c
    | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
    end.

  (* Now we're down to a base case. *)

  discriminate.

  (* And another base case. We could match against those, too. *)

  match goal with
  | |- T _ _ _ _ _ <> E => discriminate
  end.

  (* Let's restart the proof to incorporate this automation. *)

Abort.

Lemma ins_not_E : forall (V : Type) (x : key) (vx : V) (t : tree V),
    ins x vx t <> E.
Proof.
  intros. destruct t; simpl.
  - discriminate.
  - unfold balance.
    repeat
      match goal with
      | |- (if ?x then _ else _) <> _ => destruct x
      | |- match ?c with Red => _ | Black => _  end <> _=> destruct c
      | |- match ?t with E => _ | T _ _ _ _ _ => _ end  <> _=> destruct t
      | |- T _ _ _ _ _ <> E => discriminate
      end.
Qed.

(** This automation of case analysis will be quite useful in the
    rest of our development. *)

(* ################################################################# *)
(** * The BST Invariant *)

(** The BST invariant is mostly the same for red-black trees as
    it was for ordinary BSTs as defined in [SearchTree].  We
    adapt it by ignoring the color of each node, and changing from [nat]
    keys to [int]. *)

(** [ForallT P t] holds if [P k v] holds for every [(k, v)] node
    of tree [t]. *)

Fixpoint ForallT {V : Type} (P: int -> V -> Prop) (t : tree V) : Prop :=
  match t with
  | E => True
  | T c l k v r => P k v /\ ForallT P l /\ ForallT P r
  end.

Inductive BST {V : Type} : tree V -> Prop :=
| ST_E : BST E
| ST_T : forall (c : color) (l : tree V) (k : key) (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (T c l k v r).

Lemma empty_tree_BST : forall (V : Type), BST (@empty_tree V).
Proof.
  unfold empty_tree. constructor.
Qed.

(** Let's show that [insert] preserves the BST invariant, that is: *)

Theorem insert_BST : forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t ->
    BST (insert k v t).
Abort.

(** It will take quite a bit of work, but automation will help. *)

(** First, we show that if a non-empty tree would be a BST, then the
    balanced version of it is also a BST: *)

Lemma balance_BST: forall (V : Type) (c : color) (l : tree V) (k : key)
                     (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (balance c l k v r).
Proof.
  intros V c l k v r PL PR BL BR. unfold balance.

  repeat
    match goal with
    | |- BST (match ?c with Red => _ | Black => _ end)  => destruct c
    | |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end)  => destruct t
    end.

  (* 58 cases remaining. *)

  - constructor. assumption. assumption. assumption. assumption.
  - constructor; auto.
  - constructor; auto.
  - (* Now the tree gets bigger, and the proof gets more complicated. *)
    constructor; auto.

    + simpl in *. repeat split.
      (* The intro pattern [?] means to let Coq choose the name. *)
      destruct PR as [? _]. lia.

    + simpl in *. repeat split.
      * inv BR. simpl in *. destruct H5 as [? _]. lia.
      * inv BR. simpl in *. destruct H5 as [_ [? _]]. auto.
      * inv BR. simpl in *. destruct H5 as [_ [_ ?]]. auto.

    + constructor; auto.

    + inv BR. inv H7. constructor; auto.

  - constructor; auto.

  - (* 53 cases remain. This could go on for a while... *)

Abort.

(** Let's use some of what we discovered above to automate.
    Whenever we have a subgoal of the form

    ForallT _ (T _ _ _ _ _)

    we can split it.  Whenever we have a hypothesis of the form

    BST (T _ _ _ _ _)

    we can invert it.  And with a hypothesis

    ForallT _ (T _ _ _ _ _)

    we can simplify then destruct it.  Actually, the simplification
    is optional -- Coq will do the destruct without needing the
    simplification.  Anything else seems able to be finished with
    [constructor], [auto], and [lia].  Let's see how far that can
    take us...  *)

Lemma balance_BST: forall (V : Type) (c : color) (l : tree V) (k : key)
                     (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (balance c l k v r).
Proof.
  intros. unfold balance.

  repeat
    match goal with
    |  H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
    |  H: BST (T _ _ _ _ _) |- _ => inv H
    |  |- BST (T _ _ _ _ _) => constructor
    |  |- BST (match ?c with Red => _ | Black => _ end)  => destruct c
    |  |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end)  => destruct t
    |  |- ForallT _ (T _ _ _ _ _) => repeat split
    end;
    auto; try lia.

(** 41 cases remain.  It's a little disappointing that we didn't clear
    more of them.  Let's look at why are we stuck.

    All the remaining subgoals appear to be about proving an inequality
    over all the nodes of a subtree.  For example, the first subgoal
    follows from the hypotheses:

    ForallT (fun (k' : int) (_ : V) => Abs k' > Abs k0) r2
    Abs k1 < Abs k0

    The other goals look similar. *)

  
Abort.

(** To make progress, we can set up some helper lemmas. *)

Lemma ForallT_imp : forall (V : Type) (P Q : int -> V -> Prop) t,
    ForallT P t ->
    (forall k v, P k v -> Q k v) ->
    ForallT Q t.
Proof.
  induction t; intros.
  - auto.
  - destruct H as [? [? ?]]. repeat split; auto.
Qed.

Lemma ForallT_greater : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => Abs k' > Abs k) t  ->
    Abs k > Abs k0 ->
    ForallT (fun k' _ => Abs k' > Abs k0) t.
Proof.
  intros. eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

Lemma ForallT_less : forall (V : Type) (t : tree V) (k k0 : key),
    ForallT (fun k' _ => Abs k' < Abs k) t  ->
    Abs k < Abs k0 ->
    ForallT (fun k' _ => Abs k' < Abs k0) t.
Proof.
  intros; eapply ForallT_imp; eauto.
  intros. simpl in H1. lia.
Qed.

(** Now we can return to automating the proof. *)

Lemma balance_BST: forall (V : Type) (c : color) (l : tree V) (k : key)
                     (v : V) (r : tree V),
    ForallT (fun k' _ => (Abs k') < (Abs k)) l ->
    ForallT (fun k' _ => (Abs k') > (Abs k)) r ->
    BST l ->
    BST r ->
    BST (balance c l k v r).
Proof.
  intros. unfold balance.

  repeat
    match goal with
    |  H: ForallT _ (T _ _ _ _ _) |- _ => destruct H as [? [? ?] ]
    |  H: BST (T _ _ _ _ _) |- _ => inv H
    |  |- BST (T _ _ _ _ _) => constructor
    |  |- BST (match ?c with Red => _ | Black => _ end)  => destruct c
    |  |- BST (match ?t with E => _ | T _ _ _ _ _ => _ end)  => destruct t
    |  |- ForallT _ (T _ _ _ _ _) => repeat split
    end;
    auto; try lia.

  (* [all: t] applies [t] to every subgoal. *)
  all: try eapply ForallT_greater; try eapply ForallT_less; eauto; try lia.
Qed.

(** **** Exercise: 2 stars, standard (balanceP) *)

(** Prove that [balance] preserves [ForallT P]. Use proof automation
    with [match goal] and/or [all:].*)

Lemma balanceP : forall (V : Type) (P : key -> V -> Prop) (c : color) (l r : tree V)
                   (k : key) (v : V),
    ForallT P l ->
    ForallT P r ->
    P k v ->
    ForallT P (balance c l k v r).
Proof.
  intros V P c l r k v Hpl Hpr Hpk. unfold balance.
  destruct (balance_spec c l r) as [l r | l r Hl | l r Hl Hr | l r Hl Hr];
    simpl in *.
  - refine (conj _ (conj _ _)); assumption.
  - destruct Hl. simpl in *.
    + intuition.
    + destruct H; simpl in *; intuition.
  - destruct Hr as [| ? ? ? ? ? ? ? [|]]; simpl in *;
      (destruct Hl as [? ? ? ? [] [] | |];
        simpl in *; intuition).
  - destruct Hl as [? ? ? ? [] [] | |]; simpl in *;
      (destruct Hr as [? ? ? ? [] [] | |]; simpl in *; intuition).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (insP) *)

(** Prove that [ins] preserves [ForallT P]. Hint: proceed by induction on [t].
    Use the previous lemma. There's no need for automated case analysis. *)

Lemma insP : forall (V : Type) (P : key -> V -> Prop) (t : tree V) (k : key) (v : V),
    ForallT P t ->
    P k v ->
    ForallT P (ins k v t).
Proof.
  intros V P t k v Hpt Hpk. induction t; simpl in *.
  - exact (conj Hpk (conj I I)).
  - destruct Hpt as [Hpk0 [Hpt1 Hpt2]]. destruct (ltb k k0).
    + exact (balanceP _ _ _ _ _ _ _ (IHt1 Hpt1) Hpt2 Hpk0).
    + destruct (ltb k0 k).
      * exact (balanceP _ _ _ _ _ _ _ Hpt1 (IHt2 Hpt2) Hpk0).
      * simpl. exact (conj Hpk (conj Hpt1 Hpt2)).
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (ins_BST) *)

(** Prove that [ins] maintains [BST].  Proceed by induction on [t].
    You don't need any automated case analysis. *)

Lemma ins_BST : forall (V : Type) (t : tree V) (k : key) (v : V),
    BST t ->
    BST (ins k v t).
Proof.
  intros V t k v Hb. induction t; simpl.
  - apply ST_T; simpl; trivial.
  - inv Hb. bdestruct (ltb k k0).
    + apply balance_BST.
      * apply insP; assumption.
      * assumption.
      * apply IHt1; assumption.
      * assumption.
    + bdestruct (ltb k0 k).
      * apply balance_BST.
          { assumption. }
          { apply insP.
            - assumption.
            - lia. }
          { assumption. }
          { apply IHt2; assumption. }
      * assert (Ek : Abs k = Abs k0) by lia.
        rewrite <- Ek in *.
        apply ST_T; assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (insert_BST) *)

(** Prove the main theorem: [insert] preserves [BST]. You do
    not need induction. *)

Theorem insert_BST : forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t ->
    BST (insert k v t).
Proof.
  intros V t v k Ht. unfold insert, make_black.
  specialize (ins_BST V t k v Ht) as Hb.
  inv Hb.
  - apply ST_E.
  - apply ST_T; assumption.
Qed.
(** [] *)

(* ################################################################# *)
(** * Verification *)

(** We now verify that the equational specification of maps holds for
    red-black trees:

        lookup d k empty_tree = d
        lookup d k (insert k v t) = v
        lookup d k' (insert k v t) = lookup d k' t       if k <> k'

    The first equation is trivial to verify. *)

Lemma lookup_empty : forall (V : Type) (d : V) (k : key),
    lookup d k (@empty_tree V) = d.
Proof. auto. Qed.

(** The next two equations are more challenging because of [balance]. *)

(** **** Exercise: 4 stars, standard (balance_lookup) *)

(** Prove that [balance] preserves the result of [lookup] on non-empty
    trees. Use the same proof technique as in [balance_BST]. *)

Lemma Abs_lt : forall k k', ltb k k' = (Abs k <? Abs k').
Proof.
  intros k k'. bdestruct (ltb k k').
  - symmetry. apply Z.ltb_lt. exact H.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma Abs_gt : forall k k', ltb k k' = (Abs k' >? Abs k).
Proof.
  intros k k'.
  rewrite Abs_lt. rewrite Z.gtb_ltb. reflexivity.
Qed.

Ltac rewrite_Abs k :=
  repeat rewrite (Abs_lt k); repeat rewrite (Abs_gt _ k);
  unfold Z.ltb,Z.gtb.

Inductive compare_cases (l r : int) : Prop :=
  | cc_lt : Abs l < Abs r ->
      (Abs l ?= Abs r) = Lt ->
      (Abs r ?= Abs l) = Gt ->
      compare_cases l r
  | cc_eq : Abs l = Abs r ->
      (Abs l ?= Abs r) = Eq ->
      compare_cases l r
  | cc_gt : Abs r < Abs l ->
      (Abs l ?= Abs r) = Gt ->
      (Abs r ?= Abs l) = Lt ->
      compare_cases l r.

Lemma compare_spec : forall l r, compare_cases l r.
Proof.
  intros l r. destruct (Z.compare_spec (Abs l) (Abs r)).
  - apply cc_eq.
    * assumption.
    * rewrite H. apply Z.compare_refl.
  - apply cc_lt.
    * assumption.
    * apply Z.compare_lt_iff. apply H.
    * apply Z.compare_gt_iff. apply H.
  - apply cc_gt.
    * assumption.
    * apply Z.compare_gt_iff. apply H.
    * apply Z.compare_lt_iff. apply H.
Qed.

Ltac rewrite_cmp_all :=
  repeat (match goal with
          | H : Z.compare ?l ?r = _ |- context [Z.compare ?l ?r] =>
              rewrite H
          | H: Abs ?l = Abs ?r |- context [Abs ?l] =>
              rewrite H; simpl
          end).

Ltac rewrite_Abs_cmp k := simpl; rewrite_Abs k; rewrite_cmp_all.

Lemma balance_lookup: forall (V : Type) (d : V) (c : color) (k k' : key) (v : V)
                        (l r : tree V),
    BST l ->
    BST r ->
    ForallT (fun k' _ => Abs k' < Abs k) l ->
    ForallT (fun k' _ => Abs k' > Abs k) r ->
    lookup d k' (balance c l k v r) =
      if Abs k' <? Abs k
      then lookup d k' l
      else if Abs k' >? Abs k
           then lookup d k' r
           else v.
Proof.
  intros V d c k k' v l r Hbl Hbr Htl Htr.
  destruct (balance_spec c l r) as [l r | l r Hl | l r Hl Hr | l r Hl Hr];
    simpl in *.
  - rewrite_Abs k'. reflexivity.
  - destruct Hl; simpl in *.
    + destruct Htl as [Hyk _].
      rewrite_Abs k'.
      destruct (compare_spec k' k); rewrite_cmp_all.
      * reflexivity.
      * apply Z.compare_lt_iff in Hyk.
        rewrite (Z.compare_antisym (Abs y) (Abs k)).
        rewrite Hyk. simpl. reflexivity.
      * replace (Abs k' ?= Abs y) with Gt.
          { reflexivity. }
          { symmetry. apply Z.compare_gt_iff. transitivity (Abs k); assumption. }
    + destruct Htl as [Hxk [_ [Hyk _]]].
      rewrite_Abs k'.
      destruct (compare_spec k' k); rewrite_cmp_all.
      * destruct (compare_spec k' y); rewrite_cmp_all.
          { destruct (compare_spec k' x); rewrite_cmp_all;
              (destruct H; rewrite_Abs_cmp k'; reflexivity). }
          { replace (Abs y ?= Abs x) with Gt.
            - destruct H; rewrite_Abs_cmp k'; reflexivity.
            - symmetry. apply Z.compare_gt_iff.
              inv Hbl. simpl in *. lia. }
          { replace (Abs k' ?= Abs x) with Gt.
            - destruct H; rewrite_Abs_cmp k'; reflexivity.
            - symmetry. apply Z.compare_gt_iff.
              inv Hbl. simpl in *. lia. }
      * apply Z.compare_gt_iff in Hyk.
        destruct H; rewrite_Abs_cmp k'; reflexivity.
      * assert (Abs k' ?= Abs y = Gt).
          { apply Z.compare_gt_iff. transitivity (Abs k); assumption. }
        destruct H; rewrite_Abs_cmp k'; reflexivity.
  - destruct Hr; simpl in *.
    + destruct Htr as [Hyk [[Hxk _] _]]. rewrite_Abs k'.
      assert (Abs x < Abs y).
        { inv Hbr. simpl in *. lia. }
      destruct (compare_spec k' x); rewrite_cmp_all.
      * replace (Abs k' ?= Abs y) with Lt.
          { destruct Hl as [? ? ? ? [] [] | |]; rewrite_Abs_cmp k'; reflexivity. }
          { symmetry. apply Z.compare_lt_iff. lia. }
      * replace (Abs x ?= Abs k) with Gt.
        replace (Abs x ?= Abs y) with Lt.
        destruct Hl as [? ? ? ? [] [] | |]; rewrite_Abs_cmp k'; reflexivity.
      * replace (Abs k' ?= Abs k) with Gt.
          { destruct Hl as [? ? ? ? [] [] | |]; rewrite_Abs_cmp k'; reflexivity. }
          { symmetry. apply Z.compare_gt_iff. lia. }
    + destruct Htr as [Hxk [_ [Hyk _]]]. rewrite_Abs k'.
      destruct (compare_spec k' x); rewrite_cmp_all.
      * destruct (compare_spec k' k); rewrite_cmp_all;
          (destruct Hl as [? ? ? ? [] [] | |]; destruct H;
            rewrite_Abs_cmp k'; reflexivity).
      * replace (Abs x ?= Abs k) with Gt.
        destruct Hl as [? ? ? ? [] [] | |]; destruct H;
          rewrite_Abs_cmp k'; reflexivity.
      * replace (Abs k' ?= Abs k) with Gt.
          { destruct Hl as [? ? ? ? [] [] | |]; destruct H;
              rewrite_Abs_cmp k'; reflexivity. }
          { symmetry. apply Z.compare_gt_iff. lia. }
  - destruct Hl as [? ? ? ? [] [] | |];
      destruct Hr as [? ? ? ? [] [] | |]; simpl;
      rewrite_Abs k'; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (lookup_ins_eq) *)

(** Verify the second equation, though for [ins] rather than [insert].
    Proceed by induction on the evidence that [t] is a [BST].  Note
    that precondition [BST t] will be essential in your proof, unlike
    the ordinary BST's we saw in [SearchTree].

    Hint: no automation of case analysis is needed; rely on the lemmas
    we've already proved above about [balance] and [ins]. *)

Lemma lookup_ins_eq: forall (V : Type) (d : V) (t : tree V) (k : key) (v : V),
    BST t ->
    lookup d k (ins k v t) = v.
Proof.
  intros V d t k v Hb. induction t; simpl.
  - rewrite Abs_lt. rewrite Z.ltb_irrefl. reflexivity.
  - rewrite_Abs k. inv Hb. destruct (compare_spec k k0); rewrite_cmp_all.
    + rewrite balance_lookup.
      * unfold Z.ltb,Z.gtb. rewrite_cmp_all. apply IHt1; assumption.
      * apply ins_BST; assumption.
      * assumption.
      * apply insP; assumption.
      * assumption.
    + simpl. rewrite_Abs_cmp k. rewrite H in H0. rewrite H0. reflexivity.
    + rewrite balance_lookup.
      * unfold Z.ltb,Z.gtb. rewrite_cmp_all. apply IHt2; assumption.
      * assumption.
      * apply ins_BST; assumption.
      * assumption.
      * apply insP; assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (lookup_ins_neq) *)

(** Verify the third equation, again for [ins] instead of [insert].
    The same hints as for the second equation hold. *)

Theorem lookup_ins_neq: forall (V : Type) (d : V) (t : tree V) (k k' : key)
                          (v : V),
    BST t ->
    k <> k' ->
    lookup d k' (ins k v t) = lookup d k' t.
Proof.
  intros V d t k k' v Hb Hne. induction t; simpl.
  - rewrite_Abs k'. destruct (compare_spec k' k); rewrite_cmp_all.
    + reflexivity.
    + exfalso. apply Hne. apply Abs_inj. symmetry. assumption.
    + reflexivity.
  - rewrite_Abs k0. inv Hb. destruct (compare_spec k0 k); rewrite_cmp_all.
    + rewrite balance_lookup.
      * unfold Z.ltb,Z.gtb. destruct (compare_spec k0 k'); rewrite_cmp_all.
          { apply IHt2. assumption. }
          { rewrite Z.compare_refl. reflexivity. }
          { reflexivity. }
      * assumption.
      * apply ins_BST. assumption.
      * assumption.
      * apply insP; assumption.
    + rewrite_Abs k. destruct (compare_spec k k'); rewrite_cmp_all.
        { reflexivity. }
        { exfalso. apply Hne. apply Abs_inj. congruence. }
        { reflexivity. }
    + rewrite balance_lookup.
      * unfold Z.ltb,Z.gtb. destruct (compare_spec k' k0); rewrite_cmp_all.
          { apply IHt1; assumption. }
          { rewrite Z.compare_refl. reflexivity. }
          { reflexivity. }
      * apply ins_BST; assumption.
      * assumption.
      * apply insP; assumption.
      * assumption.
Qed.
(** [] *)

(** Finish verifying the second and third equations. The proofs are
    almost identical to each other. No induction is needed. *)

(** **** Exercise: 2 stars, standard (lookup_insert) *)

Theorem lookup_insert_eq : forall (V : Type) (d : V) (t : tree V) (k : key)
                             (v : V),
    BST t ->
    lookup d k (insert k v t) = v.
Proof.
  intros V d t k v Hb. unfold insert. 
  specialize (lookup_ins_eq V d t k v Hb) as H.
  destruct (ins k v t) eqn:E.
  - apply ins_not_E in E. destruct E.
  - simpl. simpl in H. apply H.
Qed.

Theorem lookup_insert_neq: forall (V : Type) (d : V) (t : tree V) (k k' : key)
                             (v : V),
    BST t ->
    k <> k' ->
    lookup d k' (insert k v t) = lookup d k' t.
Proof.
  intros V d t k k' v Hb Hne. unfold insert.
  specialize (lookup_ins_neq V d t k k' v Hb Hne) as H.
  destruct (ins k v t) eqn:E.
  - apply ins_not_E in E. destruct E.
  - simpl. simpl in H. apply H.
Qed.
(** [] *)

(** That concludes the verification of the map equations for red-black
    trees.  We have proved these main theorems: *)

Check empty_tree_BST :
  forall (V : Type),
    BST (@empty_tree V).

Check insert_BST :
  forall (V : Type) (t : tree V) (v : V) (k : key),
    BST t -> BST (insert k v t).

Check lookup_empty :
  forall (V : Type) (d : V) (k : key),
    lookup d k (@empty_tree V) = d.

Check lookup_insert_eq :
  forall (V : Type) (d : V) (t : tree V) (k : key) (v : V),
    BST t -> lookup d k (insert k v t) = v.

Check lookup_insert_neq :
  forall (V : Type) (d : V) (t : tree V) (k k' : key) (v : V),
    BST t ->
    k <> k' ->
    lookup d k' (insert k v t) = lookup d k' t.

(** We could now proceed to reprove all the facts about [elements]
    that we developed in [SearchTree].  But since [elements] does
    not not pay attention to colors, and does not rebalance the tree,
    these proofs should be a simple copy-paste from that chapter, with
    only minor edits.  This would be an uninteresting exercise, so we
    don't pursue it here. *)

(* ################################################################# *)
(** * Efficiency *)

(** Red-black trees are more efficient than ordinary search
    trees, because red-black trees stay balanced.  The [insert]
    operation ensures that these _red-black invariants_ hold: *)

(** - Local Invariant: No red node has a red child.

    - Global Invariant: Every path from the root to a leaf has the
      same number of black nodes. *)

(** Together these invariants guarantee that no leaf is more
    than twice as deep as another leaf, a property that we will here
    call _approximately balanced_.  The maximum depth of a node is
    therefore [2 log N], so the running-time of [insert] and [lookup]
    is [O(log N)], where [N] is the number of nodes in the tree.

    Coq does not have a formal time--cost model for its execution, so
    we cannot verify that logarithmic running time in Coq.  But we can
    prove that the trees are approximately balanced. *)

(** These ensure that the tree remains approximately balanced. *)

(** Relation [RB], below, formalizes the red-black
    invariants. Proposition [RB t c n] holds when [t] satisfies the
    red-black invariants, assuming that [c] is the color of [t]'s
    parent, and [n] is the black height that [t] is supposed to have.

    If [t] happens to have no parent (i.e., it is the entire tree),
    then it will be colored black by [insert], so it won't actually
    matter what color its (non-existent) parent might purportedly
    have: whether red or black, it can't violate the local invariant.

    If [t] is a leaf, then it likewise won't matter what its parent
    color is, and its black height must be zero. *)

Inductive RB {V : Type} : tree V -> color -> nat -> Prop :=
| RB_leaf: forall (c : color), RB E c 0
| RB_r: forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Red n ->
    RB r Red n ->
    RB (T Red l k v r) Black n
| RB_b: forall (c : color) (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    RB (T Black l k v r) c (S n).

(** **** Exercise: 1 star, standard (RB_blacken_parent) *)

(** Prove that blackening a parent would preserve the red-black
    invariants. *)

Lemma RB_blacken_parent : forall (V : Type) (t : tree V) (n : nat),
    RB t Red n -> RB t Black n.
Proof.
  intros V t n H. destruct H.
  - apply RB_leaf.
  - apply RB_r; assumption.
  - apply RB_b; assumption.
Qed.
(** [] *)

(** Relation [NearlyRB] expresses, "the tree is a red-black tree,
    except that it's nonempty and it is permitted to have two
    consecutive red nodes at the root only."  *)

Inductive NearlyRB {V : Type} : tree V -> nat -> Prop :=
| NearlyRB_r : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Red l k v r) n
| NearlyRB_b : forall (l r : tree V) (k : key) (v : V) (n : nat),
    RB l Black n ->
    RB r Black n ->
    NearlyRB (T Black l k v r) (S n).

(** **** Exercise: 4 stars, standard (ins_RB) *)

(** Prove that [ins] creates a tree that is either red-black or nearly
    so, depending on what the parent's color was.

    The proof is already completed for you, except for the tactic
    [prove_RB]. Replace the provided [admit] with your own proof
    automation. Use a technique similar to [ins_not_E] and
    [balance_lookup] -- that is, write a [repeat match goal] that
    finds opportunities to use tactics such as [bdestruct],
    [destruct], [inv], and [constructor]; as well as previously proved
    lemmas and [auto]. *)

Ltac prove_RB := 
  repeat (match goal with
          | |- NearlyRB (if ltb ?l ?r then _ else _) _ => bdestruct (ltb l r)
          | |- RB (if ltb ?l ?r then _ else _) _ _ => bdestruct (ltb l r)
          | H: context [ltb ?l ?r] |- _ => bdestruct (ltb l r)
          | |- NearlyRB (match ?t with | E => _ | T _ _ _ _ _ => _ end) _ =>
              destruct t
          | |- RB (match ?t with | E => _ | T _ _ _ _ _ => _ end) _ _ =>
              destruct t
          | |- NearlyRB (match ?c with | Red => _ | Black => _ end) _ =>
              destruct c
          | |- RB (match ?c with | Red => _ | Black => _ end) _ _ =>
              destruct c
          end);
  simpl;
  try assumption;
  repeat (match goal with
          | H: NearlyRB (T _ _ _ _ _) _ |- _ => inv H
          | |- NearlyRB _ _ => constructor
          end; simpl; try assumption);
  repeat (match goal with
          | H: RB ?l Red ?n |- RB ?l Black ?n => apply RB_blacken_parent
          | |- RB _ _ _ => constructor
          | H: NearlyRB ?l ?n |- RB ?l ?c ?n => inv H
          | H: RB E _ _ |- _ => inv H
          | H: RB (T _ _ _ _ _) _ _ |- _ => inv H
          end; simpl; try assumption).

Lemma ins_RB : forall (V : Type) (k : key) (v : V) (t : tree V) (n : nat),
    (RB t Black n -> NearlyRB (ins k v t) n) /\
      (RB t Red n -> RB (ins k v t) Black n).
Proof.
  induction t; split; intros; inv H; repeat constructor; simpl.
  - (* Instantiate the inductive hypotheses. *)
    specialize (IHt1 n). specialize (IHt2 n).
    (* Derive what propositional facts we can from the hypotheses. *)
    intuition.
    (* Get rid of some extraneous hypotheses. *)
    clear H H1.
    (* Finish with automation. *)
    prove_RB.

  - specialize (IHt1 n0). specialize (IHt2 n0). intuition.
    clear H0 H2.
    prove_RB.

  - specialize (IHt1 n0). specialize (IHt2 n0). intuition.
    clear H0 H2.
    prove_RB.

    (* There's nothing more you need to fill in here. Just don't
       forget to change the [Admitted.] to [Qed.] when you have
       finished developing [prove_RB]. *)
Qed.
(** [] *)

(** Therefore, [ins] produces a red-black tree when given one as input
    -- though the parent color changes. *)
Corollary ins_red : forall (V : Type) (t : tree V) (k : key) (v : V) (n : nat),
    RB t Red n -> RB (ins k v t) Black n.
Proof.
  intros. apply ins_RB. assumption.
Qed.

(** **** Exercise: 1 star, standard (RB_blacken_root) *)

(** Prove that blackening a subtree root (whose hypothetical parent is
    black) would preserve the red-black invariants, though the black
    height of the subtree might change (and the color of the parent
    would need to become red). *)

Lemma RB_blacken_root : forall (V : Type) (t : tree V) (n : nat),
    RB t Black n ->
    exists (n' : nat), RB (make_black t) Red n'.
Proof.
  intros V t n H. destruct t.
  - simpl. exists O. apply RB_leaf.
  - simpl. inv H.
    + exists (S n). apply RB_b; apply RB_blacken_parent; assumption.
    + exists (S n0). apply RB_b; assumption.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (insert_RB) *)

(** Prove that [insert] produces a red-black tree when given one as
    input.  This can be done entirely with lemmas already proved. *)

Lemma insert_RB : forall (V : Type) (t : tree V) (k : key) (v : V) (n : nat),
    RB t Red n ->
    exists (n' : nat), RB (insert k v t) Red n'.
Proof.
  intros V t k v n H. unfold insert.
  apply RB_blacken_root with n. apply ins_red. apply H.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (redblack_bound) *)

(** To confirm that red-black trees are approximately balanced, define
    functions to compute the height (i.e., maximum depth) and minimum
    depth of a red-black tree, and prove that the height is bounded by
    twice the minimum depth, plus 1.  Hints:

    - The standard library has [min] and [max] functions for [nat].

    - Note that [RB] does not require the root to be [Black].

    - Prove two auxiliary lemmas, one about an upper bound on the
      number of black nodes in a path, and another about a lower
      bound. Combine those lemmas to prove the main theorem.

    - All of the proofs can be quite short. The challenge is to invent
      helpful lemmas. *)

Fixpoint height {V : Type} (t : tree V) : nat :=
  match t with
  | E => O
  | T _ l _ _ r => S (max (height l) (height r))
  end.

Fixpoint mindepth {V : Type} (t : tree V) : nat :=
  match t with
  | E => O
  | T Red l _ _ _ => mindepth l
  | T Black l _ _ _ => S (mindepth l)
  end.

Lemma redblack_mindep (V : Type) : forall (t : tree V) c n,
  RB t c n -> mindepth t = n.
Proof.
  intros t c n H.
  induction H; simpl.
  - reflexivity.
  - exact IHRB1.
  - rewrite IHRB1. reflexivity.
Qed.

Lemma redblack_height : forall (V : Type) (t : tree V) (c : color) (n : nat),
    RB t c n ->
    (height t <= 2 * mindepth t +
      match c with
      | Red => 0
      | Black => 1
      end
    )%nat.
Proof.
  intros V t c n H. induction H; simpl.
  - destruct c; lia.
  - apply redblack_mindep in H. apply redblack_mindep in H0.
    lia.
  - apply redblack_mindep in H. apply redblack_mindep in H0.
    destruct c; lia.
Qed.

Lemma redblack_balanced : forall (V : Type) (t : tree V) (c : color) (n : nat),
    RB t c n ->
    (height t <= 2 * mindepth t + 1)%nat.
Proof.
  intros V t c n H.
  specialize (redblack_height V t c n H) as Hl.
  destruct c; lia.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_redblack_bound : option (nat*string) := None.

(** [] *)

(* ################################################################# *)
(** * Performance of Extracted Code *)

(** We can extract the red-black tree implementation: *)

Extraction "redblack.ml" empty_tree insert lookup elements.

(** Run it in the OCaml top level with these commands:

    #use "redblack.ml";;
    #use "test_searchtree.ml";;

    On a recent machine with a 2.9 GHz Intel Core i9 that prints:

    Insert and lookup 1000000 random integers in 0.860663 seconds.
    Insert and lookup 20000 random integers in 0.007908 seconds.
    Insert and lookup 20000 consecutive integers in 0.004668 seconds.

    That execution uses the bytecode interpreter.  The native compiler
    will have better performance:

      $ ocamlopt -c redblack.mli redblack.ml
      $ ocamlopt redblack.cmx -open Redblack test_searchtree.ml -o test_redblack
      $ ./test_redblack

On the same machine that prints,

    Insert and lookup 1000000 random integers in 0.475669 seconds.
    Insert and lookup 20000 random integers in 0.00312 seconds.
    Insert and lookup 20000 consecutive integers in 0.001183 seconds.
*)

(** The benchmark measurements above (and in [Extract])
    demonstrate the following:

    - On random insertions, red-black trees are about the same as
      ordinary BSTs.

    - On consecutive insertions, red-black trees are _much_ faster
      than ordinary BSTs.

    - Red-black trees are about as fast on consecutive insertions as
      on random. *)

(* 2023-08-23 11:34 *)
