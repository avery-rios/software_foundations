(** * Binom: Binomial Queues *)

(** Implementation and correctness proof of fast mergeable priority queues
   using binomial queues.

  Operation [empty] is constant time,  [insert], [delete_max], and [merge]
  are logN time.  (Well, except that comparisons on [nat] take linear time.
  Read the [Extract] chapter to see what can be done about that.) *)

(* ################################################################# *)
(** * Required Reading
  Binomial Queues {https://www.cs.princeton.edu/~appel/Binom.pdf}
  by Andrew W. Appel, 2016.

  Binomial Queues {https://www.cs.princeton.edu/~appel/BQ.pdf}
  Section 9.7 of _Algorithms 3rd Edition in Java, Parts 1-4:
    Fundamentals, Data Structures, Sorting, and Searching_,
  by Robert Sedgewick.  Addison-Wesley, 2002.
*)

(* ################################################################# *)
(** * The Program *)

From Coq Require Import Strings.String. (* for manual grading *)
From VFA Require Import Perm.
From VFA Require Import Priqueue.

Module BinomQueue <: PRIQUEUE.

Definition key := nat.

Inductive tree : Type :=
|  Node: key -> tree -> tree -> tree
|  Leaf : tree.

(** A priority queue (using the binomial queues data structure) is a
   list of trees.  The [i]'th element of the list is either [Leaf] or
   it is a power-of-2-heap with exactly [2^i] nodes.

  This program will make sense to you if you've read the Sedgewick
  reading; otherwise it is rather mysterious.
*)

Definition priqueue := list tree.

Definition empty : priqueue := nil.

Definition smash (t u:  tree) : tree :=
  match t , u with
  |  Node x t1 Leaf, Node y u1 Leaf =>
                   if  x >? y then Node x (Node y u1 t1) Leaf
                                else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf  (* arbitrary bogus tree *)
  end.

Fixpoint carry (q: list tree) (t: tree) : list tree :=
  match q, t with
  | nil, Leaf        => nil
  | nil, _            => t :: nil
  | Leaf :: q', _  => t :: q'
  | u :: q', Leaf  => u :: q'
  | u :: q', _       => Leaf :: carry q' (smash t u)
 end.

Definition insert (x: key) (q: priqueue) : priqueue :=
     carry q (Node x Leaf Leaf).

Eval compute in fold_left (fun x q =>insert q x) [3;1;4;1;5;9;2;3;5] empty.
(** 
    = [Node 5 Leaf Leaf;
       Leaf;
       Leaf;
       Node 9
          (Node 4 (Node 3 (Node 1 Leaf Leaf) (Node 1 Leaf Leaf))
             (Node 3 (Node 2 Leaf Leaf) (Node 5 Leaf Leaf)))
          Leaf]
     : priqueue
*)

Fixpoint join (p q: priqueue) (c: tree) : priqueue :=
  match p, q, c with
    [], _ , _            => carry q c
  | _, [], _             => carry p c
  | Leaf::p', Leaf::q', _              => c :: join p' q' Leaf
  | Leaf::p', q1::q', Leaf            => q1 :: join p' q' Leaf
  | Leaf::p', q1::q', Node _ _ _  => Leaf :: join p' q' (smash c q1)
  | p1::p', Leaf::q', Leaf            => p1 :: join p' q' Leaf
  | p1::p', Leaf::q',Node _ _ _   => Leaf :: join p' q' (smash c p1)
  | p1::p', q1::q', _                   => c :: join p' q' (smash p1 q1)
 end.

Fixpoint unzip (t: tree) (cont: priqueue -> priqueue) : priqueue :=
  match t with
  |  Node x t1 t2   => unzip t2 (fun q => Node x t1 Leaf  :: cont q)
  | Leaf => cont nil
  end.

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
    Node x t1 Leaf  => unzip t1 (fun u => u)
  | _ => nil   (* bogus value for ill-formed or empty trees *)
  end.

Fixpoint find_max' (current: key) (q: priqueue) : key :=
  match q with
  |  []         => current
  | Leaf::q' => find_max' current q'
  | Node x _ _ :: q' => find_max' (if x >? current then x else current) q'
  end.

Fixpoint find_max (q: priqueue) : option key :=
  match q with
  | [] => None
  | Leaf::q' => find_max q'
  | Node x _ _ :: q' => Some (find_max' x q')
 end.

Fixpoint delete_max_aux (m: key) (p: priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p'   => let (j,k) := delete_max_aux m p'  in (Leaf::j, k)
  | Node x t1 Leaf :: p' =>
       if m >? x
       then (let (j,k) := delete_max_aux m p'
             in (Node x t1 Leaf::j,k))
       else (Leaf::p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil) (* Bogus value *)
  end.

Definition delete_max (q: priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some  m => let (p',q') := delete_max_aux m q
                            in Some (m, join p' q' Leaf)
  end.

Definition merge (p q: priqueue) := join p q Leaf.

(* ################################################################# *)
(** * Characterization Predicates *)

(** [t] is a complete binary tree of depth [n], with every key <= [m] *)

Fixpoint pow2heap' (n: nat) (m: key) (t: tree) :=
 match n, m, t with
    0, m, Leaf       => True
  | 0, m, Node _ _ _  => False
  | S _, m,Leaf    => False
  | S n', m, Node k l r  =>
       m >= k /\ pow2heap' n' k l /\ pow2heap' n' m r
 end.

(** [t] is a power-of-2 heap of depth [n] *)

Definition pow2heap (n: nat) (t: tree) :=
  match t with
    Node m t1 Leaf => pow2heap' n m t1
  | _ => False
  end.

(** [l] is the [i]th tail of a binomial heap *)

Fixpoint priq'  (i: nat) (l: list tree) : Prop :=
   match l with
  | t :: l' => (t=Leaf \/ pow2heap i t) /\ priq' (S i) l'
  | nil => True
 end.

(** [q] is a binomial heap *)

Definition priq (q: priqueue) : Prop := priq' 0 q.

(* ################################################################# *)
(** * Proof of Algorithm Correctness *)

(* ================================================================= *)
(** ** Various Functions Preserve the Representation Invariant *)

(** ...that is, the [priq] property, or the closely related property [pow2heap].
*)

(** **** Exercise: 1 star, standard (empty_priq)  *)
Theorem empty_priq: priq empty.
Proof.
  unfold priq,priq'. simpl. exact I.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (smash_valid) *)
Theorem smash_valid:
       forall n t u, pow2heap n t -> pow2heap n u -> pow2heap (S n) (smash t u).
Proof.
  intros n t u Ht Hu. destruct t; simpl in *; [|contradiction].
  destruct u; simpl in *; [|contradiction].
  destruct t2; simpl in *; [contradiction|].
  destruct u2; simpl in *; [contradiction|].
  bdestruct (k >? k0); simpl.
  - refine (conj _ (conj Hu Ht)). lia.
  - refine (conj H (conj Ht Hu)).
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (carry_valid) *)
Theorem carry_valid:
           forall n q,  priq' n q ->
           forall t, (t=Leaf \/ pow2heap n t) -> priq' n (carry q t).
Proof.
  intros n q. generalize dependent n.
  induction q; intros n H t Ht.
  - destruct t.
    + destruct Ht as [Ht | Ht]; [discriminate Ht|].
      simpl in *. exact (conj (or_intror Ht) I).
    + simpl. exact I.
  - simpl in *. destruct H as [H Hpq].
    destruct a.
    + destruct H; [discriminate H|]. simpl in *.
      destruct a2; simpl in *; [contradiction|].
      destruct t.
      * destruct Ht as [Ht | Ht]; [discriminate Ht|].
        cbn delta [priq'] fix. cbn iota.
        refine (conj (or_introl eq_refl) _).
        apply (IHq _ Hpq).
        right. apply (smash_valid _ _ _ Ht).
        simpl. assumption.
      * simpl. exact (conj (or_intror H) Hpq).
    + simpl. exact (conj Ht Hpq).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (insert_valid) *)
Theorem insert_priq: forall x q, priq q -> priq (insert x q).
Proof.
  intros x q H. unfold priq in *.
  apply carry_valid.
  - apply H.
  - right. simpl. exact I.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (join_valid) *)
(* This proof is rather long, but each step is reasonably straightforward.
    There's just one [induction] to do, right at the beginning. *)
Theorem join_valid: forall p q c n, priq' n p -> priq' n q -> (c=Leaf \/ pow2heap n c) -> priq' n (join p q c).
Proof.
  induction p; intros q c n Hp Hq Hc; simpl.
  - apply carry_valid; assumption.
  - simpl in Hp. destruct Hp as [Ha Hp].
    destruct a; simpl in Ha.
    + destruct Ha as [Ha | Ha]; [discriminate Ha|].
      destruct a2; [contradiction|].
      destruct q.
      * destruct c.
          { destruct Hc as [Hc | Hc]; [discriminate Hc|].
            cbn delta [priq'] fix. cbn iota.
            refine (conj (or_introl eq_refl) _).
            apply (carry_valid _ _ Hp). right.
            apply (smash_valid _ _ _ Hc). simpl. exact Ha. }
          { simpl. exact (conj (or_intror Ha) Hp). }
      * simpl in Hq. destruct Hq as [Ht Hq].
        destruct t.
          { destruct Ht as [Ht | Ht]; [discriminate Ht|].
            cbn delta [priq'] fix. cbn iota.
            refine (conj Hc _). apply (IHp _ _ _ Hp Hq).
            right. refine (smash_valid _ _ _ _ Ht).
            simpl. exact Ha. }
          { destruct c; cbn delta [priq'] fix; cbn iota.
            - destruct Hc as [Hc | Hc]; [discriminate Hc|].
              refine (conj Ht (IHp _ _ _ Hp Hq (or_intror _))).
              apply (smash_valid _ _ _ Hc). simpl. assumption.
            - refine (conj (or_intror _) (IHp _ _ _ Hp Hq (or_introl eq_refl))).
              simpl. apply Ha. }
    + destruct q.
      * simpl. exact (conj Hc Hp).
      * simpl in Hq. destruct Hq as [Ht Hq].
        destruct t.
          { destruct Ht as [Ht | Ht]; [discriminate Ht|].
            destruct c; cbn delta [priq'] fix; cbn iota.
            - destruct Hc as [Hc | Hc]; [discriminate Hc|].
              refine (conj (or_introl eq_refl) (IHp _ _ _ Hp Hq (or_intror _))).
              exact (smash_valid _ _ _ Hc Ht).
            - cbn delta [priq'] fix. cbn iota.
              exact (conj (or_intror Ht) (IHp _ _ _ Hp Hq (or_introl eq_refl))). }
          { exact (conj Hc (IHp _ _ _ Hp Hq (or_introl eq_refl))). }
Qed.
(** [] *)

Theorem merge_priq:  forall p q, priq p -> priq q -> priq (merge p q).
Proof.
 intros. unfold merge. apply join_valid; auto.
Qed.

Lemma unzip_valid : forall t cont n m, pow2heap' n m t ->
  priq' n (cont nil) ->
  priq (unzip t cont).
Proof.
  induction t; intros cont n m Ht Hc.
  - destruct n; [contradiction Ht|].
    simpl in Ht. destruct Ht as [Hm [Ht1 Ht2]].
    simpl.
    apply (IHt2 _ _ _ Ht2). simpl.
    exact (conj (or_intror Ht1) Hc).
  - destruct n.
    + exact Hc.
    + contradiction Ht.
Qed.

Lemma heap_delete_max_priq : forall t n, pow2heap n t -> priq (heap_delete_max t).
Proof.
  refine (fun t => match t with
          | Node _ t1 Leaf => _
          | _ => fun _ _ => empty_priq
          end).
  clear t t0. simpl. intros n H.
  apply (unzip_valid _ _ _ _ H). exact I.
Qed.

Lemma delete_max_aux_priq : forall k q n,
  priq' n q ->
  let (p0,p1) := delete_max_aux k q in priq' n p0 /\ priq p1.
Proof.
  intros k q. induction q; intros n Hq.
  - simpl. exact (conj I I).
  - cbn delta [delete_max_aux] fix. cbn iota.
    destruct a as [ak al ar|].
    + destruct ar as [ark arl arr|].
      * simpl. exact (conj I I).
      * simpl in Hq. destruct Hq as [Ha Hq].
        bdestruct (k >? ak).
          { destruct (delete_max_aux k q).
            apply IHq in Hq. destruct Hq as [Hp Hp0].
            simpl. exact (conj (conj Ha Hp) Hp0). }
          { split.
            - simpl. exact (conj (or_introl eq_refl) Hq).
            - destruct Ha as [Ha | Ha]. { discriminate Ha. }
              apply (heap_delete_max_priq _ n).
              apply Ha. }
    + destruct (delete_max_aux k q).
      simpl in Hq. destruct Hq as [H Hq].
      apply IHq in Hq. destruct Hq as [Hp Hp0].
      simpl. exact (conj (conj H Hp) Hp0).
Qed.          

(** **** Exercise: 5 stars, standard, optional (delete_max_Some_priq) *)
Theorem delete_max_Some_priq:
      forall p q k, priq p -> delete_max p = Some(k,q) -> priq q.
Proof.
  unfold delete_max.
  intros p q k Hp Ed.
  destruct (find_max p); [| discriminate Ed].
  apply (delete_max_aux_priq k0) in Hp. 
  destruct (delete_max_aux k0 p).
  injection Ed as Ek Eq. subst k q.
  destruct Hp as [Hp0 Hp1].
  exact (join_valid _ _ _ _ Hp0 Hp1 (or_introl eq_refl)).
Qed.
(** [] *)

(* ================================================================= *)
(** ** The Abstraction Relation *)

(** [tree_elems t l]    means that the keys in t are the same as the
   elements of l (with repetition) *)

Inductive tree_elems: tree -> list key -> Prop :=
| tree_elems_leaf: tree_elems Leaf nil
| tree_elems_node:  forall bl br v tl tr b,
           tree_elems tl bl ->
           tree_elems tr br ->
           Permutation b (v::bl++br) ->
           tree_elems (Node v tl tr) b.

(** **** Exercise: 3 stars, standard (priqueue_elems)

    Make an inductive definition, similar to [tree_elems], to relate
  a priority queue  "l"  to a list of all its elements.

  As you can see in the definition of [tree_elems],  a [tree] relates to
  _any_ permutation of its keys, not just a single permutation.
  You should make your [priqueue_elems] relation behave similarly,
  using (basically) the same technique as in [tree_elems].
*)

Inductive priqueue_elems: list tree -> list key -> Prop :=
  | priqueue_elems_nil : priqueue_elems [] []
  | priqueue_elems_cons : forall ht hl tt tl l,
      tree_elems ht hl ->
      priqueue_elems tt tl ->
      Permutation (hl ++ tl) l ->
      priqueue_elems (ht :: tt) l
.
(* Do not modify the following line: *)
Definition manual_grade_for_priqueue_elems : option (nat*string) := None.
(** [] *)

Definition Abs (p: priqueue) (al: list key) := priqueue_elems p al.

(* ================================================================= *)
(** ** Sanity Checks on the Abstraction Relation *)

(** **** Exercise: 2 stars, standard (tree_elems_ext)

    Extensionality theorem for the tree_elems relation *)

Theorem tree_elems_ext: forall t e1 e2,
  Permutation e1 e2 -> tree_elems t e1 -> tree_elems t e2.
Proof.
  intros t e1 e2 Hp He. destruct He.
  - apply Permutation_nil in Hp. subst e2. apply tree_elems_leaf.
  - refine (tree_elems_node _ _ _ _ _ _ He1 He2 _).
    apply Permutation_sym in Hp.
    exact (perm_trans Hp H).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (tree_perm) *)
Theorem tree_perm: forall t e1 e2,
  tree_elems t e1 -> tree_elems t e2 -> Permutation e1 e2.
Proof.
  intros t e1 e2 He1. generalize dependent e2.
  induction He1; intros e2 He2.
  - inv He2. apply perm_nil.
  - inv He2. apply Permutation_sym in H6.
    refine (perm_trans H (perm_trans (perm_skip _ _) H6)).
    exact (Permutation_app (IHHe1_1 _ H3) (IHHe1_2 _ H5)).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (priqueue_elems_ext)

    To prove [priqueue_elems_ext], you should almost be able to cut-and-paste the
   proof of [tree_elems_ext], with just a few edits.  *)

Theorem priqueue_elems_ext: forall q e1 e2,
  Permutation e1 e2 -> priqueue_elems q e1 -> priqueue_elems q e2.
Proof.
  intros q e1 e2 Hp Hq. destruct Hq.
  - apply Permutation_nil in Hp. subst e2. apply priqueue_elems_nil.
  - refine (priqueue_elems_cons _ _ _ _ _ H Hq _).
    apply (perm_trans H0 Hp).
Qed.
(** [] *)

Lemma abs_perm': forall p al bl,
   Abs p al -> Abs p bl -> Permutation al bl.
Proof.
  unfold Abs.
  intros p al bl Ha. generalize dependent bl.
  induction Ha; intros bl Hb.
  - inv Hb. apply perm_nil.
  - inv Hb. apply Permutation_sym in H0.
    refine (perm_trans H0 (perm_trans _ H6)).
    exact (Permutation_app (tree_perm _ _ _ H H3) (IHHa _ H4)).
Qed.

(** **** Exercise: 2 stars, standard (abs_perm) *)
Theorem abs_perm: forall p al bl,
   priq p -> Abs p al -> Abs p bl -> Permutation al bl.
Proof.
  exact (fun p al bl _ Hea Heb => abs_perm' p al bl Hea Heb).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (can_relate) *)
Lemma tree_can_relate: forall t, exists al, tree_elems t al.
Proof.
  induction t.
  - destruct IHt1 as [ll Hl].
    destruct IHt2 as [lr Hr].
    exists (k :: ll++lr).
    apply (tree_elems_node _ _ _ _ _ _ Hl Hr (Permutation_refl _)).
  - exists []. apply tree_elems_leaf.
Qed.

Theorem can_relate:  forall p, priq p -> exists al, Abs p al.
Proof.
  intros q _. induction q.
  - exists []. apply priqueue_elems_nil.
  - destruct IHq as [tl Ht].
    destruct (tree_can_relate a) as [al Ha].
    exists (al ++ tl).
    apply (priqueue_elems_cons _ _ _ _ _ Ha Ht (Permutation_refl _)).
Qed.
(** [] *)

(* ================================================================= *)
(** ** Various Functions Preserve the Abstraction Relation *)
(** **** Exercise: 1 star, standard (empty_relate) *)
Theorem empty_relate:  Abs empty nil.
Proof.
  apply priqueue_elems_nil.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (smash_elems)

     Warning:  This proof is rather long. *)

Theorem smash_elems: forall n t u bt bu,
                     pow2heap n t -> pow2heap n u ->
                     tree_elems t bt -> tree_elems u bu ->
                     tree_elems (smash t u) (bt ++ bu).
Proof.
  intros n t u bt bu Hht Hhu Het Heu.
  destruct t; [| contradiction Hht]. destruct u; [| contradiction Hhu].
  simpl in *.
  destruct t2; [contradiction Hht|]. destruct u2; [contradiction Hhu|].
  inv Het. inv Heu.
  inv H7. inv H4. rewrite app_nil_r in *.
  bdestruct (k >? k0).
  - refine (tree_elems_node _ _ _ _ _ _ _ tree_elems_leaf _).
    + exact (tree_elems_node _ _ _ _ _ _ H3 H2 (Permutation_refl _)).
    + rewrite app_nil_r.
      refine (perm_trans (Permutation_app H5 H8) _). simpl.
      apply perm_skip. apply Permutation_sym.
      exact (Permutation_cons_app _ _ _ (Permutation_app_comm _ _)).
  - refine (tree_elems_node _ _ _ _ _ _ _ tree_elems_leaf _).
    + exact (tree_elems_node _ _ _ _ _ _ H2 H3 (Permutation_refl _)).
    + rewrite app_nil_r.
      refine (perm_trans (Permutation_app H5 H8) _). simpl.
      change (k0 :: k :: bl ++ bl0) with ([k0] ++ (k :: bl ++ bl0)).
      apply Permutation_cons_app. simpl.
      apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Optional Exercises *)

(**  Some of these proofs are quite long, but they're not especially tricky. *)

(** **** Exercise: 4 stars, standard, optional (carry_elems) *)
Theorem carry_elems:
      forall n q,  priq' n q ->
      forall t, (t=Leaf \/ pow2heap n t) ->
      forall eq et, priqueue_elems q eq ->
                          tree_elems t et ->
                          priqueue_elems (carry q t) (eq++et).
Proof.
  intros n q. generalize dependent n.
  induction q; intros n Hpq t Hht eq et Heq Het.
  - inv Heq. simpl. destruct t.
    + refine (priqueue_elems_cons _ _ _ _ _ Het priqueue_elems_nil _).
      rewrite app_nil_r. apply Permutation_refl.
    + inv Het. apply priqueue_elems_nil.
  - simpl in *.
    destruct Hpq as [Hha Hpq]. inv Heq.
    destruct a.
    + destruct Hha as [Hha | Hha]; [discriminate Hha|].
      destruct t.
      * destruct Hht as [Hht | Hht]; [discriminate Hht|].
        refine (priqueue_elems_cons _ _ _ (tl ++ (hl ++ et)) _ tree_elems_leaf _ _).
          { refine (IHq _ Hpq _ (or_intror _) _ _ H2 _).
            - apply smash_valid; assumption.
            - refine (tree_elems_ext _ _ _ (Permutation_app_comm _ _) _).
              exact (smash_elems _ _ _ _ _ Hht Hha Het H1). }
          { simpl. rewrite app_assoc.
            refine (Permutation_app _ (Permutation_refl _)).
            refine (perm_trans (Permutation_app_comm _ _) H4). }
      * inv Het. rewrite app_nil_r.
        apply (priqueue_elems_cons _ _ _ _ _ H1 H2 H4).
    + inv H1. simpl in H4.
      apply (priqueue_elems_cons _ _ _ _ _ Het H2).
      apply (perm_trans (Permutation_app_comm _ _)).
      exact (Permutation_app H4 (Permutation_refl _)).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (insert_elems) *)
Theorem insert_relate:
        forall p al k, priq p -> Abs p al -> Abs (insert k p) (k::al).
Proof.
  intros p al k Hpp Hep. unfold insert.
  apply (priqueue_elems_ext _ (al ++ [k])).
  - change (k :: al) with ([k] ++ al). apply Permutation_app_comm.
  - apply (carry_elems _ _ Hpp).
    + right. simpl. exact I.
    + exact Hep.
    + exact (tree_elems_node _ _ _ _ _ _ tree_elems_leaf tree_elems_leaf (Permutation_refl _)).
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (join_elems) *)
Theorem join_elems:
                forall p q c n,
                      priq' n p ->
                      priq' n q ->
                      (c=Leaf \/ pow2heap n c) ->
                  forall pe qe ce,
                             priqueue_elems p pe ->
                             priqueue_elems q qe ->
                             tree_elems c ce ->
                              priqueue_elems (join p q c) (ce++pe++qe).
Proof.
  induction p; intros q c n Hpp Hpq Hhc pe qe ce Hep Heq Hec.
  - inv Hep. simpl.
    refine (priqueue_elems_ext _ _ _ (Permutation_app_comm _ _) _).
    apply (carry_elems _ _ Hpq); assumption.
  - simpl. simpl in Hpp. destruct Hpp as [Hha Hpp].
    destruct a as [ak al ar|].
    + destruct Hha as [Hha | Hha]; [discriminate Hha|].
      inv Hep.
      destruct q.
      * inv Heq. rewrite app_nil_r. destruct c.
          { destruct Hhc as [Hhc | Hhc]; [discriminate Hhc|].
            apply (priqueue_elems_cons _ _ _ (tl ++ (ce ++ hl)) _ tree_elems_leaf).
            - apply (carry_elems _ _ Hpp).
              + right. apply smash_valid; assumption.
              + assumption.
              + apply (smash_elems _ _ _ _ _ Hhc Hha); assumption.
            - simpl.
              refine (perm_trans _ (Permutation_app (Permutation_refl _) H4)).
              refine (perm_trans (Permutation_app_comm _ _) _).
              rewrite app_assoc. apply Permutation_refl. }
          { inv Hec. simpl. exact (priqueue_elems_cons _ _ _ _ _ H1 H2 H4). }
      * inv Hpq. inv Heq. destruct t.
          { refine (priqueue_elems_cons _ _ _ _ _ Hec _ _).
            - destruct H as [H | Hht]; [discriminate H|].
              refine (IHp _ _ _ Hpp H0 (or_intror _) _ _ _ H2 H7 _).
              + apply smash_valid; assumption.
              + apply (smash_elems _ _ _ _ _ Hha Hht H1 H6).
            - apply (Permutation_app (Permutation_refl _)).
              refine (perm_trans _ (Permutation_app H4 H9)).
              rewrite <- app_assoc. rewrite <- app_assoc.
              apply (Permutation_app (Permutation_refl _)).
              rewrite app_assoc. rewrite app_assoc.
              apply (Permutation_app (Permutation_app_comm _ _) (Permutation_refl _)). }
          { inv H6. simpl in H9.
            pose proof (fun c ce Hhc Hec => IHp _ c _ Hpp H0 Hhc _ _ ce H2 H7 Hec) as IH.
            destruct c.
            - destruct Hhc as [Hhc | Hhc]; [discriminate Hhc|].
              refine (priqueue_elems_cons _ _ _ ((ce ++ hl) ++ tl ++ tl0) _ tree_elems_leaf _ _).
              + apply IH.
                * right. apply smash_valid; assumption.
                * apply (smash_elems _ _ _ _ _ Hhc Hha); assumption.
              + simpl. rewrite <- app_assoc.
                apply (Permutation_app (Permutation_refl _)).
                rewrite app_assoc. apply (Permutation_app H4 H9).
            - inv Hec. simpl.
              refine (priqueue_elems_cons _ _ _ ([] ++ tl ++ tl0) _ H1 _ _).
              + apply IH.
                * left. reflexivity.
                * apply tree_elems_leaf.
              + simpl. rewrite app_assoc. apply (Permutation_app H4 H9). }
    + inv Hep. inv H1. simpl in H4. destruct q.
      * inv Heq. rewrite app_nil_r.
        apply (priqueue_elems_cons _ _ _ _ _ Hec H2).
        apply (Permutation_app (Permutation_refl _) H4).
      * inv Heq. simpl in Hpq. destruct Hpq as [Hht Hpq].
        pose proof (fun c ce Hhc Hec => IHp _ c _ Hpp Hpq Hhc _ _ ce H2 H3 Hec) as IH.
        destruct t.
          { destruct Hht as [Hht | Hht]; [discriminate Hht|].
            destruct c.
            - destruct Hhc as [Hhc | Hhc]; [discriminate Hhc|].
              refine (priqueue_elems_cons _ _ _ ((ce ++ hl) ++ tl ++ tl0) _ tree_elems_leaf _ _).
              + apply IH.
                * right. apply smash_valid; assumption.
                * apply (smash_elems _ _ _ _ _ Hhc Hht); assumption.
              + simpl. rewrite <- app_assoc.
                apply (Permutation_app (Permutation_refl _)).
                apply (perm_trans (Permutation_app_comm _ _)).
                rewrite <- app_assoc.
                exact (Permutation_app H4 (perm_trans (Permutation_app_comm _ _) H6)).
            - inv Hec. simpl. refine (priqueue_elems_cons _ _ _ ([] ++ tl ++ tl0) _ H1 _ _).
              + apply IH.
                * left. reflexivity.
                * apply tree_elems_leaf.
              + simpl. refine (perm_trans _ (Permutation_app H4 H6)).
                rewrite app_assoc. rewrite app_assoc.
                refine (Permutation_app (Permutation_app_comm _ _) (Permutation_refl _)). }
          { inv H1. simpl in H6.
            refine (priqueue_elems_cons _ _ _ ([] ++ tl ++ tl0) _ Hec _ _).
            + apply IH.
              * left. reflexivity.
              * apply tree_elems_leaf.
            + simpl. apply (Permutation_app (Permutation_refl _)).
              apply (Permutation_app H4 H6). }
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (merge_relate) *)
Theorem merge_relate:
    forall p q pl ql al,
       priq p -> priq q ->
       Abs p pl -> Abs q ql -> Abs (merge p q) al ->
       Permutation al (pl++ql).
Proof.
  intros p q pl ql al Hpp Hpq Hep Heq Hea.
  apply (abs_perm (merge p q)).
  - apply merge_priq; assumption.
  - exact Hea.
  - unfold merge. change (pl ++ ql) with ([] ++ pl ++ ql).
    apply (join_elems _ _ _ _ Hpp Hpq).
    + left. reflexivity.
    + assumption.
    + assumption.
    + apply tree_elems_leaf.
Qed.
(** [] *)


(** **** Exercise: 5 stars, standard, optional (delete_max_None_relate) *)
Theorem delete_max_None_relate:
        forall p, priq p -> (Abs p nil <-> delete_max p = None).
Proof.
  intros q Hpq. split.
  - assert (perm_nil_eq : forall (l1 l2 : list key), Permutation (l1 ++ l2) [] -> l1 = [] /\ l2 = []).
      { intros l1 l2 H. apply Permutation_sym in H.
        apply Permutation_nil in H. apply app_eq_nil in H. exact H. }
    assert (H: forall q n, priq' n q -> Abs q [] -> find_max q = None).
      { induction q0; intros n Hp He.
        - reflexivity.
        - simpl in *. destruct Hp as [Ha Hq0].
          inv He.
          apply perm_nil_eq in H4. destruct H4. subst hl tl.
          destruct a.
          + inv H1. apply Permutation_nil in H7. discriminate H7.
          + exact (IHq0 _ Hq0 H2). }
    intros Hq. unfold delete_max.
    rewrite (H _ _ Hpq Hq). reflexivity.
  - intros Hd. unfold delete_max in Hd.
    destruct (find_max q) eqn:Ef.
    + destruct (delete_max_aux k q). discriminate Hd.
    + clear Hd.
      assert (H : forall q n, priq' n q -> find_max q = None -> Abs q []).
        { induction q0; intros n Hp Hf.
          - apply priqueue_elems_nil.
          - simpl in Hp. destruct Hp as [Ha Hq0].
            simpl in Hf. destruct a; [discriminate Hf|].
            exact (priqueue_elems_cons _ _ _ _ _ tree_elems_leaf (IHq0 _ Hq0 Hf) (Permutation_refl _)). }
      exact (H _ _ Hpq Ef).
Qed.
(** [] *)


Lemma tree_elems_releate : forall t n m tl,
  pow2heap' n m t ->
  tree_elems t tl ->
  Forall (ge m) tl.
Proof.
  intros t n m tl H He. generalize dependent m. generalize dependent n.
  induction He; intros n m Hp.
  - apply Forall_nil.
  - destruct n; [contradiction Hp|]. simpl in Hp.
    destruct Hp as [Hm [Hpl Hpr]].
    apply (Permutation_Forall (Permutation_sym H)).
    apply (Forall_cons _ Hm). apply Forall_app. split.
    + refine (Forall_impl _ _ (IHHe1 _ _ Hpl)). lia.
    + exact (IHHe2 _ _ Hpr).
Qed.


Lemma find_max'_relate : forall p n pl,
  priq' n p ->
  Abs p pl ->
  forall c k,
  find_max' c p = k ->
  k >= c /\ Forall (ge k) pl /\ (k = c \/ In k pl).
Proof.
  induction p; intros n pl Hp He c k Hf.
  - inv He. simpl. split.
    + lia.
    + exact (conj (Forall_nil _) (or_introl eq_refl)).
  - simpl in *. destruct Hp as [Ha Hp]. inv He.
    destruct a.
    + destruct Ha as [Ha | Ha]; [discriminate Ha|].
      specialize (IHp _ _ Hp H2).
      simpl in Ha. destruct a2; [contradiction Ha|].
      inv H1. inv H7. rewrite app_nil_r in H8. apply Permutation_sym in H8.
      assert (Forall (ge k) hl) as Hghl.
        { apply (Permutation_Forall H8). apply Forall_cons.
          - apply Nat.le_refl.
          - exact (tree_elems_releate _ _ _ _ Ha H5). }

      specialize (tree_elems_releate _ _ _ _ Ha H5) as Hgb.
      bdestruct (k >? c).
      * destruct (IHp k _ eq_refl) as [Hg [Hf Hc]].
        split; [| split].
          { lia. }
          { apply (Permutation_Forall H4). apply Forall_app. split.
            - apply (@Forall_impl _ (ge k)).
              + lia.
              + exact Hghl.
            - exact Hf. }
          { right. apply (Permutation_in _ H4). apply in_or_app.
            destruct Hc.
            - left. rewrite H0.
              apply (Permutation_in _ H8). simpl.
              left. reflexivity.
            - right. exact H0. }
      * destruct (IHp c _ eq_refl) as [Hg [Hf Hc]].
        refine (conj Hg (conj _ _)).
          { apply (Permutation_Forall H4). apply Forall_app. split.
            - apply (@Forall_impl _ (ge k)).
              + lia.
              + exact Hghl.
            - exact Hf. }
          { destruct Hc as [Hcc | Hci].
            - left. exact Hcc.
            - right. apply (Permutation_in _ H4). apply in_or_app.
              right. exact Hci. }
    + inv H1. simpl in H4. apply (priqueue_elems_ext _ _ _ H4) in H2.
      exact (IHp _ _ Hp H2 _ _ eq_refl).
Qed.

Lemma find_max_Some_relate : forall p n k pl,
  priq' n p ->
  find_max p = Some k ->
  Abs p pl ->
  Forall (ge k) pl /\ In k pl.
Proof.
  induction p; intros n k pl Hpp Hf Hep.
  - discriminate Hf.
  - simpl in *. destruct Hpp as [Hha Hpp].
    destruct a.
    + injection Hf as Hf.
      inv Hep.
      destruct Hha as [Hha | Hha]; [discriminate Hha|]. simpl in Hha.
      destruct a2; [contradiction Hha|].
      destruct (find_max'_relate _ _ _ Hpp H2 k0 _ eq_refl) as [Hg [Hf Hi]].
      inv H1. inv H7. rewrite app_nil_r in H8.
      split.
      * apply (Permutation_Forall H4). apply Forall_app. split.
          { apply (@Forall_impl _ (ge k0)).
            - lia.
            - apply (Permutation_Forall (Permutation_sym H8)).
              apply Forall_cons.
              + apply Nat.le_refl.
              + exact (tree_elems_releate _ _ _ _ Hha H5). }
          { exact Hf. }
      * apply (Permutation_in _ H4). apply in_or_app.
        destruct Hi as [Hik | Hit].
          { left. apply (Permutation_in _ (Permutation_sym H8)). left.
            symmetry. exact Hik. }
          { right. exact Hit. }
    + refine (IHp _ _ _ Hpp Hf _).
      inv Hep. inv H1. simpl in *. exact (priqueue_elems_ext _ _ _ H4 H2).
Qed.

Lemma unzip_elem : forall t cont k n tl cl,
  pow2heap' n k t ->
  Abs (cont nil) cl ->
  tree_elems t tl ->
  Abs (unzip t cont) (tl ++ cl).
Proof.
  induction t; intros cont tk n tl cl Hp Hec Het.
  - destruct n; [contradiction Hp|]. simpl in *.
    destruct Hp as [Hk [Hpt1 Hpt2]].
    inv Het. apply (priqueue_elems_ext _ (br ++ (k :: bl ++ cl))).
    + change (k :: bl ++ cl) with ((k::bl) ++ cl). rewrite app_assoc.
      refine (Permutation_app (perm_trans _ (Permutation_sym H5)) (Permutation_refl _)).
      apply Permutation_sym. apply Permutation_cons_app. apply Permutation_app_comm.
    + apply (IHt2 _ _ _ _ _ Hpt2).
      * change (k :: bl ++ cl) with ((k::bl) ++ cl).
        refine (priqueue_elems_cons _ _ _ _ _ _ Hec (Permutation_refl _)).
        apply (tree_elems_node _ _ _ _ _ _ H2 tree_elems_leaf).
        rewrite app_nil_r. apply Permutation_refl.
      * assumption.
  - inv Het. simpl. assumption. 
Qed.

Lemma delete_max_aux_relate : forall p n k pl,
  priq' n p ->
  Abs p pl ->
  Forall (ge k) pl ->
  In k pl ->
  let (p0,p1) := delete_max_aux k p in
  forall p0l p1l,
    Abs p0 p0l ->
    Abs p1 p1l ->
    Permutation pl (k :: p0l ++ p1l).
Proof.
  induction p; intros n k pl Hpp Hep Hgk Hik.
  - inv Hep. contradiction Hik.
  - simpl in *. destruct Hpp as [Ha Hpp].
    inv Hep. destruct a as [ak al ar|].
    + destruct Ha as [Ha | Ha]; [discriminate Ha|]. simpl in Ha.
      destruct ar; [contradiction Ha|].
      
      apply (Permutation_Forall (Permutation_sym H4)) in Hgk.
      apply Forall_app in Hgk. destruct Hgk as [Hgh Hgt].
      apply (Permutation_in _ (Permutation_sym H4)) in Hik.
      apply in_app_or in Hik.

      bdestruct (k >? ak).
      * assert (In k tl).
          { destruct Hik; [| assumption]. exfalso.
            inv H1. inv H9. rewrite app_nil_r in H10.
            apply (Permutation_Forall H10) in Hgh.
            apply (Permutation_in _ H10) in H0. simpl in H0.
            destruct H0; [lia|].
            apply (tree_elems_releate _ _ _ _ Ha) in H7.
            rewrite Forall_forall in H7. apply H7 in H0.
            lia. }
        specialize (IHp _ _ _ Hpp H2 Hgt H0).
        destruct (delete_max_aux k p) as [pr pk]. intros p0l p1l Hep0 Hep1.
        inv Hep0. apply (perm_trans (Permutation_sym H4)).
        apply (perm_trans (Permutation_app (tree_perm _ _ _ H1 H6) (IHp _ _ H7 Hep1))).
        apply Permutation_sym. apply Permutation_cons_app.
        rewrite app_assoc. exact (Permutation_app (Permutation_sym H9) (Permutation_refl _)).
      * inv H1. inv H8. rewrite app_nil_r in H9.
        assert (k = ak).
          { specialize (Permutation_in ak (Permutation_sym H9) (or_introl eq_refl)) as Hi.
            rewrite Forall_forall in Hgh. apply Hgh in Hi.
            lia. }
        subst ak. intros p0l p1l Hep0 Hep1.
        apply (perm_trans (Permutation_sym H4)).
        apply (perm_trans (Permutation_app H9 (Permutation_refl _))). simpl.
        apply perm_skip. apply (perm_trans (Permutation_app_comm _ _)).
        apply Permutation_app.
          { inv Hep0. inv H3. simpl in *. refine (perm_trans _ H8).
            apply (abs_perm' p); assumption. }
          { specialize (unzip_elem _ (fun u => u) _ _ _ _ Ha priqueue_elems_nil H6) as Heu.
            rewrite app_nil_r in Heu.
            exact (abs_perm' _ _ _ Heu Hep1). }
    + inv H1. simpl in *.
      apply (priqueue_elems_ext _ _ _ H4) in H2.
      specialize (IHp _ _ _ Hpp H2 Hgk Hik). destruct (delete_max_aux k p).
      intros p0l p1l Hep0 Hep1. apply IHp.
      * inv Hep0. inv H1. simpl in *. apply (priqueue_elems_ext _ _ _ H6 H3).
      * assumption.
Qed.

(** **** Exercise: 5 stars, standard, optional (delete_max_Some_relate) *)
Theorem delete_max_Some_relate:
  forall (p q: priqueue) k (pl ql: list key), priq p ->
   Abs p pl ->
   delete_max p = Some (k,q) ->
   Abs q ql ->
   Permutation pl (k::ql) /\ Forall (ge k) ql.
Proof.
  intros p q k pl ql Hp Hep Hd Heq. unfold delete_max in Hd.
  destruct (find_max p) eqn:Ef; [| discriminate Hd].
  destruct (find_max_Some_relate _ _ _ _ Hp Ef Hep) as [Hgk Hik].
  specialize (delete_max_aux_relate _ _ _ _ Hp Hep Hgk Hik) as Hda.
  specialize (delete_max_aux_priq k0 _ _ Hp) as Hpd.
  destruct (delete_max_aux k0 p). injection Hd as E0 E1. subst k q.
  assert (Permutation pl (k0 :: ql)).
    { destruct Hpd as [Hpp0 Hpp1].
      destruct (can_relate p0 Hpp0) as [p0l Hep0].
      destruct (can_relate p1 Hpp1) as [p1l Hep1].
      specialize (Hda _ _ Hep0 Hep1).
      apply (perm_trans Hda). apply perm_skip.
      apply (abs_perm (join p0 p1 Leaf)).
      + exact (join_valid _ _ _ _ Hpp0 Hpp1 (or_introl eq_refl)).
      + change (p0l ++ p1l) with ([] ++ p0l ++ p1l).
        apply join_elems with (n := 0).
        * assumption.
        * assumption.
        * left. reflexivity.
        * assumption.
        * assumption.
        * apply tree_elems_leaf.
      + assumption. }
  split.
  - exact H.
  - apply Forall_inv_tail with k0. exact (Permutation_Forall H Hgk).
Qed.
(** [] *)

(** With the following line, we're done!  We have demonstrated that
  Binomial Queues are a correct implementation of mergeable
  priority queues.  That is, we have exhibited a [Module BinomQueue]
  that satisfies the [Module Type PRIQUEUE]. *)

End BinomQueue.

(* ################################################################# *)
(** * Measurement. *)

(** **** Exercise: 5 stars, standard, optional (binom_measurement)

    Adapt the program (but not necessarily the proof) to use Ocaml integers
  as keys, in the style shown in [Extract].   Write an ML program to
  exercise it with random inputs.  Compare the runtime to the implementation
  from [Priqueue], also adapted for Ocaml integers.
*)
(** [] *)

(* 2023-08-23 11:34 *)
