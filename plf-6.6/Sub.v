(** * Sub: Subtyping *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Types.
From PLF Require Import Smallstep.
Set Default Goal Selector "!".

(* ################################################################# *)
(** * Concepts *)

(** We now turn to _subtyping_, a key feature of -- in
    particular -- object-oriented programming languages. *)

(* ================================================================= *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:

      Person  = {name:String, age:Nat}
      Student = {name:String, age:Nat, gpa:Nat}
*)

(** In the simply typed lamdba-calculus with records, the term

      (\r:Person, (r.age)+1) {name="Pat",age=21,gpa=1}

   is not typable, since it applies a function that wants a two-field
   record to an argument that actually provides three fields, while the
   [T_App] rule demands that the domain type of the function being
   applied must match the type of the argument precisely.

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field.

   More generally, a record with more fields is "at least as good in
   any context" as one with just a subset of these fields, in the
   sense that any value belonging to the longer record type can be
   used _safely_ in any context expecting the shorter record type.  If
   the context expects something with the shorter type but we actually
   give it something with the longer type, nothing bad will
   happen (formally, the program will not get stuck).

   The principle at work here is called _subtyping_.  We say that "[S]
   is a subtype of [T]", written [S <: T], if a value of type [S] can
   safely be used in any context where a value of type [T] is
   expected.  The idea of subtyping applies not only to records, but
   to all of the type constructors in the language -- functions,
   pairs, etc. *)

(** Safe substitution principle:

       - [S] is a subtype of [T], written [S <: T], if a value of type
         [S] can safely be used in any context where a value of type
         [T] is expected.
*)

(* ================================================================= *)
(** ** Subtyping and Object-Oriented Languages *)

(** Subtyping plays a fundamental role in many programming
    languages -- in particular, it is central to the design of
    object-oriented languages and their libraries.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    roughly consists of projecting out the [m] field of [o] and
    applying it to [a1..an].

    The type of an object is called a _class_ -- or, in some
    languages, an _interface_.  It describes which methods and which
    data fields the object offers.  Classes and interfaces are related
    by the _subclass_ and _subinterface_ relations.  An object
    belonging to a subclass (or subinterface) is required to provide
    all the methods and fields of one belonging to a superclass (or
    superinterface), plus possibly some more.

    The fact that an object from a subclass can be used in place of
    one from a superclass provides a degree of flexibility that is
    extremely handy for organizing complex libraries.  For example, a
    GUI toolkit like Java's Swing framework might define an abstract
    interface [Component] that collects together the common fields and
    methods of all objects having a graphical representation that can
    be displayed on the screen and interact with the user, such as the
    buttons, checkboxes, and scrollbars of a typical GUI.  A method
    that relies only on this common interface can now be applied to
    any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared "private".  Classes can give
    _initializers_ that are used when constructing objects.  Code in
    subclasses can cooperate with code in superclasses via
    _inheritance_.  Classes can have static methods and fields.  Etc.,
    etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in [Pierce 2002] (in Bib.v), if
    you are interested.)  Instead, we'll study the core concepts
    behind the subclass / subinterface relation in the simplified
    setting of the STLC. *)

(* ================================================================= *)
(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------           (T_Sub)
                               Gamma |-- t1 \in T2

    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)

(** For example, we may know that [t1] is a record with two
    fields (e.g., [T1 = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T2 = {y:B->B}]) so that we can pass [t1] to a
    function that requires just a single-field record. *)

(* ================================================================= *)
(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(* ----------------------------------------------------------------- *)
(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is
    better (richer, safer) than [U] and [U] is better than [T],
    then [S] is better than [T]...

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

    ... and a rule of _reflexivity_, since certainly any type [T] is
    as good as itself:

                                   ------                              (S_Refl)
                                   T <: T
*)

(* ----------------------------------------------------------------- *)
(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be a subtype
    of another if each of its components is.

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)

(* ----------------------------------------------------------------- *)
(** *** Arrows *)

(** The subtyping rule for arrows is a little less intuitive.
    Suppose we have functions [f] and [g] with these types:

       f : C -> Student
       g : (C->Person) -> D

    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its argument to be
    a function yielding a record of type [Person].  Also suppose that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:

                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2

    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

    But notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second.

    Here is an example that illustrates this:

       f : Person -> C
       g : (Student -> C) -> D

    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. *)

(* ----------------------------------------------------------------- *)
(** *** Records *)

(** What about subtyping for record types? *)

(** The basic intuition is that it is always safe to use a "bigger"
    record in place of a "smaller" one.  That is, given a record type,
    adding extra fields will always result in a subtype.  If some code
    is expecting a record with fields [x] and [y], it is perfectly safe
    for it to receive a record with fields [x], [y], and [z]; the [z]
    field will simply be ignored.  For example,

    {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
    {name:String, age:Nat} <: {name:String}
    {name:String} <: {}

    This is known as "width subtyping" for records. *)

(** We can also create a subtype of a record type by replacing the type
    of one of its fields with a subtype.  If some code is expecting a
    record with a field [x] of type [T], it will be happy with a record
    having a field [x] of type [S] as long as [S] is a subtype of
    [T]. For example,

    {x:Student} <: {x:Person}

    This is known as "depth subtyping". *)

(** Finally, although the fields of a record type are written in a
    particular order, the order does not really matter. For example,

    {name:String,age:Nat} <: {age:Nat,name:String}

    This is known as "permutation subtyping". *)

(** We _could_ formalize these requirements in a single subtyping rule
    for records as follows:

                        forall jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}

    That is, the record on the left should have all the field labels of
    the one on the right (and possibly more), while the types of the
    common fields should be in the subtype relation.

    However, this rule is rather heavy and hard to read, so it is often
    decomposed into three simpler rules, which can be combined using
    [S_Trans] to achieve all the same effects. *)

(** First, adding fields to the end of a record type gives a subtype:

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

    We can use [S_RcdWidth] to drop later fields of a multi-field
    record while keeping earlier fields, showing for example that
    [{age:Nat,name:String} <: {age:Nat}]. *)

(** Second, subtyping can be applied inside the components of a compound
    record type:

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

    For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
    show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** Third, subtyping can reorder fields.  For example, we
    want [{name:String, gpa:Nat, age:Nat} <: Person], but we
    haven't quite achieved this yet: using just [S_RcdDepth] and
    [S_RcdWidth] we can only drop fields from the _end_ of a record
    type.  So we add:

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces).

    - In early versions of Java, a subclass could not change the
      argument or result types of a method of its superclass (i.e., no
      depth subtyping or no arrow subtyping, depending how you look at
      it). *)

(** **** Exercise: 2 stars, standard, especially useful (arrow_sub_wrong)

    Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:

                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2

    Give a concrete example of functions [f] and [g] with the following
    types...

       f : Student -> Nat
       g : (Person -> Nat) -> Nat

    ... such that the application [g f] will get stuck during
    execution.  (Use informal syntax.  No need to prove formally that
    the application gets stuck.)

*)

(* Do not modify the following line: *)
Definition manual_grade_for_arrow_sub_wrong : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Top *)

(** Finally, it is convenient to give the subtype relation a maximum
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:

                                   --------                             (S_Top)
                                   S <: Top

    The [Top] type is an analog of the [Object] type in Java and C#. *)

(* ----------------------------------------------------------------- *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and then...

    - adding a base type [Top],

    - adding the rule of subsumption

                         Gamma |-- t1 \in T1     T1 <: T2
                         --------------------------------            (T_Sub)
                               Gamma |-- t1 \in T2

      to the typing relation, and

    - defining a subtype relation as follows:

                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm}

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {j1:T1...jn:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {j1:T1...jn:Tn}
*)

(* ================================================================= *)
(** ** Exercises *)

(** The following "thought exercises" are repeated later as formal
    exercises. *)

(** **** Exercise: 1 star, standard, optional (subtype_instances_tf_1)

    Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.
    ([A], [B], and [C] here are base types like [Bool], [Nat], etc.)

    - [T->S <: T->S]

    - [Top->U <: S->Top]

    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]

    - [T->T->U <: S->S->V]

    - [(T->T)->U <: (S->S)->V]

    - [((T->S)->T)->U <: ((S->T)->S)->V]

    - [S*V <: T*U]

    [] *)

(** **** Exercise: 2 stars, standard (subtype_order)

    The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

Write these types in order from the most specific to the most general.

Where does the type [Top->Top->Student] fit into this order?
That is, state how [Top -> (Top -> Student)] compares with each
of the five types above. It may be unrelated to some of them.  
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_order : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_instances_tf_2)

    Which of the following statements are true?  Write _true_ or
    _false_ after each one.

      forall S T,
          S <: T  ->
          S->S   <:  T->T

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 

      exists S,
           S <: S->S 

      exists S,
           S->S <: S  

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2  
*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_instances_tf_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (subtype_concepts_tf)

    Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.

    - There exists a type that is a subtype of every other type.

    - There exists a pair type that is a supertype of every other
      pair type.

    - There exists a pair type that is a subtype of every other
      pair type.

    - There exists an arrow type that is a supertype of every other
      arrow type.

    - There exists an arrow type that is a subtype of every other
      arrow type.

    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].

    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].

*)

(* Do not modify the following line: *)
Definition manual_grade_for_subtype_concepts_tf : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (proper_subtypes)

    Is the following statement true or false?  Briefly explain your
    answer.  (Here [Base n] stands for a base type, where [n] is
    a string standing for the name of the base type.  See the
    Syntax section below.)

    forall T,
         ~(T = Bool \/ exists n, T = Base n) ->
         exists S,
            S <: T  /\  S <> T
*)

(* Do not modify the following line: *)
Definition manual_grade_for_proper_subtypes : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_1)
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)

       empty |-- (\p:T*Top, p.fst) ((\z:A,z), unit) \in A->A

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (small_large_2)
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       empty |-- (\p:(A->A * B->B), p) ((\z:A,z), (\z:B,z)) \in T

   - What is the _largest_ type [T] that makes the same assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (small_large_3)
   - What is the _smallest_ type [T] that makes the following
     assertion true?

       a:A |-- (\p:(A*T), (p.snd) (p.fst)) (a, \z:A,z) \in A

   - What is the _largest_ type [T] that makes the same assertion true?

    [] *)



(** **** Exercise: 2 stars, standard (small_large_4)
   - What is the _smallest_ type [T] (if one exists) that makes the
     following assertion true?

       exists S,
         empty |-- (\p:(A*T), (p.snd) (p.fst)) \in S

   - What is the _largest_ type [T] that makes the same
     assertion true?

*)

(* Do not modify the following line: *)
Definition manual_grade_for_small_large_4 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_1)

    What is the _smallest_ type [T] (if one exists) that makes
    the following assertion true?

      exists S t,
        empty |-- (\x:T, x x) t \in S
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (smallest_2)

    What is the _smallest_ type [T] that makes the following
    assertion true?

      empty |-- (\x:Top, x) ((\z:A,z) , (\z:B,z)) \in T
*)

(* Do not modify the following line: *)
Definition manual_grade_for_smallest_2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (count_supertypes)

    How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)

    [] *)

(** **** Exercise: 2 stars, standard (pair_permutation)

    The subtyping rule for product types

                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2

    intuitively corresponds to the "depth" subtyping rule for records.
    Extending the analogy, we might consider adding a "permutation" rule

                                   --------------
                                   T1*T2 <: T2*T1

    for products.  Is this a good idea? Briefly explain why or why not.

*)

(* Do not modify the following line: *)
Definition manual_grade_for_pair_permutation : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Formal Definitions *)

Module STLCSub.

(** Most of the definitions needed to formalize what we've discussed
    above -- in particular, the syntax and operational semantics of
    the language -- are identical to what we saw in the last chapter.
    We just need to extend the typing relation with the subsumption
    rule and add a new [Inductive] definition for the subtyping
    relation.  Let's first do the identical bits. *)

(** We include products in the syntax of types and terms, but not,
    for the moment, anywhere else; the [products] exercise below will
    ask you to extend the definitions of the value relation, operational
    semantics, subtyping relation, and typing relation and to extend
    the proofs of progress and preservation to fully support products. *)

(* ================================================================= *)
(** ** Core Definitions *)

(* ----------------------------------------------------------------- *)
(** *** Syntax *)

(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise.  For the sake of more
    interesting examples, we'll add an arbitrary set of base types
    like [String], [Float], etc.  (Since they are just for examples,
    we won't bother adding any operations over these base types, but
    we could easily do so.) *)

Inductive ty : Type :=
  | Ty_Top   : ty
  | Ty_Bool  : ty
  | Ty_Base  : string -> ty
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Unit  : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
  | tm_unit : tm
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'Base' x" := (Ty_Base x) (in custom stlc at level 0).

Notation "'Top'" := (Ty_Top) (in custom stlc at level 0).

Notation "X * Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 1).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 1).

Notation "{ x }" := x (in custom stlc at level 1, x constr).

(* ----------------------------------------------------------------- *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  | <{unit}> =>
      <{unit}>
  | <{ (t1, t2) }> =>
      <{( [x:=s] t1, [x:=s] t2 )}>
  | <{t0.fst}> =>
      <{ ([x:=s] t0).fst}>
  | <{t0.snd}> =>
      <{ ([x:=s] t0).snd}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ----------------------------------------------------------------- *)
(** *** Reduction *)

(** Likewise the definitions of [value] and [step]. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>
  | v_unit :
      value <{unit}>
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{ (v1, v2) }>
.

Hint Constructors value : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Prod1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Prod2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t t',
      t --> t' ->
      <{ t.fst }> --> <{ t'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> v1
  | ST_Snd1 : forall t t',
      t --> t' ->
      <{ t.snd }> --> <{ t'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> v2
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ================================================================= *)
(** ** Subtyping *)

(** Now we come to the interesting part.  We begin by defining
    the subtyping relation and developing some of its important
    technical properties. *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
where "T '<:' U" := (subtype T U).

(** Note that we don't need any special rules for base types ([Bool]
    and [Base]): they are automatically subtypes of themselves (by
    [S_Refl]) and [Top] (by [S_Top]), and that's all we want. *)

Hint Constructors subtype : core.

Module Examples.

Open Scope string_scope.
Notation x := "x".
Notation y := "y".
Notation z := "z".

Notation A := <{Base "A"}>.
Notation B := <{Base "B"}>.
Notation C := <{Base "C"}>.

Notation String := <{Base "String"}>.
Notation Float := <{Base "Float"}>.
Notation Integer := <{Base "Integer"}>.

Example subtyping_example_0 :
  <{C->Bool}> <: <{C->Top}>.
Proof. auto. Qed.

(** **** Exercise: 2 stars, standard, optional (subtyping_judgements)

    (Leave this exercise [Admitted] until after you have finished adding product
    types to the language -- see exercise [products] -- at least up to
    this point in the file).

    Recall that, in chapter [MoreStlc], the optional section
    "Encoding Records" describes how records can be encoded as pairs.
    Using this encoding, define pair types representing the following
    record types:

    Person := { name : String }
    Student := { name : String ; gpa : Float }
    Employee := { name : String ; ssn : Integer }
*)

Definition Person : ty := <{String * (Top * Top)}>.

Definition Student : ty := <{String * (Float * Top)}>.

Definition Employee : ty := <{String * (Top * Float)}>.

(** Now use the definition of the subtype relation to prove the following: *)

Example sub_student_person :
  Student <: Person.
Proof.
  apply S_Prod.
  - apply S_Refl.
  - apply S_Prod; auto.
Qed.

Example sub_employee_person :
  Employee <: Person.
Proof.
  apply S_Prod.
  - apply S_Refl.
  - apply S_Prod; auto.
Qed.
(** [] *)

(** The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)

(** **** Exercise: 1 star, standard, optional (subtyping_example_1) *)
Example subtyping_example_1 :
  <{Top->Student}> <:  <{(C->C)->Person}>.
Proof with eauto.
  apply S_Arrow.
  - apply S_Top.
  - apply sub_student_person.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (subtyping_example_2) *)
Example subtyping_example_2 :
  <{Top->Person}> <: <{Person->Top}>.
Proof with eauto.
  apply S_Arrow; apply S_Top.
Qed.
(** [] *)

End Examples.

(* ================================================================= *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := partial_map ty.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Module Examples2.
Import Examples.

(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. *)

(** **** Exercise: 1 star, standard, optional (typing_example_0) *)
(* empty |-- ((\z:A,z), (\z:B,z)) \in (A->A * B->B) *)

Example typing_example_0 : empty |-- ((\z:A,z), (\z:B,z)) \in ((A->A) * (B->B)).
Proof.
  apply T_Prod.
  - apply T_Abs. apply T_Var. reflexivity.
  - apply T_Abs. apply T_Var. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard, optional (typing_example_1) *)
(* empty |-- (\x:(Top * B->B), x.snd) ((\z:A,z), (\z:B,z))
         \in B->B *)

Example typing_example_1 :
  empty |-- (\x:(Top * (B->B)), x.snd) ((\z:A,z), (\z:B,z)) \in (B->B).
Proof.
  apply T_App with <{Top * (B->B)}>.
  - apply T_Abs. apply T_Snd with Ty_Top. apply T_Var. reflexivity.
  - apply T_Sub with <{(A->A) * (B->B)}>.
    + apply T_Prod; (apply T_Abs; apply T_Var; reflexivity).
    + apply S_Prod.
      * apply S_Top.
      * apply S_Refl.
Qed.

(** **** Exercise: 2 stars, standard, optional (typing_example_2) *)
(* empty |-- (\z:(C->C)->(Top * B->B), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in B->B *)

Example typing_example_2 :
  empty |-- (\z:(C->C)->(Top * (B->B)), (z (\x:C,x)).snd)
              (\z:C->C, ((\z:A,z), (\z:B,z)))
         \in (B->B).
Proof.
  eapply T_App.
  - apply T_Abs. eapply T_Snd. eapply T_App.
    + apply T_Var. reflexivity.
    + apply T_Abs. apply T_Var. reflexivity.
  - eapply T_Sub.
    + apply T_Abs. apply T_Prod; (apply T_Abs; apply T_Var; reflexivity).
    + apply S_Arrow.
      * apply S_Refl.
      * apply S_Prod; auto.
Qed.

End Examples2.

(* ################################################################# *)
(** * Properties *)

(** The fundamental properties of the system that we want to
    check are the same as always: progress and preservation.  Unlike
    the extension of the STLC with references (chapter [References]),
    we don't need to change the _statements_ of these properties to
    take subtyping into account.  However, their proofs do become a
    little bit more involved. *)

(* ================================================================= *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to establish a couple of critical structural properties of the
    subtype relation:
       - [Bool] is the only subtype of [Bool], and
       - every subtype of an arrow type is itself an arrow type. *)

(** These are called _inversion lemmas_ because they play a
    similar role in proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or
    [T], each inversion lemma reasons about what this derivation must
    look like to tell us something further about the shapes of [S] and
    [T] and the existence of subtype relations between their parts. *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Bool) *)
Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; try discriminate HeqV; subst T.
  - reflexivity.
  - intuition congruence.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (sub_inversion_arrow) *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *)
    destruct (IHHs2 V1 V2 HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Arrow *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed. 
(** [] *)

(** There are additional _inversion lemmas_ for the other types:
       - [Unit] is the only subtype of [Unit], and
       - [Base n] is the only subtype of [Base n], and
       - [Top] is the only supertype of [Top]. *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Unit) *)
Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof with auto.
  intros U Hs.
  remember <{Unit}> as V.
  induction Hs; try discriminate HeqV.
  - reflexivity.
  - subst T. intuition congruence.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Base) *)
Lemma sub_inversion_Base : forall U s,
     U <: <{Base s}> ->
     U = <{Base s}>.
Proof with auto.
  intros U s Hs.
  remember <{Base s}> as V.
  induction Hs; try discriminate HeqV.
  - reflexivity.
  - subst T. intuition congruence.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (sub_inversion_Top) *)
Lemma sub_inversion_Top : forall U,
     <{ Top }> <: U ->
     U = <{ Top }>.
Proof with auto.
  intros U Hs.
  remember <{Top}> as V.
  induction Hs; try discriminate HeqV.
  - reflexivity.
  - subst S. intuition congruence.
  - symmetry. assumption.
Qed.
(** [] *)

Lemma sub_inversion_Prod : forall U V1 V2,
  U <: <{ V1 * V2 }> ->
  exists U1 U2,
    U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *) destruct (IHHs2 _ _ HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Prod *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed.

(* ================================================================= *)
(** ** Canonical Forms *)

(** The proof of the progress theorem -- that a well-typed
    non-value can always take a step -- doesn't need to change too
    much: we just need one small refinement.  When we're considering
    the case where the term in question is an application [t1 t2]
    where both [t1] and [t2] are values, we need to know that [t1] has
    the _form_ of a lambda-abstraction, so that we can apply the
    [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |-- t1 \in T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e., values) of function
    type. *)

(** **** Exercise: 3 stars, standard, optional (canonical_forms_of_arrow_types) *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros Gamma s T1 T2 Ht Hv.
  remember <{T1 -> T2}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Abs *) injection HeqT as E1 E2. subst T0 T3.
    exists x. exists T2. exists t1. reflexivity.
  - (* T_Sub *) subst T2.
    apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv U1 U2 Eu).
Qed.
(** [] *)

Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
  intros Gamma s T1 T2 Ht Hv.
  remember <{ T1 * T2 }> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Sub *) subst T2.
    apply sub_inversion_Prod in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv _ _ Eu).
  - (* T_Prod *) injection HeqT as E1 E2. subst T0 T3.
    exists t1. exists t2. reflexivity.
Qed.

(** Similarly, the canonical forms of type [Bool] are the constants
    [tm_true] and [tm_false]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The proof of progress now proceeds just like the one for the
    pure STLC, except that in several places we invoke canonical forms
    lemmas...

    _Theorem_ (Progress): For any term [t] and type [T], if [empty |--
    t \in T] then [t] is a value or [t --> t'] for some term [t'].

    _Proof_: Let [t] and [T] be given, with [empty |-- t \in T].
    Proceed by induction on the typing derivation.

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [true], and
    [false] are already values.  The [T_Var] case is vacuous
    because variables cannot be typed in the empty context.  The
    remaining cases are more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty
      |-- t2 \in T1].  Moreover, by the induction hypothesis, either
      [t1] is a value or it steps, and either [t2] is a value or it
      steps.  There are three possibilities to consider:

      - First, suppose [t1 --> t1'] for some term [t1'].  Then [t1
        t2 --> t1' t2] by [ST_App1].

      - Second, suppose [t1] is a value and [t2 --> t2'] for some term
        [t2'].  Then [t1 t2 --> t1 t2'] by rule [ST_App2] because [t1]
        is a value.

      - Third, suppose [t1] and [t2] are both values.  By the
        canonical forms lemma for arrow types, we know that [t1] has
        the form [\x:S1,s2] for some [x], [S1], and [s2].  But then
        [(\x:S1,s2) t2 --> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_If], then
      there are terms [t1], [t2], and [t3] such that [t = if t1
      then t2 else t3], with [empty |-- t1 \in Bool] and with [empty
      |-- t2 \in T] and [empty |-- t3 \in T].  Moreover, by the
      induction hypothesis, either [t1] is a value or it steps.

       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = true] or [t1 = false].  In
         either case, [t] can step, using rule [ST_IfTrue] or
         [ST_IfFalse].

       - If [t1] can step, then so can [t], by rule [ST_If].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [T2] such that [T1 <: T2] and [empty |-- t1 \in T1].  The
      desired result is exactly the induction hypothesis for the
      typing subderivation. *)

(** Formally: *)

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

(* ================================================================= *)
(** ** Inversion Lemmas for Typing *)

(** The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are immediate from
    the definition in the pure STLC (formally: that can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following inversion lemma tells us that, if we have a
    derivation of some typing statement [Gamma |-- \x:S1,t2 \in T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)

(** _Lemma_: If [Gamma |-- \x:S1,t2 \in T], then there is a type [S2]
    such that [x|->S1; Gamma |-- t2 \in S2] and [S1 -> S2 <: T].

    Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!  (Why?) *)

(** _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |--
     \x:S1,t2 \in T].  The cases for [T_Var] and [T_App] are vacuous
     as those rules cannot be used to give a type to a syntactic
     abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [x:S1;
       Gamma |-- t2 \in T12].  Picking [T12] for [S2] gives us what we
       need, since [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |-- \x:S1,t2
       \in S].  The IH for the typing subderivation tells us that there
       is some type [S2] with [S1 -> S2 <: S] and [x:S1; Gamma |-- t2
       \in S2].  Picking type [S2] gives us what we need, since [S1 ->
       S2 <: T] then follows by [S_Trans]. *)

(** Formally: *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

(** **** Exercise: 3 stars, standard, optional (typing_inversion_var) *)
Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T H.
  remember (tm_var x) as t.
  induction H; try discriminate Heqt.
  - (* T_Var *) inversion Heqt; subst. exists T1. auto.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S [Ex Hs]].
    exists S. split.
    + assumption.
    + apply S_Trans with T1; assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (typing_inversion_app) *)
Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1->T2) /\
    Gamma |-- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 H.
  remember <{ t1 t2 }> as t.
  induction H; try discriminate Heqt.
  - (* T_App *) injection Heqt as E1 E2. subst t0 t3.
    exists T2. auto.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S [Ht1 Ht2]].
    exists S. split.
    + eapply T_Sub.
      * apply Ht1.
      * apply S_Arrow; auto.
    + assumption.
Qed.
(** [] *)

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |-- unit \in T ->
    <{Unit}> <: T.
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_prod : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists S1 S2,
    Gamma |-- t1 \in S1 /\
    Gamma |-- t2 \in S2 /\
    <{S1 * S2}> <: T.
Proof.
  intros Gamma t1 t2 T H.
  remember <{ (t1, t2) }> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht1 [Ht2 Hs]]]].
    exists S1. exists S2. repeat split.
    + apply Ht1.
    + apply Ht2.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E1 E2. subst t0 t3.
    exists T1. exists T2. auto.
Qed.

Lemma typing_inversion_fst : forall Gamma t T,
  Gamma |-- t.fst \in T ->
  exists S1 S2,
    Gamma |-- t \in (S1 * S2) /\
    S1 <: T.
Proof.
  intros Gamma t1 T H.
  remember <{t1.fst}> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht Hs]]].
    exists S1. exists S2. split.
    + apply Ht.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E. subst t1.
    exists T1. exists T2. split.
    + assumption.
    + apply S_Refl.
Qed.

Lemma typing_inversion_snd : forall Gamma t T,
  Gamma |-- t.snd \in T ->
  exists S1 S2,
    Gamma |-- t \in (S1 * S2) /\
    S2 <: T.
Proof.
  intros Gamma t1 T H.
  remember <{t1.snd}> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht Hs]]].
    exists S1. exists S2. split.
    + apply Ht.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E. subst t1.
    exists T1. exists T2. split.
    + assumption.
    + apply S_Refl.
Qed.

(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.

Lemma pair_prod : forall t1 t2 T1 T2,
  empty |-- (t1, t2) \in (T1 * T2) ->
  empty |-- t1 \in T1 /\ empty |-- t2 \in T2.
Proof.
  intros t1 t2 T1 T2 H.
  apply typing_inversion_prod in H.
  destruct H as [S1 [S2 [HtS1 [HtS2 Hs]]]].
  apply sub_inversion_Prod in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
  injection E as E1 E2. subst U1 U2.
  split.
  - apply T_Sub with S1; assumption.
  - apply T_Sub with S2; assumption.
Qed.

(* ================================================================= *)
(** ** Weakening *)

(** The weakening lemma is proved as in pure STLC. *)

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

(* ================================================================= *)
(** ** Substitution *)

(** When subtyping is involved proofs are generally easier
    when done by induction on typing derivations, rather than on terms.
    The _substitution lemma_ is proved as for pure STLC, but using
    induction on the typing derivation this time (see Exercise
    substitution_preserves_typing_from_typing_ind in StlcProp.v). *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. rewrite update_eq in H. injection H as E. subst T1.
      apply weakening_empty. assumption.
    + rewrite update_neq in H; [| assumption].
      apply T_Var. assumption.
  - (* T_Abs *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. apply T_Abs. rewrite update_shadow in Ht. assumption.
    + apply T_Abs. apply IHHt. rewrite update_permute; auto.
Qed.

(* ================================================================= *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and the inversion lemma from above to extract structural
    information from typing assumptions. *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |-- t \in T] and [t --> t'], then [empty |-- t'
    \in T].

    _Proof_: Let [t] and [T] be given such that [empty |-- t \in T].
    We proceed by induction on the structure of this typing
    derivation. The [T_Abs], [T_Unit], [T_True], and [T_False] cases
    are vacuous because abstractions and constants don't step.  Case
    [T_Var] is vacuous as well, since the context is empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that [t =
       t1 t2], [T = T2], [empty |-- t1 \in T1 -> T2], and [empty |--
       t2 \in T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S,t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].

       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |-- s2 \in
       T2].  It then follows by the substitution
       lemma ([substitution_preserves_typing]) that [empty |-- [x:=t2]
       t12 \in T2] as desired.

     - If the final step of the derivation uses rule [T_If], then
       there are terms [t1], [t2], and [t3] such that [t = if t1 then
       t2 else t3], with [empty |-- t1 \in Bool] and with [empty |--
       t2 \in T] and [empty |-- t3 \in T].  Moreover, by the induction
       hypothesis, if [t1] steps to [t1'] then [empty |-- t1' : Bool].
       There are three cases to consider, depending on which rule was
       used to show [t --> t'].

          - If [t --> t'] by rule [ST_If], then [t' = if t1' then t2
            else t3] with [t1 --> t1'].  By the induction hypothesis,
            [empty |-- t1' \in Bool], and so [empty |-- t' \in T] by
            [T_If].

          - If [t --> t'] by rule [ST_IfTrue] or [ST_IfFalse], then
            either [t' = t2] or [t' = t3], and [empty |-- t' \in T]
            follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |-- t \in S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... 
  - (* T_Fst *) inversion HE; subst.
    + apply T_Fst with T2. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
  - (* T_Snd *) inversion HE; subst.
    + apply T_Snd with T1. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
Qed.

(* ================================================================= *)
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping omits record
    types for brevity.  If we want to deal with them more seriously,
    we have two choices.

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:

    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e., (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e., (Nat,(Top,(Nat,Top)))

    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding. *)

(* ================================================================= *)
(** ** Exercises *)

(** **** Exercise: 2 stars, standard (variations)

    Each part of this problem suggests a different way of changing the
    definition of the STLC with Unit and subtyping.  (These changes
    are not cumulative: each part starts from the original language.)
    In each part, list which properties (Progress, Preservation, both,
    or neither) become false.  If a property becomes false, give a
    counterexample.

    - Suppose we add the following typing rule:

                           Gamma |-- t \in S1->S2
                    S1 <: T1     T1 <: S1      S2 <: T2
                    -----------------------------------    (T_Funny1)
                           Gamma |-- t \in T1->T2

    - Suppose we add the following reduction rule:

                             --------------------         (ST_Funny21)
                             unit --> (\x:Top. x)

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny3)
                               Unit <: Top->Top

    - Suppose we add the following subtyping rule:

                               ----------------          (S_Funny4)
                               Top->Top <: Unit

    - Suppose we add the following reduction rule:

                             ---------------------      (ST_Funny5)
                             (unit t) --> (t unit)

    - Suppose we add the same reduction rule _and_ a new typing rule:

                             ---------------------       (ST_Funny5)
                             (unit t) --> (t unit)

                           ---------------------------     (T_Funny6)
                           empty |-- unit \in Top->Top

    - Suppose we _change_ the arrow subtyping rule to:

                          S1 <: T1 S2 <: T2
                          -----------------              (S_Arrow')
                          S1->S2 <: T1->T2

*)

Module Variation1.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2
  | T_Funny1 : forall Gamma t S1 S2 T1 T2,
      Gamma |-- t \in (S1 -> S2) ->
      S1 <: T1 ->
      T1 <: S1 ->
      S2 <: T2 ->
      Gamma |-- t \in (T1 -> T2)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros Gamma s T1 T2 Ht Hv.
  remember <{T1 -> T2}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Abs *) injection HeqT as E1 E2. subst T0 T3.
    exists x. exists T2. exists t1. reflexivity.
  - (* T_Sub *) subst T2.
    apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv U1 U2 Eu).
  - (* T_funny1 *) apply (IHHt Hv S1 S2). reflexivity.
Qed.
(** [] *)

Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
  intros Gamma s T1 T2 Ht Hv.
  remember <{ T1 * T2 }> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Sub *) subst T2.
    apply sub_inversion_Prod in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv _ _ Eu).
  - (* T_Prod *) injection HeqT as E1 E2. subst T0 T3.
    exists t1. exists t2. reflexivity.
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  - (* T_Funny1 *) destruct (IHhas_type H3) as [S3 [Hs Ht]].
    exists S3. split.
    + apply (S_Trans _ <{S0 -> S2}> _ Hs). apply S_Arrow; assumption.
    + assumption.
Qed.

Lemma typing_inversion_prod : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists S1 S2,
    Gamma |-- t1 \in S1 /\
    Gamma |-- t2 \in S2 /\
    <{S1 * S2}> <: T.
Proof.
  intros Gamma t1 t2 T H.
  remember <{ (t1, t2) }> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht1 [Ht2 Hs]]]].
    exists S1. exists S2. repeat split.
    + apply Ht1.
    + apply Ht2.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E1 E2. subst t0 t3.
    exists T1. exists T2. auto.
  - (* T_Funny1 *) destruct (IHhas_type Heqt) as [S3 [S4 [_ [_ Hs]]]].
    apply sub_inversion_arrow in Hs. destruct Hs as [U1 [U2 [E _]]].
    discriminate E.
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.

Lemma pair_prod : forall t1 t2 T1 T2,
  empty |-- (t1, t2) \in (T1 * T2) ->
    empty |-- t1 \in T1 /\ empty |-- t2 \in T2.
Proof.
  intros t1 t2 T1 T2 H.
  apply typing_inversion_prod in H.
  destruct H as [S1 [S2 [HtS1 [HtS2 Hs]]]].
  apply sub_inversion_Prod in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
  injection E as E1 E2. subst U1 U2.
  split.
  - apply T_Sub with S1; assumption.
  - apply T_Sub with S2; assumption.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. rewrite update_eq in H. injection H as E. subst T1.
      apply weakening_empty. assumption.
    + rewrite update_neq in H; [| assumption].
      apply T_Var. assumption.
  - (* T_Abs *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. apply T_Abs. rewrite update_shadow in Ht. assumption.
    + apply T_Abs. apply IHHt. rewrite update_permute; auto.
Qed.

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... 
  - (* T_Fst *) inversion HE; subst.
    + apply T_Fst with T2. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
  - (* T_Snd *) inversion HE; subst.
    + apply T_Snd with T1. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
Qed.

End Variation1.

Module Variation2.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Prod1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Prod2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t t',
      t --> t' ->
      <{ t.fst }> --> <{ t'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> v1
  | ST_Snd1 : forall t t',
      t --> t' ->
      <{ t.snd }> --> <{ t'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> v2
  | ST_Funny2 : forall x,
      <{ unit }> --> <{ \x:Top, x }>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

Theorem not_preservation : ~ forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof.
  intros H.
  specialize (H tm_unit (tm_abs "x" Ty_Top (tm_var "x")) 
    Ty_Unit (T_Unit _) (ST_Funny2 _)).
    apply typing_inversion_abs in H. destruct H as [S2 [Hs _]].
    apply sub_inversion_Unit in Hs. discriminate Hs.
Qed.

End Variation2.

Module Variation3.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
  | S_Funny3 : <{ Unit }> <: <{ Top -> Top }>

where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; try discriminate HeqV; subst T.
  - reflexivity.
  - intuition congruence.
Qed.
(** [] *)

Lemma sub_inversion_Unit : forall U,
     U <: <{Unit}> ->
     U = <{Unit}>.
Proof with auto.
  intros U Hs.
  remember <{Unit}> as V.
  induction Hs; try discriminate HeqV.
  - reflexivity.
  - subst T. intuition congruence.
Qed.
(** [] *)

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     U = <{ Unit }> \/
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) right. subst T. exists V1. exists V2. auto.
  - (* S_Trans *)
    destruct (IHHs2 V1 V2 HeqV) as [Eu | [U1 [U2 [Eu [HsU1 HsU2]]]]].
    + left. apply sub_inversion_Unit. rewrite Eu in Hs1. apply Hs1.
    + destruct (IHHs1 _ _ Eu) as [Es | [S1 [S2 [Es [HsS1 HsS2]]]]].
      * left. assumption.
      * right. exists S1. exists S2. repeat split.
         { apply Es. }
         { apply S_Trans with U1; assumption. }
         { apply S_Trans with U2; assumption. }
  - (* S_Arrow *) right. injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
  - (* S_Funny3 *) left. reflexivity.
Qed.
(** [] *)

Lemma sub_inversion_Prod : forall U V1 V2,
  U <: <{ V1 * V2 }> ->
  exists U1 U2,
    U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *) destruct (IHHs2 _ _ HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Prod *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed.

Theorem not_progress : ~ forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof.
  intros H.
  specialize (H <{unit unit}> Ty_Top).
  assert (Ht : empty |-- unit unit \in Top).
    { eapply T_App.
      - eapply (T_Sub _ _ _ _ (T_Unit _)).
        apply S_Funny3.
      - apply (T_Sub _ _ _ _ (T_Unit _) (S_Top _)). }
  specialize (H Ht). destruct H as [H | [t' Ht']].
  - inversion H.
  - inversion Ht'; subst; clear Ht'.
    + inversion H2.
    + inversion H3.
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_var : forall Gamma (x:string) T,
  Gamma |-- x \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T H.
  remember (tm_var x) as t.
  induction H; try discriminate Heqt.
  - (* T_Var *) inversion Heqt; subst. exists T1. auto.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S [Ex Hs]].
    exists S. split.
    + assumption.
    + apply S_Trans with T1; assumption.
Qed.
(** [] *)

Lemma typing_inversion_prod : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists S1 S2,
    Gamma |-- t1 \in S1 /\
    Gamma |-- t2 \in S2 /\
    <{S1 * S2}> <: T.
Proof.
  intros Gamma t1 t2 T H.
  remember <{ (t1, t2) }> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht1 [Ht2 Hs]]]].
    exists S1. exists S2. repeat split.
    + apply Ht1.
    + apply Ht2.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E1 E2. subst t0 t3.
    exists T1. exists T2. auto.
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [E | [U1 [U2 [Heq [Hsub1 Hsub2]]]]].
  - discriminate E.
  - injection Heq as Heq; subst... 
Qed.

Lemma pair_prod : forall t1 t2 T1 T2,
  empty |-- (t1, t2) \in (T1 * T2) ->
    empty |-- t1 \in T1 /\ empty |-- t2 \in T2.
Proof.
  intros t1 t2 T1 T2 H.
  apply typing_inversion_prod in H.
  destruct H as [S1 [S2 [HtS1 [HtS2 Hs]]]].
  apply sub_inversion_Prod in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
  injection E as E1 E2. subst U1 U2.
  split.
  - apply T_Sub with S1; assumption.
  - apply T_Sub with S2; assumption.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. rewrite update_eq in H. injection H as E. subst T1.
      apply weakening_empty. assumption.
    + rewrite update_neq in H; [| assumption].
      apply T_Var. assumption.
  - (* T_Abs *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. apply T_Abs. rewrite update_shadow in Ht. assumption.
    + apply T_Abs. apply IHHt. rewrite update_permute; auto.
Qed.

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... 
  - (* T_Fst *) inversion HE; subst.
    + apply T_Fst with T2. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
  - (* T_Snd *) inversion HE; subst.
    + apply T_Snd with T1. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
Qed.

End Variation3.

Module Variation4.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
  | S_Funny4 : <{Top->Top}> <: <{ Unit }>
where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; try discriminate HeqV; subst T.
  - reflexivity.
  - intuition congruence.
Qed.
(** [] *)

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ V1 <: U1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *)
    destruct (IHHs2 V1 V2 HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Arrow *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed. 
(** [] *)

Lemma sub_inversion_Prod : forall U V1 V2,
  U <: <{ V1 * V2 }> ->
  exists U1 U2,
    U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *) destruct (IHHs2 _ _ HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Prod *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros Gamma s T1 T2 Ht Hv.
  remember <{T1 -> T2}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Abs *) injection HeqT as E1 E2. subst T0 T3.
    exists x. exists T2. exists t1. reflexivity.
  - (* T_Sub *) subst T2.
    apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv U1 U2 Eu).
Qed.
(** [] *)

Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
  intros Gamma s T1 T2 Ht Hv.
  remember <{ T1 * T2 }> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Sub *) subst T2.
    apply sub_inversion_Prod in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv _ _ Eu).
  - (* T_Prod *) injection HeqT as E1 E2. subst T0 T3.
    exists t1. exists t2. reflexivity.
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

Lemma typing_inversion_prod : forall Gamma t1 t2 T,
  Gamma |-- (t1, t2) \in T ->
  exists S1 S2,
    Gamma |-- t1 \in S1 /\
    Gamma |-- t2 \in S2 /\
    <{S1 * S2}> <: T.
Proof.
  intros Gamma t1 t2 T H.
  remember <{ (t1, t2) }> as t.
  induction H; try discriminate Heqt.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S1 [S2 [Ht1 [Ht2 Hs]]]].
    exists S1. exists S2. repeat split.
    + apply Ht1.
    + apply Ht2.
    + apply S_Trans with T1; assumption.
  - (* T_Prod *) injection Heqt as E1 E2. subst t0 t3.
    exists T1. exists T2. auto.
Qed.

Lemma abs_arrow : forall x S1 s2 T1 T2,
  empty |-- \x:S1,s2 \in (T1->T2) ->
     T1 <: S1
  /\ (x |-> S1 ; empty) |-- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  destruct Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  injection Heq as Heq; subst...  Qed.

Lemma pair_prod : forall t1 t2 T1 T2,
  empty |-- (t1, t2) \in (T1 * T2) ->
    empty |-- t1 \in T1 /\ empty |-- t2 \in T2.
Proof.
  intros t1 t2 T1 T2 H.
  apply typing_inversion_prod in H.
  destruct H as [S1 [S2 [HtS1 [HtS2 Hs]]]].
  apply sub_inversion_Prod in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
  injection E as E1 E2. subst U1 U2.
  split.
  - apply T_Sub with S1; assumption.
  - apply T_Sub with S2; assumption.
Qed.

Lemma weakening : forall Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |-- t \in T  ->
     Gamma' |-- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Corollary weakening_empty : forall Gamma t T,
     empty |-- t \in T  ->
     Gamma |-- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma substitution_preserves_typing : forall Gamma x U t v T,
   (x |-> U ; Gamma) |-- t \in T ->
   empty |-- v \in U   ->
   Gamma |-- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T Ht Hv.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction Ht; intros Gamma' G; simpl; eauto.
  - (* T_Var *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. rewrite update_eq in H. injection H as E. subst T1.
      apply weakening_empty. assumption.
    + rewrite update_neq in H; [| assumption].
      apply T_Var. assumption.
  - (* T_Abs *) subst Gamma. destruct (String.eqb_spec x x0).
    + subst x0. apply T_Abs. rewrite update_shadow in Ht. assumption.
    + apply T_Abs. apply IHHt. rewrite update_permute; auto.
Qed.

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0... 
  - (* T_Fst *) inversion HE; subst.
    + apply T_Fst with T2. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
  - (* T_Snd *) inversion HE; subst.
    + apply T_Snd with T1. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
Qed.

End Variation4.

Module Variation5.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Prod1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Prod2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t t',
      t --> t' ->
      <{ t.fst }> --> <{ t'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> v1
  | ST_Snd1 : forall t t',
      t --> t' ->
      <{ t.snd }> --> <{ t'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> v2
  | ST_Funny5 : forall t,
      <{ unit t }> --> <{ t unit }>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

Theorem preservation : forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof with eauto.
  intros t t' T HT. generalize dependent t'.
  remember empty as Gamma.
  induction HT;
       intros t' HE; subst;
       try solve [inversion HE; subst; eauto].
  - (* T_App *)
    inversion HE; subst...
    (* Most of the cases are immediate by induction,
       and [eauto] takes care of them *)
    + (* ST_AppAbs *)
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T0...
    + (* ST_Funny5 *) apply typing_inversion_unit in HT1.
      apply sub_inversion_arrow in HT1. destruct HT1 as [U1 [U2 [E _]]].
      discriminate E.
  - (* T_Fst *) inversion HE; subst.
    + apply T_Fst with T2. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
  - (* T_Snd *) inversion HE; subst.
    + apply T_Snd with T1. apply IHHT; auto.
    + destruct (pair_prod _ _ _ _ HT). assumption.
Qed.

End Variation5.

Module Variation6.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : forall t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : forall t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
  | ST_Prod1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ (t1, t2) }> --> <{ (t1', t2) }>
  | ST_Prod2 : forall v1 t2 t2',
      value v1 ->
      t2 --> t2' ->
      <{ (v1, t2) }> --> <{ (v1, t2') }>
  | ST_Fst1 : forall t t',
      t --> t' ->
      <{ t.fst }> --> <{ t'.fst }>
  | ST_FstPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).fst }> --> v1
  | ST_Snd1 : forall t t',
      t --> t' ->
      <{ t.snd }> --> <{ t'.snd }>
  | ST_SndPair : forall v1 v2,
      value v1 ->
      value v2 ->
      <{ (v1, v2).snd }> --> v2
  | ST_Funny5 : forall t,
      <{ unit t }> --> <{ t unit }>
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2
  | T_Funny6 : empty |-- unit \in (Top -> Top)

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  s = <{ unit }> \/
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros Gamma s T1 T2 Ht Hv.
  remember <{T1 -> T2}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Abs *) right. injection HeqT as E1 E2. subst T0 T3.
    exists x. exists T2. exists t1. reflexivity.
  - (* T_Sub *) subst T2.
    apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv U1 U2 Eu).
  - (* T_Funny6 *) left. reflexivity.
Qed.
(** [] *)

Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
  intros Gamma s T1 T2 Ht Hv.
  remember <{ T1 * T2 }> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Sub *) subst T2.
    apply sub_inversion_Prod in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv _ _ Eu).
  - (* T_Prod *) injection HeqT as E1 E2. subst T0 T3.
    exists t1. exists t2. reflexivity.
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; try subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [Et | [x [S1 [s2 H1]]]].
          { subst t1. exists <{ t2 unit }>. apply ST_Funny5. }
          { subst. exists (<{ [x:=t2]s2 }>)... }
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.


Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |-- \x:S1,t2 \in T ->
     exists S2,
       <{S1->S2}> <: T
       /\ (x |-> S1 ; Gamma) |-- t2 \in S2.
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember <{\x:S1,t2}> as t.
  induction H;
    inversion Heqt; subst; intros; try solve_by_invert.
  - (* T_Abs *)
    exists T1...
  - (* T_Sub *)
    destruct IHhas_type as [S2 [Hsub Hty]]...
Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |-- t1 t2 \in T2 ->
  exists T1,
    Gamma |-- t1 \in (T1->T2) /\
    Gamma |-- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 H.
  remember <{ t1 t2 }> as t.
  induction H; try discriminate Heqt.
  - (* T_App *) injection Heqt as E1 E2. subst t0 t3.
    exists T2. auto.
  - (* T_Sub *) destruct (IHhas_type Heqt) as [S [Ht1 Ht2]].
    exists S. split.
    + eapply T_Sub.
      * apply Ht1.
      * apply S_Arrow; auto.
    + assumption.
Qed.
(** [] *)

Theorem not_preservation : ~ forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof.
  intros H.
  remember (tm_app 
    (tm_abs "x" <{Top->Top}>
      (tm_abs "y" Ty_Bool
        (tm_app (tm_var "x") (tm_var "y"))))
    tm_unit) as t.
  remember (tm_abs "y" Ty_Bool (tm_app tm_unit (tm_var "y"))) as t'.
  assert (Ht : empty |-- t \in (Bool->Top)).
    { subst t. eapply T_App.
      - apply T_Abs. apply T_Abs. eapply T_App.
        + apply T_Var. reflexivity.
        + eapply T_Sub.
          * apply T_Var. reflexivity.
          * apply S_Top.
      - apply T_Funny6. }
  subst t t'.
  specialize (H _ _ _ Ht (ST_AppAbs _ _ _ _ v_unit)). simpl in H.
  clear Ht.
  apply typing_inversion_abs in H. destruct H as [S2 [_ Ht]].
  apply typing_inversion_app in Ht. destruct Ht as [T1 [Hu _]].

  remember ("y" |-> <{Bool}>) as Gamma.
  remember tm_unit as t.
  remember <{T1->S2}> as T. generalize dependent S2. generalize dependent T1.
  induction Hu; try discriminate Heqt; intros.
  - discriminate HeqT.
  - subst T2. apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Et1 _]]].
    apply (IHHu HeqGamma Heqt _ _ Et1).
  - assert (H : None = Some <{ Bool }>).
      { replace (Some <{Bool}>) with (("y"|-><{Bool}>) "y").
        - rewrite <- HeqGamma. reflexivity.
        - reflexivity. }
    discriminate H.
Qed.

End Variation6.

Module Variation7.

Reserved Notation "T '<:' U" (at level 40).

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      S <: <{Top}>
  | S_Arrow : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1->S2}> <: <{T1->T2}>
  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      <{S1 * S2}> <: <{T1 * T2}>
where "T '<:' U" := (subtype T U).

Hint Constructors subtype : core.

Reserved Notation "Gamma '|--' t '\in' T" (at level 40,
                                          t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Pure STLC, same as before: *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  | T_True : forall Gamma,
       Gamma |-- true \in Bool
  | T_False : forall Gamma,
       Gamma |-- false \in Bool
  | T_If : forall t1 t2 t3 T1 Gamma,
       Gamma |-- t1 \in Bool ->
       Gamma |-- t2 \in T1 ->
       Gamma |-- t3 \in T1 ->
       Gamma |-- if t1 then t2 else t3 \in T1
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit
  (* New rule of subsumption: *)
  | T_Sub : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      T1 <: T2 ->
      Gamma |-- t1 \in T2
  | T_Prod : forall Gamma t1 T1 t2 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1, t2) \in (T1 * T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 * T2) ->
      Gamma |-- t.snd \in T2

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Lemma sub_inversion_Bool : forall U,
     U <: <{Bool}> ->
     U = <{Bool}>.
Proof with auto.
  intros U Hs.
  remember <{Bool}> as V.
  induction Hs; try discriminate HeqV; subst T.
  - reflexivity.
  - intuition congruence.
Qed.
(** [] *)

Lemma sub_inversion_arrow : forall U V1 V2,
     U <: <{V1->V2}> ->
     exists U1 U2,
     U = <{U1->U2}> /\ U1 <: V1 /\ U2 <: V2.
Proof with eauto.
  intros U V1 V2 Hs.
  remember <{V1->V2}> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *)
    destruct (IHHs2 V1 V2 HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Arrow *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed. 
(** [] *)

Lemma sub_inversion_Prod : forall U V1 V2,
  U <: <{ V1 * V2 }> ->
  exists U1 U2,
    U = <{ U1 * U2 }> /\ U1 <: V1 /\ U2 <: V2.
Proof.
  intros U V1 V2 Hs.
  remember <{ V1 * V2 }> as V.
  generalize dependent V2. generalize dependent V1.
  induction Hs; intros; try discriminate HeqV.
  - (* S_Refl *) subst T. exists V1. exists V2. auto.
  - (* S_Trans *) destruct (IHHs2 _ _ HeqV) as [U1 [U2 [Eu [HsU1 HsU2]]]].
    destruct (IHHs1 _ _ Eu) as [S1 [S2 [Es [HsS1 HsS2]]]].
    exists S1. exists S2. repeat split.
    + apply Es.
    + apply S_Trans with U1; assumption.
    + apply S_Trans with U2; assumption.
  - (* S_Prod *) injection HeqV as E1 E2. subst T1 T2.
    exists S1. exists S2. auto.
Qed.

Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |-- s \in (T1->T2) ->
  value s ->
  exists x S1 s2,
     s = <{\x:S1,s2}>.
Proof with eauto.
  intros Gamma s T1 T2 Ht Hv.
  remember <{T1 -> T2}> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Abs *) injection HeqT as E1 E2. subst T0 T3.
    exists x. exists T2. exists t1. reflexivity.
  - (* T_Sub *) subst T2.
    apply sub_inversion_arrow in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv U1 U2 Eu).
Qed.
(** [] *)

Lemma canonical_forms_of_Pair : forall Gamma s T1 T2,
  Gamma |-- s \in (T1 * T2) ->
  value s ->
  exists v1 v2, s = <{ (v1, v2) }>.
Proof.
  intros Gamma s T1 T2 Ht Hv.
  remember <{ T1 * T2 }> as T.
  generalize dependent T2. generalize dependent T1.
  induction Ht; intros; try solve_by_invert.
  - (* T_Sub *) subst T2.
    apply sub_inversion_Prod in H. destruct H as [U1 [U2 [Eu _]]].
    apply (IHHt Hv _ _ Eu).
  - (* T_Prod *) injection HeqT as E1 E2. subst T0 T3.
    exists t1. exists t2. reflexivity.
Qed.

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |-- s \in Bool ->
  value s ->
  s = tm_true \/ s = tm_false.
Proof with eauto.
  intros Gamma s Hty Hv.
  remember <{Bool}> as T.
  induction Hty; try solve_by_invert...
  - (* T_Sub *)
    subst. apply sub_inversion_Bool in H. subst...
Qed.

Theorem progress : forall t T,
     empty |-- t \in T ->
     value t \/ exists t', t --> t'.
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  assert (E : @empty ty = @empty ty) by reflexivity.
  induction Ht; subst Gamma; auto.
  - (* T_Var *)
    discriminate.
  - (* T_App *)
    right.
    destruct IHHt1; subst...
    + (* t1 is a value *)
      destruct IHHt2; subst...
      * (* t2 is a value *)
        eapply canonical_forms_of_arrow_types in Ht1; [|assumption].
        destruct Ht1 as [x [S1 [s2 H1]]]. subst.
        exists (<{ [x:=t2]s2 }>)...
      * (* t2 steps *)
        destruct H0 as [t2' Hstp]. exists <{ t1 t2' }>...
    + (* t1 steps *)
      destruct H as [t1' Hstp]. exists <{ t1' t2 }>...
  - (* T_If *)
    right.
    destruct IHHt1.
    + (* t1 is a value *) eauto.
    + apply canonical_forms_of_Bool in Ht1; [|assumption].
      destruct Ht1; subst...
    + destruct H. rename x into t1'. eauto. 
  - (* T_Prod *)
    destruct (IHHt1 E) as [Hv1 | [t1' Ht1']].
    + destruct (IHHt2 E) as [Hv2 | [t2' Ht2']].
      * left. apply v_pair; assumption.
      * right. exists <{ (t1, t2') }>. apply ST_Prod2; assumption.
    + right. exists <{ (t1', t2) }>. apply ST_Prod1; assumption.
  - (* T_Fst *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v1. inversion Hv. apply ST_FstPair; assumption.
    + exists <{ t'.fst }>. apply ST_Fst1. assumption.
  - (* T_Snd *) right. destruct (IHHt E) as [Hv | [t' Ht']].
    + destruct (canonical_forms_of_Pair _ _ _ _ Ht Hv) as [v1 [v2 Et]].
      subst t. exists v2. inversion Hv. apply ST_SndPair; assumption.
    + exists <{ t'.snd }>. apply ST_Snd1. assumption.
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |-- unit \in T ->
    <{Unit}> <: T.
Proof with eauto.
  intros Gamma T Htyp. remember <{ unit }> as tu.
  induction Htyp;
    inversion Heqtu; subst; intros...
Qed.

Theorem not_preservation : ~ forall t t' T,
     empty |-- t \in T  ->
     t --> t'  ->
     empty |-- t' \in T.
Proof.
  intros H.
  remember (tm_app
    (tm_abs "x" Ty_Bool
      (tm_if (tm_var "x") tm_true tm_false))
    tm_unit) as t.
  remember (tm_if tm_unit tm_true tm_false) as t'.
  assert (Ht : empty |-- t \in Bool).
    { subst t. eapply T_App.
      - eapply T_Sub.
        + apply T_Abs. apply T_If; auto.
        + apply S_Arrow.
          * apply S_Top.
          * apply S_Refl.
      - eapply T_Sub.
        + apply T_Unit.
        + apply S_Top. }
  subst t t'.
  specialize (H _ _ _ Ht (ST_AppAbs _ _ _ _ v_unit)).
  clear Ht. simpl in H.

  remember <{ if unit then true else false }> as t1.
  induction H; try discriminate Heqt1.
  - injection Heqt1 as E _ _. subst t1.
    apply typing_inversion_unit in H.
    apply sub_inversion_Bool in H. discriminate H.
  - apply (IHhas_type Heqt1).
Qed.

End Variation7.

(* Do not modify the following line: *)
Definition manual_grade_for_variations : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Exercise: Adding Products *)

(** **** Exercise: 5 stars, standard (products)

    Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension by modifying the definitions and proofs above:

    - Constructors for pairs, first and second projections, and
      product types have already been added to the definitions of
      [ty] and [tm].  Also, the definition of substitution has been
      extended.

    - Extend the surrounding definitions accordingly (refer to chapter
      [MoreSTLC]):

        - value relation
        - operational semantics
        - typing relation

    - Extend the subtyping relation with this rule:

                        S1 <: T1    S2 <: T2
                        --------------------   (S_Prod)
                         S1 * S2 <: T1 * T2

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add a couple of completely new lemmas.) *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_products_value_step : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_subtype_has_type : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_progress : option (nat*string) := None.
(* Do not modify the following line: *)
Definition manual_grade_for_products_preservation : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Formalized "Thought Exercises" *)

(** The following are formal exercises based on the previous "thought
    exercises." *)

Module FormalThoughtExercises.
Import Examples.
Notation p := "p".
Notation a := "a".

Definition TF P := P \/ ~P.

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1a) *)
Theorem formal_subtype_instances_tf_1a:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->S}> <: <{T->S}>).
Proof.
  left. intros S T U V _ _. apply S_Refl.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1b) *)
Theorem formal_subtype_instances_tf_1b:
  TF (forall S T U V, S <: T -> U <: V ->
         <{Top->U}> <: <{S->Top}>).
Proof.
  left. intros S T U V _ _.
  apply S_Arrow.
  - apply S_Top.
  - apply S_Top.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1c) *)
Theorem formal_subtype_instances_tf_1c:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(C->C)->(A*B)}> <: <{(C->C)->(Top*B)}>).
Proof.
  left. intros _ _ _ _ _ _. apply S_Arrow.
  - apply S_Refl.
  - apply S_Prod.
    * apply S_Top.
    * apply S_Refl.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1d) *)
Theorem formal_subtype_instances_tf_1d:
  TF (forall S T U V, S <: T -> U <: V ->
         <{T->(T->U)}> <: <{S->(S->V)}>).
Proof.
  left. intros S T U V Hst Huv. apply S_Arrow.
  - apply Hst.
  - apply S_Arrow.
    + apply Hst.
    + apply Huv.
Qed.
(** [] *)

Lemma top_not_unit : ~ Ty_Top <: Ty_Unit.
Proof.
  intros H. apply sub_inversion_Top in H. discriminate H.
Qed.

Lemma sub_inversion_arrow2 : forall T1 T2 U1 U2,
  <{T1 -> T2}> <: <{ U1 -> U2 }> ->
  U1 <: T1 /\ T2 <: U2.
Proof.
  intros. apply sub_inversion_arrow in H.
  destruct H as [S1 [S2 [E [Hs1 Hs2]]]].
  injection E as E1 E2. subst.
  split; assumption.
Qed.

Lemma sub_inversion_Prod2 : forall T1 T2 U1 U2,
  <{ T1 * T2 }> <: <{ U1 * U2 }> ->
  T1 <: U1 /\ T2 <: U2.
Proof.
  intros. apply sub_inversion_Prod in H.
  destruct H as [S1 [S2 [E [Hs1 Hs2]]]].
  injection E as E1 E2. subst.
  split; assumption.
Qed.

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1e) *)
Theorem formal_subtype_instances_tf_1e:
  TF (forall S T U V, S <: T -> U <: V ->
         <{(T->T)->U}> <: <{(S->S)->V}>).
Proof.
  right. intros H.
  specialize (H Ty_Unit Ty_Top Ty_Unit Ty_Unit (S_Top _) (S_Refl _)).
  apply sub_inversion_arrow2 in H. destruct H as [HsU1 _].
  apply sub_inversion_arrow2 in HsU1. destruct HsU1 as [HsU1 _].
  apply (top_not_unit HsU1).
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1f) *)
Theorem formal_subtype_instances_tf_1f:
  TF (forall S T U V, S <: T -> U <: V ->
         <{((T->S)->T)->U}> <: <{((S->T)->S)->V}>).
Proof.
  left. intros S T U V Hst Huv. apply S_Arrow.
  - apply S_Arrow.
    + apply S_Arrow; apply Hst.
    + apply Hst.
  - apply Huv.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard, optional (formal_subtype_instances_tf_1g) *)
Theorem formal_subtype_instances_tf_1g:
  TF (forall S T U V, S <: T -> U <: V ->
         <{S*V}> <: <{T*U}>).
Proof.
  right. intros H.
  specialize (H Ty_Unit Ty_Unit Ty_Unit Ty_Top (S_Refl _) (S_Top _)).
  apply sub_inversion_Prod2 in H. destruct H as [_ HsU2].
  apply (top_not_unit HsU2).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2a) *)
Theorem formal_subtype_instances_tf_2a:
  TF (forall S T,
         S <: T ->
         <{S->S}> <: <{T->T}>).
Proof.
  right. intros H. specialize (H Ty_Unit Ty_Top (S_Top _)).
  apply sub_inversion_arrow2 in H. destruct H as [HsU1 _].
  apply (top_not_unit HsU1).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2b) *)
Theorem formal_subtype_instances_tf_2b:
  TF (forall S,
         S <: <{A->A}> ->
         exists T,
           S = <{T->T}> /\ T <: A).
Proof.
  right. intros H.
  specialize (H
    (Ty_Arrow Ty_Top (Ty_Base "A"))
    (S_Arrow _ _ _ _ (S_Top _) (S_Refl _))).
  destruct H as [T [E Hs]].
  injection E as E1 _. subst T.
  apply sub_inversion_Top in Hs. discriminate Hs.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2d)

    Hint: Assert a generalization of the statement to be proved and
    use induction on a type (rather than on a subtyping
    derviation). *)
Theorem formal_subtype_instances_tf_2d:
  TF (exists S,
         S <: <{S->S}>).
Proof.
  right. 
  assert (H : forall S T, ~ S <: <{T->S}>).
    { induction S; intros T H;
        destruct (sub_inversion_arrow _ _ _ H) as [U1 [U2 [E [_ HsU2]]]]; 
        try discriminate E.
      - injection E as _ E. subst U2.
        apply (IHS2 _ HsU2). }
  intros [S Hs]. apply (H S S Hs).
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_instances_tf_2e) *)
Theorem formal_subtype_instances_tf_2e:
  TF (exists S,
         <{S->S}> <: S).
Proof.
  left. exists Ty_Top. apply S_Top.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfa) *)
Theorem formal_subtype_concepts_tfa:
  TF (exists T, forall S, S <: T).
Proof.
  left. exists Ty_Top. apply S_Top.
Qed.
(** [] *)

Theorem no_min_sub : ~ exists T, forall S, T <: S.
Proof.
  intros [T H]. destruct T;
    try (specialize (H Ty_Unit); apply sub_inversion_Unit in H; discriminate H).
  - specialize (H Ty_Bool). apply sub_inversion_Bool in H.
    discriminate H.
Qed.

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfb) *)
Theorem formal_subtype_concepts_tfb:
  TF (exists T, forall S, T <: S).
Proof.
  right. exact no_min_sub.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfc) *)
Theorem formal_subtype_concepts_tfc:
  TF (exists T1 T2, forall S1 S2, <{S1*S2}> <: <{T1*T2}>).
Proof.
  left. exists Ty_Top. exists Ty_Top. intros S1 S2.
  apply S_Prod; apply S_Top.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfd) *)
Theorem formal_subtype_concepts_tfd:
  TF (exists T1 T2, forall S1 S2, <{T1*T2}> <: <{S1*S2}>).
Proof.
  right. intros [T1 [T2 H]].
  apply no_min_sub.
  exists T2. intros S. specialize (H T1 S).
  apply sub_inversion_Prod2 in H. intuition.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfe) *)
Theorem formal_subtype_concepts_tfe:
  TF (exists T1 T2, forall S1 S2, <{S1->S2}> <: <{T1->T2}>).
Proof.
  right. intros [T1 [T2 H]].
  apply no_min_sub.
  exists T1. intros S. specialize (H S T2).
  apply sub_inversion_arrow2 in H. intuition.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tff) *)
Theorem formal_subtype_concepts_tff:
  TF (exists T1 T2, forall S1 S2, <{T1->T2}> <: <{S1->S2}>).
Proof.
  right. intros [T1 [T2 H]].
  apply no_min_sub.
  exists T2. intros S. specialize (H T1 S).
  apply sub_inversion_arrow2 in H. intuition.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfg) *)

Fixpoint ty_fun1 i :=
  match i with
  | 0 => Ty_Top
  | S n => Ty_Prod Ty_Top (ty_fun1 n)
  end.

Lemma ty_fun1_inj : forall i j, i <> j -> ty_fun1 i <> ty_fun1 j.
Proof.
  induction i; intros j Hne.
  + destruct j.
    * exfalso. apply Hne. reflexivity.
    * discriminate.
  + destruct j.
    * discriminate.
    * rewrite -> PeanoNat.Nat.succ_inj_wd_neg in Hne. apply IHi in Hne.
      intros H. injection H as H. exact (Hne H).
Qed.

Lemma ty_fun1_sub : forall i, ty_fun1 (S i) <: ty_fun1 i.
Proof.
  induction i.
  + apply S_Top.
  + apply S_Prod.
    * apply S_Refl.
    * apply IHi.
Qed.

Theorem formal_subtype_concepts_tfg:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f (S i) <: f i)).
Proof.
  left. exists ty_fun1.
  split.
  - exact ty_fun1_inj.
  - exact ty_fun1_sub.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (formal_subtype_concepts_tfh) *)
Theorem formal_subtype_concepts_tfh:
  TF (exists f : nat -> ty,
         (forall i j, i <> j -> f i <> f j) /\
         (forall i, f i <: f (S i))).
Proof.
  left. exists (fun i => Ty_Arrow (ty_fun1 i) Ty_Top).
  split.
  - intros i j Hne H. apply ty_fun1_inj in Hne.
    injection H as H. exact (Hne H).
  - intros i. apply S_Arrow.
    + apply ty_fun1_sub.
    + apply S_Refl.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (formal_proper_subtypes) *)
Theorem formal_proper_subtypes:
  TF (forall T,
         ~(T = <{Bool}> \/ (exists n, T = <{Base n}>) \/ T = <{Unit}>) ->
         exists S,
           S <: T /\ S <> T).
Proof.
  right. intros H.
  specialize (H (Ty_Arrow Ty_Top Ty_Unit)).
  destruct H as [S [Hs Hne]].
  - intros [contra | [[n contra] | contra]]; discriminate contra.
  - apply sub_inversion_arrow in Hs. destruct Hs as [U1 [U2 [E [HsU1 HsU2]]]].
    subst S.
    apply sub_inversion_Top in HsU1. subst U1.
    apply sub_inversion_Unit in HsU2. subst U2.
    apply Hne. reflexivity.
Qed.
(** [] *)

Definition smallest_largest HT :=
  (* There exists a smallest and a largest. *)
  (exists TS TL, forall T, TS <: T /\ T <: TL <-> HT T)
  \/
  (* There exists a smallest, but no largest. *)
  ((exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists a largest, but not smallest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   (exists TL, forall T, T <: TL <-> HT T))
  \/
  (* There exists neither a smallest nor a largest. *)
  (~(exists TS, forall T, TS <: T <-> HT T) /\
   ~(exists TL, forall T, T <: TL <-> HT T)).

Lemma typing_inv_var : forall Gamma (x:string) T U,
  Gamma x = Some U ->
  Gamma |-- x \in T ->
  U <: T.
Proof.
  intros. apply typing_inversion_var in H0.
  destruct H0 as [S [E Hs]].
  rewrite E in H. injection H as Eu. subst S. apply Hs.
Qed.

(** **** Exercise: 3 stars, advanced, optional (formal_small_large_1) *)
Theorem formal_small_large_1:
  smallest_largest
  (fun T =>
   empty |-- <{(\p:T*Top, p.fst) ((\z:A, z), unit)}> \in <{A->A}>).
Proof.
  left. exists <{A->A}>. exists <{A->A}>. intros T. split.
  - intros [Haa Ht].
    apply sub_inversion_arrow in Ht. destruct Ht as [U1 [U2 [E [_ HsU2]]]].
    subst T.
    apply sub_inversion_Base in HsU2. subst U2.
    apply sub_inversion_arrow2 in Haa. destruct Haa as [HsU1 _].
    apply sub_inversion_Base in HsU1. subst U1.

    eapply T_App.
    + apply T_Abs. apply T_Fst with Ty_Top. apply T_Var. reflexivity.
    + apply T_Prod.
      * apply T_Abs. apply T_Var. reflexivity.
      * eapply T_Sub; eauto.
  - intros H. apply and_comm.
    apply typing_inversion_app in H. destruct H as [T1 [Hl Hr]].
    apply abs_arrow in Hl. destruct Hl as [HsT1 Hp].
    apply typing_inversion_fst in Hp. destruct Hp as [S1 [S3 [Hp HsS12]]].
    eapply typing_inv_var in Hp; [| reflexivity].
    apply sub_inversion_Prod2 in Hp. destruct Hp as [HsTS1 _]. clear S3.

    assert (HsT : T <: <{ A->A }>).
      { apply S_Trans with S1.
        - apply HsTS1.
        - apply HsS12. }
    clear HsTS1 S1 HsS12.

    apply typing_inversion_prod in Hr. destruct Hr as [S1 [S2 [Ha [_ HsP]]]].
    apply typing_inversion_abs in Ha. destruct Ha as [S3 [HsArr Hz]].
    assert (HsS12 : <{ S1 * S2 }> <: <{ T * Top }>).
      { eapply S_Trans with T1; assumption. }
    clear T1 HsT1 HsP.
    apply sub_inversion_Prod2 in HsS12. destruct HsS12 as [HsS1 _]. clear S2.
    assert (HsAS3 : <{ A -> S3 }> <: T).
      { eapply S_Trans with S1; assumption. }
    clear S1 HsS1 HsArr.

    apply sub_inversion_arrow in HsT. destruct HsT as [U1 [U2 [E [HsU1 HsU2]]]].
    subst T.
    apply sub_inversion_arrow2 in HsAS3. destruct HsAS3 as [Ha _].
    apply sub_inversion_Base in HsU2. subst U2.
    split.
    + apply S_Arrow; auto.
    + apply S_Arrow; auto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (formal_small_large_2) *)
Theorem formal_small_large_2:
  smallest_largest
  (fun T =>
   empty |-- <{(\p:(A->A)*(B->B), p) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
  assert (H : forall T,
    (empty |-- <{(\p:(A->A)*(B->B), p) ((\z:A, z), (\z:B, z))}> \in T) <->
    <{(A->A) * (B->B)}> <: T).
    { intros T. split.
      - intros H. apply typing_inversion_app in H. destruct H as [T1 [Hl _]].
        apply abs_arrow in Hl. destruct Hl as [_ Hp].
        eapply typing_inv_var in Hp;[|reflexivity].
        assumption.
      - intros H. eapply T_App.
        + apply T_Abs. eapply T_Sub.
          * apply T_Var. reflexivity.
          * apply H.
        + apply T_Prod; apply T_Abs; apply T_Var; reflexivity. }
  left. exists <{ (A->A) * (B->B)}>. exists Ty_Top. intros T. split.
  - intros [Hs _]. apply H. assumption.
  - intros Ht. apply H in Ht. split.
    + assumption.
    + apply S_Top.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (formal_small_large_3) *)
Theorem formal_small_large_3:
  smallest_largest
  (fun T =>
   (a |-> A) |-- <{(\p:A*T, (p.snd) (p.fst)) (a, \z:A, z)}> \in A).
Proof.
  assert (H : forall T,
    ((a |-> A) |-- <{(\p:A*T, (p.snd) (p.fst)) (a, \z:A, z)}> \in A) <->
    T = <{A->A}>).
    { intros T. split.
      - intros H. apply typing_inversion_app in H. destruct H as [T1 [Htl Htr]].
        
        apply typing_inversion_prod in Htr. destruct Htr as [S1 [S2 [Htf [Hts HsS12]]]].
        eapply typing_inv_var in Htf;[|reflexivity].
        apply typing_inversion_abs in Hts. destruct Hts as [S3 [HsAS3 _]].
        assert (HsL : <{A * (A->S3)}> <: T1).
          { eapply S_Trans.
            - apply S_Prod.
              + apply Htf.
              + apply HsAS3.
            - apply HsS12. }
        clear S1 S2 Htf HsAS3 HsS12.

        apply typing_inversion_abs in Htl. destruct Htl as [S1 [HsAT Ht]].
        apply sub_inversion_arrow2 in HsAT. destruct HsAT as [HsT1 HsS1].
        apply sub_inversion_Base in HsS1. subst S1.
        assert (HsAAS3 : <{A*(A->S3)}> <: <{A*T}>)
          by (apply S_Trans with T1; assumption).
        clear T1 HsT1 HsL.
        apply sub_inversion_Prod2 in HsAAS3. destruct HsAAS3 as [_ HsAS3].

        apply typing_inversion_app in Ht. destruct Ht as [T2 [Hts _]].
        apply typing_inversion_snd in Hts. destruct Hts as [S4 [S5 [Hp HsS5]]].
        eapply typing_inv_var in Hp; [| reflexivity].
        apply sub_inversion_Prod2 in Hp. destruct Hp as [_ HsT'].
        assert (HsT : T <: <{ T2 -> A }>)
          by (apply S_Trans with S5; assumption).
        clear S4 S5 HsS5 HsT'. 

        apply sub_inversion_arrow in HsT. destruct HsT as [U1 [U2 [E [_ Hs2]]]].
        subst T.
        apply sub_inversion_Base in Hs2. subst U2.
        apply sub_inversion_arrow2 in HsAS3. destruct HsAS3 as [HsU1 _].
        apply sub_inversion_Base in HsU1. subst U1.
        reflexivity.
      - intros E. subst. eapply T_App.
        + apply T_Abs. eapply T_App.
          * apply T_Snd with A. apply T_Var. reflexivity.
          * eapply T_Fst. apply T_Var. reflexivity.
        + apply T_Prod.
          * apply T_Var. reflexivity. 
          * apply T_Abs. apply T_Var. reflexivity. }
  left. exists <{A->A}>. exists <{A->A}>.
  intros T. split.
  - intros [H1 H2].
    apply H. apply sub_inversion_arrow in H2. destruct H2 as [U1 [U2 [E [_ Hs2]]]].
    subst T.
    apply sub_inversion_Base in Hs2. subst U2.
    apply sub_inversion_arrow2 in H1. destruct H1 as [HsU1 _].
    apply sub_inversion_Base in HsU1. subst U1.
    reflexivity.
  - intros Ht. apply H in Ht. subst T. split; apply S_Refl.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (formal_small_large_4) *)
Theorem formal_small_large_4:
  smallest_largest
  (fun T =>
   exists S,
     empty |-- <{\p:A*T, (p.snd) (p.fst)}> \in S).
Proof.
  assert (H: forall T,
    (exists S, empty |-- <{\p:A*T, (p.snd) (p.fst)}> \in S) <->
    (exists U, T <: <{A->U}>)).
    { intros T. split.
      - intros [S H].
        apply typing_inversion_abs in H. destruct H as [S1 [_ Hts]].
        apply typing_inversion_app in Hts. destruct Hts as [S2 [Htf Hts]].

        apply typing_inversion_fst in Hts. destruct Hts as [S3 [S4 [Hp HsS1]]].
        eapply typing_inv_var in Hp; [| reflexivity].
        apply sub_inversion_Prod2 in Hp as [HsA' _].
        assert (HsA : A <: S2)
          by (apply S_Trans with S3; assumption).
        clear S3 S4 HsA' HsS1.

        apply typing_inversion_snd in Htf. destruct Htf as [S3 [S4 [Hp HsS4]]].
        eapply typing_inv_var in Hp; [| reflexivity].
        apply sub_inversion_Prod2 in Hp as [_ HsT'].
        assert (HsT : T <: <{ S2 -> S1 }>)
          by (apply S_Trans with S4; assumption).
        clear S3 S4 HsT' HsS4.

        apply sub_inversion_arrow in HsT. destruct HsT as [U1 [U2 [E [HsU1 HsU2]]]].
        subst T. exists S1.
        apply S_Arrow.
        + apply S_Trans with S2; assumption.
        + assumption.
      - intros [U HsT]. exists <{(A*T)->U}>.
        apply T_Abs. eapply T_App.
        + eapply T_Sub.
          * eapply T_Snd. apply T_Var. reflexivity.
          * apply HsT.
        + eapply T_Fst. apply T_Var. reflexivity. }
  right. right. left.
  setoid_rewrite H. clear H. split.
  - intros [Ts Ht].
    assert (exists U, <{ Top }> <: <{ A->U }>).
      { apply Ht. apply S_Top. }
    destruct H. apply sub_inversion_Top in H. discriminate H.
  - exists <{A->Top}>. intros T. split.
    + intros H. apply sub_inversion_arrow in H. destruct H as [U1 [U2 [E [HsA HsU2]]]].
      subst T. exists U2. apply S_Arrow.
      * apply HsA.
      * apply S_Refl.
    + intros [U Hs]. eapply S_Trans.
      * apply Hs.
      * apply S_Arrow; auto.
Qed.
(** [] *)

Definition smallest P :=
  TF (exists TS, forall T, TS <: T <-> P T).

(** **** Exercise: 3 stars, standard, optional (formal_smallest_1) *)
Theorem formal_smallest_1:
  smallest
  (fun T =>
   exists S t,
     empty |-- <{ (\x:T, x x) t }> \in S).
Proof.
  assert (H: forall T,
    (exists S t, empty |-- <{ (\x:T, x x) t }> \in S) <->
    (exists U S t, empty |-- t \in T /\ T <: U /\ T = <{U -> S}>)).
    { intros T. split.
      - intros [S [t H]].
        apply typing_inversion_app in H. destruct H as [T1 [Ha Htr]].
        apply typing_inversion_abs in Ha. destruct Ha as [S1 [HsTS Ht]].
        apply typing_inversion_app in Ht. destruct Ht as [S2 [Ht1 Ht2]].
        eapply typing_inv_var in Ht1; [| reflexivity].
        eapply typing_inv_var in Ht2; [| reflexivity].
        apply sub_inversion_arrow in Ht1. destruct Ht1 as [U1 [U2 [E [HsU1 HsU2]]]].
        subst T.
        exists U1. exists U2. exists t. split; [| split].
        + apply sub_inversion_arrow2 in HsTS. destruct HsTS as [HsT1 _].
          eapply T_Sub.
          * apply Htr.
          * apply HsT1.
        + apply S_Trans with S2; assumption.
        + reflexivity.
      - intros [U [S [t [Ht [HsT E]]]]]. subst T.
        exists S. exists t. eapply T_App.
        + apply T_Abs. eapply T_App.
          * apply T_Var. reflexivity.
          * eapply T_Sub.
              { apply T_Var. reflexivity. }
              { apply HsT. }
        + apply Ht. }
  right. intros [TS Ht].
  setoid_rewrite H in Ht. clear H.
  assert (E : exists U S t, empty |-- t \in TS /\ TS <: U /\ TS = <{ U-> S }>).
    { apply Ht. apply S_Refl. }
  destruct E as [U [S [t [HtTS [HsTS ETS]]]]]. subst TS.
  
  assert (Hu : Ty_Arrow U S <: <{Top->Unit}>).
    { apply Ht. exists Ty_Top. exists Ty_Unit. exists <{\x:Top, tm_unit}>.
      split; [| split].
      - apply T_Abs. apply T_Unit.
      - apply S_Top.
      - reflexivity. }
  assert (Hb : Ty_Arrow U S <: <{Top->Bool}>).
    { apply Ht. exists Ty_Top. exists Ty_Bool. exists <{\x:Top, true}>.
      split; [| split].
      - apply T_Abs. apply T_True.
      - apply S_Top.
      - reflexivity. }
  apply sub_inversion_arrow2 in Hu. destruct Hu as [_ Hu].
  apply sub_inversion_Unit in Hu. subst S.
  apply sub_inversion_arrow2 in Hb. destruct Hb as [_ Hb].
  apply sub_inversion_Bool in Hb.
  discriminate Hb.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (formal_smallest_2) *)
Theorem formal_smallest_2:
  smallest
  (fun T =>
   empty |-- <{(\x:Top, x) ((\z:A, z), (\z:B, z))}> \in T).
Proof.
  left. exists Ty_Top. intros T. split.
  - intros H. apply sub_inversion_Top in H. subst T.
    eapply T_App.
    + apply T_Abs. apply T_Var. reflexivity.
    + eapply T_Sub.
      * apply T_Prod; apply T_Abs; apply T_Var; reflexivity.
      * apply S_Top.
  - intros H.
    apply typing_inversion_app in H. destruct H as [T1 [Ht _]].
    apply abs_arrow in Ht. destruct Ht as [_ Ht].
    eapply typing_inv_var in Ht; [| reflexivity].
    apply Ht.
Qed.
(** [] *)

End FormalThoughtExercises.

End STLCSub.

(* 2024-01-03 15:04 *)
