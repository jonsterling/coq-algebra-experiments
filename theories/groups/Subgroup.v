From algebra Require Import Foundation.
From algebra.groups Require AbelianGroup GroupHom.
From algebra Require Category.

Module Group := AbelianGroup.
Import Group.Exports Category.Exports GroupHom.Exports.

Declare Scope subgroup_scope.
Delimit Scope group_scope with grp.
Delimit Scope subgroup_scope with subgroup.

Set Primitive Projections.

Module Class.
  Record axioms (A : [Group]) (I : A → Prop) :=
    Class
      {zero : I 0%grp;
       neg : ∀ x : A, I x → I (Group.neg x);
       add : ∀ x y : A, I x → I y → I (x + y)%grp}.
End Class.

Record type A := Pack {pred; class : Class.axioms A pred}.

Module PredCoercion.
  Coercion pred : type >-> Funclass.
End PredCoercion.
Import PredCoercion.

Section Operations.
  Context {A : [Group]} {I : type A}.
  Definition zero := Class.zero _ _ (class _ I).
  Definition add := Class.add _ _ (class _ I).
  Definition neg := Class.neg _ _ (class _ I).
End Operations.

Definition is_leq {A} (I J : type A) : Prop :=
  ∀ x : A, I x → J x.

Definition is_equiv {A} (I J : type A) : Prop :=
  is_leq I J ∧ is_leq J I.

Definition is_total {A} (I : type A) : Prop :=
  ∀ x : A, I x.

Lemma extensionality {A} : ∀ I J : type A, is_equiv I J → I = J.
Proof.
  move=> [I clI] [J clJ] [IJ JI].
  suff Q : I = J.
  * induction Q.
    suff Q : clI = clJ; auto.
    by rewrite Q.
  * ext => ?; ext; split.
    - apply: IJ.
    - apply: JI.
Qed.

Definition group {A} : type A → [Group].
  move=> ϕ.
  unshelve econstructor.
  - exact: ({x : A | ϕ x}).
  - Group.make_class.
    + axiom "zero".
      econstructor; apply: zero.
    + axiom "add".
      move=> x y.
      exists (sval x + sval y : A)%grp.
      apply: add; by expose_subset.
    + axiom "neg".
      move=> x.
      exists (Group.neg (sval x)).
      apply: neg; by expose_subset.
    + abstract
      (split; move=> *; apply: eq_subset; simpl;
       by [autorewrite with group] + by [rewrite Group.addC]).
Qed.

Module Notation.
  Infix "≅" := is_equiv (at level 70) : subgroup_scope.
  Infix "≤" := is_leq (at level 70) : subgroup_scope.
End Notation.

Definition category : [Group] → Category.type.
  move=> A.
  exists (type A) is_leq.
  unshelve eapply Category.make_class;
  by [firstorder | firstorder | abstract firstorder].
Defined.

Module GroupCoercion.
  Local Definition group_coercion {A} : type A → Group.type := group.
  Coercion group_coercion : type >-> Group.type.
End GroupCoercion.

Module Exports.
  Export PredCoercion.
  Export GroupCoercion.
  Export Notation.
End Exports.
