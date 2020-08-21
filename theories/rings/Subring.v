From algebra Require Import Foundation.
From algebra.rings Require Ring RingHom.
From algebra Require Category.

Import Ring.Exports RingHom.Exports Category.Exports.
Open Scope ring_scope.

Set Primitive Projections.

Module Class.
  Record axioms (A : [Ring]) (I : A → Prop) :=
    Class
      {zero : I 0;
       one : I 1;
       neg : ∀ x, I (Ring.neg x);
       add : ∀ x y, I x → I y → I (x + y);
       mul : ∀ x y, I x → I y → I (x ⋅ y)}.
End Class.

Record type A := Pack {pred; class : Class.axioms A pred}.

Module PredCoercion.
  Coercion pred : type >-> Funclass.
End PredCoercion.
Import PredCoercion.

Section Operations.
  Context {A : [Ring]} {I : type A}.
  Definition zero := Class.zero _ _ (class _ I).
  Definition neg := Class.neg _ _ (class _ I).
  Definition add := Class.add _ _ (class _ I).
  Definition one := Class.one _ _ (class _ I).
  Definition mul := Class.mul _ _ (class _ I).
End Operations.

Definition ring {A} : type A → [Ring].
  move=> I.
  unshelve econstructor.
  - exact: ({x : A | I x}).
  - unshelve apply: Ring.make_class.
    + axiom "zero"; econstructor; apply: zero.
    + axiom "add" => x y.
      exists (sval x + sval y).
      by apply: add; expose_subset.
    + axiom "neg" => x.
      exists (Ring.neg (sval x)); apply: neg.
    + axiom "one"; econstructor; apply: one.
    + axiom "mul" => x y.
      exists (sval x ⋅ sval y).
      by apply: mul; expose_subset.
    + repeat split => *; move=> *; apply: eq_subset; simpl;
      try by autorewrite with ring.
      * apply: Ring.addC.
      * apply: Ring.mulC.
Defined.


Definition hom {A} (I : type A) : [Ring] (ring I) A.
  unshelve econstructor.
  - case; auto.
  - split; simpl; auto.
Defined.

Module Exports.
  Export PredCoercion.
End Exports.
