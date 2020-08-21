From algebra Require Import Foundation.
From algebra.rings Require Ring RingHom.
From algebra.groups Require Subgroup.
From algebra Require Category.


Import Ring.Exports RingHom.Exports Subgroup.Exports Category.Exports.
Open Scope ring_scope.

Module Class.
  Record axioms {A : [Ring]} (I : Subgroup.type (Ring.additive_group A)) :=
    Class
      {mul : forall x y : A, I y → I (x ⋅ y)}.
End Class.

Record type A := Pack {subgroup; class : @Class.axioms A subgroup}.

Module Coercions.
  Export Subgroup.Exports.
  Coercion subgroup : type >-> Subgroup.type.
End Coercions.

Import Coercions.

Open Scope subgroup_scope.

Definition is_proper {A} (I : type A) : Prop :=
  ¬ ∀ x : A, I x.

Open Scope ring_scope.

Definition is_prime {A} (I : type A) : Prop :=
  is_proper I ∧ ∀ x y : A, I (x ⋅ y) → I x ∨ I y.

Definition is_maximal {A} (I : type A) : Prop :=
  is_proper I ∧
  ∀ J : type A, I ≤ J → I ≅ J ∨ Subgroup.is_total J.

Definition category (A : [Ring]) : Category.type.
  unshelve econstructor.
  - exact (type A).
  - move=> I J.
    exact (Subgroup.is_leq I J).
  - unshelve esplit; firstorder.
Defined.

Module Exports.
  Export Coercions.

  Notation "[Ideal: A ]" := (category A).
End Exports.
