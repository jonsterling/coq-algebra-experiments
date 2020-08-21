From algebra Require Import Foundation.
From algebra.rings Require Ring.
From algebra Require Category.

Import Ring.Exports Category.Exports.
Open Scope ring_scope.

Module Class.
  Record axioms {A B : Ring.type} (f : A → B) : Prop :=
    {zero : f 0 = 0;
     one : f 1 = 1;
     neg : forall x, f (Ring.neg x) = Ring.neg (f x);
     mul : ∀ x y, f (x ⋅ y) = f x ⋅ f y;
     add : ∀ x y, f (x + y) = f x + f y}.
End Class.

Record type (A B : Ring.type) := Pack {hom; class : @Class.axioms A B hom}.

Module FunCoercion.
  Coercion hom : type >-> Funclass.
End FunCoercion.

Import FunCoercion.

Section Operations.
  Context {A B : Ring.type} {f : type A B}.
  Definition zero := Class.zero _ (class _ _ f).
  Definition one := Class.one _ (class _ _ f).
  Definition mul := Class.mul _ (class _ _ f).
  Definition add := Class.add _ (class _ _ f).
  Definition neg := Class.neg _ (class _ _ f).
End Operations.

Hint Rewrite @zero @one @neg @mul @add : ring.

Lemma extensionality {A B} : ∀ f g : type A B, hom _ _ f = hom _ _ g → f = g.
Proof.
  move=> [f hf] [g hg] //= α.
  induction α.
  replace hf with hg; auto.
Qed.

Instance ring_hom_ext {A B} : ExtLaw (type A B) _ :=
  {ext_law := extensionality}.

Definition idn {A} : type A A.
  unshelve econstructor.
  - exact (fun x => x).
  - abstract (split; auto).
Defined.

Definition seq {A B C} : type A B → type B C → type A C.
  move=> AB BC.
  unshelve econstructor.
  - move=> a.
    apply: BC.
    apply: AB.
    exact: a.
  - abstract (constructor => *; by autorewrite with ring).
Defined.

Definition category : Category.type.
  exists Ring.type type.
  unshelve apply: Category.make_class.
  - axiom "idn".
    apply: @idn.
  - axiom "seq".
    apply: @seq.
  - abstract (repeat split => *; by ext).
Defined.

Module Exports.
  Export FunCoercion.
  Notation "[Ring]" := category.
End Exports.
