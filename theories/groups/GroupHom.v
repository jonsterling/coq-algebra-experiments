From algebra Require Import Foundation.
From algebra Require Category.
From algebra.groups Require Import AbelianGroup.

Module Group := AbelianGroup.
Import Group.Exports.

Open Scope group_scope.

Module Class.
  Record axioms {A B : Group.type} (f : A → B) :=
    {zero : f 0 = 0;
     add : ∀ x y, f (x + y) = f x + f y;
     neg : ∀ x, f (Group.neg x) = Group.neg (f x)}.
End Class.

Record type (A B : Group.type) := Pack {hom; class : @Class.axioms A B hom}.

Module FunCoercion.
  Coercion hom : type >-> Funclass.
End FunCoercion.

Lemma extensionality {A B} : ∀ f g : type A B, hom _ _ f = hom _ _ g → f = g.
Proof.
  move=> [f hf] [g hg] //= α.
  induction α.
  replace hf with hg; auto.
Qed.

Instance hom_ext {A B} : ExtLaw (type A B) _ :=
  {ext_law := extensionality}.

Section Operations.
  Context {A B} {f : type A B}.
  Definition zero := Class.zero _ (class _ _ f).
  Definition add := Class.add _ (class _ _ f).
  Definition neg := Class.neg _ (class _ _ f).
End Operations.

Hint Rewrite @zero @add @neg : group.

Ltac make := unshelve apply: Pack.

Import FunCoercion.

Definition category : Category.type.
  exists Group.type type.
  unshelve apply: Category.make_class.
  - axiom "idn" => A; make.
    + auto.
    + abstract (split; auto).
  - axiom "seq" => A B C f g; make.
    + move=> x.
      exact: (g (f x)).
    + abstract (split => *; by autorewrite with group).
  - abstract (split => *; by ext).
Defined.

Module Exports.
  Export FunCoercion.

  Notation "[Group]" := category : type_scope.
End Exports.
