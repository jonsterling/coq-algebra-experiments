Require Export Unicode.Utf8.
Require Export ssreflect ssrfun.
Require Import Program.Equality.
Require Import Logic.ProofIrrelevance.
Require Import Logic.PropExtensionality.
Require Import Logic.FunctionalExtensionality.
Require Export Strings.String.

Close Scope nat_scope.
Set Primitive Projections.
Set Program Mode.

Hint Immediate proof_irrelevance : core.

From Coq.Classes Require Import RelationClasses.

Record EqRel A :=
  {EqRel_rel :> A → A → Prop;
   EqRel_equiv : Equivalence EqRel_rel}.

Existing Instances EqRel_equiv.

Lemma eq_subset {A : Type} {P : A → Prop} : ∀ (x y : {x : A | P x}), (x : A) = (y : A) → x = y.
Proof.
  move=> [x hx] [y hy] //= Q.
  dependent induction Q.
  have Q: hx = hy; auto.
  by rewrite Q.
Qed.

(* This is a nice tactic to add to the context whatever follows from the subset assumptions. *)
Ltac expose_subset :=
  repeat
    match goal with
    | [H : {x : ?A | @?P x} |- _] =>
      match goal with
      | [I : P (sval H) |- _] => idtac
      | _ => have ? : P (sval H); first by case: H => [? ?]; auto
      end
    end.

(* A useful tactic for incrementally rewriting an equation in a dependent record. Q is an equation of primitive tuples, and x0 and x1 are parallel components of the record in the goal that are equal as a consequence of Q. *)
Ltac proj_eq Q x0 x1 :=
  let H := fresh in
  suff H : x0 = x1;
  [dependent induction H | by dependent induction Q].


Record Case (name : string) (tp : Type) := {case_val : tp}.
Arguments case_val [_] [_].

Notation "⟨ name ∷ tp ⟩" := (Case name tp).
Notation "! f" := (case_val f) (at level 10).

Definition make_case (name : string) {tp} : tp → Case name tp.
  move=> x.
  constructor.
  exact: x.
Defined.

Open Scope string_scope.

Ltac axiom name :=
  refine (make_case name _); simpl.

Class ExtLaw (A : Type) (B : A → A → Type) :=
  {ext_law : ∀ x y : A, B x y → x = y}.

Instance prop_ext : ExtLaw Prop _ :=
  {ext_law := propositional_extensionality}.

Instance fun_ext {A B : Type} : ExtLaw (A → B) (λ f g, ∀ x, f x = g x) :=
  {ext_law := functional_extensionality}.

Instance dep_fun_ext {A : Type} {B : A → Type} : ExtLaw (∀ x, B x) _ :=
  {ext_law := functional_extensionality_dep}.

Instance subset_ext {A : Type} {P : A → Prop} : ExtLaw {x : A | P x} _ :=
  {ext_law := eq_subset}.

Instance sigma_ext {A : Type} {B : A → Type}
  : ExtLaw {x : A & B x} (λ p q, {α : projT1 p = projT1 q | eq_rect (projT1 p) _ (projT2 p) (projT1 q) α = projT2 q}).
Obligation 1.
Proof. by apply: eq_sigT. Qed.

Ltac ext :=
  apply: ext_law;
  match goal with
  | [|- {x : ?A | @?B x}] => unshelve econstructor
  | _ => idtac
  end;
  cbn.
