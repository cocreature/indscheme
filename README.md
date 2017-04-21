# Coq tactic to automatically prove induction schemes when the recursion is nested inside a list

## Background
For the inductively defined

```coq
Inductive term :=
| tnat : nat -> term
| tlist : list term -> term.
```

Coq will generate an induction scheme of type
```coq
forall (P : term -> Prop),
  (forall n : nat, P (tnat n)) ->
  (forall l : list term, P (tlist l)) ->
  forall t : term, P t.
```

However, this is often too weak and you need an induction scheme that also provides `Forall P l`.

This library provides an `indscheme` tactic which can be used to automatically prove induction schemes similar to that, e.g.,

```coq
Lemma term_ind' :
  forall (P : term -> Prop),
    (forall n : nat, P (tnat n)) ->
    (forall l : list term, Forall' P l -> P (tlist l)) ->
    forall t : term, P t.
Proof.
  indscheme.
Qed.
```

## Status

The tatic works for simple cases as the one shown above but is very
fragile and only supports generating induction schemes of
unparametrized types. It also expects to find `Forall'`, a variant of
`Forall` situated in `Type`, in a `Util` module.

```coq
Inductive Forall' {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil' : Forall' P nil
| Forall_cons' : forall {x : A} {l : list A}, P x -> Forall' P l -> Forall' P (x :: l).
```
