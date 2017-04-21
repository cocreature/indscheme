Declare ML Module "indscheme".

Inductive Forall' {A : Type} (P : A -> Type) : list A -> Type :=
| Forall_nil' : Forall' P nil
| Forall_cons' : forall {x : A} {l : list A}, P x -> Forall' P l -> Forall' P (x :: l).
