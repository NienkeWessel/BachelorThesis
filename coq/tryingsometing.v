Require Import ZArith List.

Variable string : Type.
Variable lifetime : Type.

Inductive zext : Type :=  (*This is Zext*)
nondec  (*To denote a variable has not been declarated*)
| dec  (*To denote a variable has been declarated*)
| val (_ : Z).

(*Arithmetic expressions: x | n | e1 + e2 *)
Inductive aexpr : Type := avar (s : string) | anum (n :Z) | aplus (a1 a2:aexpr).

(*Instruction set: x := e | S1;S2 | skip | a:let x:t in S *)
Inductive instr : Type :=
  assign (_ : string) (_ : aexpr) | sequence (_ _: instr)
 | skip | let_in (_ : lifetime) (_ : string) (_: instr).


(*The state is a list of pairs, where the first denotes a variable and the second a value*)
Definition state := list (string * zext).


(*Basically the definition of the fancy A*)
Inductive aeval : state -> aexpr -> zext -> Prop :=
ae_num : forall r n, aeval r (anum n) (val n) (*n evaluates to n*)
| ae_var1 : forall r x v, aeval ((x,v)::r) (avar x) v
| ae_var2 : forall r x y v v1 , x <> y -> aeval r (avar x) v1 ->
aeval ((y,v)::r) (avar x) v1
(*| (*e1 + e2 evaluates to n1 + n2 if e1->n1 and e2->n2*) 
ae_plus : forall r e1 e2 v1 v2,
aeval r e1 (val v1) -> aeval r e2 (val v2) ->
aeval r (aplus e1 e2) (v1 + v2)*).


(*When we want to update the state, we call this function*)
Inductive update : state -> string -> zext-> state -> Prop :=
| s_up1 : forall r x v v1, update ((x,v)::r) x v1 ((x,v1):: r)
| s_up2 : forall r r1 x y v v1, update r x v1 r1 ->
x <> y -> update ((y,v)::r) x v1 ((y,v)::r1).


(*The actual natural semantics rules*)
Inductive exec : state->instr->state->Prop :=
| SN1 : forall r, exec r skip r
| SN2 : forall r r1 x e v,
aeval r e v -> update r x v r1 -> exec r (assign x e) r1
| SN3 : forall r r1 r2 i1 i2,
exec r i1 r1 -> exec r1 i2 r2 ->
exec r (sequence i1 i2) r2.