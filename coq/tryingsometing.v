Require Import ZArith List.
Open Scope Z_scope.


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
| (*e1 + e2 evaluates to n1 + n2 if e1->n1 and e2->n2*) 
ae_plus : forall r e1 e2 v1 v2 w1 w2, 
v1 = (val w1) -> v2 = (val w2) ->
aeval r e1 v1 -> aeval r e2 v2 ->
aeval r (aplus e1 e2) (val (w1 + w2))
| (*either e1 or e2 evaluates to nothing*) 
ae_plus_fail : forall r e1 e2 v1 v2, 
v1 = nondec \/ v2 = nondec \/ v1 = dec \/ v2 = dec ->
aeval r (aplus e1 e2) nondec
(*| (*Not encountered yet*)
ae_doesntmatter : forall e, aeval nil e nondec*)
.


(*When we want to update the state, we call this function*)
Inductive update : state -> string -> zext-> state -> Prop :=
| s_up1 : forall r x v v1, update ((x,v)::r) x v1 ((x,v1):: r)
| s_up2 : forall r r1 x y v v1, update r x v1 r1 ->
x <> y -> update ((y,v)::r) x v1 ((y,v)::r1).

Definition usedvars := list string.

Inductive findvars : usedvars -> aexpr -> usedvars -> Prop :=
| try1: forall l x, findvars l (avar x) (x::l) (*variables*)
| try2: forall l x y l1 l2, (findvars l x l1) -> (findvars l1 y l2) -> 
findvars l (aplus x y) l2(*addition*)
| try3: forall l i, findvars l (anum i) l(*integers*)
.


Inductive updateforev : state -> aexpr -> state -> Prop :=
| try11: forall l x l1, update l x nondec l1 -> updateforev l (avar x) l1 (*variables*)
| try21: forall l x y l1 l2, (updateforev l x l1) -> (updateforev l1 y l2) -> 
updateforev l (aplus x y) l2(*addition*)
| try31: forall l i, updateforev l (anum i) l(*integers*)
.

(*The actual natural semantics rules*)
Inductive exec : state->instr->state->Prop :=
| SN1 : forall r, exec r skip r (*skip rule*)
| SN2 : forall r r1 x e v r2,
aeval r e v -> update r x v r1 -> updateforev r1 e r2
-> aeval r (avar x) dec (*A[x]s = dec*)
-> not (aeval r e nondec)
-> exec r (assign x e) r2
(*assignment*)
| SN4 : forall r x r1 r2 r3 y i a, (*s = r*)
update r x dec r1 (*s[x |-> dec] = r1*)
-> exec r1 i r2 (*<S, r1> -> r2 = s'*)
-> aeval r (avar x) y (*r(x) = y = s(x)*)
-> update r2 x y r3 (*r3 = s'[x |-> s(x)]*)
-> exec r (let_in a x i) r3(*let-statement*)
| SN3 : forall r r1 r2 i1 i2,
exec r i1 r1 -> exec r1 i2 r2 
-> exec r (sequence i1 i2) r2 (*composition*). 


(*assign z (anum 5)*)
Lemma Thalf:
 forall z, exec ((z, dec)::nil) (assign z (anum 5)) ((z, val 5)::nil)
.
Proof.
intros z.
apply SN2 with (r1 := ((z,val 5)::nil)) (v := (val 5)).
apply ae_num.
apply s_up1.
apply try31.
apply ae_var1.
admit. (*I get stuck here!*)
Qed.

(* let_in a (avar "z") (assign (avar "z") 5)
let z in
z := 5;
*)

Lemma T1:
 forall z a, exec ((z, nondec)::nil) (let_in a z (assign z (anum 5))) ((z, nondec)::nil)
.
Proof.
intros z. 
intros a.
apply SN4 with (r1 := ((z, dec)::nil)) (r2 := ((z, (val 5))::nil)) (y := nondec).
apply s_up1.
apply SN2 with (r1 := ((z, (val 5))::nil)) (v := (val 5)).
apply ae_num.
apply s_up1.
apply try31.
apply ae_var1.
unfold not.
admit.
apply ae_var1.
apply s_up1.
Qed.


