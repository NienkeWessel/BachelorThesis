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
ae_num : forall s n, aeval s (anum n) (val n) (*n evaluates to n*)
| ae_var1 : forall s x v, aeval ((x,v)::s) (avar x) v
| ae_var2 : forall s x y v1 v2 , x <> y 
-> aeval s (avar x) v2 
-> aeval ((y,v1)::s) (avar x) v2
| (*e1 + e2 evaluates to n1 + n2 if e1->n1 and e2->n2*) 
ae_plus : forall s e1 e2 v1 v2 w1 w2, 
v1 = (val w1) -> v2 = (val w2) ->
aeval s e1 v1 -> aeval s e2 v2 ->
aeval s (aplus e1 e2) (val (w1 + w2))
| (*either e1 or e2 evaluates to nothing*) 
ae_plus_fail : forall s e1 e2 v1 v2, 
v1 = nondec \/ v2 = nondec \/ v1 = dec \/ v2 = dec ->
aeval s (aplus e1 e2) nondec
(*| (*Not encountered yet*)
ae_doesntmatter : forall e, aeval nil e nondec*)
.


(*When we want to update the state, we call this function*)
Inductive update : state -> string -> zext-> state -> Prop :=
| s_up1 : forall s x v v1, update ((x,v)::s) x v1 ((x,v1):: s)
| s_up2 : forall s s1 x y v v1, update s x v1 s1 ->
x <> y -> update ((y,v)::s) x v1 ((y,v)::s1).

(*Definition usedvars := list string.

Inductive findvars : usedvars -> aexpr -> usedvars -> Prop :=
| try1: forall l x, findvars l (avar x) (x::l) (*variables*)
| try2: forall l x y l1 l2, (findvars l x l1) -> (findvars l1 y l2) -> 
findvars l (aplus x y) l2(*addition*)
| try3: forall l i, findvars l (anum i) l(*integers*)
.
*)

Inductive updateE : state -> aexpr -> state -> Prop :=
| s_up3: forall s x s1, update s x nondec s1 -> updateE s (avar x) s1 (*variables*)
| s_up4: forall s x y s1 s2, (updateE s x s1) -> (updateE s1 y s2) -> 
updateE s (aplus x y) s2(*addition*)
| s_up5: forall s i, updateE s (anum i) s(*integers*)
.

(*The actual natural semantics rules*)
Inductive exec : state->instr->state->Prop :=
| exec_skip : forall s, exec s skip s (*skip rule*)
| exec_ass : forall s x e v s1 s2,
aeval s e v -> update s x v s1 -> updateE s1 e s2
-> aeval s (avar x) dec (*A[x]s = dec*)
-> not (aeval s e nondec)
-> exec s (assign x e) s2
(*assignment*)
| exec_let : forall s x s1 s2 s3 y i a, (*s is starting state*)
update s x dec s1 (*s[x |-> dec] = s1*)
-> exec s1 i s2 (*<S, s1> -> s2 = s'*)
-> aeval s (avar x) y (*y = s(x)*)
-> update s2 x y s3 (*s3 = s'[x |-> s(x)]*)
-> exec s (let_in a x i) s3(*let-statement*)
| exec_comp : forall s s1 s2 i1 i2,
exec s i1 s1 -> exec s1 i2 s2 
-> exec s (sequence i1 i2) s2 (*composition*). 


(*assign z (anum 5)*)
Lemma Thalf:
 forall z, exec ((z, dec)::nil) (assign z (anum 5)) ((z, val 5)::nil)
.
Proof.
intros z.
apply exec_ass with (s1 := ((z,val 5)::nil)) (v := (val 5)).
apply ae_num.
apply s_up1.
apply s_up5.
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
apply exec_let with (s1 := ((z, dec)::nil)) (s2 := ((z, (val 5))::nil)) (y := nondec).
apply s_up1.
apply exec_ass with (s1 := ((z, (val 5))::nil)) (v := (val 5)).
apply ae_num.
apply s_up1.
apply s_up5.
apply ae_var1.
unfold not.
admit.
apply ae_var1.
apply s_up1.
Qed.


Lemma eval_deterministic :
 forall s e n n1, aeval s e n -> aeval s e n1 -> n = n1
.
Proof.
admit.
Qed.

