From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Coq.Program.Equality.

Require Import Arith_base.
Require Import Vectors.Fin.
Require Import Vectors.VectorDef.
Require Import Bool.

Class Lex (A : Set) (FCross : A -> A -> A) (CP : A -> A -> Prop) : Prop := {
    transformable : forall (x : A), {P | ~ CP x (P x)};
    anti_identity : forall (x y : A), ~ CP x y -> ~ CP x (FCross x y);
    convergent_equality : forall (x y : A), x = y -> CP x y;
    crossover_identity : forall (y : A), {x | ~ (CP x y) -> CP (FCross x y) y}
}.

Class Agent {A : Set} {f : A -> A -> A} {f'} (H : Lex f f') (T : Set) := {
 memory : T -> A
}.

Section Env.
Variables X B A : Set.
Variable f : X -> X -> X.
Variable f' : X -> X -> bool.
Variable K : Lex f f'.
Variable H : Set -> Set.
Variable C : H A -> B -> Prop.
Variable point : forall x y , C x y -> A.
Variable Perception : forall {x y : B} (k : H A), C k x -> C k y -> Prop.
Variable Action : forall {x y : B} (k : H A) (x' : C k x) (y' : C k y), H A -> Prop.
Variable AG : Agent K A.

Record Functions : Type := F' {
   faction : H A -> H A;
   flang : H A -> H A
}.

Record Interation x y k (P : Functions) : Prop := I' {
    consistency_action : forall (x' : C ((flang P) k) x) (y' : C ((flang P) k) y) (H' : Perception x' y'),
                Action x' y' ((faction P) ((flang P)k));

    knowlegde : forall (x' : C k x) (y' : C k y) (a : C ((flang P) k) x)  (H' : Perception x' y'),
         memory (point a)  = (f (memory (point x')) (memory ((point y'))))
  
}.

Class Environment (k : H A) (H' : Functions) : Prop := {
  inhabited : forall (x : H A), {b | C x b};
  active : forall (k : H A), {y : (B * B) | {c : (C k (fst y) * C k (snd y)) | Perception (fst c) (snd c)}};
  iterate : forall {x y : B}  (x' : C k x) (y' : C k y), Interation x y k H'; 
  
}.

Notation "f ∘ g" := (fun x => f (g x)) (at level 80, right associativity).

Class State {f' g'} {k} := {
  inductive_environment : 
    Environment k (F' f' g') /\ (forall k (x :  Environment k (F' f' g')), Environment ((g' ∘ f') k) (F' f' g'));
}.


End Env.

Inductive binary := |zero : binary |one : binary.

Inductive lex n := 
|lex' : t binary (S n) -> lex n.

Fixpoint invert_binary {y} (x : t binary y) : t binary y.
induction x.
refine (nil _).
destruct h.
refine (cons _ one _ (invert_binary _ x)).
refine (cons _ zero _ (invert_binary _ x)).
Defined.

Theorem _not_conservation: 
  forall n (x : lex n), {P : forall {n} {h : lex n}, lex n | x <> P n x}.
move => x'.
pose (fun y (x : lex y) => 
  match x with
    |@lex' _ v  => @lex' y (invert_binary v)
  end).
intros; exists l.
destruct x; simpl; injection; intros.
clear H.
move : H0.
elim/@caseS' : t.
intros.
destruct h.
inversion H0.
inversion H0.
Qed.


Export VectorNotations.

Definition case1 {A} (P : t A 1 -> Type)
  (H : forall h, @P [h]) (v: t A 1) : P v :=
match v with
  |h :: t => match t with
    |nil _ => H h
  end
  |_ => fun devil => False_ind (@IDProp) devil 
end.

Definition case_2nat (P : nat -> nat -> Type) 
  (H : P 0 0) (H' : forall y, P 0 (S y)) (H1 : forall x, P (S x) 0) 
     (H2 : forall x y, P (S x) (S y))
   : forall x y, P x y.
move => x y.
destruct x.
destruct y.
exact H.
refine (H' y).
destruct y.
refine (H1 x).
refine (H2 x y).
Defined.

Definition case_2t {A} (P : forall n, t A (S n) -> t A (S n) -> Type) 
    (H' : forall n a b (t t' : t A n), P _ (a :: t) (b :: t'))
   : forall n (x y : t A (S n)), P _ x y.
move => n x.
refine (match x in (t _ (S n)) return (forall (y : (t A (S n))), P n x y) with 
  |@cons _ k q c => _
 end).
elim/@caseS'.
intros.
refine (H' _ k h _ _).
Defined.

Definition rect_SS' {A} (P : forall n, t A (S n) -> Type)
  (H : forall n h a (t : t A (S n)), P _ t -> P _ (a :: h :: t)) (H' : forall h, @P 0 [h]) (H1' : forall h v, @P 1 [h; v]) : forall n (x : t A (S n)), P _ x. 
  
  refine (fix fix_S n (v : t A (S n)) {struct v} : P n v := _).
  refine (match v as c in (t _ (S n)) return P n c with
  |cons _ h 0 v' => match v' with
      |@nil _ => _
    end
  | cons _ h 1 v1 => _
  | cons _ a (S (S n')) v' => _
  | _ => fun devil => False_rect (@IDProp) devil
  end).

intros.
refine (H' h).
intros.
refine (match v1 with
  |@cons _ k 0 q => match q in (t _ 0) with
    |@nil _ => _ 
  end
 end).

refine (H1' h k).
refine (match v' as c in (t _ (S (S n'))) return P (S (S n')) (a :: c) with
  |@cons _ k n q => _
 end).

destruct n.
exact idProp.
refine (H _ k a _ (fix_S _ q)).

Defined.


Definition rect_2S {A B} (P:forall {n}, t A (S n) -> t B (S n) -> Type)
  (bas : forall x y, P [x] [y]) (rect : forall {n} (v1 : t A (S n)) (v2 : t B (S n)), P v1 v2 ->
    forall a b, P (a :: v1) (b :: v2)) : 
     forall {n} (v1 : t A (S n)) (v2 : t B (S n)), P v1 v2.

  refine (fix rect2_fix {n} (v1 : t A (S n)) : forall v2 : t B (S n), P _ v1 v2 :=
  match v1 in t _ (S n) with
  | [] => idProp
  | @cons _ h1 (S n') t1 => fun v2 =>
    caseS' v2 (fun v2' => P _ (h1::t1) v2') (fun h2 t2 => rect _ _ _ (rect2_fix t1 t2) h1 h2)
  |cons _ a 0 x' => fun (v2 : t B 1) => _ 
 end).

elim/@case0 : x'.
refine (match v2 with
  |cons _ b 0 y' => match y' with
      |nil _ => _
      |_ => _
    end
  end).

elim/@case0 : y'.
refine (bas a b).
exact idProp.
Defined.

Fixpoint cross_binary_vector {n} (x : t binary (S n)) (y : t binary (S n)) : t binary (S n).
elim/@rect_2S  : x/y.
intros.
refine (cons _ y _ (nil _)).
intros.

refine (match (a, b) with
  |(one, one) => (cons _ a _ (cross_binary_vector _ v1 v2))
  |(zero, zero) => (cons _ a _ (cross_binary_vector _ v1 v2))
  |(x', y') => (cons _ b _ v1)
 end).

Defined.


Definition cross_lex {n} (x : lex n) (y : lex n) : lex n.
constructor.
destruct x.
destruct y.
refine (cross_binary_vector t t0).
Defined.


Definition b_rect (P : binary -> binary -> Type) (H : P one one) (H' : P zero zero) (H1' : P one zero) (H2' : P zero one) (x y : binary) : P x y. 
intros.
destruct x.
destruct y.
move => //=.
move => //=.
destruct y.
move => //=.
move => //=.
Defined.

Theorem crossover_binary : 
  forall   n
           (x : t binary (S n))
           (y : t binary (S n)),
           x <> y ->
           x <> cross_binary_vector x y.

  have : forall t t0, lex' t <> lex' t0 -> t <> t0.
  intros.
  cbv in H.
  cbv.
  move => h'.
    have : lex' t = lex' t0.
    congruence.
  tauto.

  have : forall n h x y, cons _ n h x <> cons _ n h y -> x <> y.
   intros.
   move => H'.
   congruence.
  move => H'.

  have : forall h n x y, x <> y -> cons _ n h x <> cons _ n h y.
   intros. 
   move => H2'.
   pose (fun a n (x : t a (S n)) => match x in (t _ (S n)) with
     |@cons _ _ _ x => x
     end).
   pose (@f_equal (t T (S h)) (t T h) (@y0 _ _) _ _ H2').
   simpl in e.
   tauto.
 move => K.

intros.
move : H; elim/@rect_2S : y/x0.
intros; unfold cross_binary_vector; simpl in *.
auto.
intros; move : H0 H; elim/@b_rect : a/b.
intros.
unfold cross_binary_vector; simpl; fold @cross_binary_vector.
apply H' in H0; apply H in H0.
auto.
intros.
unfold cross_binary_vector; simpl; fold @cross_binary_vector.
apply H' in H0; apply H in H0;apply : K.
trivial.
intros.
unfold cross_binary_vector; simpl; fold @cross_binary_vector.
move => H2'.
inversion H2'.
intros.
unfold cross_binary_vector; simpl; fold @cross_binary_vector.
move => H2';inversion H2'.
Qed.

Definition eq_vector_binary : forall (n : nat), t binary (S n) -> t binary (S n) -> bool.
  pose (fun (x y : binary) => match (x, y) with
  |(one, one) => true
  |(zero, zero) => true
  |(x, y) => false
  end).
  
  refine (fix fix_S n (t t0 : t binary (S n)) {struct t} := _).
  elim/@rect_2S : t/t0.
  intros;refine (b x y).
  intros;refine ((b a b0) && (fix_S _ v1 v2)).
Defined.

Definition lex_binary : forall (n : nat), lex n -> lex n -> bool.
intros.
destruct H.
destruct H0.
refine (eq_vector_binary t t0).
Defined.

Theorem lex_eq : forall n (v y : lex n), lex_binary v y = true -> v = y.
intros.
destruct v. destruct y.
move : H.
elim/@rect_2S : t/t0.
move => x y.
elim/b_rect : x/y.
trivial.
trivial.
simpl in *; congruence.
simpl in *; congruence.
intros.
move : H0.
elim/b_rect : a/b.
 - intros; simpl in *; apply H in H0; congruence.
 - intros; simpl in *; apply H in H0; congruence.
 - intros; simpl in *; congruence.
 - intros; simpl in *; congruence.
Qed.

Definition lex_prop : forall (n : nat), lex n -> lex n -> Prop.
intros.
exact (lex_binary H H0 = true).
Defined.

Fixpoint imperfect_binary_cpy {n} (x : t binary (S n)) : t binary (S n).
elim/@rectS : x.
case.
exact (cons _ one _ (nil _)).
exact (cons _ zero _ (nil _)).
intros.
refine (cons _ a _ (imperfect_binary_cpy _ v)).
Defined.

Theorem unique_binary_object_convergent_complement {n} (y : t binary (S n)) :
   {x | x <> y -> cross_binary_vector x y = y}.
exists (imperfect_binary_cpy y).
move : y; elim/@rectS.
case => //=.
case => //= H' V hi h.
have : imperfect_binary_cpy V <> V.
congruence.
move => H.
have : cross_binary_vector (imperfect_binary_cpy V) V = V.
apply : hi H; move => H3.
congruence.
have : imperfect_binary_cpy V <> V.
congruence.
move => H.
have : cross_binary_vector (imperfect_binary_cpy V) V = V.
apply : hi H; move => H3.
congruence.
Qed.


Theorem neg_of_convergent_lex : forall n (x : lex n) y, x <> y -> lex_binary x y = false.

  have : forall x y, lex_binary x y = false -> ~ lex_binary x y = true.
  move => n0 x0 y0.
  destruct (lex_binary x0 y0).
  move => h2.
  inversion h2.
  move => H2 H3.
  inversion H3.

intros.
destruct x0.
destruct y.
move : H.
elim/@rect_2S : t/t0.
move => x0 y.
elim/@b_rect : x0/y.
intros.
destruct H.
auto.
intros.
destruct H.
auto.
auto.
intros.
done.
intros.
move : H H0.
pose (fun n (x : t binary (S n)) => match x in t _ (S n) with
  |a :: b => b
 end).
pose (fun n (x : t binary (S n)) => match x in t _ (S n) with
  |a :: b => a
 end).
  have : forall x v v', lex' (x :: v) <> lex' (x :: v') -> lex' v <> lex' v'.
  case => n1. elim/@caseS'.
  move => h n2; elim/@caseS'.
  move => h0; elim/@case0.
  elim/@case0 : n2.
  intros; move => H2.
  injection H2; move => n2; subst.
  by contradiction H.
  intros.
  move => H2'.
     have : v = v'.
     congruence.
  move => H3; rewrite H3 in H.
  by contradiction H.
move => H2'.
elim/@b_rect : a/b.
intros; simpl in *; apply H2' in H0.
tauto.
intros; apply H2' in H0; tauto.
intros; trivial.
intros; trivial.
Qed.

Theorem lex_binary_eqv : forall {n} (m : lex n), lex_binary m m = true.
  intros.
  destruct m.
  elim/@rectS : t.
  by destruct a.
  by elim.  
Qed.

Theorem neg_of_convergent_lex' : forall n (x : lex n) y, lex_binary x y = false -> x <> y.

  have : forall x y, lex_binary x y = false -> ~ lex_binary x y = true.
  move => n0 x0 y0.
  destruct (lex_binary x0 y0).
  move => h2.
  inversion h2.
  move => H2 H3.
  inversion H3.

intros.
apply x in H.
move => H2.
destruct x0.
destruct y.
move : H2 H.
elim/@rect_2S : t/t0.
move => x0 y.
elim/@b_rect : x0/y.
auto.
auto.
intros; inversion H2.
intros; inversion H2.
move => n0 v1 v2 H a b.

pose (fun n (x : t binary (S n)) => match x in t _ (S n) with
  |a :: b => b
 end).

elim/@b_rect : a/b.
intros.
simpl in *.
  have : one :: v1 = one :: v2.
  congruence.
move => e'.
apply (@f_equal _ _ (@y (S n0))) in e'; simpl in e'.
  have : lex' v1 = lex' v2.
  congruence.
auto.
intros.
simpl in *.
  have : zero :: v1 = zero :: v2.
  congruence.
move => e'.
apply (@f_equal _ _ (@y (S n0))) in e'; simpl in e'.
  have : lex' v1 = lex' v2.
  congruence.
auto.
intros.
inversion H2.
intros.
inversion H2.
Qed.

Instance binary_lex : forall x, Lex (@cross_lex x) (@lex_prop x).
 {
 
  constructor.

  (* The proof of lex transform *)
  intros.
  pose (_not_conservation x0).
  destruct s.
  exists (x1 x).
  apply not_true_iff_false.
  apply (neg_of_convergent_lex).
  trivial.
  
  (*Anti-identity proof of crossover function *)
  intros.
  destruct x0.
  destruct y.
  unfold lex_prop in *.
  apply not_true_iff_false.
  
  apply not_true_is_false in H.
  apply neg_of_convergent_lex.
  apply neg_of_convergent_lex' in H.
  move => H2.
  unfold cross_lex in H2.
    have : t <> t0.
    congruence.
  move => H2'.
  pose (@crossover_binary _ _ _ H2').
  congruence.

  (*Convergence implies to definitional equality *)
  intros.
  unfold lex_prop.
  rewrite H.
  clear H x0.
  apply : lex_binary_eqv.

  (*Existence of Convergence aproximation from x to y*)
  intros.
  destruct y.
  destruct (unique_binary_object_convergent_complement t).
  exists (lex' x0).
  move => H'.
  unfold lex_prop in *.
  
  apply not_true_is_false  in H'.
    have : x0 <> t.
    set (neg_of_convergent_lex' H'); congruence.
  move => H.
  apply e in H.
  unfold cross_lex.
  rewrite H.
  apply : lex_binary_eqv.
}
Defined.

Inductive SAgent n :=
   T' : lex n -> SAgent n.

Definition agent_lex {n} (x : SAgent n) := 
  match x with
    |@T' _ l => l
 end.

Fixpoint len {a} {n} (x : t a n) :=
  match x with
    |_ :: y => (len y) + 1
    |[] => 0
  end.


(*The class Agent is just a proof that there is a depedent product of a lex
  and one construction and the depedent product carry a memory that map the construction
   with one lexical memory *)

Instance SAgent' : forall x, Agent (binary_lex x) (SAgent x). {
  constructor.
  refine (@agent_lex x).
}
Defined.

Require Import Coq.Init.Specif.

Definition get_agent {n} {l} (ls : t (SAgent n) l) (y : nat) (H : y < l) : SAgent n := nth_order ls H.

Definition boundness {n} {l} (ls : t (SAgent n) l) (y : nat) : Prop := y < l.

Definition view {l} {n} {y} {y'} (v : t (SAgent n) (S l)) (H : y < (S l)) (H' : y' < (S l)) := 
  (y =? 0) && (y' =? l) = true.

Definition match_lex {l} {n} (v : t (SAgent n) (S l)) : t (SAgent n) (S l).

  have : 0 < S l /\ l < S l.
  auto with arith.
move => h.
destruct h.
set f' := v[@of_nat_lt H].
set s' := v[@of_nat_lt H0].

refine (replace (replace v (of_nat_lt H0) (T' (cross_lex (memory s') (memory f')))) 
  (of_nat_lt H) (T' (cross_lex (memory f') (memory s')))).
Defined.

Definition action_prop {l} {n} {y} {y'} (v : t (SAgent n) (S l)) (H : y < S l) (H' : y' < S l) : t (SAgent n) (S l) -> Prop.
move => v'.
refine (get_agent v H = get_agent v' H').
Defined.

Definition tail := (fun a n (v : t a (S n))  => match v in (t _ (S n)) with
   |@cons _ _ _ v' => v'
   |@nil _ => idProp
 end).

Theorem head_get : forall a n (x : t a (S n)) (H : 0 < (S n)), hd x = nth x (Fin.of_nat_lt H).
intros.
move : H.
by elim/@caseS : x.
Qed.

Theorem last_tail : forall a n (x : t a (S n)) (H : n < (S n)), last x = nth x (Fin.of_nat_lt H).
intros.
move : H.
elim/@rectS : x.
intros.
by simpl.
intros.
simpl in *.
generalize (lt_S_n n0 (S n0) H0).
move => t.
pose (H t).
trivial.
Qed.

Theorem shift_hd_get' : forall A n (x : t A (S n)) (H : n < (S n)) (a : A), (shiftin a x)[@FS (Fin.of_nat_lt H)] = a.
intros.
move : H.
elim/@rect_SS' : x.
intros.
simpl in *.
by set (H (lt_S_n n0 (S n0)
                       (lt_S_n (S n0) 
                          (S (S n0)) H0))).
trivial.
intros.
simpl in *.
trivial.
Defined.

Theorem of_nat_lt_c : forall x y (v : x < y) (v' : x < y), of_nat_lt v = of_nat_lt v'.
move => x y.
elim/@nat_double_ind : x/y.
intros.
destruct n.
inversion v.
simpl in *; trivial.
intros;inversion v.
intros.
set (H (lt_S_n n m v) (lt_S_n n m v')); simpl in *; rewrite e.
reflexivity.
Qed.

Definition shift {l} {n} (v : t (SAgent n) (S l)) : t (SAgent n) (S l).
destruct l.
exact v.
destruct l.
refine (cons _ (hd (tail v)) _ (cons _ (hd v) _ (nil _))).
refine (shiftin (hd v) (tail v)).
Defined.


Theorem inj : forall n l (x y : t (SAgent n) (S l)), shift x = shift y -> x = y.
  have : forall a b v1 v2, shiftin a v1 = shiftin b v2 -> v1 = v2 /\ a = b.
  intros.
  move : H.
  elim/@rect2 : v1/v2.
  constructor; trivial.
  simpl in H; congruence.
  intros.
  simpl in *.
  pose (fun n (x : t T (S n)) => match x in (t _ (S n)) with
     |@cons _ _ _ y => y
   end).
  pose (fun n (x : t T (S n)) => match x in (t _ (S n)) with
     |@cons _ x _ _ => x
   end).
 set (f_equal (@y0 _) H0).
 set (f_equal (@y _) H0).
 simpl in *.
 apply H in e0.
 destruct e0.
 constructor.
 congruence.
 trivial.

intros; move : H.
elim/@rect_2S : x0/y.
trivial.
intros.
destruct n0.
simpl in H0; injection H0; move : H H0.
elim/@caseS' : v1; elim/@caseS' : v2.
move => h t h0 t0.
elim/@case0 : t; elim/@case0 : t0.
intros.
simpl in *; subst; trivial.
simpl in *.
destruct n0.
by destruct (@x _ _ a b _ _ H0); subst.
by destruct (@x _ _ a b _ _ H0); subst.
Qed.

Theorem shift_back : forall n s (x : t (SAgent s) (S n)) (H : n < S n) (H' : 0 < S n), (shift x)[@of_nat_lt H] = x[@of_nat_lt H'].
move => n s.
elim/@rect_SS'.
intros;simpl in *; apply : shift_hd_get'.
done.
done.
Qed.

Theorem law1 : forall l y (k : t (SAgent l) (S y)) (x' : y < S y) (y' : 0 < S y), get_agent (match_lex k) y' = get_agent (shift (match_lex k)) x'.
  intros.
  move : x' y'.
  unfold get_agent.
  unfold nth_order.
  elim/@rectS : k.
  done.
  destruct n.
  done.
  simpl; unfold caseS'.
  elim/@caseS'.
  intros;move : H; elim/@caseS' : t.
  intros;symmetry.
  apply : shift_hd_get'.
Qed.

Theorem law2 : forall  l y (k : t (SAgent l) (S y)) (x' : y < S y) (y' : 0 < S y), agent_lex (match_lex k)[@of_nat_lt y'] = cross_lex (agent_lex k[@of_nat_lt y']) (agent_lex k[@of_nat_lt x']).
  move => l y.
  elim/@rectS.
  intros; trivial.
  intros; simpl in *.
  by rewrite (of_nat_lt_c (lt_S_n n (S n) (le_n (S (S n)))) (lt_S_n n (S n) x')).
Qed.

Instance SEnvironment : forall x y (k : t (SAgent x) (S y)),
   @Environment _ _ _ _ _ _ (
  fun x => t x (S y)) boundness get_agent (@view _ _) (@action_prop _ _) (SAgent' x) k (F' shift match_lex).
{
  constructor.
  exists 0.
  elim/@caseS : x0.
  unfold boundness.
  auto with arith.
  
  intros. 
  unfold boundness in *.
  exists (0, y).
  exists (Nat.lt_0_succ y, @le_n (S y)).
  unfold view.
  simpl.
  apply : Nat.eqb_refl.
  
  intros.
  constructor;intros.
  unfold view in H'.
  unfold action_prop.
  
  unfold boundness in *.
  simpl.
  clear x' y'.
  move : x'0 y'0 H'.
  destruct y.
  elim/@case_2nat : x0/y0.
  intros.
  simpl.
  elim/@caseS' : k.
  unfold get_agent.
  pose (of_nat_lt_c x'0 y'0).
  tauto.
  intros.
  inversion H'.
  intros; inversion H'.
  intros; inversion H'.
  
  intros.
  apply andb_true_iff in H'.
  destruct H'.
  apply beq_nat_true in H.
  apply beq_nat_true in H0.
  subst.
  move : x'0 y'0.
  intros; apply : law1.
 
  simpl in *.
  unfold boundness in *.
  unfold view in H'.
  apply andb_true_iff in H'.
  destruct H'.
  apply beq_nat_true in H; apply beq_nat_true in H0.
  subst.
 
  unfold get_agent; unfold nth_order.
    have : of_nat_lt a = of_nat_lt x'0.
    apply of_nat_lt_c.
  move => H2; rewrite H2.
  apply : law2.
}
 
Defined.

Instance SUniverse : forall x y (v : t (SAgent x) (S y)), @State _ _ _ _ _ _ (
  fun x => t x (S y)) boundness get_agent (@view _ _) (@action_prop _ _) (SAgent' x) shift match_lex v.
constructor.
intros.

constructor.
(*when P(0) for environment *)
apply : SEnvironment.
intros.
constructor.
(*when P k -> P (k + 1), for the environment *)
unfold boundness in *.
move => H2; exists y; auto with arith.
intros; unfold boundness in *; exists (0, y); exists (Nat.lt_0_succ y, @le_n (S y)).
unfold view; apply : Nat.eqb_refl.
intros; constructor; simpl.
intros;unfold action_prop; unfold boundness in *; apply andb_true_iff in H'.
destruct H'.
apply beq_nat_true in H; apply beq_nat_true in H0.
subst.
(*both law1 and law2 proofs of inductive interaction was straightfoward, once law1 and law2 were 
    strong enough to generalization of any type obeying just the type constaint *)
apply : law1.
intros; unfold boundness in *; apply andb_true_iff in H'.
destruct H'.
apply beq_nat_true in H; apply beq_nat_true in H0.
subst.
apply : law2.
Defined.

