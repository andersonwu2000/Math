section prop
variable {p q r : Prop}

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => ⟨h.right, h.left⟩)
    (fun h : q ∧ p => ⟨h.right, h.left⟩)
def or_swap (h: p ∨ q): q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q => or_swap h)
    (fun h : q ∨ p => or_swap h)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun h : (p ∧ q) ∧ r => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,
  fun h : p ∧ (q ∧ r) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩
example : (p ∨ q) ∨ r →  p ∨ (q ∨ r) :=
  fun h : (p ∨ q) ∨ r => h.elim
      (fun hpq : p ∨ q => hpq.elim
        (fun t : p => Or.inl t)
        (fun t : q => Or.inr (Or.inl t))
      )
      (fun hr : r => Or.inr (Or.inr hr))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    fun lhs : p → (q → r) =>
    (fun hpq : p ∧ q => (lhs hpq.left) hpq.right),
    fun rhs : p ∧ q → r =>
    (fun hp : p => (fun hq : q => rhs ⟨hp, hq⟩))
  ⟩
example : p ∨ False ↔ p :=
⟨
  fun lhs : p ∨ False => lhs.elim id False.elim,
  fun rhs : p => Or.inl rhs
⟩

example : ¬(p ↔ ¬p) :=
  fun h : p ↔ ¬p =>
    have hp : ¬p := fun t => h.mp t t
    hp (h.mpr hp)

-- 排中律
open Classical
example : p ∨ ¬p := em p
example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

end prop


section quantifier
variable (α : Type) (p q : α → Prop) (r : Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨
    fun h : (∀ x, p x ∧ q x) =>
      ⟨fun x => (h x).left, fun x => (h x).right⟩,
    fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun x => ⟨h.left x, h.right x⟩
  ⟩
-- ∀ intro : 建立函數
-- ∀ elim  : 函數代入
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : (∀ x, p x → q x) =>
  fun k : (∀ x, p x) =>
    fun x => (h x) (k x)
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h k x => (h x) (k x)
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
  fun x => h.elim (fun hl => Or.inl (hl x)) (fun hr => Or.inr (hr x))

variable (x y : Nat)

-- 計算性證明
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    _ = (x + y) * x + (x + y) * y        :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x * y + y * y)  :=
      by rw [Nat.add_mul, Nat.add_mul]
    _ = x * x + y * x + x * y + y * y    :=
      by rw [←Nat.add_assoc]


open Classical
-- ∃ intro : ⟨t, proof of p(t)⟩
-- ∃ elim  : let ⟨t, p(t)⟩ := p
example : ∃ x : Nat, x > 0 :=
  ⟨1, (Nat.zero_lt_succ 0)⟩
example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨
    fun h => fun k =>
      let ⟨w, k'⟩ := k
      absurd (h w) k',
    fun h => fun x => byContradiction
      (fun k : ¬ p x => absurd ⟨x, k⟩ h)
  ⟩
example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x => h1 ⟨x, h3⟩
      show False from h h2)
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨
    fun h => fun k =>
      let ⟨w, h'⟩ := h
      absurd h' (k w),
    fun h => byContradiction
      (fun k : ¬ (∃ x, p x) =>
        h (fun x => fun k' => k ⟨x, k'⟩)
      )
  ⟩

example : (∀ x, p x ∨ r) → (∀ x, p x) ∨ r :=
  fun h : (∀ x, p x ∨ r) => byContradiction
    (fun h' : ¬ ((∀ x, p x) ∨ r) =>
      have k : ∃ x, ¬ p x := byContradiction
        (fun k' : ¬ (∃ x, ¬ p x) =>
          have k'' : ∀ x, p x :=
            fun x => byContradiction
              fun w => absurd ⟨x, w⟩ k'
          absurd (Or.inl k'') h'
        )
      let ⟨w, k'⟩ := k
      (h w).elim
        (fun hl => absurd hl k')
        (fun hr => absurd (Or.inr hr) h')
    )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let H := h barber
  let contra := fun t => H.mp t t
  contra (H.mpr contra)

def prime (n : Nat) : Prop :=
  ∀ m k : Nat, m * k = n → m = n ∨ k = n

end quantifier


namespace tactics
variable (α : Type)

example (p q : α → Prop) :
    (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨w, hpw, hqw⟩
  exact ⟨w, hqw, hpw⟩


open Nat
example (P : Nat → Prop) (h₀ : P 0)
    (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m
  . exact h₀
  . case succ m' =>
    exact h₁ m'

-- 邏輯連接詞的策略
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨h, k⟩
    cases k
    . apply Or.inl
      constructor
      repeat assumption
    . rename_i hr
      have : p ∧ r := ⟨h, hr⟩
      exact Or.inr this
  . intro
    | Or.inl ⟨hp, hq⟩ =>
      constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ =>
      constructor; assumption; apply Or.inr; assumption

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro ⟨h, k⟩
    simp_all
  . intro k
    cases k <;> simp_all

-- 策略組合
variable (p q r : Prop)
example (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption | constructor)

example (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  simp_all

example (k : Nat) (f : Nat → Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

@[local simp] def g (m n : Nat) : Nat :=
  m + n + m
example {m n : Nat} (h' : 0 = m) : (g m n) = n := by
  simp [←h']

example (w x y z : Nat) (p : Nat → Prop)
       : p (x * y + z * w * x) → p (x * w * z + y * x) := by
  intro h
  simp [Nat.add_comm, Nat.mul_comm]
  simp [Nat.mul_assoc] at h
  assumption

-- simp 選項、split 拆分 if-else/match
def f (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, _] => b+1
  | _, _      => 1

#eval f [7, 9] (xs := [1, 2, 0])
#check f
#check @f

example (xs ys : List Nat) (h : f xs ys = 0) : False := by
  simp [f] at h
  split at h <;> simp +arith at h


-- attribute of simp
variable (x y : Nat)

section local_comm
attribute [simp] Nat.add_comm  -- generally
example : x + y = y + x := by
  simp
attribute [local simp] Nat.mul_comm  -- locally
example : x + y = y + x := by
  simp
attribute [-simp] Nat.add_comm  -- locally
example : x + y = y + x := by
  simp [Nat.add_comm]
end local_comm

example : x + y = y + x := by
  simp?
example : x * y = y * x := by
  simp [Nat.mul_comm]

-- 自定義策略
syntax "triv" : tactic
macro_rules
  | `(tactic| triv) => `(tactic| rfl)
macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

macro_rules
  | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv



end tactics

section interacting

-- notation:65 a " + " b:66 " + " c:66 => a + b - c
-- #eval 1 + 2 + 3

-- infixl:65   " + " => HAdd.hAdd
-- -- a + b + c = (a + b) + c
-- infix:50    " ~ " => Eq
-- -- a ~ b ~ c = a ~ (b ~ c)
-- infixr:80   " ^ " => HPow.hPow
-- -- a ^ b ^ c = a ^ (b ^ c)
-- prefix:100  "-"   => Neg.neg
-- postfix:max "⁻¹"  => Inv.inv

-- notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
-- notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
-- notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
-- notation:100 "-" arg:100 => Neg.neg arg
--  -- `max` is a shorthand for precedence 1024:
-- notation:1024 arg:1024 "⁻¹" => Inv.inv arg

variable (m n : Nat)
variable (i j : Int)

-- Coercions
#check i + m
#check 2 + 2 = 4

-- set_option pp.explicit true
-- -- implicit arguments
-- set_option pp.universes true
-- -- hidden universe parameters
-- set_option pp.notation false
-- -- output using defined notations
set_option autoImplicit true
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
#check @compose

def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
-- ≤ as isPrefix
instance : LE (List α) where
  le := isPrefix
theorem List.isPrefix_self (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

-- Sugar for Simple Functions
#check (· + 1)

def h {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable {α} [Add α]

example : h = fun (a c : α) => a + c := rfl

end interacting


set_option autoImplicit true

namespace inductive_types
universe u v

inductive NAT where
  | zero : NAT
  | succ : NAT → NAT
#eval NAT.succ NAT.zero
#check NAT.rec

open NAT
def add (m n : NAT) : NAT :=
  match n with
  | zero   => m
  | succ n => succ (add m n)
#eval add zero.succ zero.succ
instance : Add NAT where
  add := add

theorem add_succ (m n : NAT) : m + n.succ = (m + n).succ :=
  rfl
theorem zero_add : zero + n = n :=
  NAT.rec
    -- (motive := fun n => zero + n = n)
    rfl
    (fun (n : NAT) (p : zero + n = n) => by simp_all [add_succ])
    n
theorem zero_add' : zero + n = n := by
  induction n with
  | zero => rfl
  | succ n p => simp [*, add_succ]
theorem zero_add'' : ∀ n, zero + n = n
  | zero => rfl
  | succ n => congrArg succ (zero_add'' n)
theorem succ_add (m : NAT) : m + zero = zero + m := by
  simp [zero_add]
  rfl
theorem add_assoc (m n k : NAT) : m + n + k = m + (n + k) := by
  induction k <;> simp_all [succ_add, add_succ, zero_add]

inductive SUM (α : Type u) (β : Type v) where
  | inl (a : α) : SUM α β
  | inr : β → SUM α β
#check SUM.inl 3

inductive SIgma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → SIgma β
#check SIgma.mk 4 [4, 7, 1, 2].toArray.toVector



namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons (h : α) (t : List α) : List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append (nil) as = as :=
  rfl
theorem cons_append (a : α) (as bs : List α) :
    append (cons a as) bs = cons a (append as bs) :=
  rfl
theorem append_nil (as : List α) : append as nil = as :=
  List.rec
    -- (motive := fun as => append as nil = as)
    rfl (fun as p => by simp_all [cons_append]) as
-- theorem append_nil' (as : List α) : append as nil = as := by
--   fun_induction append
--   . rfl
--   . simp_all [cons_append]
theorem append_assoc (as bs cs : List α) :
    append (append as bs) cs = append as (append bs cs) :=
  List.rec
    rfl (fun a as p => by simp_all [cons_append]) as
def length {α : Type u} (l : List α) : Nat :=
  match l with
  | nil => 0
  | cons _ as => 1 + length as
#eval @length Nat (append (cons 2 nil) (cons 2 nil))

end List
end Hidden

example (p : Nat → Prop)
    (hz : p 0) (hs : ∀ n, p (Nat.succ n)) :
    ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

namespace Hidden
inductive Vect (α : Type u) : Nat → Type u where
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
#check Vect Nat 2
#check Vect.nil (α := Nat)

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
#check Eq.refl (α := Nat)
#check Eq.rec
example : Eq 3 3 := Eq.refl
example : ¬ Eq 2 3 := fun _ => by contradiction
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | Eq.refl => h₂
end Hidden

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

inductive prop where
  | T : prop
  | F : prop
  | var : Nat → prop
  | not : prop → prop
  | or : prop → prop → prop
  | and : prop → prop → prop

open prop
def subst (n : Nat) (p q : prop) : prop :=
  match p with
  | T => T
  | F => F
  | var m => cond (n=m) q (var m)
  | prop.not a => not (subst n a q)
  | prop.or  a b => or (subst n a q) (subst n b q)
  | prop.and a b => and (subst n a q) (subst n b q)
#eval subst 1 (or (var 1) (or F (var 0))) (var 3)

end inductive_types


namespace induction

def tail1 {α : Type u} : List α → List α
  | []      => []
  | _ :: as => as
#eval tail1 [1, 2, 3]

-- structurally recursive definitions
def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n
-- #eval fib 32  -- slow
#print fib
#reduce fib 32 -- fast

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

def replicate (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate (n : Nat) (a : α) :
    (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α) :
      (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 => simp +arith [replicate.loop, aux n]

-- well-founded recursive definitions
-- prove termination using well-founded recursion
def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => 2 + ack x (ack (x+1) y)
-- termination_by x y => (x, y)  -- lexicographic order

theorem ack_gt_zero : ack n m > 0 := by
  fun_induction ack with
  | case1 y => simp
  | case2 x ih => assumption
  | case3 x y ih1 ih2 => simp [Nat.zero_lt_of_ne_zero]

-- mutually recursive definitions
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

-- Dependent Pattern Matching
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
def tail : Vect α (n+1) → Vect α n
  | Vect.cons _ as => as

inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)
def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | _, ImageOf.imf a => a

variable (a : α)
#check ImageOf.imf


namespace Hidden

def exp : Nat → Nat → Nat
  | _, 0 => 1
  | m, n+1 => m * exp m n

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr

open Expr

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro e
  fun_cases eval
  all_goals first | rfl |
    simp [simpConst]
    split <;> simp_all <;> rfl

end Hidden
end induction


namespace struct_and_class

-- inductive type with 1 constructor: mk
-- construct new type (PROD α β) from α and β
structure PROD (α : Type u) (β : Type v) where
-- mk ::
  fst : α
  snd : β

def p := PROD.mk true 3
-- def p : PROD Bool Nat := {fst := true, snd := 5}
-- def p := {fst := true, snd := 5 : PROD _ _}
#eval p.fst
#eval {p with snd := false}
#eval PROD.casesOn p
  (motive := fun _ : PROD Bool Nat => Nat)
  (fun b n => cond b (2*n) (2*n+1))

-- Inheritance
structure extPROD (α β : Type u) extends PROD α β  where
  prod : α × β
def q : extPROD Bool Nat :=
  {p with prod := (p.fst, p.snd)}
#eval q.prod


-- structure ADD (α : Type u) where
--   add : α → α → α
-- #eval {add := Nat.mul : Add _}.add 10 20

class Add (α : Type u) where
  add : α → α → α

instance : Add Nat where
  add := Nat.add
instance : Add Int := {add := Int.add}
instance F : Add Float where
  add := Float.add
#check (Add.add : Nat → Nat → Nat)

def N := (inferInstance : Add Nat)
#eval N.add 2 3
#eval F.add 2 3
#eval Add.add (10 : Float) 2

export Add (add)
instance (α : Type u) [Add β] : Add (α → β) where
  add f g := fun (a : α) => add (f a) (g a)
def f₀ := (· + 1)
#eval (add f₀ f₀) 2

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide}
instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"
#eval {num := 2, den := 3, inv := by decide : Rational}
#eval (2 : Rational)


namespace Ex
-- Infer the type of γ
class MUL (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  mul : α → β → γ
export MUL (mul)

@[default_instance 20]  -- 200 : prioity
scoped instance : MUL Int Int Int where
  mul := Int.mul
local instance : MUL Nat Nat Nat where
  mul := Nat.mul
#eval mul (γ := Int) (2 : Int) (3 : Int)  -- with no outParam
#eval mul (2 : Int) (3 : Int)

def xs : List Int := [1, 2, 3]
#eval (fun y => xs.map (fun x => x * y)) 2  -- @default_instance
end Ex

-- #check mul (2 : Int) (3 : Int)  -- error (scoped instance)
open Ex
-- #check mul 2 3  -- error (local instance)
#check mul (2 : Int) (3 : Int)

-- coercion : type → type
instance : Coe (List Nat) Int where
  coe b := b.sum
#eval mul ↑3 ↑[2, 3]

-- coercion : type → sort
class ext where
  set : Type u
  rel : set → set → Prop
  rule (a b : set) : a = b → rel a b
instance : CoeSort ext (Type u) where
  coe s := s.set
example (E : ext) (a : E) : ext.rel a a :=  -- (a : E.set)
  (ext.rule a a) rfl

-- coercion : type → function type
class funct (E₁ E₂ : ext) where
  func : E₁ → E₂
  rule (a b : E₁) : E₁.rel a b → E₂.rel (func a) (func b)
instance (E₁ E₂ : ext) : CoeFun (funct E₁ E₂) (fun _ => E₁ → E₂) where
  coe m := m.func
example (f : funct E₁ E₂) (a : E₁) : E₂.rel (f a) (f a) :=
  by simp [ext.rule]

variable (n : Nat)
#check (inferInstance : Decidable (n = 0))
#eval (fun n => if n>0 then 1 else 0) 5
-- #check (inferInstance : Decidable (∃ x, x = 0))  -- error
-- #eval if (∃ x, x = 0) then 1 else 0  --error
open Classical
#check (inferInstance : Decidable (∃ x, x = 0))

end struct_and_class


section subst_and_axiom
section tactic_conv
-- convert a term (in goal) into ...
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0) : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . rfl
    . tactic =>  -- go back to tactic mode
      assumption

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    args
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]

example (w x y z : Nat) (p : Nat → Prop)
        : p (x * y + z * w * x) → p (x * w * z + y * x) := by
  intro
  simp [Nat.add_comm]
  conv in y * x =>
    apply Nat.mul_comm
  conv in x * w * z =>
    simp [Nat.mul_comm]
    simp [←Nat.mul_assoc]
  assumption

def f (x : Nat) := x + 2
theorem ex (x : Nat) : f x = x + f 0 :=
  have h : f 0 = 2 := rfl
  have k : f x = x + 2 := rfl
  h ▸ k ▸ rfl   -- substitution
end tactic_conv


section extensionality
-- prop extensionality
variable (a b c : Prop)
theorem thm (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

theorem tteq : (True ∧ True) = True :=
  propext (by simp)

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

#reduce val  -- no reduce
#check val

-- function extensionality
def Set (α : Type u) := α → Prop

def mem (x : α) (a : Set α) := a x
infix:50 (priority := high) "∈" => mem

def empty : Set α := fun _ => False
notation (priority := high) "∅" => empty

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b
infix:70 " ∩ " => inter

#print funext
theorem setext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b)
  : a = b := by
  funext x
  apply propext (h x)

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext (by simp [mem, inter])

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext (by simp [mem, inter, empty])

end extensionality


section quotient  -- Quotient

variable (R : α → α → Prop) (r : α)
#check Quot R      -- the quotient structure α/R
#check Quot.mk R r -- ⟦r⟧ : α/R
#check Quot.ind    -- ∀ r:α, P(⟦r⟧) → ∀ q:α/R, P(q)
#check Quot.lift   -- α/R → β : ⟦r⟧ ↦ f(r)  if well-define
#check Quot.sound  -- a R b → ⟦a⟧ = ⟦b⟧  is an axiom

-- ⟦a⟧ is the closure of a
theorem closure_le : Quot.mk Nat.le n = Quot.mk Nat.le m := by
  cases Nat.le_or_ge n m with
  | inl k => apply Quot.sound k
  | inr k => exact Classical.byContradiction (by
      intro k'
      have not_k' := Eq.comm.mp (Quot.sound k)
      contradiction)
#print axioms closure_le


--- example : unordered pair
def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)
infix:50 " ~ " => eqv

--- Setoid : a type with a equivalence relation
theorem eqv.symm : p₁ ~ p₂ → p₂ ~ p₁ := by
  intro h
  cases h <;> simp_all [eqv]
theorem eqv.trans : p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃ := by
  intro h k
  cases h <;> cases k <;> simp_all [eqv]
theorem is_equivalence : Equivalence (@eqv α) := {
  refl  := by simp_all [eqv],
  symm  := eqv.symm,
  trans := eqv.trans }
instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r     := eqv
  iseqv := is_equivalence
example (a b : α) : (a, b) ≈ (b, a) :=
  Or.inr (by simp)

--- Quotient : quotient on equivalence relation
def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)
def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)
notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂
example : {a, b} = {b, a} :=
  have h : eqv (a, b) (b, a) := by simp [eqv]
  Quot.sound h

--- define ∈ : α × UProd α → Prop
--- mem_fn a (a, b) ∨ mem_fn a (b, a)
def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂
--- Umem a {a, b} ∨ Umem a {b, a}
def Umem (a : α) (u : UProd α) : Prop :=
  let f : α × α → Prop := fun x => mem_fn a x
  have lemma (p₁ p₂ : α × α) (h : p₁ ~ p₂) :
    mem_fn a p₁ = mem_fn a p₂ := by
      cases h <;> simp_all [mem_fn, Or.comm]
  (Quot.lift f lemma) u

infix:50 (priority := high) " ∈ " => Umem
theorem UProd1 (a b : α) : a ∈ {a, b} :=
  Or.inl rfl
theorem UProd2 (h : c ∈ {a, b}) : c = a ∨ c = b :=
  by assumption

end quotient

section axioms
#check Classical.choice

class inductive nonempty (α : Sort u) : Prop where
  | intro (val : α) : nonempty α

noncomputable
def choice (α : Sort u) : nonempty α → α := by
  intro p
  have q : ∃ x : α, True := (fun ⟨a⟩ => ⟨a, trivial⟩) p
  -- error, Exists.elim gets a Prop
  -- exact Exists.elim q (fun w _ => w)
  exact Classical.choose q   -- noncomputable

open Classical
#check em
theorem em (p : Prop) : p ∨ ¬p := by
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have not_uv_or_p : u ≠ v ∨ p := by
    have u_def : U u := choose_spec exU
    have v_def : V v := choose_spec exV
    cases u_def <;> cases v_def <;> simp [*]
  have p_implies_uv : p → u = v := by
    intro hp
    have hpred : U = V := by
      funext x
      have h : U x ↔ V x := by simp [U, V, hp]
      exact propext h
    have h₀ : @choose _ U exU = @choose _ V exV := by
      simp [hpred]
    exact h₀
  cases not_uv_or_p <;> simp_all

end axioms
end subst_and_axiom

section programming

#eval s!"{2 - 1} + green = ice cream"

opaque contain : univ → univ → Prop
notation A "∈" B => contain A B

-- lean --run Test\Test\Thm_Prov.lean
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"


#check pure
