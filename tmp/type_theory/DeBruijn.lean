inductive Member : α → List α → Type
  | head : Member a (a::as)
  | tail : Member a bs → Member a (b::bs)

inductive Ty where
  | nat
  | bool
  | fn : Ty → Ty → Ty

inductive Term : List Ty → Ty → Type
  | var   : Member ty ctx → Term ctx ty
  | const : Nat → Term ctx .nat
  | truth : Bool → Term ctx .bool
  | plus  : Term ctx .nat → Term ctx .nat → Term ctx .nat
  | app   : Term ctx (.fn dom ran) → Term ctx dom → Term ctx ran
  | lam   : Term (dom :: ctx) ran → Term ctx (.fn dom ran)
  | «let» : Term ctx ty₁ → Term (ty₁ :: ctx) ty₂ → Term ctx ty₂


inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v)
  | nil  : HList β []
  | cons : β i → HList β is → HList β (i::is)
infix:67 " ;; " => HList.cons
notation "[" "]" => HList.nil

def HList.get : HList β is → Member i is → β i
  | a;;as, .head   => a
  | _;;as, .tail h => as.get h

@[reducible]
def Ty.denote : Ty → Type
  | nat    => Nat
  | bool   => Bool
  | fn a b => a.denote → b.denote

@[simp]
def Term.denote : Term ctx ty → HList Ty.denote ctx → ty.denote
  | var h,     env => env.get h
  | const n,   _   => n
  | truth b,   _   => b
  | plus a b,  env => a.denote env + b.denote env
  | app f a,   env => f.denote env (a.denote env)
  | lam b,     env => fun x => b.denote (x ;; env)
  | «let» a b, env => b.denote (a.denote env ;; env)

@[simp]
def Term.constFold : Term ctx ty → Term ctx ty
  | const n   => const n
  | truth b   => truth b
  | var h     => var h
  | app f a   => app f.constFold a.constFold
  | lam b     => lam b.constFold
  | «let» a b => «let» a.constFold b.constFold
  | plus a b  =>
    match a.constFold, b.constFold with
    | const n, const m => const (n+m)
    | a',      b'      => plus a' b'

theorem Term.constFold_sound (e : Term ctx ty) :
    e.constFold.denote env = e.denote env := by
  induction e with simp [*]
  | plus a b iha ihb =>
    split
    next he₁ he₂ => simp [← iha, ← ihb, he₁, he₂]
    next => simp [iha, ihb]



section Example
open Ty Term Member

def HL : HList (Vector Nat) [2, 3] :=
  let a₀: Vector Nat 2 := ⟨#[1, 2], by simp⟩
  let a₁: Vector Nat 3 := ⟨#[1, 2, 3], by simp⟩
  a₀ ;; (a₁ ;; [])

#reduce HList.get HL .head
#reduce HList.get HL (Member.tail Member.head)

def Hctx : HList Ty.denote [nat, fn nat nat] :=
  let a₀: Ty.denote nat := 2
  let a₁: Ty.denote (fn nat nat) := fun x => x + 2
  a₀ ;; (a₁ ;; [])

def t : Term [nat, fn nat nat] (fn nat nat) :=
  let x : Term [nat, nat, fn nat nat] nat := var head
  lam x
def t' : Term [nat, fn nat nat] (fn nat nat) :=
  lam (var (tail head))
def t'' : Term [nat, fn nat nat] (fn nat nat) :=
  var (tail head)

#reduce Term.denote t Hctx
#reduce Term.denote t' Hctx
#reduce Term.denote t'' Hctx

def add : Term [] (fn nat (fn nat nat)) :=
  let x : Term [nat, nat] nat := var head
  let y : Term [nat, nat] nat := var (tail head)
  let p : Term [nat, nat] nat := plus x y
  lam (lam p)

#reduce Term.denote add HList.nil
