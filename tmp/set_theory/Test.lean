import MATH.set_theory.Basic

open Classical

def compose : (f : A ⟶ B) → (g : B ⟶ C) →
    univ → univ → Prop := by
  intros f' g'
  exact fun x o =>
    if x' : x ∈ A
    then
      let y := eval f' x'
      have y' : y ∈ B := (choose_spec (f'.left x x')).left
      let z := eval g' y'
      o = z
    else False

-- x ∈ A ∧ z ∈ C  =>  f x f(x) ∧ g f(x) gf(x)

noncomputable
def f (n : Nat) : Nat :=
  if ∃ m, m < n then 0 else 1

example : f 0 = 1 := by
  have h : ¬ ∃ m, m < 0 := by simp
  simp_all [f]

theorem asdf : ∃ m, m < 1 := ⟨0, by simp⟩

example : f 1 = 0 := by
  have h : ∃ m, m < 1 := ⟨0, by simp⟩
  simp [f]
