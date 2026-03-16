
structure function (_ : Setoid A) (_ : Setoid B) where
  f : A → B
  Functional : x ≈ y → f x ≈ f y

notation A "⇉" B => function A B
-- instance : CoeFun (A ⇉ B) (λ _ => Quotient A → Quotient B) where
--   coe f := Quotient.lift
--     (fun x => Quotient.mk B (f.f x))
--     (fun _ _ h => Quotient.sound (f.Functional h))
instance (Set₁ : Setoid A) (Set₂ : Setoid B) : CoeFun (Set₁ ⇉ Set₂) (λ _ => Setoid A → Setoid B) where
  coe f := fun x => f.f x.

instance : Setoid (A ⇉ B) where
  r f g := ∀ x, f x ≈ g x

def function.comp (f : A ⇉ B) (g : B ⇉ C) : A ⇉ C where
  f := g.f ∘ f.f
  Functional h := g.Functional (f.Functional h)

notation f "⊚" g => function.comp f g
