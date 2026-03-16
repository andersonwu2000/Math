import MATH.Category.Morphism.PreserveReflect

/-!
# Functor/Essentially.lean

Essentially surjective / essentially injective functor 及相關性質。

## 定義
- `Functor.EssentiallySurjective` — ∀ A, ∃ X, F[X] ≅ A
- `Functor.EssentiallyInjective` — F[X] ≅ F[Y] → X ≅ Y

## 定理
- `fullyFaithful_essentiallyInjective` — fully faithful ⟹ essentially injective
### `Functor.EssentiallySurjective`
- `.id` — identity functor 是 essentially surjective
- `.comp` — essentially surjective 在合成下封閉
- `.of_comp` — G ○ F essentially surjective ⟹ G essentially surjective
-/

namespace CategoryTheory

variable {C D : Category}

/-- Essentially surjective：∀ A, ∃ X, F[X] ≅ A -/
class Functor.EssentiallySurjective (F : C ⥤ D) : Prop where
  obj_surj : ∀ A : D.obj, ∃ X : C.obj, Nonempty (F[X] ≅[D] A)

/-- Essentially injective：F[X] ≅ F[Y] → X ≅ Y -/
class Functor.EssentiallyInjective (F : C ⥤ D) where
  obj_inj {X Y : C.obj} : (F[X] ≅[D] F[Y]) → Nonempty (X ≅[C] Y)

/-- Identity functor 是 essentially surjective -/
instance Functor.EssentiallySurjective.id :
    (𝟙[Cat] C).EssentiallySurjective where
  obj_surj A := ⟨A, ⟨Iso.refl⟩⟩

/-- Essentially surjective 在合成下封閉 -/
instance Functor.EssentiallySurjective.comp
    {E : Category} (F : C ⥤ D) (G : D ⥤ E)
    [F.EssentiallySurjective] [G.EssentiallySurjective] :
    (G ○[Cat] F).EssentiallySurjective where
  obj_surj A := by
    obtain ⟨B, ⟨iB⟩⟩ := EssentiallySurjective.obj_surj (F := G) A
    obtain ⟨X, ⟨iX⟩⟩ := EssentiallySurjective.obj_surj (F := F) B
    exact ⟨X, ⟨(Preserve.Iso G iX).trans iB⟩⟩

/-- G ○ F essentially surjective ⟹ G essentially surjective -/
lemma Functor.EssentiallySurjective.of_comp
    {E : Category} (F : C ⥤ D) (G : D ⥤ E)
    [h : (G ○[Cat] F).EssentiallySurjective] :
    G.EssentiallySurjective where
  obj_surj A := by
    obtain ⟨X, ⟨i⟩⟩ := h.obj_surj A
    exact ⟨F[X], ⟨i⟩⟩

/-- Fully faithful functor 是 essentially injective -/
noncomputable
instance fullyFaithful_essentiallyInjective
    (F : C ⥤ D) [F.FullyFaithful] : F.EssentiallyInjective where
  obj_inj i := ⟨Reflect.Iso F i⟩

end CategoryTheory
