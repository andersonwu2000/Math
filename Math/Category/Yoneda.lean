import MATH.Category.Structure.Types
import MATH.Category.Functor.FullyFaithful

/-!
# Yoneda.lean

Yoneda embedding 與 Yoneda lemma。

## 定義
- `Yoneda` — Yoneda embedding `C ⥤ ⟦Cᵒᵖ, Types⟧`
- `CoYoneda` — co-Yoneda embedding `Cᵒᵖ ⥤ ⟦C, Types⟧`

## 定理
### `Yoneda` / `CoYoneda`
- `.principal` / `.principal_naturality` — Yoneda principal lemma
- `.Equiv` — Yoneda equivalence `(Hom[–, X] ⇒ F) ≅ F[X]`
- `.Lemma` — Yoneda lemma `Hom[Yonedaᵒᵖ–, –] ≅ Evaluation`
- `.FullyFaithful` — Yoneda embedding 是 fully faithful
-/

namespace CategoryTheory

/-- Yoneda embedding `Yoneda[X] = Hom[–, X]` -/
@[simps]
def Yoneda : C ⥤ ⟦Cᵒᵖ, Types⟧ where
  obj X := Hom[–, X]
  map f := Hom[–, f]
  map_comp g f := by ext; simp; grind

namespace Yoneda
variable {C : Category}

@[simp]
lemma map_eq_comp {f : X ⟶ Y} :
  Yoneda[f] = {app Z g := f ○ g, naturality := by simp} := by
    ext; simp; grind

/-- Yoneda principal：`F[f] (α·X (𝟙 X)) = α·A f` -/
@[simp, grind =, grind _=_]
lemma principal
  (α : Hom[–, X] ⇒ F) (f : A ⟶ X) :
  F[f] (α·X (𝟙 X)) = α·A f := by
  have := (Types.naturality_apply α f) (𝟙 X)
  simp_all

@[simp, grind =]
lemma principal_naturality
  (f : Y ⟶ X) (α : Hom[–, X] ⇒ F) (γ : F ⇒ G) :
  G[f] (γ·X (α·X (𝟙 X))) = γ·Y (α·Y f) := by
  have := (Types.naturality_apply γ f) (α·X (𝟙 X))
  simp_all

/-- Yoneda equivalence：`(Hom[–, X] ⇒ F) ≅ F[X]` -/
@[simp]
def Equiv (X : C.obj) (F : Cᵒᵖ ⥤ Types) :
  (Hom[–, X] ⇒ F) ≅[Types] F[X] where
  hom α := α·X (𝟙 X)
  inv a := {app _ f := F[f] a}
  inv_hom_id := by simp; rfl

abbrev Evaluation : Cᵒᵖ × ⟦Cᵒᵖ, Types⟧ ⥤ Types where
  obj := fun (X, F) => F[X]
  map := fun {X Y} (f, α) => Y.2[f] ○[Types] α·X.1

/-- Yoneda lemma：`Hom[Yonedaᵒᵖ–, –] ≅ Evaluation` -/
@[simp]
def Lemma :
  Hom[Yonedaᵒᵖ–, –] ≅[⟦Cᵒᵖ × ⟦Cᵒᵖ, Types⟧, Types⟧] Evaluation :=
  NatIso.ofComponents
  {app := fun (X, F) => (Equiv X.op F).hom}
  (fun (X, F) => inferInstance)

lemma map_eq_inv :
  Yoneda.map = (Equiv X Hom[–, Y]).inv := by
  ext; simp

/-- Yoneda embedding 是 fully faithful -/
instance FullyFaithful :
  (Yoneda : C ⥤ _).FullyFaithful where
  map_bijective {X Y} := ⟨
    fun _ _ p => by
      simp at p
      simpa using congrFun₂ p X (𝟙 X),
    fun α => ⟨α·X (𝟙 X), by ext Z g; have := (Types.naturality_apply α g) (𝟙 X); simp_all⟩ ⟩

end Yoneda

-- ─── CoYoneda ─────────────────────────────────────────────────────────────

/-- Co-Yoneda embedding `CoYoneda[X] = Hom[X, –]` -/
@[simps]
def CoYoneda : Cᵒᵖ ⥤ ⟦C, Types⟧ where
  obj X := Hom[X, –]
  map f := Hom[f, –]
  map_comp g f := by aesop_cat; ext; grind

namespace CoYoneda
variable {C : Category}

@[simp]
lemma map_eq_comp {f : X ⟶ Y} :
  CoYoneda[f] = {app Z g := g ○ f, naturality := by simp} := by
    ext; simp; grind

/-- Co-Yoneda principal：`F[f] (α·X (𝟙 X)) = α·A f` -/
@[simp, grind =, grind _=_]
lemma principal
  (α : Hom[X, –] ⇒ F) (f : A ⟶ X) :
  F[f] (α·X (𝟙[C] X)) = α·A f := by
  have := Types.naturality_apply α f (𝟙 X)
  simp_all

@[simp, grind =]
lemma principal_naturality
  (f : Y ⟶ X) (α : Hom[X, –] ⇒ F) (γ : F ⇒ G) :
  G[f] (γ·X (α·X (𝟙[C] X))) = γ·Y (α·Y f) := by
  have := (Types.naturality_apply γ f) (α·X (𝟙[C] X))
  simp_all

/-- Co-Yoneda equivalence：`(Hom[X, –] ⇒ F) ≅ F[X]` -/
@[simp]
def Equiv (X : C.obj) (F : C ⥤ Types) :
  (Hom[X, –] ⇒ F) ≅[Types] F[X] where
  hom α := α·X (𝟙 X)
  inv a := {app _ f := F[f] a}

abbrev Evaluation : C × ⟦C, Types⟧ ⥤ Types where
  obj := fun (X, F) => F[X]
  map := fun {X Y} (f, α) => Y.2[f] ○[Types] α·X.1

/-- Co-Yoneda lemma：`Hom[CoYonedaᵒᵖ–, –] ≅ Evaluation` -/
@[simp]
def Lemma :
  Hom[CoYonedaᵒᵖ–, –] ≅[⟦C × ⟦C, Types⟧, Types⟧] Evaluation :=
  NatIso.ofComponents
    {app := fun (X, F) => (Equiv X F).hom}
    (fun (X, F) => inferInstance)

@[simp, grind =, grind _=_]
lemma map_eq_inv :
  CoYoneda.map = (Equiv X Hom[Y, –]).inv := by
  ext; simp

/-- Co-Yoneda embedding 是 fully faithful -/
instance FullyFaithful :
  (CoYoneda : Cᵒᵖ ⥤ _).FullyFaithful where
  map_bijective {Y X} := ⟨
    fun _ _ p => by
      simp at p
      simpa using congrFun₂ p Y (𝟙 Y),
    fun α => ⟨α·Y (𝟙 Y), by ext Z g; have := (Types.naturality_apply α g) (𝟙[C] Y); simp_all⟩ ⟩

end CoYoneda

end CategoryTheory
