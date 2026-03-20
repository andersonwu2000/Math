import MATH.Category.Functor.Basic

/-!
# Morphism/EpiMono.lean

Mono/epi morphism 與 split mono/epi。

## 定義
- `Category.hom.IsMono` / `.IsEpi` — mono/epi morphism
- `Category.hom.IsSplitMono` / `.IsSplitEpi` — split mono/epi
- `Mono` / `Epi` — mono/epi structure（`X ↣ Y`、`X ↠ Y`）

## 定理
### `Category.hom.IsMono`
- `.cancel` — `f ○ h = f ○ k ↔ h = k`
- `.comp` — mono ○ mono = mono
- `.mono_of_mono` — 從合成推出
### `Category.hom.IsEpi`
- `.cancel` — `h ○ f = k ○ f ↔ h = k`
- `.comp` — epi ○ epi = epi
- `.epi_of_epi` — 從合成推出
### `Category.hom.IsSplitMono`
- `.IsMono` — split mono ⟹ mono
### `Category.hom.IsSplitEpi`
- `.IsEpi` — split epi ⟹ epi
-/

namespace CategoryTheory
variable {C : Category}

namespace Category.hom
variable {X Y Z : C.obj} (f : X ⟶[C] Y) (g : Y ⟶[C] Z)

/-- Monomorphism：左 cancellation `f ○ h = f ○ k → h = k` -/
class IsMono where
  right_uni : f ○ h = f ○ k → h = k := by aesop_cat

/-- Epimorphism：右 cancellation `h ○ f = k ○ f → h = k` -/
class IsEpi where
  left_uni : h ○ f = k ○ f → h = k := by aesop_cat

instance IsMono.op [p : f.IsMono] : f.op.IsEpi where
  left_uni h := p.right_uni h

instance IsMono.comp [p : f.IsMono] [q : g.IsMono] : (g ○ f).IsMono where
  right_uni h := p.right_uni (q.right_uni (by grind))

lemma IsMono.cancel [f.IsMono] : f ○ h = f ○ k ↔ h = k :=
  ⟨IsMono.right_uni, Whisker.left_cancel f⟩

/-- 若 `g ○ f` mono，則 `f` mono -/
lemma IsMono.mono_of_mono [p : (g ○ f).IsMono] : f.IsMono where
  right_uni _ := by
    apply p.right_uni
    grind

instance IsEpi.op [p : f.IsEpi] : f.op.IsMono where
  right_uni h := p.left_uni h

instance IsEpi.comp [p : f.IsEpi] [q : g.IsEpi] : (g ○ f).IsEpi where
  left_uni h := q.left_uni (p.left_uni (by grind))

lemma IsEpi.cancel [f.IsEpi] : h ○ f = k ○ f ↔ h = k :=
  ⟨IsEpi.left_uni, Whisker.right_cancel f⟩

/-- 若 `g ○ f` epi，則 `g` epi -/
lemma IsEpi.epi_of_epi [p : (g ○ f).IsEpi] : g.IsEpi where
  left_uni _ := by
    apply p.left_uni
    grind

end Category.hom

section MonoEpi

/-- Monomorphism structure -/
structure Mono (X Y) where
  hom : X ⟶[C] Y
  right_uni : hom ○ f = hom ○ g → f = g := by simp

notation X " ↣[" C "] " Y => @Mono C X Y
notation X " ↣ " Y => Mono X Y

instance Mono.IsMono (f : X ↣ Y) : f.hom.IsMono where
  right_uni := f.right_uni

/-- Epimorphism structure -/
structure Epi (X Y) where
  hom : X ⟶[C] Y
  left_uni : f ○ hom = g ○ hom → f = g := by simp

notation X " ↠[" C "] " Y => @Epi C X Y
notation X " ↠ " Y => Epi X Y

instance Epi.IsEpi (f : X ↠ Y) : f.hom.IsEpi where
  left_uni := f.left_uni

end MonoEpi

section Split

namespace Category.hom
variable {X Y Z : C.obj} (f : X ⟶[C] Y) (g : Y ⟶[C] Z)

/-- Split monomorphism：存在左逆 `left_inv ○ f = 𝟙` -/
class IsSplitMono where
  left_inv : Y ⟶ X
  inv_hom_id : left_inv ○ f = 𝟙 := by aesop_cat

attribute [simp, grind =] IsSplitMono.inv_hom_id

/-- Split epimorphism：存在右逆 `f ○ right_inv = 𝟙` -/
class IsSplitEpi where
  right_inv : Y ⟶ X
  hom_inv_id : f ○ right_inv = 𝟙 := by aesop_cat

attribute [simp, grind =] IsSplitEpi.hom_inv_id

abbrev left_inv [f.IsSplitMono] := IsSplitMono.left_inv f

instance IsSplitMono.op [f.IsSplitMono] : f.left_inv.IsSplitEpi where
  right_inv := f

instance IsSplitMono.comp [f.IsSplitMono] [g.IsSplitMono] :
  (g ○ f).IsSplitMono where
  left_inv := f.left_inv ○ g.left_inv
  inv_hom_id := by grind

instance IsSplitMono.IsMono [p : f.IsSplitMono] : f.IsMono where
  right_uni {_ g h} w := by
    rw [←Category.comp_id _ g, ←p.inv_hom_id]; grind

lemma IsSplitMono.left_uni [f.IsSplitMono] :
  f ○ h = f ○ k → h = k := by simp [IsMono.cancel]

lemma IsSplitMono.cancel [f.IsSplitMono] :
  f ○ h = f ○ k ↔ h = k := by simp [IsMono.cancel]

@[simp, grind =]
lemma IsSplitMono.id_assoc [f.IsSplitMono] :
  f.left_inv ○ f ○ h = h := by simp [←Category.assoc]

@[simp, grind =]
lemma IsSplitMono.map_inv_hom_id [f.IsSplitMono] :
  F[f.left_inv] ○ F[f] = 𝟙 := by grind

abbrev right_inv [f.IsSplitEpi] := IsSplitEpi.right_inv f

instance IsSplitEpi.op [f.IsSplitEpi] : f.right_inv.IsSplitMono where
  left_inv := f

instance IsSplitEpi.comp [f.IsSplitEpi] [g.IsSplitEpi] :
  (g ○ f).IsSplitEpi where
  right_inv := f.right_inv ○ g.right_inv
  hom_inv_id := by grind

instance IsSplitEpi.IsEpi [p : f.IsSplitEpi] : f.IsEpi where
  left_uni {_ g h} w := by
    rw [←Category.id_comp _ g, ←p.hom_inv_id]; grind

lemma IsSplitEpi.right_uni [f.IsSplitEpi] :
  h ○ f = k ○ f → h = k := by simp [IsEpi.cancel]

lemma IsSplitEpi.cancel [f.IsSplitEpi] :
  h ○ f = k ○ f ↔ h = k := by simp [IsEpi.cancel]

@[simp, grind =]
lemma IsSplitEpi.id_assoc [f.IsSplitEpi] :
  f ○ f.right_inv ○ h = h := by simp [←Category.assoc]

@[simp, grind =]
lemma IsSplitEpi.map_hom_inv_id [f.IsSplitEpi] :
  F[f] ○ F[f.right_inv] = 𝟙 := by grind

end Category.hom
end Split
end CategoryTheory
