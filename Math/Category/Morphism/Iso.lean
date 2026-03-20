import MATH.Category.Morphism.EpiMono

/-!
# Morphism/Iso.lean

Isomorphism。

## 定義
- `Iso` — isomorphism `X ≅ Y`（hom、inv、hom_inv_id、inv_hom_id）
- `Category.hom.IsIso` — 可逆 morphism typeclass

## 定理
### `Iso`
- `.refl` / `.symm` / `.trans` — 自反、對稱、遞移
### `Category.hom`
- `splitMono_epi_IsIso` — split mono + epi ⟹ iso
- `splitEpi_mono_IsIso` — split epi + mono ⟹ iso
-/

namespace CategoryTheory
variable {C : Category}

/-- Isomorphism `i : X ≅ Y`：`hom`、`inv`、`hom_inv_id`、`inv_hom_id` -/
structure Iso (X Y : C.obj) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ○ inv = 𝟙 := by aesop_cat
  inv_hom_id : inv ○ hom = 𝟙 := by aesop_cat

notation:50 X " ≅[" C "] " Y => @Iso C X Y
notation:50 X " ≅ " Y => Iso X Y
attribute [simp, grind =] Iso.hom_inv_id Iso.inv_hom_id

namespace Iso

@[ext, grind ext]
lemma ext {i j : X ≅ Y} (p : i.hom = j.hom) : i = j := by
  suffices i.inv = j.inv by grind [Iso]
  have h : i.inv = i.inv ○ j.hom ○ j.inv := by simp
  rwa [←p, ←Category.assoc, i.inv_hom_id, Category.comp_id] at h

/-- `i.op : X ≅[Cᵒᵖ] Y` -/
abbrev op (i : X ≅[C] Y) : X ≅[Cᵒᵖ] Y where
  hom := i.inv
  inv := i.hom

/-- Reflexivity -/
@[refl]
abbrev refl : X ≅ X where
  hom := 𝟙 X
  inv := 𝟙 X

/-- Symmetry -/
@[symm]
abbrev symm (i : X ≅ Y) : Y ≅ X where
  hom := i.inv
  inv := i.hom

/-- Transitivity -/
@[trans]
abbrev trans
  (i : X ≅ Y) (j : Y ≅ Z) : X ≅ Z where
  hom := j.hom ○ i.hom
  inv := i.inv ○ j.inv
  hom_inv_id := by grind
  inv_hom_id := by grind

end Iso

namespace Category.hom
variable {C : Category} {X Y : C.obj} (f : X ⟶ Y)

/-- 可逆 morphism：`inv ○ f = 𝟙` 且 `f ○ inv = 𝟙` -/
class IsIso where
  inv : Y ⟶ X
  inv_hom_id : inv ○ f = 𝟙 := by aesop_cat
  hom_inv_id : f ○ inv = 𝟙 := by aesop_cat

attribute [simp, grind =] IsIso.hom_inv_id IsIso.inv_hom_id
abbrev inv [f.IsIso] : Y ⟶ X := IsIso.inv f
notation:max f:max "⁻¹" => inv f

end Category.hom

-- ─── IsIso ───────────────────────────────────────────────────────────────────

namespace IsIso
variable (f : X ⟶ Y) (g : Y ⟶ Z)

instance id : (𝟙 X).IsIso where
  inv := 𝟙

instance trans [f.IsIso] [g.IsIso] : (g ○ f).IsIso where
  inv := f⁻¹ ○ g⁻¹
  inv_hom_id := by grind
  hom_inv_id := by grind

@[simp, grind =]
lemma inv_id : (𝟙 X)⁻¹ = 𝟙 := rfl

instance inv_isIso [f.IsIso] : f⁻¹.IsIso where
  inv := f

@[simp, grind =, grind _=_]
lemma inv_comp [f.IsIso] [g.IsIso] :
  (g ○ f)⁻¹ = f⁻¹ ○ g⁻¹ := rfl

instance IsSplitMono [f.IsIso] : f.IsSplitMono where
  left_inv := f⁻¹

instance IsSplitEpi [f.IsIso] : f.IsSplitEpi where
  right_inv := f⁻¹

instance IsMono [f.IsIso] : f.IsMono :=
  (IsIso.IsSplitMono f).IsMono

instance IsEpi [f.IsIso] : f.IsEpi :=
  (IsIso.IsSplitEpi f).IsEpi

@[simp, grind =]
lemma id_assoc_left [f.IsIso] :
  f⁻¹ ○ f ○ h = h := by simp [←Category.assoc]

@[simp, grind =]
lemma id_assoc_right [f.IsIso] :
  f ○ f⁻¹ ○ h = h := by simp [←Category.assoc]
@[simp, grind =]
lemma map_hom_inv_id [f.IsIso] :
  F[f] ○ F[f⁻¹] = 𝟙 := by grind

@[simp, grind =]
lemma map_inv_hom_id [f.IsIso] :
  F[f⁻¹] ○ F[f] = 𝟙 := by grind

end IsIso

instance Iso.IsIso (i : X ≅ Y) : i.hom.IsIso where
  inv := i.inv

instance Iso.invIsIso (i : X ≅ Y) : i.inv.IsIso where
  inv := i.hom

-- ─── Category.hom ────────────────────────────────────────────────────────────

namespace Category.hom

/-- Split mono + epi ⟹ iso -/
@[reducible]
noncomputable
def splitMono_epi_IsIso (f : X ⟶ Y)
  [p : f.IsSplitMono] [q : f.IsEpi] : f.IsIso where
  inv := f.left_inv
  inv_hom_id := p.inv_hom_id
  hom_inv_id := by
    have h : f ○ 𝟙 = 𝟙 ○ f := by simp
    rw [←p.inv_hom_id, ←Category.assoc] at h
    exact q.left_uni h

/-- Split epi + mono ⟹ iso -/
@[reducible]
noncomputable
def splitEpi_mono_IsIso (f : X ⟶ Y)
  [p : f.IsSplitEpi] [q : f.IsMono] : f.IsIso where
  inv := f.right_inv
  hom_inv_id := p.hom_inv_id
  inv_hom_id := by
    have h : 𝟙 ○ f = f ○ 𝟙 := by simp
    rw [←p.hom_inv_id, Category.assoc] at h
    exact q.right_uni h

end Category.hom
end CategoryTheory
