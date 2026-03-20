import MATH.Category.NatTrans.Iso
import MATH.Category.Functor.BiFunctor

/-!
# Structure/Types.lean

Types category 與 Hom bifunctor。

## 定義
- `Types` — type 為 object、函數為 morphism 的 category
- `Types.Terminal` / `Types.Initial` — Types 的 terminal / initial object（`PUnit` / `PEmpty`）
- `Hom` — Hom bifunctor `Cᵒᵖ × C ⥤ Types`

## 定理
### `Types`
- `.mono_iff_injective` / `.epi_iff_surjective` — mono/epi ↔ injective/surjective
- `.epi_to_splitEpi` — epi ⟹ split epi（in Types）
- `.iso_to_bijection` / `.bijection_to_iso` — iso ↔ bijective
### `NatIso`
- `.hom_inv_id_app_apply` / `.inv_hom_id_app_apply` — 逐點消去律
-/

namespace CategoryTheory

/-- `Types`：type 為 object、函數為 morphism 的 category -/
abbrev Types.{u} : Category where
  obj := Type u
  hom X Y := X → Y
  id X := id
  comp f g := f ∘ g

attribute [simp] Function.comp_def

/-- `Hom` bifunctor `Cᵒᵖ × C ⥤ Types`：`Hom[f, g] h = g ○ h ○ f` -/
@[simp]
def Hom : Cᵒᵖ × C ⥤ Types where
  obj X := X.1 ⟶[C] X.2
  map f h := f.2 ○ h ○ f.1.op

-- ─── Types ──────────────────────────────────────────────────────────────────

namespace Types

/-- Types 的 terminal object -/
abbrev Terminal : Types.obj := PUnit

/-- Types 的 initial object -/
abbrev Initial : Types.obj := PEmpty

@[ext]
lemma ext
  (f g : X ⟶[Types] Y) (h : ∀ x, f x = g x) : f = g :=
  funext h

/-- Naturality 逐點版：`α·Y (F[f] a) = G[f] (α·X a)` -/
@[simp, grind =]
lemma naturality_apply
  (α : F ⇒[C, Types] G) (f : X ⟶ Y) (a : F[X]) :
  α·Y (F[f] a) = G[f] (α·X a) :=
  congrFun (α.naturality f) a

/-- `(g ○ f) x = g (f x)` -/
lemma comp_apply (g : Y ⟶[Types] Z) (f : X ⟶ Y) (x : X) :
  g (f x) = (g ○ f) x := rfl

/-- `i.inv (i.hom x) = x` -/
@[simp, grind =]
lemma hom_inv_id_apply
  (x : X) (i : X ≅[Types] Y) : i.inv (i.hom x) = x :=
  congrFun i.inv_hom_id x

/-- `i.hom (i.inv y) = y` -/
@[simp, grind =]
lemma inv_hom_id_apply
  (y : Y) (i : X ≅[Types] Y) : i.hom (i.inv y) = y :=
  congrFun i.hom_inv_id y

@[simp]
lemma eq_symm_apply
  (x : X) (y : Y) (i : X ≅[Types] Y) :
  x = i.inv y ↔ i.hom x = y := by aesop_cat

@[simp]
lemma symm_eq_apply
  (x : X) (y : Y) (i : X ≅[Types] Y) :
  i.inv y = x ↔ y = i.hom x := by aesop_cat

open Function
variable {f : X ⟶[Types] Y}

/-- Mono ↔ injective -/
lemma mono_iff_injective : Injective f ↔ f.IsMono := ⟨
  fun p => ⟨fun q => by
    funext z
    exact p (congrFun q z)⟩,
  fun p x1 x2 h => by
    let Point (a : X) : PUnit ⟶[Types] X := fun _ => a
    have q : f ○ Point x1 = f ○ Point x2 := by grind
    exact congrFun (p.right_uni q) PUnit.unit ⟩

lemma Mono.injective [p : f.IsMono] : f x = f y → x = y :=
  fun q => mono_iff_injective.mpr p q

/-- Epi ↔ surjective -/
lemma epi_iff_surjective : Surjective f ↔ f.IsEpi := ⟨
  fun p => ⟨fun q => by
    funext z
    let ⟨a, p⟩ := p z
    repeat rw [←p]
    exact (congrFun q a)⟩,
  fun p y => by
    by_contra q
    let g : Y ⟶[Types] ULift Prop := fun a => .up True
    let h : Y ⟶[Types] ULift Prop := fun a => .up (a ≠ y)
    have q : g ○ f = h ○ f := by simp_all [g, h]
    simpa [g, h] using congrFun (p.left_uni q) ⟩

lemma Epi.surjective [p : f.IsEpi] (y : Y) : ∃ x : X, f x = y :=
  epi_iff_surjective.mpr p y

/-- Epi ⟹ split epi -/
noncomputable
instance epi_to_splitEpi [p : f.IsEpi] : f.IsSplitEpi where
  right_inv y :=
    Classical.choose (epi_iff_surjective.mpr p y)
  hom_inv_id := by
    ext y
    simpa using Classical.choose_spec (epi_iff_surjective.mpr p y)

/-- Iso ⟹ bijective -/
def iso_to_bijection [p : f.IsIso] : Bijective f :=
  ⟨mono_iff_injective.mpr (IsIso.IsMono f), epi_iff_surjective.mpr (IsIso.IsEpi f)⟩

/-- Bijective ⟹ iso -/
noncomputable
instance bijection_to_iso (p : Bijective f) : f.IsIso where
  inv y := Classical.choose (p.2 y)
  inv_hom_id := by
    funext x
    exact p.1 (Classical.choose_spec (p.2 (f x)))
  hom_inv_id := by
    funext y
    exact Classical.choose_spec (p.2 y)

lemma Iso.injective [p : f.IsIso] : f x = f y → x = y := Mono.injective
lemma Iso.surjective [p : f.IsIso] (y : Y) : ∃ x : X, f x = y := Epi.surjective y

@[simp]
lemma Iso.inv_hom_id [p : f.IsIso] : f⁻¹ (f x) = x := by
  simpa using congrFun p.inv_hom_id x

@[simp]
lemma Iso.hom_inv_id [p : f.IsIso] : f (f⁻¹ y) = y := by
  simpa using congrFun p.hom_inv_id y

/-- Mono + epi ⟹ iso -/
noncomputable
instance epi_mono_to_iso [p : f.IsMono] [q : f.IsEpi] : f.IsIso :=
  bijection_to_iso ⟨mono_iff_injective.mpr p, epi_iff_surjective.mpr q⟩

end Types

-- ─── Functor ─────────────────────────────────────────────────────────────────

namespace Functor
variable (F G : C ⥤ Types)

/-- `F[i.inv] (F[i.hom] a) = a` -/
@[simp, grind =]
lemma map_inv_map_hom_apply (i : X ≅[C] Y) (a : F[X]) :
  F[i.inv] (F[i.hom] a) = a := by
    rw [Types.comp_apply F[i.inv], ←F.map_comp]; simp

/-- `F[i.hom] (F[i.inv] a) = a` -/
@[simp, grind =]
lemma map_hom_map_inv_apply (i : X ≅[C] Y) (a : F[Y]) :
  F[i.hom] (F[i.inv] a) = a := by
    rw [Types.comp_apply F[i.hom], ←F.map_comp]; simp

end Functor

-- ─── NatIso ──────────────────────────────────────────────────────────────────

namespace NatIso
variable {F G : C ⥤ Types} (α : F ≅ G)

/-- `α.inv·X (α.hom·X x) = x` -/
@[simp, grind =]
lemma hom_inv_id_app_apply :
  α.inv·X (α.hom·X x) = x :=
  congr_fun (α.inv_hom_id_app X) x

/-- `α.hom·X (α.inv·X x) = x` -/
@[simp, grind =]
lemma inv_hom_id_app_apply :
  α.hom·X (α.inv·X x) = x :=
  congr_fun (α.hom_inv_id_app X) x

lemma eq_symm_apply {x : F[X]} :
  x = α.inv·X y ↔ α.hom·X x = y := by aesop_cat

lemma symm_eq_apply {x : F[X]} :
  α.inv·X y = x ↔ y = α.hom·X x := by aesop_cat

end NatIso
end CategoryTheory
