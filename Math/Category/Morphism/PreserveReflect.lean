import MATH.Category.Functor.FullyFaithful

-- set_option trace.Meta.synthInstance true
-- set_option profiler true

/-!
# Morphism/PreserveReflect.lean

Functor 保持與反射 morphism 性質。

## 定理
### `Preserve`
- `.IsSplitMono` / `.IsSplitEpi` / `.IsIso` — functor 保持 split mono/epi、iso
- `.Iso` — `X ≅ Y → F[X] ≅ F[Y]`
### `Reflect`
- `.IsMono` / `.IsEpi` — faithful functor 反射 mono/epi
- `.IsSplitMono` / `.IsSplitEpi` / `.IsIso` — fully faithful 反射
- `.Iso` — `F[X] ≅ F[Y] → X ≅ Y`（fully faithful）
-/

namespace CategoryTheory

variable (F : C ⥤ D) (f : X ⟶[C] Y)

namespace Preserve

instance IsSplitMono [f.IsSplitMono] : F[f].IsSplitMono where
  left_inv := F.map f.left_inv
  inv_hom_id := by grind

instance IsSplitEpi [f.IsSplitEpi] : F[f].IsSplitEpi where
  right_inv := F.map f.right_inv
  hom_inv_id := by grind

instance IsIso [f.IsIso] : F[f].IsIso where
  inv := F[f.inv]

@[simp, grind =, grind _=_]
lemma IsIso.map_inv [f.IsIso] : F[f.inv] = F[f].inv := rfl

def Iso (i : X ≅ Y) : F[X] ≅ F[Y] where
  hom := F[i.hom]
  inv := F[i.inv]
  hom_inv_id := by grind
  inv_hom_id := by grind

@[simp, grind =]
lemma Iso.hom (i : X ≅ Y) :
  (Iso F i).hom = F[i.hom] := rfl

@[simp, grind =]
lemma Iso.inv (i : X ≅ Y) :
  (Iso F i).inv = F[i.inv] := rfl

end Preserve

namespace Reflect
lemma IsMono
  [F.Faithful] [p : F[f].IsMono] : f.IsMono where
  right_uni {_ g h} _ :=
    Functor.map_injective_iff.mp (p.right_uni (by grind))

lemma IsEpi
  [F.Faithful] [p : F[f].IsEpi] : f.IsEpi where
  left_uni {Z g h} _ :=
    Functor.map_injective_iff.mp (p.left_uni (by grind))

@[reducible]
noncomputable
def IsSplitMono
  [F.FullyFaithful] [F[f].IsSplitMono] : f.IsSplitMono where
  left_inv := F.preimage F[f].left_inv
  inv_hom_id := F.map_injective (by simp [F.map_preimage_id])

@[reducible]
noncomputable
def IsSplitEpi
  [F.FullyFaithful] [F[f].IsSplitEpi] : f.IsSplitEpi where
  right_inv := F.preimage F[f].right_inv
  hom_inv_id := F.map_injective (by simp [F.map_preimage_id])

@[reducible]
noncomputable
def IsIso [F.FullyFaithful] [F[f].IsIso] : f.IsIso where
  inv := F.preimage F[f]⁻¹
  inv_hom_id := F.map_injective (by simp [F.map_preimage_id])
  hom_inv_id := F.map_injective (by simp [F.map_preimage_id])

noncomputable
def Iso [F.FullyFaithful] (i : F[X] ≅ F[Y]) : X ≅ Y where
  hom := F.preimage i.hom
  inv := F.preimage i.inv
  hom_inv_id := F.map_injective (by simp [F.map_preimage_id])
  inv_hom_id := F.map_injective (by simp [F.map_preimage_id])

end Reflect
end CategoryTheory
