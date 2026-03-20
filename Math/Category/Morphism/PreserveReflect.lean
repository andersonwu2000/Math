import MATH.Category.Functor.FullyFaithful

/-!
# Morphism/PreserveReflect.lean

Functor 保持與反射 morphism 性質。

## 定理
### `Preserve`
- `.IsSplitMono` / `.IsSplitEpi` / `.IsIso` — functor 保持 split mono/epi、iso
- `.Iso` — `X ≅ Y → F[X] ≅ F[Y]`
- `.NatIso` — `G ≅ H → F ○ G ≅ F ○ H`
### `Reflect`
- `.IsMono` / `.IsEpi` — faithful functor 反射 mono/epi
- `.IsSplitMono` / `.IsSplitEpi` / `.IsIso` — fully faithful 反射
- `.Iso` — `F[X] ≅ F[Y] → X ≅ Y`（fully faithful）
- `.NatIso` — `F ○ G ≅ F ○ H → G ≅ H`（fully faithful）
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

/-- `G ≅ H → F ○ G ≅ F ○ H` -/
def NatIso (α : G ≅[⟦B, C⟧] H) : F ○[Cat] G ≅[⟦B, D⟧] F ○[Cat] H where
  hom := { app b := F[α.hom·b], naturality f := NatTrans.functor_naturality F α.hom f }
  inv := { app b := F[α.inv·b], naturality f := NatTrans.functor_naturality F α.inv f }
  hom_inv_id := by ext b; simp [← Functor.map_comp]
  inv_hom_id := by ext b; simp [← Functor.map_comp]

end Preserve

-- ─── Reflect ──────────────────────────────────────────────────────────────────

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

/-- `F ○ G ≅ F ○ H → G ≅ H`（fully faithful） -/
noncomputable
def NatIso [F.FullyFaithful] (α : F ○[Cat] G ≅[⟦B, D⟧] F ○[Cat] H) : G ≅[⟦B, C⟧] H where
  hom := { app b := F.preimage (α.hom·b),
            naturality f := F.map_injective (by
              simp only [Functor.map_comp, F.map_preimage_id]
              exact α.hom.naturality f) }
  inv := { app b := F.preimage (α.inv·b),
            naturality f := F.map_injective (by
              simp only [Functor.map_comp, F.map_preimage_id]
              exact α.inv.naturality f) }
  hom_inv_id := by ext b; apply F.map_injective; simp [F.map_preimage_id]
  inv_hom_id := by ext b; apply F.map_injective; simp [F.map_preimage_id]

end Reflect
end CategoryTheory
