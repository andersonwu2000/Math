import MATH.Category.Basic.Functor

/-
`Mono Epi`
  op comp cancel
`Category.hom`
  IsMono IsEpi
  Mono Epi : IsMono/Epi → Mono/Epi
  hom_eq
  right_uni left_uni

`Split Mono/Epi`
  op comp
  Mono Epi
`Category.hom`
  IsSplitMono IsSplitEpi
  SplitMono SplitEpi : Is... to ...
  hom_eq
  inv_hom_id hom_inv_id
-/

-- set_option trace.Meta.synthInstance true
-- set_option profiler true

namespace category
variable {C : Category}


namespace Category.hom
variable {X Y Z : C.obj} (f : X ⟶[C] Y) (g : Y ⟶[C] Z)

class IsMono where
  right_uni : f ∘ h = f ∘ k → h = k := by simp

class IsEpi where
  left_uni : h ∘ f = k ∘ f → h = k := by simp

instance IsMono.op [p : f.IsMono] : f.op.IsEpi where
  left_uni _ := by
    apply p.right_uni
    simp_all

instance IsEpi.op [p : f.IsEpi] : f.op.IsMono where
  right_uni _ := by
    apply p.left_uni
    simp_all

instance IsMono.comp [p : f.IsMono] [q : g.IsMono] : (g ∘ f).IsMono where
  right_uni _ := by
    apply p.right_uni
    apply q.right_uni
    simp_all

instance IsEpi.comp [p : f.IsEpi] [q : g.IsEpi] : (g ∘ f).IsEpi where
  left_uni _ := by
    apply q.left_uni
    apply p.left_uni
    simp_all

lemma IsMono.cancel [f.IsMono] :
  f ∘ h = f ∘ k ↔ h = k :=
  ⟨IsMono.right_uni, Whisker.left_cancel f⟩

lemma IsEpi.cancel [f.IsEpi] :
  h ∘ f = k ∘ f ↔ h = k :=
  ⟨IsEpi.left_uni, Whisker.right_cancel f⟩

theorem IsMono.mono_of_mono [p : (g ∘ f).IsMono] : f.IsMono where
  right_uni _ := by
    apply p.right_uni
    grind

theorem IsEpi.epi_of_epi [p : (g ∘ f).IsEpi] : g.IsEpi where
  left_uni _ := by
    apply p.left_uni
    grind


end Category.hom
section MonoEpi

structure Mono (X Y) where
  hom : X ⟶[C] Y
  right_uni : hom ∘ f = hom ∘ g → f = g := by simp

notation X "↣[" C "]" Y => @Mono C X Y
notation X "↣" Y => Mono X Y

structure Epi (X Y) where
  hom : X ⟶[C] Y
  left_uni : f ∘ hom = g ∘ hom → f = g := by simp

notation X "↠[" C "]" Y => @Epi C X Y
notation X "↠" Y => Epi X Y

instance Mono.IsMono (f : X ↣ Y) : f.hom.IsMono where
  right_uni := f.right_uni

instance Epi.IsEpi (f : X ↠ Y) : f.hom.IsEpi where
  left_uni := f.left_uni

end MonoEpi


section Split

namespace Category.hom
variable {X Y Z : C.obj} (f : X ⟶[C] Y) (g : Y ⟶[C] Z)

class IsSplitMono where
  left_inv : Y ⟶ X
  inv_hom_id : left_inv ∘ f = 𝟙 X := by simp

class IsSplitEpi where
  right_inv : Y ⟶ X
  hom_inv_id : f ∘ right_inv = 𝟙 Y := by simp

attribute [simp, grind =] IsSplitMono.inv_hom_id IsSplitEpi.hom_inv_id

abbrev left_inv [f.IsSplitMono] := IsSplitMono.left_inv f
abbrev right_inv [f.IsSplitEpi] := IsSplitEpi.right_inv f

instance IsSplitMono.op [p : f.IsSplitMono] : f.left_inv.IsSplitEpi where
  right_inv := f
  hom_inv_id := p.inv_hom_id

instance IsSplitEpi.op [p : f.IsSplitEpi] : f.right_inv.IsSplitMono where
  left_inv := f
  inv_hom_id := p.hom_inv_id

instance IsSplitMono.comp [p : f.IsSplitMono] [q : g.IsSplitMono] :
  (g ∘ f).IsSplitMono where
  left_inv := f.left_inv ∘ g.left_inv
  inv_hom_id := by grind

instance IsSplitEpi.comp [p : f.IsSplitEpi] [q : g.IsSplitEpi] :
  (g ∘ f).IsSplitEpi where
  right_inv := f.right_inv ∘ g.right_inv
  hom_inv_id := by grind

instance IsSplitMono.IsMono [p : f.IsSplitMono] : f.IsMono where
  right_uni {_ g h} _ := by
    rw [←Category.comp_id _ g, ←p.inv_hom_id]
    grind

instance IsSplitEpi.IsEpi [p : f.IsSplitEpi] : f.IsEpi where
  left_uni {_ g h} w := by
    rw [←Category.id_comp _ g, ←p.hom_inv_id]
    grind

theorem IsSplitMono.left_uni [f.IsSplitMono] :
  f ∘ h = f ∘ k → h = k := by simp [IsMono.cancel]

theorem IsSplitEpi.right_uni [f.IsSplitEpi] :
  h ∘ f = k ∘ f → h = k := by simp [IsEpi.cancel]

-- @[simp, grind =]
theorem IsSplitMono.cancel [f.IsSplitMono] :
  f ∘ h = f ∘ k ↔ h = k := by simp [IsMono.cancel]

-- @[simp, grind =]
theorem IsSplitEpi.cancel [f.IsSplitEpi] :
  h ∘ f = k ∘ f ↔ h = k := by simp [IsEpi.cancel]

@[simp, grind =]
theorem IsSplitMono.id_assoc [f.IsSplitMono] :
  f.left_inv ∘ f ∘ h = h := by simp [←Category.assoc]

@[simp, grind =]
theorem IsSplitEpi.id_assoc [f.IsSplitEpi] :
  f ∘ f.right_inv ∘ h = h := by simp [←Category.assoc]

end Category.hom
namespace Functor
variable (F : C ⥤ D) {X Y} (f : X ⟶[C] Y)

instance SplitMono.map [f.IsSplitMono] : F[f].IsSplitMono where
  left_inv := F.map f.left_inv
  inv_hom_id := by grind

instance SplitEpi.map [f.IsSplitEpi] : F[f].IsSplitEpi where
  right_inv := F.map f.right_inv
  hom_inv_id := by grind

@[simp]
theorem SplitMono.map_inv_hom_id [f.IsSplitMono] :
  F[f.left_inv] ∘ F[f] = 𝟙 _ := by grind

@[simp]
theorem SplitEpi.map_hom_inv_id [f.IsSplitEpi] :
  F[f] ∘ F[f.right_inv] = 𝟙 _ := by grind

end Functor
end Split
section SplitEpiMono


@[ext]
structure SplitMono (X Y) where
  hom : X ⟶[C] Y
  left_inv : Y ⟶[C] X
  inv_hom_id : left_inv ∘ hom = 𝟙 X := by simp

@[ext]
structure SplitEpi (X Y) where
  hom : X ⟶[C] Y
  right_inv : Y ⟶[C] X
  hom_inv_id : hom ∘ right_inv = 𝟙 Y := by simp

instance SplitMono.IsSplitMono (f : SplitMono X Y) : f.hom.IsSplitMono where
  left_inv := f.left_inv
  inv_hom_id := f.inv_hom_id

instance SplitEpi.IsSplitEpi (f : SplitEpi X Y) : f.hom.IsSplitEpi where
  right_inv := f.right_inv
  hom_inv_id := f.hom_inv_id

end SplitEpiMono
