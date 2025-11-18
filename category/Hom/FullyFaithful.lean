import MATH.Category.Hom.Basic

set_option trace.Meta.synthInstance true
set_option profiler true

namespace category
namespace Functor
variable (F : C ⥤ D)

class Faithful where
  map_injective X Y :
    let f : _ ⟶[Types] _ := @F.map X Y
    f.IsMono

class Full where
  map_surjective X Y :
    let f : _ ⟶[Types] _ := @F.map X Y
    f.IsEpi

class FullyFaithful where
  map_bijective X Y :
    let f : _ ⟶[Types] _ := @F.map X Y
    f.IsIso

-- theorem Faithful.ofMono
--   (_ : ∀ X Y, Category.hom.IsMono (C := Types) (@F.map X Y)) : F.Faithful where
--   map_injective X Y := Types.hom.Injective (@F.map X Y)

-- instance Full.Epi [F.Full] :
--   Category.hom.IsEpi (C := Types) (@F.map X Y) :=
--   Types.hom.Surjective.IsEpi (@F.map X Y) (map_surjective X Y)

-- theorem Full.ofEpi
--   (_ : ∀ X Y, Category.hom.IsEpi (C := Types) (@F.map X Y)) : F.Full where
--   map_surjective X Y := Types.hom.Surjective (@F.map X Y)

-- noncomputable
-- instance FullyFaithful.Iso [F.FullyFaithful] :
--   Category.hom.IsIso (C := Types) (@F.map X Y) :=
--   Types.hom.Bijective.IsIso (@F.map X Y) (map_bijective X Y)

-- theorem FullyFaithful.ofIso
--   (_ : ∀ X Y, Category.hom.IsIso (C := Types) (@F.map X Y)) : F.FullyFaithful where
--   map_bijective X Y := Types.hom.Bijective (@F.map X Y)

-- instance FullyFaithful.full [F.FullyFaithful] : F.Full where
--   map_surjective X Y := (map_bijective X Y).2

-- instance FullyFaithful.faithful [F.FullyFaithful] : F.Faithful where
--   map_injective X Y := (map_bijective X Y).1

-- instance Faithful.ofFullyFaithful [F.Faithful] [F.Full] : F.FullyFaithful where
--   map_bijective X Y := ⟨Faithful.map_injective X Y, Full.map_surjective X Y⟩

-- instance FullyFaithful.id : (𝟙[Cat] C).FullyFaithful where
--   map_bijective X Y := ⟨fun _ => by simp, fun _ => by simp⟩

variable (f : X ⟶[C] Y)

theorem Faithful.reflect_Mono
  [p : F.Faithful] [q : F[f].IsMono] : f.IsMono where
  right_uni {Z g h} _ := by
    have r : F[f] ∘ F[g] = F[f] ∘ F[h] := by grind
    apply q.right_uni at r
    let sd := p.map_injective Z X
    exact Types.hom.injective (@F.map Z X) r

theorem Faithful.reflect_Epi
  [p : F.Faithful] [q : F[f].IsEpi] : f.IsEpi where
  left_uni {Z g h} _ := by
    have r : F[g] ∘ F[f] = F[h] ∘ F[f] := by grind
    apply q.left_uni at r
    let sd := p.map_injective Y Z
    exact Types.hom.injective (@F.map Y Z) r


end Functor
end category
