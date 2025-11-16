import MATH.Category.Hom.Basic

namespace category
namespace Functor
variable (F : C ⥤ D)

class Faithful where
  map_injective X Y : Function.Injective (@F.map X Y)

class Full where
  map_surjective X Y : Function.Surjective (@F.map X Y)

class FullyFaithful where
  map_bijective X Y : Function.Bijective (@F.map X Y)

instance FullyFaithful.full [F.FullyFaithful] : F.Full where
  map_surjective X Y := (map_bijective X Y).2

instance FullyFaithful.faithful [F.FullyFaithful] : F.Faithful where
  map_injective X Y := (map_bijective X Y).1

instance Faithful.of_fully_faithful [F.Faithful] [F.Full] : F.FullyFaithful where
  map_bijective X Y := ⟨Faithful.map_injective X Y, Full.map_surjective X Y⟩

instance FullyFaithful.id : (𝟙[Cat] C).FullyFaithful where
  map_bijective X Y := ⟨fun _ => by simp, fun _ => by simp⟩

end Functor
end category
