import MATH.category.Hom

namespace category


def Full (F : C ⥤ D) :=
  ∀ X Y, Function.Surjective (@F.map X Y)

def Faithful (F : C ⥤ D) :=
  ∀ X Y, Function.Injective (@F.map X Y)

def FullyFaithful (F : C ⥤ D) :=
  ∀ X Y, Function.Bijective (@F.map X Y)
