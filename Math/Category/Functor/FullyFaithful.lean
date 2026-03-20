import MATH.Category.Structure.Types

/-!
# Functor/FullyFaithful.lean

Full、faithful、fully faithful functor。

## 定義
- `Functor.Full` — map 為 surjection
- `Functor.Faithful` — map 為 injection
- `Functor.FullyFaithful` — map 為 bijection

## 定理
### `Functor`
- `.preimage` — full functor 的 preimage
- `.map_preimage_id` — `F[F.preimage f] = f`
- `.map_injective_iff` — `F[g] = F[h] ↔ g = h`
- `.preimage_map_id` — `F.preimage F[f] = f`
-/

namespace CategoryTheory
namespace Functor
open Function
variable {F : C ⥤ D}

section Full

/-- Full functor：`F.map` 是 surjection -/
class Full where
  map_surjective {X Y} : Surjective (@F.map X Y)

lemma map_surjective [F.Full] {X Y} : Surjective (@F.map X Y) :=
  Full.map_surjective

/-- Preimage：`(F[X] ⟶ F[Y]) → (X ⟶ Y)` -/
noncomputable
def preimage [F.Full] : (F[X] ⟶ F[Y]) → (X ⟶ Y) :=
  surjInv F.map_surjective

/-- `F[F.preimage f] = f` -/
@[simp]
lemma map_preimage_id [F.Full] (f : F[X] ⟶ F[Y]) :
  F[F.preimage f] = f := (F.map_surjective f).choose_spec

end Full

section Faithful

/-- Faithful functor：`F.map` 是 injection -/
class Faithful where
  map_injective {X Y} : Injective (@F.map X Y)

lemma map_injective [F.Faithful] {X Y} : Injective (@F.map X Y) :=
  Faithful.map_injective

/-- `F[g] = F[h] ↔ g = h` -/
lemma map_injective_iff [F.Faithful] {g h : X ⟶ Y} :
  F[g] = F[h] ↔ g = h :=
  ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

end Faithful

section FullyFaithful

/-- Fully faithful functor：`F.map` 是 bijection -/
class FullyFaithful where
  map_bijective {X Y} : Bijective (@F.map X Y)

lemma map_bijective [F.FullyFaithful] {X Y} : Bijective (@F.map X Y) :=
  FullyFaithful.map_bijective

instance FullyFaithful.full [F.FullyFaithful] : F.Full where
  map_surjective := F.map_bijective.2

instance FullyFaithful.faithful [F.FullyFaithful] : F.Faithful where
  map_injective {_ _} := F.map_bijective.1

noncomputable
instance FullyFaithful.ofFullyFaithful [F.Faithful] [F.Full] : F.FullyFaithful where
  map_bijective := ⟨F.map_injective, F.map_surjective⟩

instance FullyFaithful.id : (𝟙[Cat] C).FullyFaithful where
  map_bijective {_ _} := ⟨fun _ => by simp, fun _ => by simp⟩

/-- `F.preimage F[f] = f` -/
lemma preimage_map_id [F.FullyFaithful] :
  F.preimage F[f] = f := F.map_injective (F.map_surjective F[f]).choose_spec

end FullyFaithful
end Functor
end CategoryTheory
