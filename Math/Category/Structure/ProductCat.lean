import MATH.Category.NatTrans.Iso

/-!
# Structure/ProductCat.lean

Product category。

## 定義
- `ProductCat` — product category `C × D`
- `Functor.Prod` / `NatTrans.Prod` — product functor / nat trans

## 定理
### `ProductCat`
- `.fst` / `.snd` — 投影 functor
- `.eval` — evaluation functor `⟦C, D⟧ × C ⥤ D`
- `.swap` — `C × D ≅[Cat] D × C`
- `.assoc` — `(C × D) × E ≅[Cat] C × (D × E)`
-/

namespace CategoryTheory

/-- Product category `C × D`：逐分量的 object、morphism、composition -/
@[simps]
def ProductCat (C D : Category) : Category where
  obj := C.obj × D.obj
  hom X Y := C.hom X.1 Y.1 × D.hom X.2 Y.2
  id X := (𝟙, 𝟙)
  comp f g := (f.1 ○ g.1, f.2 ○ g.2)

notation:50 C:51 "×" D:50 => ProductCat C D

abbrev Category.hom.Prod
  (f : X ⟶[C] Y) (g : A ⟶[D] B) :
  (X, A) ⟶[C × D] (Y, B) := (f, g)

/-- Product functor `F.Prod G : C × C' ⥤ D × D'` -/
def Functor.Prod (F : C ⥤ D) (G : C' ⥤ D') : C × C' ⥤ D × D' where
  obj := fun (x, x') => (F[x], G[x'])
  map := fun (f, f') => (F[f], G[f'])

/-- Product natural transformation `α.Prod β` -/
abbrev NatTrans.Prod {F G : C ⥤ D} {F' G' : C' ⥤ D'}
  (α : F ⇒ G) (β : F' ⇒ G') : F.Prod F' ⇒ G.Prod G' where
  app := fun (x, x') => (α·x, β·x')
  naturality := by simp [Functor.Prod]

namespace ProductCat

def fst : C × D ⥤ C where
  obj X := X.1
  map f := f.1

def snd : C × D ⥤ D where
  obj X := X.2
  map f := f.2

/-- Evaluation functor `eval : ⟦C, D⟧ × C ⥤ D` -/
abbrev eval : ⟦C, D⟧ × C ⥤ D where
  obj p := p.1[p.2]
  map {p q} m := m.1·q.2 ○ p.1[m.2]

/-- `C × D ≅[Cat] D × C` -/
def swap : (C × D) ≅[Cat] D × C where
  hom := { obj := fun (x, y) => (y, x), map := fun (f, g) => (g, f) }
  inv := { obj := fun (x, y) => (y, x), map := fun (f, g) => (g, f) }

/-- `(C × D) × E ≅[Cat] C × (D × E)` -/
def assoc : ((C × D) × E) ≅[Cat] C × (D × E) where
  hom := {
    obj := fun ((x, y), z) => (x, (y, z)),
    map := fun ((f, g), h) => (f, (g, h)) }
  inv := {
    obj := fun (x, (y, z)) => ((x, y), z),
    map := fun (f, (g, h)) => ((f, g), h) }

end ProductCat
end CategoryTheory
