import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Logic.Function.Basic

-- import Mathlib.Data.NNReal.Defs
-- import Mathlib.LinearAlgebra.TensorProduct.Basic
-- import Mathlib.Algebra.Algebra.Hom

-- open TensorProduct

-- class NormedField (F : Type u) [Field F] [Algebra ℝ F] where
--   norm : F → NNReal
--   zero : norm x = 0 ↔ x = 0
--   norm_mul {r : ℝ} {x : F} : norm (r • x) = r * norm x
--   norm_le : norm (x + y) ≤ norm x + norm y
-- notation "|" x "|" => NormedField.norm x

-- class NormedSpace (F : Type u) (M : Type v)
--   [Field F] [Algebra ℝ F] [NormedField F] [AddCommGroup M]
--   extends Module F M where
--   norm : M → NNReal
--   zero : norm x = 0 ↔ x = 0
--   norm_mul {r : F} {x : M} : norm (r • x) = |r| * norm x
--   norm_le : norm (x + y) ≤ norm x + norm y
-- notation "‖" x "‖" => NormedField.norm x

-- class StarAlgebra (R : Type u) (A : Type v)
--   [CommRing R] [Ring A] extends Algebra R A where
--   conj : AlgHom R A A
--   inv : conj ∘ conj = id

-- def dual {F : Type u} (V : Type v) [Field F]
--   [s : StarAlgebra ℝ F] [AddCommGroup V] [m : Module F V] :
--   Module F V :=
--   Module.compHom (R := F) V s.conj
-- notation V "*" => dual V 𝒫
def sdf := ZFSet ⊕ ZFSet

#print axioms ZFSet.sUnion
#print axioms Cardinal.cantor
#print axioms Function.cantor_injective
