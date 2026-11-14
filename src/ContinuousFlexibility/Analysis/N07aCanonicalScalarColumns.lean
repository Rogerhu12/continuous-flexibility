module

public import ContinuousFlexibility.Analysis.N07aGeometryOpenCoefficients

/-!
# The actual canonical scalar columns in the open jet algebra

The three columns are the genuine source transforms of the cutoff
divergence, the ν derivative, and the chosen compatibility source. Their
spatial regularity, periodicity and finite-piece bounds come directly
from the corresponding primitive atoms.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff

namespace N07aCanonicalOpenCoefficient

variable {S : PhysicalSpacesData} {K : CanonicalData S} {m : ℕ}

def constMul (c : ℝ) (χ : N07aCanonicalOpenCoefficient S K m) :
    N07aCanonicalOpenCoefficient S K m where
  value := fun p => c * χ.value p
  smooth := contDiffOn_const.mul χ.smooth
  periodic := by
    intro p hp
    rw [χ.periodic p hp]
  bounded := by
    intro a b
    obtain ⟨B, hB, hb⟩ := χ.bounded a b
    refine ⟨|c| * B, mul_nonneg (abs_nonneg c) hB, ?_⟩
    filter_upwards [hb] with p hp
    rw [spaces_mixedDerivative_const_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hp (abs_nonneg c)

theorem constMul_value (c : ℝ) (χ : N07aCanonicalOpenCoefficient S K m) :
    (constMul c χ).value = fun p => c * χ.value p := rfl

end N07aCanonicalOpenCoefficient

def n07aScalarColumnAtom (i : Fin 3) : CanonicalGeometry.Atom :=
  ![.leftColumn, .nuColumn, .auxiliaryColumn] i

def n07aScalarColumn (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (L : ReturnCorrectionData S) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 3) : PolarPoint → ℝ :=
  ![canonicalSource S K z m (divergenceOperator (L.coefficients z) (fun p => S.chiLeft p.1)),
    canonicalSource S K z m (nuColumnField D S C z),
    canonicalSource S K z m ((S.height (3 / 4 : ℝ)).decode S.psi)] i

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07aScalarColumn_unit (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 3) :
    n07aScalarColumn D S C L K z m i ∘ CanonicalGeometry.canonicalUnitPoint K m =
      CanonicalGeometry.atom D T S C L K z m (n07aScalarColumnAtom i) := by
  fin_cases i <;> rfl

def n07aReferenceScalarOpenCoefficient
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    N07aCanonicalOpenCoefficient S K m :=
  n07aCanonicalOpenCoefficientOfUnit hm
    (n07aScalarColumn D S C L K (C.referenceState, 0) m i)
    (by rw [n07aScalarColumn_unit]; exact (hJ.1 m (n07aScalarColumnAtom i)).1)
    (by
      intro p hp
      have h := (hJ.1 m (n07aScalarColumnAtom i)).2 p hp
      simpa only [← n07aScalarColumn_unit, Function.comp_apply] using h)
    (by
      intro a b
      rw [n07aScalarColumn_unit]
      obtain ⟨B, _, hb⟩ := hJ.2 (a + b)
      refine ⟨|B * T.E0 (T.sample (K.cell m)) ^ B|, abs_nonneg _, ?_⟩
      intro p hp
      exact (hb m (n07aScalarColumnAtom i) p hp a b le_rfl).trans (le_abs_self _))

theorem n07aReferenceScalarOpenCoefficient_value
    (hJ : CanonicalGeometry.ReferenceJets D T S C L K)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    (n07aReferenceScalarOpenCoefficient hJ m hm i).value =
      n07aScalarColumn D S C L K (C.referenceState, 0) m i := rfl

def n07aCurrentScalarOpenCoefficient
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    N07aCanonicalOpenCoefficient S K m :=
  n07aCanonicalOpenCoefficientOfUnit hm
    (n07aScalarColumn D S C L K (liftSectorParameter S C z) m i)
    (by rw [n07aScalarColumn_unit]; exact (hcur.1 z hz m (n07aScalarColumnAtom i)).1)
    (by
      intro p hp
      have h := (hcur.1 z hz m (n07aScalarColumnAtom i)).2 p hp
      simpa only [← n07aScalarColumn_unit, Function.comp_apply] using h)
    (by
      intro a b
      rw [n07aScalarColumn_unit]
      exact n07a_currentAtom_bounded href hcur z hz m (n07aScalarColumnAtom i) a b)

theorem n07aCurrentScalarOpenCoefficient_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    (n07aCurrentScalarOpenCoefficient href hcur z hz m hm i).value =
      n07aScalarColumn D S C L K (liftSectorParameter S C z) m i := rfl

end ContinuousFlexibility.Analysis
