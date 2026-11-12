import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# The actual principal coefficients belong to the interior jet algebra

Reference jets and genuine current-minus-reference jets give bounded jets
of the same current functions. Affine unit rescaling transfers these
primitive geometric bounds to the original canonical interval.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base : ℕ} {ε : ℝ}

theorem n07a_currentAtom_bounded
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (atom : CanonicalGeometry.Atom) (a b : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ CanonicalGeometry.unitStrip,
      |mixedDerivative a b
        (CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m atom) p| ≤ B := by
  let f := CanonicalGeometry.atom D T S C L K (liftSectorParameter S C z) m atom
  let f₀ := CanonicalGeometry.atom D T S C L K (C.referenceState, 0) m atom
  have hf := (hcur.1 z hz m atom).1
  have hf₀ := (href.1 m atom).1
  obtain ⟨loss, hb⟩ := hcur.2.1
  obtain ⟨B₁, _, hB₁⟩ := hb (a + b)
  obtain ⟨B₀, _, hB₀⟩ := href.2 (a + b)
  let M := B₁ * T.E0 (T.sample (K.cell m)) ^ B₁ *
    T.H (T.sample (K.cell m)) ^ (3 / 4 : ℝ) *
      CanonicalGeometry.parameterGrading S (a + b + loss) z +
        B₀ * T.E0 (T.sample (K.cell m)) ^ B₀
  refine ⟨|M|, abs_nonneg _, ?_⟩
  intro p hp
  have hsum : (fun q => (f q - f₀ q) + f₀ q) = f :=
    funext fun q => sub_add_cancel _ _
  have hderiv : mixedDerivative a b f p =
      mixedDerivative a b (fun q => f q - f₀ q) p + mixedDerivative a b f₀ p := by
    rw [← n07a_mixedDerivative_add_on (isOpen_Ioo.prod isOpen_univ)
      (hf.sub hf₀) hf₀ a b hp, hsum]
  have hdiff := hB₁ z hz m atom ⟨p, hp⟩ a b le_rfl
  have href' := hB₀ m atom p hp a b le_rfl
  change |mixedDerivative a b (fun q => f q - f₀ q) p| ≤ _ at hdiff
  calc
    |mixedDerivative a b f p| ≤
        |mixedDerivative a b (fun q => f q - f₀ q) p| +
          |mixedDerivative a b f₀ p| := by rw [hderiv]; exact abs_add_le _ _
    _ ≤ M := add_le_add hdiff href'
    _ ≤ |M| := le_abs_self _

def n07aPrincipalAtom (i : Fin 5) : CanonicalGeometry.Atom :=
  ![.principalA, .principalB, .principalC, .principalAInverse, .potential] i

def n07aPrincipalField (K : CanonicalData S) (z : AnnularState S × ℝ)
    (m : ℕ) (i : Fin 5) : PolarPoint → ℝ :=
  ![(K.coefficients z m).a, (K.coefficients z m).b, (K.coefficients z m).c,
    fun p => ((K.coefficients z m).a p)⁻¹, K.potential z m] i

theorem n07aPrincipalField_unit (z : AnnularState S × ℝ) (m : ℕ) (i : Fin 5) :
    n07aPrincipalField K z m i ∘ CanonicalGeometry.canonicalUnitPoint K m =
      CanonicalGeometry.atom D T S C L K z m (n07aPrincipalAtom i) := by
  fin_cases i <;> rfl

/-- This coefficient is the chosen actual principal function, not a new
candidate satisfying only the geometric estimates. -/
def n07aCurrentOpenCoefficient
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 5) :
    N07aCanonicalOpenCoefficient S K m :=
  n07aCanonicalOpenCoefficientOfUnit hm
    (n07aPrincipalField K (liftSectorParameter S C z) m i)
    (by rw [n07aPrincipalField_unit]; exact (hcur.1 z hz m (n07aPrincipalAtom i)).1)
    (by
      intro p hp
      have h := (hcur.1 z hz m (n07aPrincipalAtom i)).2 p hp
      simpa only [← n07aPrincipalField_unit, Function.comp_def] using h)
    (by
      intro a b
      rw [n07aPrincipalField_unit]
      exact n07a_currentAtom_bounded href hcur z hz m (n07aPrincipalAtom i) a b)

theorem n07aCurrentOpenCoefficient_value
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 5) :
    (n07aCurrentOpenCoefficient href hcur z hz m hm i).value =
      n07aPrincipalField K (liftSectorParameter S C z) m i := rfl

end ContinuousFlexibility.Analysis
