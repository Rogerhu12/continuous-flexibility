import ContinuousFlexibility.Analysis.N07aActualCubicFactors
import ContinuousFlexibility.Analysis.N07aCanonicalUnitCoefficient

/-!
# First jets of the actual cubic difference

Differentiation on the open unit strip retains the precise powers of the
endpoint weight. These identities use the divided atoms already present
in the canonical geometry, without extending them across an endpoint.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

theorem n07a_unitCubic_firstNormal {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g unitStrip) (c : ℝ)
    {p : PolarPoint} (hp : p ∈ unitStrip) :
    mixedDerivative 1 0 (fun q => c * cylinderWeight q.1 ^ 3 * g q) p =
      c * (3 * cylinderWeight p.1 ^ 2 * (1 - 2 * p.1) * g p +
        cylinderWeight p.1 ^ 3 * mixedDerivative 1 0 g p) := by
  have hg' := ((hg.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).comp p.1
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun r => g (r, p.2)) p.1 at hg'
  have hd := (((cylinderWeight_hasDerivAt p.1).fun_pow 3).const_mul c).fun_mul hg'.hasDerivAt
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one]
  rw [hd.deriv]
  norm_num
  ring

theorem n07a_unitCubic_firstAngular {g : PolarPoint → ℝ}
    (c : ℝ) (p : PolarPoint) :
    mixedDerivative 0 1 (fun q => c * cylinderWeight q.1 ^ 3 * g q) p =
      c * cylinderWeight p.1 ^ 3 * mixedDerivative 0 1 g p := by
  simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_one,
    deriv_const_mul_field]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

theorem n07aUnitDifferenceAtom_cubic_firstNormal
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) {p : PolarPoint} (hp : p ∈ unitStrip) :
    mixedDerivative 1 0 (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i)) p =
      (K.right m - K.left m) ^ 6 *
        (3 * cylinderWeight p.1 ^ 2 * (1 - 2 * p.1) *
          n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) p +
        cylinderWeight p.1 ^ 3 *
          mixedDerivative 1 0 (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) p) := by
  rw [n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ)
    (n07aUnitDifferenceAtom_cubic h01 h04 hz hm hlen i) 1 0 hp]
  exact n07a_unitCubic_firstNormal (n07aUnitDifferenceAtom_contDiff href hcur hz m _) _ hp

theorem n07aUnitDifferenceAtom_cubic_firstAngular
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) {p : PolarPoint} (hp : p ∈ unitStrip) :
    mixedDerivative 0 1 (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i)) p =
      (K.right m - K.left m) ^ 6 * cylinderWeight p.1 ^ 3 *
        mixedDerivative 0 1 (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) p := by
  rw [n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ)
    (n07aUnitDifferenceAtom_cubic h01 h04 hz hm hlen i) 0 1 hp]
  exact n07a_unitCubic_firstAngular _ p

theorem n07aUnitDifferenceAtom_principal_jet (z : Parameter S) (m : ℕ)
    (i : Fin 3) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i)) p =
      (K.right m - K.left m) ^ a * mixedDerivative a b
        (fun q => n07aCubicPrincipalField K (liftSectorParameter S C z) m i q -
          n07aCubicPrincipalField K (C.referenceState, 0) m i q)
        (canonicalUnitPoint K m p) := by
  have he : n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i) =
      fun q => n07aCubicPrincipalField K (liftSectorParameter S C z) m i (canonicalUnitPoint K m q) -
        n07aCubicPrincipalField K (C.referenceState, 0) m i (canonicalUnitPoint K m q) := by
    fin_cases i <;> rfl
  rw [he]
  exact n07a_mixedDerivative_radialAffine
    (fun q => n07aCubicPrincipalField K (liftSectorParameter S C z) m i q -
      n07aCubicPrincipalField K (C.referenceState, 0) m i q)
    (K.left m) (K.right m - K.left m) a b p

end ContinuousFlexibility.Analysis
