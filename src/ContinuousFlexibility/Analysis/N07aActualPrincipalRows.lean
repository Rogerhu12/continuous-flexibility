import ContinuousFlexibility.Analysis.N06PrincipalJetAlgebra
import ContinuousFlexibility.Analysis.N07aCubicMatrixRows
import ContinuousFlexibility.Analysis.N07aActualCoefficientBlocks

/-!
# Matrix rows of the actual principal difference

The original current-minus-reference multipliers and their first jets
retain the exact cubic endpoint gain after affine normalization. A
single statement covers cosine and sine multiplication entries.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

def n07aActualPrincipalDifference
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    N07aCanonicalOpenCoefficient S K m :=
  ![(n07aCurrentOpenCoefficient href hcur z hz m hm 0).sub
      (n07aReferenceOpenCoefficient href m hm 0),
    (n07aCurrentOpenCoefficient href hcur z hz m hm 1).sub
      (n07aReferenceOpenCoefficient href m hm 1),
    (n07aCurrentOpenCoefficient href hcur z hz m hm 2).sub
      (n07aReferenceOpenCoefficient href m hm 2)] i

theorem n07aActualPrincipalDifference_value
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) :
    (n07aActualPrincipalDifference href hcur z hz m hm i).value =
      fun q => n07aCubicPrincipalField K (liftSectorParameter S C z) m i q -
        n07aCubicPrincipalField K (C.referenceState, 0) m i q := by
  fin_cases i <;> rfl

theorem n07aCanonicalUnitPoint_intervalMap (K : CanonicalData S) (m : ℕ) (x θ : ℝ) :
    canonicalUnitPoint K m (x, θ) = (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) := by
  apply Prod.ext
  · exact add_comm _ _
  · rfl

theorem n07aActualPrincipalDifference_unit_jet
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    (z : Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (m : ℕ) (hm : K.left m < K.right m) (i : Fin 3) (a b : ℕ) (x θ : ℝ) :
    mixedDerivative a b (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicPrincipalAtom i)) (x, θ) =
      (K.right m - K.left m) ^ a *
        ((n07aActualPrincipalDifference href hcur z hz m hm i).jet a b).value
          (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) := by
  rw [n07aUnitDifferenceAtom_principal_jet, n07aCanonicalUnitPoint_intervalMap]
  change _ = (K.right m - K.left m) ^ a *
    mixedDerivative a b (n07aActualPrincipalDifference href hcur z hz m hm i).value _
  rw [n07aActualPrincipalDifference_value]

theorem n07a_actualPrincipal_value_matrix
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) (sine : Bool) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (l j : ℕ) :
    n07aTrigMatrixEntry sine
      (fun θ => (n07aActualPrincipalDifference href hcur z hz m hlen i).value
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j =
      (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 *
        n07aTrigMatrixEntry sine
          (fun θ => n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) (x, θ)) l j := by
  have he : (fun θ => (n07aActualPrincipalDifference href hcur z hz m hlen i).value
      (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) =
      fun θ => (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 *
        n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) (x, θ) := by
    funext θ
    have h := n07aActualPrincipalDifference_unit_jet href hcur z hz m hlen i 0 0 x θ
    simp only [N07aCanonicalOpenCoefficient.jet, spaces_mixedDerivative_zero,
      pow_zero, one_mul] at h
    rw [← h]
    exact n07aUnitDifferenceAtom_cubic h01 h04 hz hm hlen i ⟨hx, mem_univ _⟩
  rw [he, n07aTrigMatrixEntry_const_mul]

theorem n07a_actualPrincipal_angular_matrix
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) (sine : Bool) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (l j : ℕ) :
    n07aTrigMatrixEntry sine
      (fun θ => ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 0 1).value
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j =
      (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 *
        n07aTrigMatrixEntry sine
          (n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) 0 1 x) l j := by
  have he : (fun θ => ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 0 1).value
      (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) =
      fun θ => (K.right m - K.left m) ^ 6 * cylinderWeight x ^ 3 *
        n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) 0 1 x θ := by
    funext θ
    have h := n07aActualPrincipalDifference_unit_jet href hcur z hz m hlen i 0 1 x θ
    simp only [pow_zero, one_mul] at h
    rw [← h]
    exact n07aUnitDifferenceAtom_cubic_firstAngular h01 h04 hz hm hlen i ⟨hx, mem_univ _⟩
  rw [he, n07aTrigMatrixEntry_const_mul]

theorem n07a_actualPrincipal_normal_matrix_bound
    (h01 : N01Properties D T S C base loss ε)
    (h04 : N04Properties D T S C L K base loss ε)
    (href : ReferenceJets D T S C L K) (hcur : CurrentJets D T S C L K base ε)
    {z : Parameter S} (hz : z ∈ sectorNeighborhood S base ε ε)
    {m : ℕ} (hm : K.positive m = true) (hlen : K.left m < K.right m)
    (i : Fin 3) (sine : Bool) {x κ M : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hM : 0 ≤ M)
    (l j : ℕ)
    (h₀ : |κ * n07aTrigMatrixEntry sine
      (fun θ => n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i) (x, θ)) l j| ≤ M)
    (h₁ : |κ * n07aTrigMatrixEntry sine
      (n07aUnitJetRow (n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)) 1 0 x) l j| ≤ M) :
    |κ * n07aTrigMatrixEntry sine
      (fun θ => ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 1 0).value
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| ≤
      4 * (K.right m - K.left m) ^ 5 * cylinderWeight x ^ 2 * M := by
  let g := n07aUnitDifferenceAtom D T S C L K z m (n07aCubicDividedAtom i)
  have hg := n07aUnitDifferenceAtom_contDiff href hcur hz m (n07aCubicDividedAtom i)
  have hb := n07a_unitCubic_firstNormal_matrix_bound sine hg
    (show 0 ≤ (K.right m - K.left m) ^ 6 by positivity) hM hx l j h₀ h₁
  have he : (fun θ => mixedDerivative 1 0
      (fun q => (K.right m - K.left m) ^ 6 * cylinderWeight q.1 ^ 3 * g q) (x, θ)) =
      fun θ => (K.right m - K.left m) *
        ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 1 0).value
          (n07aIntervalUnitMap (K.left m) (K.right m) x, θ) := by
    funext θ
    rw [← n07a_mixedDerivative_eqOn (isOpen_Ioo.prod isOpen_univ)
      (n07aUnitDifferenceAtom_cubic h01 h04 hz hm hlen i) 1 0 ⟨hx, mem_univ _⟩,
      n07aActualPrincipalDifference_unit_jet href hcur z hz m hlen i 1 0 x θ, pow_one]
  rw [he, n07aTrigMatrixEntry_const_mul] at hb
  have hlenpos : 0 < K.right m - K.left m := sub_pos.mpr hlen
  have hleft : |κ * ((K.right m - K.left m) * n07aTrigMatrixEntry sine
      (fun θ => ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 1 0).value
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j)| =
      (K.right m - K.left m) * |κ * n07aTrigMatrixEntry sine
      (fun θ => ((n07aActualPrincipalDifference href hcur z hz m hlen i).jet 1 0).value
        (n07aIntervalUnitMap (K.left m) (K.right m) x, θ)) l j| := by
    rw [mul_left_comm κ (K.right m - K.left m),
      abs_mul, abs_of_pos hlenpos]
  rw [hleft] at hb
  apply (mul_le_mul_iff_right₀ hlenpos).mp
  exact hb.trans_eq (by ring)

end ContinuousFlexibility.Analysis
