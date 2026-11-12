import ContinuousFlexibility.Analysis.ReturnCorrectionRelativeDiscriminant
import ContinuousFlexibility.Analysis.ReturnCorrectionSpeedGap
import ContinuousFlexibility.Analysis.N01NegativeOpticalLower

/-!
# A common reference lower bound for the actual corrected field

The optical cutoff and its collar data are kept fixed. The genuine
weighted speed-error estimate supplies one further state radius, before
all components and physical points. On active collars the corrected
discriminant retains one quarter of the original one; off the active
patch it is unchanged. The N01 half-ball estimate then gives a uniform
reference-relative lower bound throughout every negative component.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false

def N04ReturnReferenceDiscriminantBound (D : ReferenceData)
    (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (χ : ℕ → ℝ → ℝ) (base : ℕ) (ε : ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ m p,
    p.1 ∈ Ioo (C.left m) (C.right m) →
    D.w p.1 ^ 2 * (-deriv D.w p.1 / (p.1 * D.w p.1)) / 128 ≤
      (returnCorrectedCoefficients D S C χ z).b p ^ 2 -
        (returnCorrectedCoefficients D S C χ z).a p *
          (returnCorrectedCoefficients D S C χ z).c p

/-- The hypotheses on the cutoff and the original collar discriminant
are supplied by `exists_opticalCorrection_flow`. No cutoff is reselected
and no lower bound on the corrected field is assumed. -/
theorem N01Properties.n04Coordinates_returnCorrected_reference_lower
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (χ : ℕ → ℝ → ℝ) (j : ℕ → ℕ) {J A lam P : ℝ}
    (hJ : 0 < J) (hA : 0 ≤ A) (hlam : 0 < lam) (hP : 0 ≤ P)
    (hcell : ∀ m, Ioo (C.left m) (C.right m) ⊆ D.cells (j m))
    (hcutoff : ∀ m r, |deriv (χ m) r| ≤ J * radialE (D.cellIndex (j m)) ^ A)
    (hcollar : ∀ z ∈ stateNeighborhood S C base ε, ∀ m p,
      p.1 ∈ tsupport (deriv (χ m)) →
      (lam * radialE (D.cellIndex (j m)) ^ (-P) / 2) ^ 2 ≤
        (originalCoefficients D S C z).b p ^ 2 -
          (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) :
    ∃ base' : ℕ, ∃ ε' : ℝ, base ≤ base' ∧ 0 < ε' ∧ ε' ≤ ε / 2 ∧
      N01Properties D T S C base' loss ε' ∧
      N04ReturnReferenceDiscriminantBound D S C χ base' ε' := by
  obtain ⟨parameterLoss, V, K, hV, hK, herror⟩ :=
    hN.returnCorrectedMinusSpeed_error_radial_small hS hT χ j hJ hA hP hcell hcutoff
  obtain ⟨U, hU, hupper⟩ := hN.originalRadialCoefficient_uniform_upper
  let base' := max base (1 + loss + parameterLoss)
  let ε' := min (ε / 2) (min (1 / 2) (min K⁻¹ (lam / (4 * U * V))))
  have hε' : 0 < ε' := lt_min (half_pos hN.2.1)
    (lt_min (by norm_num) (lt_min (inv_pos.mpr hK) (div_pos hlam (by positivity))))
  have hεhalf : ε' ≤ ε / 2 := min_le_left _ _
  have hεold : ε' ≤ ε := hεhalf.trans (half_le_self hN.2.1.le)
  have hεone : ε' ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεK : K * ε' ≤ 1 := by
    have hi : ε' ≤ K⁻¹ := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    exact (mul_le_mul_of_nonneg_left hi hK.le).trans_eq (mul_inv_cancel₀ hK.ne')
  have hεV : V * ε' ≤ lam / (4 * U) := by
    have hi : ε' ≤ lam / (4 * U * V) := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    refine (mul_le_mul_of_nonneg_left hi hV.le).trans_eq ?_
    field_simp [hU.ne', hV.ne']
    <;> ring
  have hb : base ≤ base' := le_max_left _ _
  have hh : 1 + loss + parameterLoss ≤ base' := le_max_right _ _
  refine ⟨base', ε', hb, hε', hεhalf,
    hN.restrict_neighborhood hT hb hε' hεold, ?_⟩
  intro z hz hs m p hp
  have hzold := stateNeighborhood_mono S C hb hεold hz
  have hzhalf := stateNeighborhood_mono S C hb hεhalf hz
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hC.1 m).1.trans hp.1, hp.2.trans (hC.1 m).2.2⟩, mem_univ _⟩
  have hr : 0 < p.1 := hgeom.1.1.trans hpD.1.1
  have hw : 0 < D.w p.1 := hgeom.1.2.2.2.2.1 p.1 hpD.1
  have hreference : 0 < D.w p.1 ^ 2 * (-deriv D.w p.1 / (p.1 * D.w p.1)) / 32 :=
    div_pos (mul_pos (sq_pos_of_pos hw)
      (div_pos (neg_pos.mpr (hC.2.2.2.1 m p.1 hp)) (mul_pos hr hw))) (by norm_num)
  have horiginal := hN.n04Coordinates_original_discriminant_lower hS hT hzhalf hs m hp
  have hdisc : 0 < (originalCoefficients D S C z).b p ^ 2 -
      (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p :=
    hreference.trans_le horiginal
  have ha := hN.originalRadialCoefficient_pos hzold hs hpD
  obtain ⟨haR, hbR, hcR⟩ := originalCoefficients_parity_of_physical hS C z p.1 p.2
  have hreflection := minusCharacteristicSpeed_reflection (originalCoefficients D S C z)
    p.1 p.2 haR hbR hcR
  have hquarter := n04Coordinates_returnCorrectedDiscriminant_quarter
    (D := D) hC.2.2.1 χ z m p hp ha hdisc hreflection (by
      intro hχ
      have hd : 0 < lam * radialE (D.cellIndex (j m)) ^ (-P) / 2 :=
        div_pos (mul_pos hlam (Real.rpow_pos_of_pos (Real.exp_pos _) _)) (by norm_num)
      have hgaplower := characteristic_halfGap_lower_of_discriminant ha
        (hupper z hzold hs p hpD) hd.le
        (hcollar z hzold m p (subset_tsupport _ hχ))
      have hsmall : V * ε' * radialE (D.cellIndex (j m)) ^ (-P) ≤
          (Real.sqrt ((originalCoefficients D S C z).b p ^ 2 -
            (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) /
              (originalCoefficients D S C z).a p) / 2 := by
        calc
          _ ≤ (lam / (4 * U)) * radialE (D.cellIndex (j m)) ^ (-P) :=
            mul_le_mul_of_nonneg_right hεV (Real.rpow_nonneg (Real.exp_pos _).le _)
          _ = ((lam * radialE (D.cellIndex (j m)) ^ (-P) / 2) / U) / 2 := by
            field_simp [hU.ne']
            <;> ring
          _ ≤ _ := div_le_div_of_nonneg_right hgaplower (by norm_num)
      have herr (θ : ℝ) := herror base' hb hh ε' hε'.le hεold hεone hεK
        z hz hs m (p.1, θ) ⟨hp.1.le, hp.2.le⟩
      exact ⟨(herr p.2).trans hsmall, (herr (-p.2)).trans hsmall⟩)
  calc
    _ = (D.w p.1 ^ 2 * (-deriv D.w p.1 / (p.1 * D.w p.1)) / 32) / 4 := by ring
    _ ≤ ((originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p) / 4 :=
      div_le_div_of_nonneg_right horiginal (by norm_num)
    _ ≤ _ := hquarter

end ContinuousFlexibility.Statements
