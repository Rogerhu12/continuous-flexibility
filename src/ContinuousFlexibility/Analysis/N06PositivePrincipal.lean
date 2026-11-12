import ContinuousFlexibility.Analysis.N05ReferenceSymbols
import ContinuousFlexibility.Analysis.N06NuFiniteJets
import ContinuousFlexibility.Analysis.NeighborhoodProfileBounds
import ContinuousFlexibility.Scalar.TypeCorrection

/-!
# Positivity of the actual corrected principal form

The original N01 denominator bounds make the radial coefficient positive
throughout the original neighbourhood.  For the determinant on the
positive region, the compact border support supplies a genuine uniform
smaller neighbourhood: the actual profile there is `w exp (nu chi)`.
No derivative-ratio condition is read into the N01 specification.

The final algebraic lemmas apply to actual Frechet coordinate partials,
so a nonzero forward Jacobian gives two strictly positive coordinate
responses.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Completing the square for a genuine positive two-dimensional
symmetric principal form. -/
theorem n06_positive_principal_quadratic {a b c x y : ℝ}
    (ha : 0 < a) (hdet : 0 < a * c - b ^ 2) (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  have he : a * (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) =
      (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by ring
  have hs : 0 < (a * x + b * y) ^ 2 + (a * c - b ^ 2) * y ^ 2 := by
    by_cases hy : y = 0
    · have hx : x ≠ 0 := hxy.resolve_right (not_not.mpr hy)
      simpa only [hy, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using
        sq_pos_of_ne_zero (mul_ne_zero ha.ne' hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hdet (sq_pos_of_ne_zero hy))
  exact (mul_pos_iff_of_pos_left ha).mp (he.symm ▸ hs)

theorem n06_principalPair_pos {A : SymmetricCoefficients}
    {f : PolarPoint → ℝ} {p : PolarPoint}
    (ha : 0 < A.a p) (hdet : 0 < A.a p * A.c p - A.b p ^ 2)
    (hf : radialPartial f p ≠ 0 ∨ angularPartial f p ≠ 0) :
    0 < n05PrincipalPair A f f p := by
  have h := n06_positive_principal_quadratic ha hdet hf
  convert h using 1 <;> simp only [n05PrincipalPair] <;> ring

/-- Both coordinate differentials of an actual local diffeomorphism
are nonzero, and hence have positive principal response. -/
theorem n06_principalPair_coordinates_pos {A : SymmetricCoefficients}
    {Ψ : PolarPoint → PolarPoint} {p : PolarPoint}
    (ha : 0 < A.a p) (hdet : 0 < A.a p * A.c p - A.b p ^ 2)
    (hΨ : DifferentiableAt ℝ Ψ p) (hJ : planeJacobian Ψ p ≠ 0) :
    0 < n05PrincipalPair A (fun q => (Ψ q).1) (fun q => (Ψ q).1) p ∧
      0 < n05PrincipalPair A (fun q => (Ψ q).2) (fun q => (Ψ q).2) p := by
  have hj := n05_planeJacobian_eq_partials hΨ
  have hfirst : radialPartial (fun q => (Ψ q).1) p ≠ 0 ∨
      angularPartial (fun q => (Ψ q).1) p ≠ 0 := by
    by_cases hr : radialPartial (fun q => (Ψ q).1) p = 0
    · right
      intro ht
      apply hJ
      simp only [hr, ht, zero_mul, sub_zero] at hj
      exact hj
    · exact Or.inl hr
  have hsecond : radialPartial (fun q => (Ψ q).2) p ≠ 0 ∨
      angularPartial (fun q => (Ψ q).2) p ≠ 0 := by
    by_cases hr : radialPartial (fun q => (Ψ q).2) p = 0
    · right
      intro ht
      apply hJ
      simp only [hr, ht, mul_zero, sub_zero] at hj
      exact hj
    · exact Or.inl hr
  exact ⟨n06_principalPair_pos ha hdet hfirst, n06_principalPair_pos ha hdet hsecond⟩

/-- The original compact border gives a uniform radius preserving the
positive profile derivative.  This is a quantitative construction from
the true cutoff, not a new type-stability hypothesis. -/
theorem n06_trueBorder_positive_slope_radius {D : ReferenceData}
    (hw : ContDiff ℝ ∞ D.w) (hborder : RadialTrueBorder D) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν : ℝ, |ν| < δ → ∀ r : ℝ,
      0 < deriv D.w r → 0 < deriv D.w r + D.w r * (ν * deriv D.chi r) := by
  have hK : IsCompact (tsupport D.chi) := hborder.2.1
  have hratio : ContinuousOn
      (fun r => D.w r * deriv D.chi r / deriv D.w r) (tsupport D.chi) :=
    (hw.continuous.mul (hborder.1.continuous_deriv (by simp))).continuousOn.div
      (hw.continuous_deriv (by simp)).continuousOn
      (fun r hr => (hborder.2.2.1 hr).2.ne')
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn hratio
  let B : ℝ := max 1 B₀
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hproduct (r : ℝ) (hr : 0 < deriv D.w r) :
      |D.w r * deriv D.chi r| ≤ B * deriv D.w r := by
    by_cases hmem : r ∈ tsupport D.chi
    · have hb0 : |D.w r * deriv D.chi r / deriv D.w r| ≤ B₀ := by
        simpa only [Real.norm_eq_abs] using hB₀ r hmem
      have hratio' : |D.w r * deriv D.chi r / deriv D.w r| ≤ B :=
        hb0.trans (le_max_right _ _)
      rw [abs_div, abs_of_pos hr] at hratio'
      exact (div_le_iff₀ hr).mp hratio'
    · rw [deriv_of_notMem_tsupport hmem, mul_zero, abs_zero]
      exact mul_nonneg hB.le hr.le
  refine ⟨(2 * B)⁻¹, inv_pos.mpr (mul_pos (by norm_num) hB), ?_⟩
  intro ν hν r hr
  have hsmall : |ν| * B < (1 / 2 : ℝ) := by
    have hh := mul_lt_mul_of_pos_right hν hB
    have he : (2 * B)⁻¹ * B = (1 / 2 : ℝ) := by field_simp [hB.ne']
    exact he ▸ hh
  have habs : |D.w r * (ν * deriv D.chi r)| < (1 / 2 : ℝ) * deriv D.w r := by
    calc
      |D.w r * (ν * deriv D.chi r)| = |ν| * |D.w r * deriv D.chi r| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |ν| * (B * deriv D.w r) :=
        mul_le_mul_of_nonneg_left (hproduct r hr) (abs_nonneg ν)
      _ = (|ν| * B) * deriv D.w r := by ring
      _ < (1 / 2 : ℝ) * deriv D.w r := mul_lt_mul_of_pos_right hsmall hr
  have hneg := neg_abs_le (D.w r * (ν * deriv D.chi r))
  linarith only [habs, hneg, hr]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- The true profile derivative stays positive throughout the positive
region after shrinking only the actual scalar profile parameter. -/
theorem n06_stateProfile_positive_slope_radius
    (h01 : N01Properties D T S C base loss ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : AnnularState S, |x.2.1| < δ →
      ∀ r : ℝ, 0 < deriv D.w r → 0 < deriv (stateProfile D S C x) r := by
  have hw : ContDiff ℝ ∞ D.w := h01.1.1.choose_spec.1.2.2.1.1
  have hborder : RadialTrueBorder D := h01.1.2.2.2.1
  obtain ⟨δ, hδ, hpositive⟩ := n06_trueBorder_positive_slope_radius hw hborder
  refine ⟨δ, hδ, ?_⟩
  intro x hx r hr
  rw [(n06_stateProfile_jets_on_positive hw hborder.1 h01.2.2.2.1 x hr).2]
  exact mul_pos (hpositive x.2.1 hx r hr) (Real.exp_pos _)

private theorem n06_positivePrincipal_denominators
    (h01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < stateProfile D S C z.1 p.1 ∧
      0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) ∧
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hb := h01.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hw : 0 < D.w p.1 := h01.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hprofile : 0 < stateProfile D S C z.1 p.1 :=
    (div_pos_iff_of_pos_right hw).mp (lt_of_lt_of_le (by norm_num) hb.1)
  exact ⟨hprofile,
    (div_pos_iff_of_pos_right hprofile).mp (lt_of_lt_of_le (by norm_num) hb.2.2.1),
    lt_of_lt_of_le (by norm_num) hb.2.2.2.2.1⟩

/-- Positivity of the true corrected radial coefficient already holds
on the original N01 neighbourhood, on either type region. -/
theorem n06_corrected_radialCoefficient_pos
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < (L.coefficients z).a p := by
  have hd := n06_positivePrincipal_denominators h01 hz hs hp
  rw [h03.1 z hz hs p]
  exact mul_pos hd.2.1 (inverseDThreeHalves_pos _ hd.2.2)

/-- The actual positive-region determinant has its literal profile
formula.  No positivity of the perturbed derivative is assumed here. -/
theorem n06_corrected_determinant_eq_on_positive
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (hpos : 0 < deriv D.w p.1) :
    (L.coefficients z).a p * (L.coefficients z).c p - (L.coefficients z).b p ^ 2 =
      (stateProfile D S C z.1 p.1 * deriv (stateProfile D S C z.1) p.1 / p.1) /
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 := by
  have hd := n06_positivePrincipal_denominators h01 hz hs hp
  have hbc := h03.2.1 z hz hs p hp hpos
  rw [h03.1 z hz hs p, hbc.1.eq_of_nhds, hbc.2.eq_of_nhds]
  exact polar_corrected_determinant (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT h01 z.1).differentiable (by simp) p.1)
    (h01.1.1.choose_spec.1.1.trans hp.1.1).ne' hd.2.2 hd.2.1.ne'

/-- A scalar radius obtained from the original data makes the actual
corrected principal form positive on the entire positive region. -/
theorem n06_corrected_positivePrincipal_radius
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ stateNeighborhood S C base ε,
      stateSector S z.1 → |z.1.2.1| < δ → ∀ p ∈ annularOpen D,
        0 < deriv D.w p.1 → 0 < (L.coefficients z).a p ∧
          0 < (L.coefficients z).a p * (L.coefficients z).c p -
            (L.coefficients z).b p ^ 2 := by
  obtain ⟨δ, hδ, hpositive⟩ := n06_stateProfile_positive_slope_radius h01
  refine ⟨δ, hδ, ?_⟩
  intro z hz hs hν p hp hpos
  have hd := n06_positivePrincipal_denominators h01 hz hs hp
  refine ⟨n06_corrected_radialCoefficient_pos h01 h03 hz hs hp, ?_⟩
  rw [n06_corrected_determinant_eq_on_positive hT hS h01 h03 hz hs hp hpos]
  exact div_pos
    (div_pos (mul_pos hd.1 (hpositive z.1 hν p.1 hpos))
      (h01.1.1.choose_spec.1.1.trans hp.1.1))
    (sq_pos_of_pos hd.2.2)

private theorem n06_positivePrincipal_scalar_small
    (hνzero : C.referenceState.2.1 = 0) {δ : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base δ) :
    |z.1.2.1| < δ := by
  have hνeq : (z.1 - C.referenceState).2.1 = z.1.2.1 := by
    change z.1.2.1 - C.referenceState.2.1 = z.1.2.1
    rw [hνzero, sub_zero]
  exact ((congrArg abs hνeq).symm.trans_le
    (neighborhoodStateGrading_controls_le S base (z.1 - C.referenceState)).1).trans_lt hz.1

private theorem n06_positivePrincipal_neighborhood_mem
    {δ : ℝ} {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base (min ε δ)) :
    z ∈ stateNeighborhood S C base ε :=
  ⟨hz.1.trans_le (min_le_left _ _), hz.2.trans_le (min_le_left _ _)⟩

private theorem n06_positivePrincipal_shrink
    {P : AnnularState S × ℝ → Prop} (hε : 0 < ε)
    (hνzero : C.referenceState.2.1 = 0)
    (hdata : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ stateNeighborhood S C base ε,
      stateSector S z.1 → |z.1.2.1| < δ → P z) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 → P z := by
  obtain ⟨δ, hδ, hP⟩ := hdata
  refine ⟨min ε δ, lt_min hε hδ, min_le_left _ _, ?_⟩
  intro z hz hs
  exact hP z (n06_positivePrincipal_neighborhood_mem hz) hs
    ((n06_positivePrincipal_scalar_small hνzero hz).trans_le (min_le_right _ _))

/-- The scalar radius is realized by an actual smaller neighbourhood.
Only the original data occur in the hypotheses. -/
theorem n06_exists_positivePrincipal_neighborhood
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h01 : N01Properties D T S C base loss ε)
    (h03 : N03Properties D T S C R L base ε) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      ∀ z ∈ stateNeighborhood S C base ε', stateSector S z.1 →
        ∀ p ∈ annularOpen D, 0 < deriv D.w p.1 →
          0 < (L.coefficients z).a p ∧
            0 < (L.coefficients z).a p * (L.coefficients z).c p -
              (L.coefficients z).b p ^ 2 := by
  exact n06_positivePrincipal_shrink h01.2.1 h01.2.2.1.2.2.1
    (n06_corrected_positivePrincipal_radius hT hS h01 h03)

end ContinuousFlexibility.Statements
