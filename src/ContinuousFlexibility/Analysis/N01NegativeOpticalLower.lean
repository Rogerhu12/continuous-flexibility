import ContinuousFlexibility.Analysis.N04bStateProfileType

/-!
# A common reference lower bound for the negative optical radicand

The N01 flow tower forces positivity along every affine state line on
the original state ball. Evaluating that same affine radicand at twice
the state displacement gives a reference-relative lower bound on the
half-radius ball. The radius is fixed before the negative component and
the physical point; no componentwise infimum of state radii is used.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

local instance n04CoordinatesOpticalLowerStateSMul (S : PhysicalSpacesData) :
    SMul ℝ (AnnularState S) := Prod.instSMul

/-- The optical radicand itself, before taking a square root, is affine
in the logarithmic perturbation parameter. -/
theorem n04Coordinates_opticalLogPerturbation_radicand
    {w f : ℝ → ℝ} {t r : ℝ}
    (hw : DifferentiableAt ℝ w r) (hf : DifferentiableAt ℝ f r)
    (hr : r ≠ 0) (hwr : w r ≠ 0) :
    -deriv (opticalLogPerturbation w f t) r /
        (r * opticalLogPerturbation w f t r) =
      -deriv w r / (r * w r) + (-deriv f r / r) * t := by
  have hd := (hw.hasDerivAt.mul ((hf.hasDerivAt.const_mul t).exp)).deriv
  change deriv (fun s => w s * Real.exp (t * f s)) r = _ at hd
  change -deriv (fun s => w s * Real.exp (t * f s)) r /
    (r * (w r * Real.exp (t * f r))) = _
  rw [hd]
  field_simp [hr, hwr, (Real.exp_pos (t * f r)).ne']
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

/-- One shrinking of the state ball works simultaneously on every
negative component, including arbitrarily close to its two roots. -/
theorem N01Properties.n04Coordinates_stateProfile_opticalRadicand_half
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {x : AnnularState S}
    (hx : stateGrading S base (x - C.referenceState) < ε / 2)
    (m : ℕ) {r : ℝ} (hr : r ∈ Ioo (C.left m) (C.right m)) :
    (-deriv D.w r / (r * D.w r)) / 2 <
      -deriv (stateProfile D S C x) r / (r * stateProfile D S C x r) := by
  let v : AnnularState S := x - C.referenceState
  have ht : |(2 : ℝ)| * stateGrading S base v < ε := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change 2 * stateGrading S base (x - C.referenceState) < ε
    linarith only [hx]
  have hdouble := hN.n04b_stateLine_radicand_pos hS hT v m hr ht
  have hline : C.referenceState + (1 : ℝ) • v = x := by
    dsimp only [v]
    rw [one_smul]
    abel
  have hp : stateProfile D S C x =
      opticalLogPerturbation D.w (n04bStateLogExponent D S C v) 1 := by
    simpa only [hline] using n04b_stateProfile_reference_line hN.2.2.1 v 1
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hrD : r ∈ Ioo D.a D.b :=
    ⟨(hcontrol.1 m).1.trans hr.1, hr.2.trans (hcontrol.1 m).2.2⟩
  have heq := n04Coordinates_opticalLogPerturbation_radicand
    (t := (1 : ℝ)) (hgeom.1.2.2.1.1.differentiable (by simp) r)
    ((hN.n04b_stateLogExponent_contDiffAt v hrD).differentiableAt (by simp))
    (hgeom.1.1.trans hrD.1).ne' (hgeom.1.2.2.2.2.1 r hrD).ne'
  rw [hp, heq]
  linarith only [hdouble]

private theorem n04Coordinates_discriminant_reference_bound
    {w P d q Δ : ℝ} (hw : 0 < w) (hd : 0 ≤ d) (hΔ : 0 < Δ)
    (hΔupper : Δ ≤ 2) (hP : w / 2 ≤ P) (hq : d / 2 ≤ q) :
    w ^ 2 * d / 32 ≤ P ^ 2 * q / Δ ^ 2 := by
  have hP2 : w ^ 2 / 4 ≤ P ^ 2 := by
    have h := pow_le_pow_left₀ (div_pos hw (by norm_num : (0 : ℝ) < 2)).le hP 2
    nlinarith only [h]
  have hΔ2 : Δ ^ 2 ≤ 4 := by
    simpa using pow_le_pow_left₀ hΔ.le hΔupper 2
  have hnum : (w ^ 2 / 4) * (d / 2) ≤ P ^ 2 * q :=
    mul_le_mul hP2 hq (div_nonneg hd (by norm_num)) (sq_nonneg P)
  apply (le_div_iff₀ (sq_pos_of_pos hΔ)).mpr
  calc
    (w ^ 2 * d / 32) * Δ ^ 2 ≤ (w ^ 2 * d / 32) * 4 :=
      mul_le_mul_of_nonneg_left hΔ2 (by positivity)
    _ = (w ^ 2 / 4) * (d / 2) := by ring
    _ ≤ P ^ 2 * q := hnum

/-- The actual original discriminant has a positive reference lower
bound on the same half-radius neighborhood, for every residual parameter
and every angle in the sector. Compact interior lower bounds therefore
depend only on the reference component. -/
theorem N01Properties.n04Coordinates_original_discriminant_lower
    (hN : N01Properties D T S C base loss ε)
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base (ε / 2))
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p.1 ∈ Ioo (C.left m) (C.right m)) :
    D.w p.1 ^ 2 * (-deriv D.w p.1 / (p.1 * D.w p.1)) / 32 ≤
      (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p := by
  obtain ⟨_, hgeom⟩ := hN.1.1
  have hcontrol : controlGeometryConditions D S C := hN.2.2.2.1
  have hpD : p ∈ annularOpen D :=
    ⟨⟨(hcontrol.1 m).1.trans hp.1, hp.2.trans (hcontrol.1 m).2.2⟩, mem_univ _⟩
  have hr : 0 < p.1 := hgeom.1.1.trans hpD.1.1
  have hw : 0 < D.w p.1 := hgeom.1.2.2.2.2.1 p.1 hpD.1
  have hP : 0 < stateProfile D S C z.1 p.1 := mul_pos hw (Real.exp_pos _)
  have hzold : z ∈ stateNeighborhood S C base ε :=
    stateNeighborhood_mono S C le_rfl (half_le_self hN.2.1.le) hz
  have hg := hN.2.2.2.2.2.2.2.2.2.1 z hzold hs p hpD
  have hPbound : D.w p.1 / 2 ≤ stateProfile D S C z.1 p.1 := by
    have h := (le_div_iff₀ hw).mp hg.1
    linarith only [h]
  have hQ : 0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
      (heightRadial (stateHeight D S C z) p)
      (angularPartial (heightAngular (stateHeight D S C z)) p) :=
    (div_pos_iff_of_pos_right hP).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7 / 8) hg.2.2.1)
  have hΔ : 0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hg.2.2.2.2.1
  have hΔupper : polarDiscriminant (stateProfile D S C z.1)
      (stateHeight D S C z) p ≤ 2 :=
    hg.2.2.2.2.2.trans (by norm_num)
  have href : 0 ≤ -deriv D.w p.1 / (p.1 * D.w p.1) :=
    (div_pos (neg_pos.mpr (hcontrol.2.2.2.1 m p.1 hp)) (mul_pos hr hw)).le
  have hopt := (hN.n04Coordinates_stateProfile_opticalRadicand_half hS hT hz.1 m hp).le
  have hbound := n04Coordinates_discriminant_reference_bound hw href hΔ hΔupper
    hPbound hopt
  have hdet := polar_corrected_determinant (stateHeight D S C z)
    ((contDiff_stateProfile_of_n01 hS hT hN z.1).differentiable (by simp) p.1)
    hr.ne' hΔ hQ.ne'
  have heq : (originalCoefficients D S C z).b p ^ 2 -
        (originalCoefficients D S C z).a p * (originalCoefficients D S C z).c p =
      stateProfile D S C z.1 p.1 ^ 2 *
          (-deriv (stateProfile D S C z.1) p.1 /
            (p.1 * stateProfile D S C z.1 p.1)) /
        polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 := by
    change polarLinearB (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2 -
        polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p *
          polarCorrectedC (stateProfile D S C z.1) (stateHeight D S C z) p = _
    calc
      _ = -((stateProfile D S C z.1 p.1 * deriv (stateProfile D S C z.1) p.1 / p.1) /
          polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ^ 2) := by
        linarith only [hdet]
      _ = _ := by
        field_simp [hr.ne', hP.ne', hΔ.ne']
        ring
  exact hbound.trans_eq heq.symm

end ContinuousFlexibility.Statements
