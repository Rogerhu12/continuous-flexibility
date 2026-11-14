module

public import ContinuousFlexibility.Analysis.N07bReferenceTransportExtension
public import ContinuousFlexibility.Analysis.N07bReferenceCompactDecay
public import ContinuousFlexibility.Analysis.N07bReferenceForcingSymmetry
public import ContinuousFlexibility.Analysis.N07bCompactReferenceSources
public import ContinuousFlexibility.Analysis.N07bCutoffRadialBridge

/-!
# The transported physical field lies in the actual reference graph

The physical-space cutoff and the reference cutoff may differ. Their
actual difference has compact support inside the radial core, so it has
every material height exponent. The same argument applies to the actual
physical cutoff flux. This retains the prescribed left constant without
identifying the two cutoffs.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff

set_option backward.isDefEq.respectTransparency true

theorem n07b_cutoff_difference_height_bound
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hT : IsMaterialData D T) (hborder : RadialTrueBorder D)
    (hχ : CutoffConditions D χ) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |χ r - D.chiLeft r| ≤ C * T.H r ^ γ := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := n07b_cutoff_difference_core_support hχ hborder
  exact n07b_compact_radial_height_bound hT hJ hJcore
    (hχ.1.continuous.sub hborder.2.2.2.2.1.continuous).continuousOn hzero γ

theorem n07b_cutoff_flux_height_bound
    {D : ReferenceData} {T : MaterialData} {χ : ℝ → ℝ}
    (hgeom : RadialProfileGeometry D) (hT : IsMaterialData D T)
    (hχ : CutoffConditions D χ) (γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ radialCore D,
      |deriv (fun t => D.w t * deriv χ t) r| ≤ C * T.H r ^ γ := by
  obtain ⟨J, hJ, hJcore, hzero⟩ := n07b_cutoffFlux_compact_support hχ
  have hflux : ContDiff ℝ ∞ (fun t => D.w t * deriv χ t) :=
    hgeom.2.2.1.1.mul (contDiff_infty_iff_deriv.mp hχ.1).2
  exact n07b_compact_radial_height_bound hT hJ hJcore
    (contDiff_infty_iff_deriv.mp hflux).2.continuous.continuousOn
    (fun r _ hr => hzero r hr 0) γ

/-- The actual derivative expression splits off any smooth radial cutoff. -/
theorem n07b_referencePDE_add_radial_cutoff
    {D : ReferenceData} (hgeom : RadialProfileGeometry D)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {R : PolarPoint → ℝ}
    (hR : ContDiff ℝ 2 R) (a : ℝ) (x : PolarPoint) :
    radialPDE D.w (fun r θ => R (r, θ) + a * χ r) x.1 x.2 =
      radialPDE D.w (fun r θ => R (r, θ)) x.1 x.2 +
        a * deriv (fun t => D.w t * deriv χ t) x.1 := by
  have hχ' : ContDiff ℝ 2 (fun p : PolarPoint => a * χ p.1) :=
    contDiff_const.mul ((hχ.comp contDiff_fst).of_le (by simp))
  rw [n07b_c2_radialPDE_add (hgeom.2.2.1.1.differentiable (by simp)) hR hχ' x]
  change radialPDE D.w (fun r θ => R (r, θ)) x.1 x.2 +
    radialPDE D.w (fun r _ => a * χ r) x.1 x.2 = _
  rw [r11b_radialPDE_radial D.w (fun r => a * χ r) x.1 x.2]
  have hflux : (fun t => D.w t * deriv (fun r => a * χ r) t) =
      fun t => a * (D.w t * deriv χ t) := by
    funext t
    rw [deriv_const_mul_field]
    ring
  rw [hflux, deriv_const_mul_field]

/-- Finite actual jets of the remainder give the full reference graph,
including the physical cutoff and border scalar. No source-space or graph
membership is a premise. -/
theorem n07b_referenceGraph_of_remainder_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hborder : RadialTrueBorder D) (hχ : CutoffConditions D S.chiLeft)
    {γ δ A K : ℝ} (hγ : 0 < γ) (hγδ : γ < δ) (hK : 0 ≤ K)
    {R : PolarPoint → ℝ} (hR : ContDiff ℝ 2 R)
    (hRp : Function.Periodic R (0, Real.pi))
    (hRe : ∀ r θ, R (r, -θ) = R (r, θ))
    (hjet : ∀ x ∈ annularOpen D, ∀ n : ℕ, n ≤ 2 →
      ‖iteratedFDeriv ℝ n R x‖ ≤ K * T.H x.1 ^ δ * T.M x.1 ^ A)
    (a μ M₀ M₁ : ℝ)
    (hrow : referenceRow D (fun p => R p + a * S.chiLeft p.1) = 0) :
    ReferenceGraph D γ M₀ M₁
      ((fun p => R p + a * S.chiLeft p.1), μ)
      (n07bReferenceForcing D μ (fun p => R p + a * S.chiLeft p.1), 0) := by
  obtain ⟨δ', hγδ', hδ'δ⟩ := exists_between hγδ
  have hgeom : RadialProfileGeometry D := hD.choose_spec.1
  let η : PolarPoint → ℝ := fun p => R p + a * S.chiLeft p.1
  have hη : ContDiff ℝ 2 η :=
    hR.add (contDiff_const.mul ((hχ.1.comp contDiff_fst).of_le (by simp)))
  have hηp : Function.Periodic η (0, Real.pi) := by
    intro p
    simp only [η, hRp p, Prod.fst_add, add_zero]
  have hηe : ∀ r θ, η (r, -θ) = η (r, θ) := by
    intro r θ
    simp only [η, hRe r θ]
  obtain ⟨C₁, hC₁, hgap⟩ := n07b_material_height_gap_bound hT hδ'δ A
  obtain ⟨Cχ, hCχ, hcut⟩ := n07b_cutoff_difference_height_bound hT hborder hχ δ'
  have hrem : ∀ x ∈ annularOpen D, |η x - a * D.chiLeft x.1| ≤
      (K * C₁ + |a| * Cχ) * T.H x.1 ^ δ' := by
    intro x hx
    have hzero := hjet x hx 0 (by omega)
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hzero
    have hRbound : |R x| ≤ K * C₁ * T.H x.1 ^ δ' := by
      calc
        _ ≤ K * (T.H x.1 ^ δ * T.M x.1 ^ A) := by
          simpa only [mul_assoc] using hzero
        _ ≤ K * (C₁ * T.H x.1 ^ δ') := mul_le_mul_of_nonneg_left (hgap x.1 hx.1) hK
        _ = _ := by ring
    calc
      _ = |R x + a * (S.chiLeft x.1 - D.chiLeft x.1)| := by dsimp only [η]; congr 1; ring
      _ ≤ |R x| + |a| * |S.chiLeft x.1 - D.chiLeft x.1| := by
        simpa only [abs_mul] using abs_add_le (R x) (a * (S.chiLeft x.1 - D.chiLeft x.1))
      _ ≤ K * C₁ * T.H x.1 ^ δ' + |a| * (Cχ * T.H x.1 ^ δ') :=
        add_le_add hRbound (mul_le_mul_of_nonneg_left (hcut x.1 hx.1) (abs_nonneg _))
      _ = _ := by ring
  obtain ⟨CP, hCP, hP⟩ := n07b_referencePDE_decay_of_frechet_jets hgeom hT hδ'δ hK hR hjet
  obtain ⟨CF, hCF, hF⟩ := n07b_cutoff_flux_height_bound hgeom hT hχ δ'
  obtain ⟨CQ, hCQ, hQ⟩ := n07b_referenceColumn_cosine_height_bound hgeom hT hborder δ' 2
  have hforcing : ∀ x ∈ annularOpen D,
      |n07bReferenceForcing D μ η x| ≤
        (CP + |a| * CF + |μ| * CQ) * T.H x.1 ^ δ' := by
    intro x hx
    change |radialPDE D.w (fun r θ => R (r, θ) + a * S.chiLeft r) x.1 x.2 +
      μ * referenceColumn D x.1 * cosineMode 2 x.2| ≤ _
    rw [n07b_referencePDE_add_radial_cutoff hgeom hχ.1 hR a x,
      mul_assoc μ (referenceColumn D x.1) (cosineMode 2 x.2)]
    calc
      _ ≤ |radialPDE D.w (fun r θ => R (r, θ)) x.1 x.2| +
          |a| * |deriv (fun t => D.w t * deriv S.chiLeft t) x.1| +
          |μ| * |referenceColumn D x.1 * cosineMode 2 x.2| := by
        calc
          _ ≤ |radialPDE D.w (fun r θ => R (r, θ)) x.1 x.2 +
              a * deriv (fun t => D.w t * deriv S.chiLeft t) x.1| +
              |μ * (referenceColumn D x.1 * cosineMode 2 x.2)| := abs_add_le _ _
          _ ≤ (|radialPDE D.w (fun r θ => R (r, θ)) x.1 x.2| +
              |a * deriv (fun t => D.w t * deriv S.chiLeft t) x.1|) +
              |μ * (referenceColumn D x.1 * cosineMode 2 x.2)| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by simp only [abs_mul]
      _ ≤ CP * T.H x.1 ^ δ' + |a| * (CF * T.H x.1 ^ δ') +
          |μ| * (CQ * T.H x.1 ^ δ') :=
        add_le_add (add_le_add (hP x hx)
          (mul_le_mul_of_nonneg_left (hF x.1 hx.1) (abs_nonneg _)))
          (mul_le_mul_of_nonneg_left (hQ x hx) (abs_nonneg _))
      _ = _ := by ring
  exact n07b_referenceGraph_of_material_decay hD hT hborder
    (hγ.trans hγδ') hγδ'
    (add_nonneg (mul_nonneg hK hC₁.le) (mul_nonneg (abs_nonneg _) hCχ))
    (add_nonneg (add_nonneg hCP (mul_nonneg (abs_nonneg _) hCF))
      (mul_nonneg (abs_nonneg _) hCQ))
    hη hηp hηe (n07bReferenceForcing_periodic D μ hηp)
    (n07bReferenceForcing_even D μ hηe) (fun _ _ => rfl) hrow hrem hforcing M₀ M₁

end ContinuousFlexibility.Analysis
