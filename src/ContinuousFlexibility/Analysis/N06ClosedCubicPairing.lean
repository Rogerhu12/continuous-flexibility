import ContinuousFlexibility.Analysis.N06FiniteWeakGreen
import ContinuousFlexibility.Analysis.N06WeakCubicLimit
import ContinuousFlexibility.Analysis.N06HalfPhysicalPairing
import ContinuousFlexibility.Analysis.N06UnitWeakGraphData

/-!
# Cubic perturbation pairings for tests nonzero at the endpoints

The actual two conormal coefficients contain the factor `d^3`. Their
endpoint values therefore vanish for every finite C1/H2 field. The
resulting finite identity passes to the same original L2 value and five
graph limits. No boundary trace of the infinite reconstruction is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
open ContinuousFlexibility.Radial ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- Vanishing of the two actual conormal coefficients, with no regularity
assumption on the field whose totalized partials occur in the flux. -/
theorem n06_cubic_greenNormalFlux_zero (d A B C φ U : PolarPoint → ℝ)
    {p : PolarPoint} (hd : d p = 0) :
    greenNormalFlux (n06CubicCoefficients d A B C).a
      (n06CubicCoefficients d A B C).b φ U p = 0 := by
  simp only [greenNormalFlux, symmetricNormalFlux, n06CubicCoefficients,
    hd, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul, zero_add, mul_zero, sub_self]

theorem n06_unitCubic_greenNormalFlux_endpoints (A B C φ U : PolarPoint → ℝ) (θ : ℝ) :
    greenNormalFlux (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C).a
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C).b φ U (0, θ) = 0 ∧
    greenNormalFlux (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C).a
      (n06CubicCoefficients (fun p => cylinderWeight p.1) A B C).b φ U (1, θ) = 0 := by
  constructor <;> apply n06_cubic_greenNormalFlux_zero <;> norm_num [cylinderWeight]

/-- The original full-period physical measure is exactly twice the
original half-period unit measure for a genuine periodic integrand. -/
theorem n06_fullUnit_integral_eq_two_half {D : ReferenceData}
    (hl : D.a = 0) (hr : D.b = 1) {f : PolarPoint → ℝ}
    (hp : Function.Periodic f (0, Real.pi))
    (hf : Integrable f (radialPhysicalMeasure D)) :
    (∫ p, f p ∂radialPhysicalMeasure D) = 2 * ∫ p, f p ∂cylinderWindowMeasure 0 := by
  have hab : D.a ≤ D.b := by rw [hl, hr]; norm_num
  have hμle : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) ≤
      radialPhysicalMeasure D :=
    Measure.restrict_mono (Set.prod_mono subset_rfl
      (Ioc_subset_Ioc_right (by linarith [Real.pi_pos]))) le_rfl
  have hh : IntegrableOn f (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) := hf.mono_measure hμle
  have hmean := n06_physicalMean_eq_halfIntegral hab hp hh
  rw [r11b_integral_angularMean_eq hab hf] at hmean
  have hμ : volume.restrict (radialCore D ×ˢ Ioc (0 : ℝ) Real.pi) =
      cylinderWindowMeasure 0 := by
    simpa only [radialCore, hl, hr] using n06_unitCanonicalMeasure_eq_window
  rw [hμ] at hmean
  apply mul_left_cancel₀ (inv_ne_zero (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero))
  calc
    (2 * Real.pi)⁻¹ * (∫ p, f p ∂radialPhysicalMeasure D) =
        Real.pi⁻¹ * ∫ p, f p ∂cylinderWindowMeasure 0 := hmean
    _ = (2 * Real.pi)⁻¹ * (2 * ∫ p, f p ∂cylinderWindowMeasure 0) := by
      field_simp [Real.pi_ne_zero]
      <;> ring

private theorem finiteMixed_periodic (s : Finset ℕ) (v : ℕ → ℝ → ℝ) (a b : ℕ) :
    Function.Periodic (n06FiniteMixedField s v a b) (0, Real.pi) := by
  intro p
  unfold n06FiniteMixedField r11bFiniteSynthesis
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun t => iteratedDeriv a (v i) p.1 * t)
    (circleFourier_periodic_iteratedDeriv (referenceAngularBasis_periodic i) b p.2))

private theorem divergence_periodic {L : SymmetricCoefficients} {φ : PolarPoint → ℝ}
    (ha : Function.Periodic L.a (0, Real.pi))
    (hb : Function.Periodic L.b (0, Real.pi))
    (hc : Function.Periodic L.c (0, Real.pi))
    (hφ : Function.Periodic φ (0, Real.pi)) :
    Function.Periodic (divergenceOperator L φ) (0, Real.pi) :=
  (periodic_radialPartial ((ha.mul (periodic_radialPartial hφ)).add
    (hb.mul (periodic_angularPartial hφ)))).add
    (periodic_angularPartial ((hb.mul (periodic_radialPartial hφ)).add
      (hc.mul (periodic_angularPartial hφ))))

private theorem weakDivergence_periodic (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    {L : SymmetricCoefficients}
    (ha : Function.Periodic L.a (0, Real.pi))
    (hb : Function.Periodic L.b (0, Real.pi))
    (hc : Function.Periodic L.c (0, Real.pi)) :
    Function.Periodic (n06WeakDivergenceExpression L
      (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
      (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
      (n06FiniteMixedField s v 0 2)) (0, Real.pi) :=
  (((ha.mul (finiteMixed_periodic s v 2 0)).add
    ((periodic_radialPartial ha).mul (finiteMixed_periodic s v 1 0))).add
    ((hb.mul (finiteMixed_periodic s v 1 1)).add
      ((periodic_angularPartial hb).mul (finiteMixed_periodic s v 1 0)))).add
      ((hb.mul (finiteMixed_periodic s v 1 1)).add
        ((periodic_radialPartial hb).mul (finiteMixed_periodic s v 0 1))) |>.add
          ((hc.mul (finiteMixed_periodic s v 0 2)).add
            ((periodic_angularPartial hc).mul (finiteMixed_periodic s v 0 1)))

private theorem divergence_contDiff {L : SymmetricCoefficients} {φ : PolarPoint → ℝ}
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (divergenceOperator L φ) :=
  (contDiff_cylinder_radialPartial
    ((ha.mul (contDiff_cylinder_radialPartial hφ)).add
      (hb.mul (contDiff_cylinder_angularPartial hφ)))).add
    (contDiff_cylinder_angularPartial
      ((hb.mul (contDiff_cylinder_radialPartial hφ)).add
        (hc.mul (contDiff_cylinder_angularPartial hφ))))

private theorem weakDivergence_pairing_integrable {D : ReferenceData}
    {U Ur Ut Urr Urt Utt φ : PolarPoint → ℝ}
    (hrow : N06PhysicalWeakH2Row D U Ur Ut Urr Urt Utt)
    (L : SymmetricCoefficients)
    (ha : ContDiff ℝ ∞ L.a) (hb : ContDiff ℝ ∞ L.b) (hc : ContDiff ℝ ∞ L.c)
    (hφ : Continuous φ) :
    Integrable (fun p => n06WeakDivergenceExpression L Ur Ut Urr Urt Utt p * φ p)
      (radialPhysicalMeasure D) := by
  have hI (f a : PolarPoint → ℝ) (hf : MemLp f 2 (radialPhysicalMeasure D))
      (hA : Continuous a) : Integrable (fun p => f p * (a p * φ p))
        (radialPhysicalMeasure D) := hf.integrable_mul (r11b_continuous_memLp (hA.mul hφ))
  have h₁ := (hI Urr L.a hrow.radial_radial_memLp ha.continuous).add
    (hI Ur (radialPartial L.a) hrow.radial_memLp (contDiff_cylinder_radialPartial ha).continuous)
  have h₂ := (hI Urt L.b hrow.radial_angular_memLp hb.continuous).add
    (hI Ur (angularPartial L.b) hrow.radial_memLp (contDiff_cylinder_angularPartial hb).continuous)
  have h₃ := (hI Urt L.b hrow.radial_angular_memLp hb.continuous).add
    (hI Ut (radialPartial L.b) hrow.angular_memLp (contDiff_cylinder_radialPartial hb).continuous)
  have h₄ := (hI Utt L.c hrow.angular_angular_memLp hc.continuous).add
    (hI Ut (angularPartial L.c) hrow.angular_memLp (contDiff_cylinder_angularPartial hc).continuous)
  apply (((h₁.add h₂).add h₃).add h₄).congr
  filter_upwards with p
  simp only [n06WeakDivergenceExpression, Pi.add_apply]
  ring

/-- Finite H2 modes satisfy the genuine cubic distribution identity even
for smooth periodic tests which are nonzero at both ends of the unit interval.
The record update is used only for the interval measure, not as a new profile. -/
theorem n06_finite_weak_cubic_pairing_closed (D : ReferenceData)
    (s : Finset ℕ) (v : ℕ → ℝ → ℝ)
    (hC₁ : ∀ i ∈ s, ContDiff ℝ 1 (v i))
    (hAC : ∀ i ∈ s, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i ∈ s, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i ∈ s, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i ∈ s, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hpA : Function.Periodic A (0, Real.pi))
    (hpB : Function.Periodic B (0, Real.pi))
    (hpC : Function.Periodic C (0, Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, r11bFiniteSynthesis s v referenceAngularBasis p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂cylinderWindowMeasure 0) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
          n06WeakFiniteGraphFields s v 0 i p) * φ p ∂cylinderWindowMeasure 0 := by
  let D₀ : ReferenceData := { D with a := 0, b := 1 }
  let U := n06FiniteMixedField s v 0 0
  let L := n06CubicCoefficients (fun q => cylinderWeight q.1) A B C
  let Q := n06WeakDivergenceExpression L
    (n06FiniteMixedField s v 1 0) (n06FiniteMixedField s v 0 1)
    (n06FiniteMixedField s v 2 0) (n06FiniteMixedField s v 1 1)
    (n06FiniteMixedField s v 0 2)
  have hrow := n06_finiteMixedField_physical_weakH2 (D := D₀)
    (by norm_num [D₀]) s v hC₁ hAC hv hv₁ hv₂
  have hd : ContDiff ℝ ∞ (fun p : PolarPoint => cylinderWeight p.1 ^ 3) := by
    change ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 * (1 - p.1)) ^ 3)
    exact (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3
  have hdp : Function.Periodic (fun p : PolarPoint => cylinderWeight p.1 ^ 3)
      (0, Real.pi) := by
    intro p
    simp only [Prod.fst_add, add_zero]
  have hLa : ContDiff ℝ ∞ L.a := hd.mul hA
  have hLb : ContDiff ℝ ∞ L.b := hd.mul hB
  have hLc : ContDiff ℝ ∞ L.c := hd.mul hC
  have hLap : Function.Periodic L.a (0, Real.pi) := hdp.mul hpA
  have hLbp : Function.Periodic L.b (0, Real.pi) := hdp.mul hpB
  have hLcp : Function.Periodic L.c (0, Real.pi) := hdp.mul hpC
  have hgreen := n06_physical_weak_divergence_green hrow L hLa hLb hLc
    (reference_periodic_two_pi hLap) (reference_periodic_two_pi hLbp)
    (reference_periodic_two_pi hLcp) hφ (reference_periodic_two_pi hφp)
  have hboundary : (∫ θ in (0 : ℝ)..2 * Real.pi,
      greenNormalFlux L.a L.b φ U (D₀.b, θ) -
        greenNormalFlux L.a L.b φ U (D₀.a, θ)) = 0 := by
    calc
      _ = ∫ _θ in (0 : ℝ)..2 * Real.pi, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        change greenNormalFlux L.a L.b φ U (1, θ) -
          greenNormalFlux L.a L.b φ U (0, θ) = 0
        rw [(n06_unitCubic_greenNormalFlux_endpoints A B C φ U θ).1,
          (n06_unitCubic_greenNormalFlux_endpoints A B C φ U θ).2, sub_self]
      _ = 0 := intervalIntegral.integral_zero
  change (∫ p, Q p * φ p ∂radialPhysicalMeasure D₀) -
    (∫ p, U p * divergenceOperator L φ p ∂radialPhysicalMeasure D₀) = _ at hgreen
  rw [hboundary] at hgreen
  have hQ : Integrable (fun p => Q p * φ p) (radialPhysicalMeasure D₀) :=
    weakDivergence_pairing_integrable hrow L hLa hLb hLc hφ.continuous
  have hL : Integrable (fun p => U p * divergenceOperator L φ p) (radialPhysicalMeasure D₀) :=
    hrow.value_memLp.integrable_mul
      (r11b_continuous_memLp (divergence_contDiff hLa hLb hLc hφ).continuous)
  have hQp : Function.Periodic (fun p => Q p * φ p) (0, Real.pi) :=
    (weakDivergence_periodic s v hLap hLbp hLcp).mul hφp
  have hLp : Function.Periodic (fun p => U p * divergenceOperator L φ p) (0, Real.pi) :=
    (finiteMixed_periodic s v 0 0).mul (divergence_periodic hLap hLbp hLcp hφp)
  have heq := sub_eq_zero.mp hgreen
  rw [n06_fullUnit_integral_eq_two_half (D := D₀) rfl rfl hQp hQ,
    n06_fullUnit_integral_eq_two_half (D := D₀) rfl rfl hLp hL] at heq
  have hhalf : (∫ p, U p * divergenceOperator L φ p ∂cylinderWindowMeasure 0) =
      ∫ p, Q p * φ p ∂cylinderWindowMeasure 0 :=
    (mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) heq).symm
  calc
    _ = ∫ p, Q p * φ p ∂cylinderWindowMeasure 0 := hhalf
    _ = _ := by
      apply integral_congr_ae
      rw [← n06_unitCanonicalMeasure_eq_window]
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioc)] with p hp
      have he := n06_finiteWeakCubic_expansion_eq_sum s v
        (hA.differentiable (by simp) p) (hB.differentiable (by simp) p)
        (hC.differentiable (by simp) p) (Ioo_subset_Icc_self hp.1)
      exact congrArg (fun x : ℝ => x * φ p) he

private theorem closed_graph_pairing_sum {μ : Measure PolarPoint}
    (X M : Fin 5 → PolarPoint → ℝ) (φ : PolarPoint → ℝ)
    (hI : ∀ i, Integrable (fun p => X i p * (M i p * φ p)) μ) :
    (∫ p, (∑ i : Fin 5, M i p * X i p) * φ p ∂μ) =
      ∑ i : Fin 5, ∫ p, X i p * (M i p * φ p) ∂μ := by
  calc
    _ = ∫ p, ∑ i : Fin 5, X i p * (M i p * φ p) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hI i)

/-- The original five L2 graph limits inherit the closed-interval cubic
pairing. The finite identities are proved above, not assumed as input. -/
theorem n06_weak_cubic_pairing_closed_of_finite_limits (D : ReferenceData)
    {μ : Measure PolarPoint} (hμ : μ = cylinderWindowMeasure 0)
    (U : Lp ℝ 2 μ) (G : Fin 5 → Lp ℝ 2 μ) (v : ℕ → ℝ → ℝ)
    (hC₁ : ∀ i, ContDiff ℝ 1 (v i))
    (hAC : ∀ i, AbsolutelyContinuousOnInterval (deriv (v i)) 0 1)
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₁ : ∀ i, MemLp (deriv (v i)) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hv₂ : ∀ i, MemLp (deriv (deriv (v i))) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hUN : ∀ N, MemLp (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2 μ)
    (hGN : ∀ N i, MemLp (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i) 2 μ)
    (hUlim : Tendsto (fun N => (hUN N).toLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis)) atTop (𝓝 U))
    (hGlim : ∀ i, Tendsto (fun N => (hGN N i).toLp
      (n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i)) atTop (𝓝 (G i)))
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hpA : Function.Periodic A (0, Real.pi))
    (hpB : Function.Periodic B (0, Real.pi))
    (hpC : Function.Periodic C (0, Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, U p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p ∂μ) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p * G i p) * φ p ∂μ := by
  subst μ
  let M := n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C
  let L := n06CubicCoefficients (fun q => cylinderWeight q.1) A B C
  have hM (i : Fin 5) : Continuous (M i) :=
    n06CubicGraphMultipliers_continuous cylinderWeight_continuous
      (continuous_const.sub (continuous_const.mul continuous_id)) hA hB hC i
  have htestM (i : Fin 5) : MemLp (fun p => M i p * φ p) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow ((hM i).mul hφ.continuous) 0
  have hd : ContDiff ℝ ∞ (fun p : PolarPoint => cylinderWeight p.1 ^ 3) := by
    change ContDiff ℝ ∞ (fun p : PolarPoint => (p.1 * (1 - p.1)) ^ 3)
    exact (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).pow 3
  have htestL : MemLp (divergenceOperator L φ) 2 (cylinderWindowMeasure 0) :=
    continuous_memLp_cylinderWindow
      (divergence_contDiff (hd.mul hA) (hd.mul hB) (hd.mul hC) hφ).continuous 0
  have hleft : Tendsto (fun N => ∫ p,
      r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis p *
        divergenceOperator L φ p ∂cylinderWindowMeasure 0) atTop
      (𝓝 (∫ p, U p * divergenceOperator L φ p ∂cylinderWindowMeasure 0)) :=
    r11b_tendsto_integral_mul_of_L2_tendsto hUN (Lp.memLp U) htestL
      (by simpa only [Lp.toLp_coeFn] using hUlim)
  have hright (i : Fin 5) : Tendsto (fun N => ∫ p,
      n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i p * (M i p * φ p)
        ∂cylinderWindowMeasure 0) atTop
      (𝓝 (∫ p, G i p * (M i p * φ p) ∂cylinderWindowMeasure 0)) :=
    r11b_tendsto_integral_mul_of_L2_tendsto (fun N => hGN N i) (Lp.memLp (G i)) (htestM i)
      (by simpa only [Lp.toLp_coeFn] using hGlim i)
  have hseq : (fun N => ∫ p,
      r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis p *
        divergenceOperator L φ p ∂cylinderWindowMeasure 0) =
      fun N => ∑ i : Fin 5, ∫ p,
        n06WeakFiniteGraphFields (Finset.range (N + 1)) v 0 i p * (M i p * φ p)
          ∂cylinderWindowMeasure 0 := by
    funext N
    exact (n06_finite_weak_cubic_pairing_closed D (Finset.range (N + 1)) v
      (fun i _ => hC₁ i) (fun i _ => hAC i) (fun i _ => hv i)
      (fun i _ => hv₁ i) (fun i _ => hv₂ i) hA hB hC hpA hpB hpC hφ hφp).trans
        (closed_graph_pairing_sum _ M φ (fun i => (hGN N i).integrable_mul (htestM i)))
  rw [hseq] at hleft
  have heq := tendsto_nhds_unique hleft
    (tendsto_finsetSum Finset.univ (fun i _ => hright i))
  exact heq.trans (closed_graph_pairing_sum (fun i => (G i : PolarPoint → ℝ)) M φ
    (fun i => (Lp.memLp (G i)).integrable_mul (htestM i))).symm

/-- The same AE modal representatives retained by graph completion
reconstruct the original value in the original canonical L2 space. -/
theorem n06_canonical_representative_values_tendsto
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (U : Fin (b + 1) → CanonicalL2 S Kc m)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    (v : ℕ → ℝ → ℝ)
    (hv : ∀ i, MemLp (v i) 2 (volume.restrict (Ioo (0 : ℝ) 1)))
    (hveq : ∀ i, n06HalfCosineCoefficient (U 0) i =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] v i) :
    ∃ hUN : ∀ N, MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2
        (canonicalMeasure S Kc m),
      Tendsto (fun N => (hUN N).toLp
        (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis))
        atTop (𝓝 (U 0)) := by
  have hμ := n06_canonical_unit_measure_eq_window hl hr
  obtain ⟨hUC, hUlim⟩ := n06_canonicalCosineCut_jetRow_tendsto U hUeven hUjets
  let hUN (N : ℕ) : MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2
        (canonicalMeasure S Kc m) :=
    (congrArg (fun ν : Measure PolarPoint => MemLp
      (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) 2 ν) hμ).mpr
        (n06_weak_finiteSynthesis_memLp _ v referenceAngularBasis
          (fun i _ => hv i) (fun i _ => (contDiff_referenceAngularBasis i).continuous))
  have hclass (N : ℕ) :
      (hUN N).toLp (r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) =
        (hUC N 0).toLp (mixedDerivative 0 (0 : Fin (b + 1)).val
          (n06CylinderCosineCut N (U 0))) := by
    have hae : n06CylinderCosineCut N (U 0) =ᵐ[canonicalMeasure S Kc m]
        r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis :=
      (congrArg (fun ν : Measure PolarPoint =>
        n06CylinderCosineCut N (U 0) =ᵐ[ν]
          r11bFiniteSynthesis (Finset.range (N + 1)) v referenceAngularBasis) hμ).mpr
        (n06_weak_finiteSynthesis_congr_ae (Finset.range (N + 1))
          (n06HalfCosineCoefficient (U 0)) v referenceAngularBasis (fun i _ => hveq i))
    apply (hUN N).toLp_congr (hUC N 0)
    simpa only [Fin.val_zero, spaces_mixedDerivative_zero] using hae.symm
  refine ⟨hUN, ?_⟩
  exact (n06_tendsto_component_of_sum_sq_errors hUlim (0 : Fin (b + 1))).congr'
    (Eventually.of_forall (fun N => (hclass N).symm))

/-- The already constructed actual weak graph package supplies every
limit and every modal regularity premise of the closed-boundary pairing. -/
theorem N06UnitWeakGraphData.closed_cubic_pairing
    {S : PhysicalSpacesData} {Kc : CanonicalData S} {m b : ℕ}
    {a c V : ℝ → ℝ}
    {U F : PiLp 2 (fun _ : Fin (b + 1) => CanonicalL2 S Kc m)} {K : ℝ}
    (P : N06UnitWeakGraphData a c V U F K)
    (D : ReferenceData)
    (hl : Kc.left m = 0) (hr : Kc.right m = 1)
    (hUeven : (fun p : PolarPoint => U 0 (p.1, Real.pi - p.2))
      =ᵐ[canonicalMeasure S Kc m] (U 0 : PolarPoint → ℝ))
    (hUjets : ∀ k, WeakCanonicalAngularDerivative S Kc m (U 0) (U k) k.val)
    {A B C φ : PolarPoint → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hC : ContDiff ℝ ∞ C)
    (hpA : Function.Periodic A (0, Real.pi))
    (hpB : Function.Periodic B (0, Real.pi))
    (hpC : Function.Periodic C (0, Real.pi))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (0, Real.pi)) :
    (∫ p, U 0 p *
      divergenceOperator (n06CubicCoefficients (fun q => cylinderWeight q.1) A B C) φ p
        ∂canonicalMeasure S Kc m) =
      ∫ p, (∑ i : Fin 5,
        n06CubicGraphMultipliers cylinderWeight (fun r => 1 - 2 * r) A B C i p *
          P.field i 0 p) * φ p ∂canonicalMeasure S Kc m := by
  obtain ⟨hUN, hUlim⟩ := n06_canonical_representative_values_tendsto hl hr
    (fun k => U k) hUeven hUjets P.modes
    (fun i => (P.representative i).memLp) (fun i => (P.representative i).ae_eq)
  exact n06_weak_cubic_pairing_closed_of_finite_limits D
    (n06_canonical_unit_measure_eq_window hl hr) (U 0) (fun i => P.field i 0) P.modes
    (fun i => (P.representative i).contDiffOne)
    (fun i => (P.representative i).firstAC)
    (fun i => (P.representative i).memLp)
    (fun i => (P.representative i).firstMemLp)
    (fun i => (P.representative i).secondMemLp)
    hUN (fun N i => P.cutMemLp N 0 i) hUlim (fun i => P.cut_tendsto 0 i)
    hA hB hC hpA hpB hpC hφ hφp

end ContinuousFlexibility.Analysis
