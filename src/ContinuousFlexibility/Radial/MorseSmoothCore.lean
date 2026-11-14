module

public import ContinuousFlexibility.Radial.LpConvolution
public import ContinuousFlexibility.Radial.MorseEnergyCutoff
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# A smooth compact core for the physical Morse energy form

The approximation is in all three actual L² coordinates: the function,
its weak derivative, and its exponential weight. The scalar convolution
is identified with the vector-valued L² convolution by actual test
integrals. No point evaluation functional on L² is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology Convolution ContDiff

set_option backward.isDefEq.respectTransparency false

theorem morseCompact_memLp_integrable {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) : Integrable f volume :=
  (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hc)

/-- Fubini for the actual scalar convolution and a compact test. -/
theorem morseConvolution_integral_test {κ f φ : ℝ → ℝ}
    (hκ : Integrable κ volume) (hf : Integrable f volume)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x : ℝ, (κ ⋆ f) x * φ x) =
      ∫ t : ℝ, κ t * ∫ x : ℝ, f (x - t) * φ x := by
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hcφ
  have hi : Integrable (fun p : ℝ × ℝ => κ p.2 * f (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      hκ.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hf
  have hp : Integrable
      (fun p : ℝ × ℝ => (κ p.2 * f (p.1 - p.2)) * φ p.1)
      (volume.prod volume) :=
    hi.mul_bdd (hφ.measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => hC p.1))
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hp]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change (∫ x : ℝ, κ t * f (x - t) * φ x) = κ t * ∫ x : ℝ, f (x - t) * φ x
    rw [← integral_const_mul]
    congr 1
    funext x
    ring)

theorem morseConvolution_contDiff {κ f : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (κ ⋆ f) :=
  hcκ.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ
    (hf.locallyIntegrable (by norm_num))

theorem morseConvolution_memLp {κ f : ℝ → ℝ}
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hf : MemLp f 2 volume) (hcf : HasCompactSupport f) : MemLp (κ ⋆ f) 2 volume :=
  (morseConvolution_contDiff hκ hcκ hf).continuous.memLp_of_hasCompactSupport
    (HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcκ hcf)

/-- Identification of the actual scalar convolution with the Bochner
convolution in L². Compact support supplies scalar L¹ for Fubini. -/
theorem morseConvolution_toLp {κ f : ℝ → ℝ} (u : MorseL2)
    (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hcf : HasCompactSupport f) (huf : (u : ℝ → ℝ) =ᵐ[volume] f) :
    (morseConvolution_memLp hκ hcκ (MemLp.ae_eq huf (Lp.memLp u)) hcf).toLp (κ ⋆ f) =
      realL2Convolution κ u := by
  have hf : MemLp f 2 volume := MemLp.ae_eq huf (Lp.memLp u)
  have hs := morseConvolution_contDiff hκ hcκ hf
  have hc := HasCompactSupport.convolution (μ := volume)
    (ContinuousLinearMap.lsmul ℝ ℝ) hcκ hcf
  have hm : MemLp (κ ⋆ f) 2 volume := hs.continuous.memLp_of_hasCompactSupport hc
  have hk : Integrable κ volume := hκ.continuous.integrable_of_hasCompactSupport hcκ
  apply Lp.ext
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (hm.toLp (κ ⋆ f))).locallyIntegrable (by norm_num))
    ((Lp.memLp (realL2Convolution κ u)).locallyIntegrable (by norm_num))
  intro φ hφ hcφ
  have ht := (compactSmooth_morseEnergyDomain hφ hcφ).2.1
  have heq : morseTestPairing φ ht (realL2Convolution κ u) =
      ∫ x : ℝ, (κ ⋆ f) x * φ x := by
    rw [realL2Convolution_pairing hk]
    calc
      (∫ t : ℝ, κ t * morseTestPairing φ ht (realL2Translate t u)) =
          ∫ t : ℝ, κ t * ∫ x : ℝ, f (x - t) * φ x := by
        apply integral_congr_ae
        refine Eventually.of_forall (fun t => ?_)
        change κ t * morseTestPairing φ ht (realL2Translate t u) =
          κ t * ∫ x : ℝ, f (x - t) * φ x
        rw [morseTestPairing_apply]
        congr 1
        apply integral_congr_ae
        have hft := huf.comp_tendsto
          (measurePreserving_sub_right volume t).quasiMeasurePreserving.tendsto_ae
        filter_upwards [realL2Translate_coeFn t u, hft] with x hx hfx
        change u (x - t) = f (x - t) at hfx
        rw [hx, hfx]
      _ = ∫ x : ℝ, (κ ⋆ f) x * φ x :=
        (morseConvolution_integral_test hk (morseCompact_memLp_integrable hf hcf)
          hφ.continuous hcφ).symm
  rw [morseTestPairing_apply] at heq
  calc
    (∫ x : ℝ, φ x • (hm.toLp (κ ⋆ f)) x) = ∫ x : ℝ, (κ ⋆ f) x * φ x := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hm] with x hx
      simp only [hx, smul_eq_mul, mul_comm]
    _ = ∫ x : ℝ, φ x • realL2Convolution κ u x := by
      simpa only [smul_eq_mul, mul_comm] using heq.symm

/-- A compact scalar representative for each physical energy coordinate. -/
def morseCompactRepresentative (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (i : Fin 3) : ℝ → ℝ := Classical.choose (hc i)

theorem morseCompactRepresentative_support (u : MorseWeakEnergy)
    (hc : MorseCompactEnergy u) (i : Fin 3) :
    HasCompactSupport (morseCompactRepresentative u hc i) :=
  (Classical.choose_spec (hc i)).1

theorem morseCompactRepresentative_ae (u : MorseWeakEnergy)
    (hc : MorseCompactEnergy u) (i : Fin 3) :
    (morseEnergyCoordinate i u : ℝ → ℝ) =ᵐ[volume] morseCompactRepresentative u hc i :=
  (Classical.choose_spec (hc i)).2

theorem morseCompactRepresentative_memLp (u : MorseWeakEnergy)
    (hc : MorseCompactEnergy u) (i : Fin 3) :
    MemLp (morseCompactRepresentative u hc i) 2 volume :=
  MemLp.ae_eq (morseCompactRepresentative_ae u hc i) (Lp.memLp (morseEnergyCoordinate i u))

theorem morseCompactRepresentative_weight_ae (u : MorseWeakEnergy)
    (hc : MorseCompactEnergy u) :
    morseCompactRepresentative u hc 2 =ᵐ[volume]
      (fun x => exp (-x) * morseCompactRepresentative u hc 0 x) := by
  filter_upwards [morseCompactRepresentative_ae u hc 0,
    morseCompactRepresentative_ae u hc 2, morseEnergyWeight_ae u] with x h0 h2 hw
  change morseEnergyBase u x = _ at h0
  change morseEnergyWeight u x = _ at h2
  rw [← h2, hw, h0]

/-- Differentiation of the actual mollification uses the defining weak
derivative with the translated reflected smooth kernel as a test. -/
theorem morseConvolution_deriv {κ f g : ℝ → ℝ} {u d : MorseL2}
    (hD : MorseWeakDerivativeL2 u d) (hκ : ContDiff ℝ ∞ κ)
    (hcκ : HasCompactSupport κ) (huf : (u : ℝ → ℝ) =ᵐ[volume] f)
    (hdg : (d : ℝ → ℝ) =ᵐ[volume] g) :
    deriv (κ ⋆ f) = κ ⋆ g := by
  have hf : MemLp f 2 volume := MemLp.ae_eq huf (Lp.memLp u)
  funext x
  let φ : ℝ → ℝ := fun y => κ (x - y)
  have hφ : ContDiff ℝ ∞ φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := by
    simpa only [φ, Function.comp_def, Homeomorph.trans_apply, Homeomorph.coe_neg,
      Homeomorph.coe_addLeft, sub_eq_add_neg] using
      hcκ.comp_homeomorph ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft x))
  have hdφ : deriv φ = fun y => -deriv κ (x - y) := by
    funext y
    exact ((hκ.differentiable (by norm_num) (x - y)).hasDerivAt.comp_const_sub x y).deriv
  have hw : (∫ y : ℝ, g y * κ (x - y)) = ∫ y : ℝ, f y * deriv κ (x - y) := by
    calc
      (∫ y : ℝ, g y * κ (x - y)) = ∫ y : ℝ, d y * φ y := by
        apply integral_congr_ae
        filter_upwards [hdg] with y hy
        rw [hy]
      _ = -(∫ y : ℝ, u y * deriv φ y) := hD φ hφ hcφ
      _ = ∫ y : ℝ, f y * deriv κ (x - y) := by
        rw [hdφ]
        simp only [mul_neg, integral_neg, neg_neg]
        apply integral_congr_ae
        filter_upwards [huf] with y hy
        rw [hy]
  rw [(hcκ.hasDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hκ.of_le (by norm_num)) (hf.locallyIntegrable (by norm_num)) x).deriv]
  rw [convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ, deriv κ (x - y) * f y) = ∫ y : ℝ, f y * deriv κ (x - y) := by
      simp only [mul_comm]
    _ = ∫ y : ℝ, g y * κ (x - y) := hw.symm
    _ = ∫ y : ℝ, κ (x - y) * g y := by simp only [mul_comm]

def morseTiltedKernel (κ : ℝ → ℝ) (t : ℝ) : ℝ := exp (-t) * κ t

theorem morseTiltedKernel_contDiff {κ : ℝ → ℝ} (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (morseTiltedKernel κ) :=
  contDiff_id.neg.exp.mul hκ

theorem morseTiltedKernel_support {κ : ℝ → ℝ} (hcκ : HasCompactSupport κ) :
    HasCompactSupport (morseTiltedKernel κ) := hcκ.mul_left

/-- The exponential weight is preserved by an explicitly tilted kernel. -/
theorem morseConvolution_weight {κ f z : ℝ → ℝ}
    (hz : z =ᵐ[volume] (fun y => exp (-y) * f y)) (x : ℝ) :
    exp (-x) * (κ ⋆ f) x = (morseTiltedKernel κ ⋆ z) x := by
  rw [convolution_lsmul_swap, convolution_lsmul_swap, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hz] with y hy
  simp only [smul_eq_mul, morseTiltedKernel, hy]
  have he : exp (-(x - y)) * exp (-y) = exp (-x) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    exp (-x) * (κ (x - y) * f y) =
        (exp (-(x - y)) * exp (-y)) * (κ (x - y) * f y) := by rw [he]
    _ = (exp (-(x - y)) * κ (x - y)) * (exp (-y) * f y) := by ring

/-- Actual scalar mollification, lifted with its actual derivative and weight. -/
def morseCompactSmoothing (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) :
    MorseWeakEnergy :=
  morseEnergyLift (compactSmooth_morseEnergyDomain
    (morseConvolution_contDiff hκ hcκ (morseCompactRepresentative_memLp u hc 0))
    (HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hcκ (morseCompactRepresentative_support u hc 0)))

theorem morseCompactSmoothing_base (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) :
    morseEnergyBase (morseCompactSmoothing u hc κ hκ hcκ) =
      realL2Convolution κ (morseEnergyBase u) := by
  unfold morseCompactSmoothing
  rw [morseEnergyLift_base]
  exact morseConvolution_toLp (morseEnergyBase u) hκ hcκ
    (morseCompactRepresentative_support u hc 0) (morseCompactRepresentative_ae u hc 0)

theorem morseCompactSmoothing_derivative (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) :
    morseEnergyDerivative (morseCompactSmoothing u hc κ hκ hcκ) =
      realL2Convolution κ (morseEnergyDerivative u) := by
  let f := morseCompactRepresentative u hc 0
  let d := morseCompactRepresentative u hc 1
  have hs := morseConvolution_contDiff hκ hcκ (morseCompactRepresentative_memLp u hc 0)
  have hsc := HasCompactSupport.convolution (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hcκ (morseCompactRepresentative_support u hc 0)
  have ht := compactSmooth_morseEnergyDomain hs hsc
  have hdm : MemLp (κ ⋆ d) 2 volume := morseConvolution_memLp hκ hcκ
    (morseCompactRepresentative_memLp u hc 1) (morseCompactRepresentative_support u hc 1)
  have he : deriv (κ ⋆ f) = κ ⋆ d := morseConvolution_deriv
    (morseEnergyDerivative_weak u) hκ hcκ
    (morseCompactRepresentative_ae u hc 0) (morseCompactRepresentative_ae u hc 1)
  change ht.2.2.1.toLp (deriv (κ ⋆ f)) = _
  calc
    ht.2.2.1.toLp (deriv (κ ⋆ f)) = hdm.toLp (κ ⋆ d) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall (fun x => congrFun he x))
    _ = realL2Convolution κ (morseEnergyDerivative u) :=
      morseConvolution_toLp (morseEnergyDerivative u) hκ hcκ
        (morseCompactRepresentative_support u hc 1) (morseCompactRepresentative_ae u hc 1)

theorem morseCompactSmoothing_weight (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ) :
    morseEnergyWeight (morseCompactSmoothing u hc κ hκ hcκ) =
      realL2Convolution (morseTiltedKernel κ) (morseEnergyWeight u) := by
  let f := morseCompactRepresentative u hc 0
  let z := morseCompactRepresentative u hc 2
  have hs := morseConvolution_contDiff hκ hcκ (morseCompactRepresentative_memLp u hc 0)
  have hsc := HasCompactSupport.convolution (μ := volume) (ContinuousLinearMap.lsmul ℝ ℝ)
    hcκ (morseCompactRepresentative_support u hc 0)
  have ht := compactSmooth_morseEnergyDomain hs hsc
  have htk := morseTiltedKernel_contDiff hκ
  have htck := morseTiltedKernel_support hcκ
  have hzm : MemLp (morseTiltedKernel κ ⋆ z) 2 volume := morseConvolution_memLp htk htck
    (morseCompactRepresentative_memLp u hc 2) (morseCompactRepresentative_support u hc 2)
  change ht.2.2.2.toLp (fun x => exp (-x) * (κ ⋆ f) x) = _
  calc
    ht.2.2.2.toLp (fun x => exp (-x) * (κ ⋆ f) x) =
        hzm.toLp (morseTiltedKernel κ ⋆ z) :=
      MemLp.toLp_congr _ _ (Eventually.of_forall
        (morseConvolution_weight (morseCompactRepresentative_weight_ae u hc)))
    _ = realL2Convolution (morseTiltedKernel κ) (morseEnergyWeight u) :=
      morseConvolution_toLp (morseEnergyWeight u) htk htck
        (morseCompactRepresentative_support u hc 2) (morseCompactRepresentative_ae u hc 2)

/-- Explicit positive-radius smooth kernels; their outer radius tends to zero. -/
def morseMollifierBump (N : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((N : ℝ) + 1)
  rOut := 2 * (1 / ((N : ℝ) + 1))
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith

def morseMollifier (N : ℕ) : ℝ → ℝ := (morseMollifierBump N).normed volume

theorem morseMollifier_contDiff (N : ℕ) : ContDiff ℝ ∞ (morseMollifier N) :=
  (morseMollifierBump N).contDiff_normed

theorem morseMollifier_support (N : ℕ) : HasCompactSupport (morseMollifier N) :=
  (morseMollifierBump N).hasCompactSupport_normed

theorem morseMollifier_nonneg (N : ℕ) (x : ℝ) : 0 ≤ morseMollifier N x :=
  (morseMollifierBump N).nonneg_normed x

theorem morseMollifier_integral (N : ℕ) : (∫ x : ℝ, morseMollifier N x) = 1 :=
  (morseMollifierBump N).integral_normed

theorem morseMollifier_support_tendsto :
    Tendsto (fun N => Function.support (morseMollifier N)) atTop (𝓝 (0 : ℝ)).smallSets := by
  apply ContDiffBump.tendsto_support_normed_smallSets
  simpa only [morseMollifierBump, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

theorem morseMollifier_convolution_tendsto (u : MorseL2) :
    Tendsto (fun N => realL2Convolution (morseMollifier N) u) atTop (𝓝 u) :=
  realL2Convolution_tendsto (Eventually.of_forall morseMollifier_nonneg)
    (Eventually.of_forall morseMollifier_integral) morseMollifier_support_tendsto u

/-- The tilted kernels converge strongly as well. This is a convolution
with the continuous L²-valued function `s ↦ exp(s) • Translate(-s) u`.
No global bound on the exponential multiplier is assumed. -/
theorem morseMollifier_tilted_convolution_tendsto (u : MorseL2) :
    Tendsto (fun N => realL2Convolution (morseTiltedKernel (morseMollifier N)) u)
      atTop (𝓝 u) := by
  let g : ℝ → RealL2 := fun s => exp s • realL2Translate (-s) u
  have hg : Continuous g := continuous_exp.smul
    ((continuous_realL2Translate u).comp continuous_neg)
  have hcg : Tendsto (Function.uncurry (fun _ : ℕ => g))
      (atTop ×ˢ 𝓝 (0 : ℝ)) (𝓝 u) := by
    change Tendsto (g ∘ (Prod.snd : ℕ × ℝ → ℝ)) (atTop ×ˢ 𝓝 (0 : ℝ)) (𝓝 u)
    have h := (hg.tendsto 0).comp
      (tendsto_snd : Tendsto (Prod.snd : ℕ × ℝ → ℝ) (atTop ×ˢ 𝓝 0) (𝓝 0))
    simpa only [g, exp_zero, neg_zero, realL2Translate_zero, one_smul] using h
  have h := convolution_tendsto_right (μ := (volume : Measure ℝ))
    (g := fun _ : ℕ => g) (k := fun _ : ℕ => (0 : ℝ))
    (Eventually.of_forall morseMollifier_nonneg)
    (Eventually.of_forall morseMollifier_integral) morseMollifier_support_tendsto
    (Eventually.of_forall (fun _ => hg.aestronglyMeasurable)) hcg tendsto_const_nhds
  convert h using 1
  funext N
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    g, neg_neg, realL2Convolution, morseTiltedKernel, smul_smul, mul_comm]

def morseCompactSmoothApprox (u : MorseWeakEnergy) (hc : MorseCompactEnergy u)
    (N : ℕ) : MorseWeakEnergy :=
  morseCompactSmoothing u hc (morseMollifier N)
    (morseMollifier_contDiff N) (morseMollifier_support N)

theorem morseCompactSmoothApprox_tendsto (u : MorseWeakEnergy) (hc : MorseCompactEnergy u) :
    Tendsto (morseCompactSmoothApprox u hc) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  have h0 := morseMollifier_convolution_tendsto (morseEnergyBase u)
  have h1 := morseMollifier_convolution_tendsto (morseEnergyDerivative u)
  have h2 := morseMollifier_tilted_convolution_tendsto (morseEnergyWeight u)
  have hp : Tendsto (fun N : ℕ => fun i : Fin 3 => (morseCompactSmoothApprox u hc N).val i)
      atTop (𝓝 (fun i : Fin 3 => u.val i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · change Tendsto (fun N => morseEnergyBase (morseCompactSmoothApprox u hc N))
        atTop (𝓝 (morseEnergyBase u))
      simpa only [morseCompactSmoothApprox, morseCompactSmoothing_base] using h0
    · change Tendsto (fun N => morseEnergyDerivative (morseCompactSmoothApprox u hc N))
        atTop (𝓝 (morseEnergyDerivative u))
      simpa only [morseCompactSmoothApprox, morseCompactSmoothing_derivative] using h1
    · change Tendsto (fun N => morseEnergyWeight (morseCompactSmoothApprox u hc N))
        atTop (𝓝 (morseEnergyWeight u))
      simpa only [morseCompactSmoothApprox, morseCompactSmoothing_weight] using h2
  have ht := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => MorseL2)).symm.continuous.tendsto
    (fun i : Fin 3 => u.val i)).comp hp
  convert ht using 1 <;> rfl

/-- Genuine smooth compactly supported functions, with their actual
derivative and exponential weight, are dense in the full physical energy space. -/
theorem morseCompactSmoothEnergy_dense :
    Dense {u : MorseWeakEnergy | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
      (hcφ : HasCompactSupport φ),
      u = morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ)} := by
  let S : Set MorseWeakEnergy := {u | ∃ (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ),
    u = morseEnergyLift (compactSmooth_morseEnergyDomain hφ hcφ)}
  have hc : {u : MorseWeakEnergy | MorseCompactEnergy u} ⊆ closure S := by
    intro u hu
    apply mem_closure_of_tendsto (morseCompactSmoothApprox_tendsto u hu)
    apply Eventually.of_forall
    intro N
    exact ⟨morseMollifier N ⋆ morseCompactRepresentative u hu 0,
      morseConvolution_contDiff (morseMollifier_contDiff N) (morseMollifier_support N)
        (morseCompactRepresentative_memLp u hu 0),
      HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
        (morseMollifier_support N) (morseCompactRepresentative_support u hu 0), rfl⟩
  intro u
  exact (closure_minimal hc isClosed_closure) (morseCompactEnergy_dense u)

end ContinuousFlexibility.Radial
