module

public import ContinuousFlexibility.Radial.MorseDarbouxIntertwining

/-!
# Ground states of the Morse partner family

The annihilation equation has an integrating factor on the entire line.
Compact primitives of zero-integral tests detect that the resulting
locally integrable function is almost everywhere constant.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

set_option backward.isDefEq.respectTransparency false

private theorem morseCompactPrimitive {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hzero : (∫ x : ℝ, g x) = 0) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ deriv P = g := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  let a : ℝ := -|R| - 1
  let b : ℝ := |R| + 1
  let P (x : ℝ) := ∫ t in a..x, g t
  have hP (x : ℝ) : HasDerivAt P (g x) x :=
    (hg.continuous.integral_hasStrictDerivAt a x).hasDerivAt
  have hd : deriv P = g := funext (fun x => (hP x).deriv)
  have hgzero (x : ℝ) (hx : x ∉ Ioc a b) : g x = 0 := by
    by_contra h
    have hs : x ∈ tsupport g := subset_closure (show x ∈ Function.support g from h)
    have hbound : |x| ≤ R := by
      simpa only [Real.dist_eq, sub_zero] using Metric.mem_closedBall.mp (hR hs)
    have h := abs_le.mp (hbound.trans (le_abs_self R))
    exact hx ⟨by dsimp [a]; linarith [h.1], by dsimp [b]; linarith [h.2]⟩
  refine ⟨P, contDiff_infty_iff_deriv.mpr ⟨fun x => (hP x).differentiableAt, hd.symm ▸ hg⟩, ?_, hd⟩
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc a b))
  intro x hx
  change (∫ t in a..x, g t) = 0
  by_cases hxa : x < a
  · have hI : (∫ t in Ioc x a, g t) = 0 := by
      calc
        _ = ∫ _ in Ioc x a, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          exact hgzero t (fun hm => (not_lt_of_ge ht.2) hm.1)
        _ = _ := by simp
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxa.le, hI, neg_zero]
  · have hax : a ≤ x := le_of_not_gt hxa
    have hbx : b < x := lt_of_not_ge (fun h => hx ⟨hax, h⟩)
    have hout (t : ℝ) (ht : t ∉ Ioc a x) : g t = 0 :=
      hgzero t (fun hm => ht ⟨hm.1, hm.2.trans hbx.le⟩)
    rw [intervalIntegral.integral_of_le hax]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hzero

private theorem morse_ae_constant_of_weak_deriv_zero {F : ℝ → ℝ} (hF : LocallyIntegrable F volume)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ, F x * deriv φ x) = 0) :
    ∃ c : ℝ, F =ᵐ[volume] fun _ => c := by
  let η := morseMollifier 0
  have hη : ContDiff ℝ ∞ η := morseMollifier_contDiff 0
  have hcη : HasCompactSupport η := morseMollifier_support 0
  have hη₁ : (∫ x : ℝ, η x) = 1 := morseMollifier_integral 0
  let c := ∫ x : ℝ, F x * η x
  refine ⟨c, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq hF continuous_const.locallyIntegrable
  intro φ hφ hc
  let M := ∫ x : ℝ, φ x
  let g (x : ℝ) := φ x - M * η x
  have hg : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hη)
  have hcg : HasCompactSupport g := hc.sub (hcη.mul_left (f := fun _ => M))
  have hφI : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hc
  have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hcη
  have hgzero : (∫ x : ℝ, g x) = 0 := by
    change (∫ x : ℝ, φ x - M * η x) = 0
    rw [integral_sub hφI (hηI.const_mul M), integral_const_mul, hη₁, mul_one]
    exact sub_self _
  obtain ⟨P, hP, hcP, hdP⟩ := morseCompactPrimitive hg hcg hgzero
  have hPg := hzero P hP hcP
  rw [hdP] at hPg
  have hFφ : Integrable (fun x => F x * φ x) volume := by
    simpa only [smul_eq_mul] using hF.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hFη : Integrable (fun x => F x * η x) volume := by
    simpa only [smul_eq_mul] using hF.integrable_smul_right_of_hasCompactSupport hη.continuous hcη
  have hsplit : (∫ x : ℝ, F x * g x) = (∫ x : ℝ, F x * φ x) - M * c := by
    calc
      _ = ∫ x : ℝ, F x * φ x - M * (F x * η x) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        dsimp [g]
        ring
      _ = _ := by rw [integral_sub hFφ (hFη.const_mul M), integral_const_mul]
  rw [hsplit] at hPg
  calc
    _ = ∫ x : ℝ, F x * φ x := by simp only [smul_eq_mul, mul_comm]
    _ = M * c := sub_eq_zero.mp hPg
    _ = _ := by simp only [smul_eq_mul, integral_mul_const, M]

private def morseIntegratingFactor (α w x : ℝ) : ℝ := exp (α * x + w * exp (-x))

private theorem morseIntegratingFactor_contDiff (α w : ℝ) : ContDiff ℝ ∞ (morseIntegratingFactor α w) :=
  ((contDiff_const.mul contDiff_id).add (contDiff_const.mul contDiff_id.neg.exp)).exp

private theorem morseIntegratingFactor_deriv (α w x : ℝ) :
    deriv (morseIntegratingFactor α w) x = (α - w * exp (-x)) * morseIntegratingFactor α w x := by
  have h := (((hasDerivAt_id x).const_mul α).add (((hasDerivAt_id x).neg.exp).const_mul w)).exp.deriv
  unfold morseIntegratingFactor
  simp only [Pi.add_apply, Pi.neg_apply, id_eq, mul_one] at h
  rw [h]
  ring

private theorem morseIntegratingFactor_mul_ground (α w x : ℝ) :
    morseIntegratingFactor α w x * morseGround α w x = 1 := by
  unfold morseIntegratingFactor morseGround
  rw [← exp_add, show α * x + w * exp (-x) + (-α * x - w * exp (-x)) = 0 by ring, exp_zero]

/-- Every true annihilation-kernel vector is a scalar multiple of the
classical ground function almost everywhere. -/
theorem morseAnnihilationL2_ae_ground {α w : ℝ} (U : MorseWeakEnergy)
    (hD : morseAnnihilationL2 α w U = 0) :
    ∃ c : ℝ, (morseEnergyBase U : ℝ → ℝ) =ᵐ[volume] fun x => c * morseGround α w x := by
  let I := morseIntegratingFactor α w
  let u := morseEnergyBase U
  let F (x : ℝ) := I x * u x
  have hI : ContDiff ℝ ∞ I := morseIntegratingFactor_contDiff α w
  have hF : LocallyIntegrable F volume := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    obtain ⟨C, hC⟩ := hK.bddAbove_image hI.continuous.norm.continuousOn
    have hu := (Lp.memLp u).locallyIntegrable (by norm_num)
    apply (hu.integrableOn_isCompact hK).bdd_mul hI.continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hC (mem_image_of_mem _ hx)
  have hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x : ℝ, F x * deriv φ x) = 0 := by
    intro φ hφ hc
    let ψ (x : ℝ) := I x * φ x
    have hψ : ContDiff ℝ ∞ ψ := hI.mul hφ
    have hcψ : HasCompactSupport ψ := hc.mul_left
    have hpair := morseAnnihilationL2_compact_adjoint α w U hψ hcψ
    dsimp only at hpair
    rw [hD, inner_zero_left] at hpair
    have hcancel (x : ℝ) : morseCreation α w ψ x = -I x * deriv φ x := by
      have hdψ : deriv ψ x = deriv I x * φ x + I x * deriv φ x :=
        (((hI.differentiable (by simp) x).hasDerivAt).mul ((hφ.differentiable (by simp) x).hasDerivAt)).deriv
      unfold morseCreation
      rw [hdψ]
      have hId : deriv I x = (α - w * exp (-x)) * I x := morseIntegratingFactor_deriv α w x
      rw [hId]
      dsimp [ψ]
      ring
    have he : (∫ x : ℝ, u x * morseCreation α w ψ x) = -(∫ x : ℝ, F x * deriv φ x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hcancel x]
      dsimp [F]
      ring
    change 0 = ∫ x : ℝ, u x * morseCreation α w ψ x at hpair
    rw [he] at hpair
    linarith
  obtain ⟨c, hc⟩ := morse_ae_constant_of_weak_deriv_zero hF hweak
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change I x * u x = c at hx
  change u x = c * morseGround α w x
  have hIg : I x * morseGround α w x = 1 := morseIntegratingFactor_mul_ground α w x
  calc
    _ = (I x * morseGround α w x) * u x := by
      rw [hIg, one_mul]
    _ = (I x * u x) * morseGround α w x := by ring
    _ = _ := by rw [hx]

theorem morseAnnihilationL2_eq_zero_implies_pos {α w : ℝ} (hw : 0 < w) (U : MorseWeakEnergy)
    (hu : morseEnergyBase U ≠ 0) (hD : morseAnnihilationL2 α w U = 0) : 0 < α := by
  obtain ⟨c, hc⟩ := morseAnnihilationL2_ae_ground U hD
  have hc₀ : c ≠ 0 := by
    intro hz
    apply hu
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hc] with x hx
    simp only [hx, hz, zero_mul, Pi.zero_apply]
  have hmem : MemLp (fun x => c * morseGround α w x) 2 volume :=
    (memLp_congr_ae hc).mp (Lp.memLp (morseEnergyBase U))
  have he : (c⁻¹ • (fun x => c * morseGround α w x)) =ᵐ[volume] morseGround α w := by
    apply Eventually.of_forall
    intro x
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  exact (memLp_morseGround_iff hw).mp ((memLp_congr_ae he).mp (hmem.const_smul c⁻¹))

def morseGroundL2 {α w : ℝ} (hα : 0 < α) (hw : 0 < w) : MorseL2 :=
  (memLp_morseGround hα hw).toLp (morseGround α w)

theorem morseGroundL2_ae {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    (morseGroundL2 hα hw : ℝ → ℝ) =ᵐ[volume] morseGround α w :=
  MemLp.coeFn_toLp (memLp_morseGround hα hw)

theorem morseGroundL2_ne_zero {α w : ℝ} (hα : 0 < α) (hw : 0 < w) :
    morseGroundL2 hα hw ≠ 0 := by
  intro hz
  have hz' := Lp.eq_zero_iff_ae_eq_zero.mp hz
  obtain ⟨x, hx⟩ := ((morseGroundL2_ae hα hw).symm.trans hz').exists
  exact (morseGround_pos α w x).ne' hx

theorem morseGroundL2_mem_graph {α w : ℝ} (hα : 0 < α) (hw : 0 < w) (b : ℝ) :
    (morseGroundL2 hα hw, (b - α ^ 2) • morseGroundL2 hα hw) ∈ morseAssociatedGraph α w b := by
  let hE := morseGround_energyDomain hα hw
  let U := morseEnergyLift hE
  have hD : morseAnnihilationL2 α w U = 0 := by
    let hA := morseAnnihilation_memLp_of_energy hE α w
    change morseAnnihilationL2 α w (morseEnergyLift hE) = 0
    rw [morseAnnihilationL2_lift hE α w hA]
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [MemLp.coeFn_toLp hA] with x hx
    simpa only [morseAnnihilation_ground, Pi.zero_apply] using hx
  refine ⟨U, rfl, ?_⟩
  intro W
  change morsePhysicalForm α w b U W = ⟪(b - α ^ 2) • morseEnergyBase U, morseEnergyBase W⟫_ℝ
  rw [morsePhysicalForm_factorization, hD, inner_zero_left, zero_add, real_inner_smul_left]

/-- The actual weak ground eigenspace is the span of the nonzero `L²`
ground function. -/
theorem morseGround_weakGraph_iff_span {α w : ℝ} (hα : 0 < α) (hw : 0 < w) (b : ℝ) (u : MorseL2) :
    Statements.WeakSchrodingerGraph (morsePartnerPotential α w b) u ((b - α ^ 2) • u) ↔
      ∃ c : ℝ, u = c • morseGroundL2 hα hw := by
  rw [morsePartner_weakGraph_iff_associated α b hw]
  constructor
  · intro hu
    have hu' := hu
    obtain ⟨U, hU, _⟩ := hu
    change morseEnergyBase U = u at hU
    have hgraph : (morseEnergyBase U, (b - α ^ 2) • morseEnergyBase U) ∈ morseAssociatedGraph α w b := by
      rw [hU]
      exact hu'
    have hnorm : ‖morseAnnihilationL2 α w U‖ ^ 2 = 0 := by
      rw [morseAnnihilationL2_eigen_norm_sq U hgraph]
      ring
    obtain ⟨c, hc⟩ := morseAnnihilationL2_ae_ground U (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
    refine ⟨c, ?_⟩
    rw [← hU]
    apply Lp.ext
    filter_upwards [hc, Lp.coeFn_smul c (morseGroundL2 hα hw), morseGroundL2_ae hα hw] with x hcx hs hg
    rw [hcx, hs]
    simp only [Pi.smul_apply, smul_eq_mul, hg]
  · rintro ⟨c, rfl⟩
    rw [smul_comm (b - α ^ 2) c]
    exact (morseAssociatedGraph α w b).smul_mem c (morseGroundL2_mem_graph hα hw b)

private theorem morseWeight_inner_self_nonneg (U : MorseWeakEnergy) :
    0 ≤ ⟪morseEnergyWeight U, morseEnergyBase U⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [morseEnergyWeight_ae U] with x hx
  simp only [RCLike.inner_apply, conj_trivial, hx, Pi.zero_apply]
  nlinarith only [mul_nonneg (exp_pos (-x)).le (sq_nonneg (morseEnergyBase U x))]

theorem morsePhysicalForm_threshold_le_of_nonpos {α w : ℝ} (hα : α ≤ 0) (hw : 0 ≤ w)
    (b : ℝ) (U : MorseWeakEnergy) :
    b * ‖morseEnergyBase U‖ ^ 2 ≤ morsePhysicalForm α w b U U := by
  have hq := morsePhysicalForm_factorization 0 w b U U
  simp only [real_inner_self_eq_norm_sq, zero_pow (by decide : 2 ≠ 0), sub_zero] at hq
  have hd : morsePhysicalForm α w b U U - morsePhysicalForm 0 w b U U =
      (-2 * w * α) * ⟪morseEnergyWeight U, morseEnergyBase U⟫_ℝ := by
    simp only [morsePhysicalForm_apply]
    ring
  have hcoef : 0 ≤ -2 * w * α := by
    have h := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw) (neg_nonneg.mpr hα)
    nlinarith only [h]
  linarith only [hq, hd, sq_nonneg ‖morseAnnihilationL2 0 w U‖,
    mul_nonneg hcoef (morseWeight_inner_self_nonneg U)]

theorem not_morsePartnerEigen_lt_threshold_of_nonpos {α w : ℝ} (hα : α ≤ 0) (hw : 0 < w)
    (b E : ℝ) (hE : E < b) : ¬ Statements.ActualEigenvalue (morsePartnerPotential α w b) E := by
  rintro ⟨u, hu, hweak⟩
  have hgraph := (morsePartner_weakGraph_iff_associated α b hw u (E • u)).mp hweak
  obtain ⟨U, hU, hpair⟩ := hgraph
  change morseEnergyBase U = u at hU
  have hq := hpair U
  change morsePhysicalForm α w b U U = ⟪E • u, morseEnergyBase U⟫_ℝ at hq
  rw [hU, real_inner_smul_left, real_inner_self_eq_norm_sq] at hq
  have hb := morsePhysicalForm_threshold_le_of_nonpos hα hw.le b U
  rw [hU, hq] at hb
  have hnorm := sq_pos_of_pos (norm_pos_iff.mpr hu)
  exact (not_le.mpr (mul_lt_mul_of_pos_right hE hnorm)) hb

end ContinuousFlexibility.Radial
