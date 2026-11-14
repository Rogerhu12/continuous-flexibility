module

public import ContinuousFlexibility.Analysis.CylinderTestPairing
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Periodic extension from the cylinder to the plane

The half-open angular tiles are disjoint and each carries the actual
cylinder measure under translation. Compactly supported tests can be
summed over the translates and transferred to the defining weak equations.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

private def cylinderBaseTile : Set PolarPoint := univ ×ˢ Ico 0 Real.pi

private theorem measurableSet_cylinderBaseTile : MeasurableSet cylinderBaseTile :=
  MeasurableSet.univ.prod measurableSet_Ico

private theorem materialCylinderMeasure_eq_restrict_baseTile :
    materialCylinderMeasure = volume.restrict cylinderBaseTile := by
  rw [materialCylinderMeasure_eq_prod]
  change (volume : Measure ℝ).prod angleMeasure =
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ico 0 Real.pi)
  rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h : (volume : Measure ℝ).restrict (Ico 0 Real.pi) = angleMeasure :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [h]

def cylinderAngularShift (k : ℤ) : PolarPoint ≃ᵐ PolarPoint where
  toFun := fun p => (p.1, p.2 + k • Real.pi)
  invFun := fun p => (p.1, p.2 - k • Real.pi)
  left_inv := by rintro ⟨x, θ⟩; simp
  right_inv := by rintro ⟨x, θ⟩; simp
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add_const _)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub_const _)

private theorem measurePreserving_cylinderAngularShift (k : ℤ) :
    MeasurePreserving (cylinderAngularShift k) volume volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (k • Real.pi))

def cylinderAngleTile (k : ℤ) : Set PolarPoint :=
  (cylinderAngularShift k).symm ⁻¹' cylinderBaseTile

theorem measurableSet_cylinderAngleTile (k : ℤ) : MeasurableSet (cylinderAngleTile k) :=
  (cylinderAngularShift k).symm.measurable measurableSet_cylinderBaseTile

private theorem mem_cylinderAngleTile_iff (p : PolarPoint) (k : ℤ) :
    p ∈ cylinderAngleTile k ↔ toIcoDiv Real.pi_pos 0 p.2 = k := by
  change ((p.1, p.2 - k • Real.pi) ∈ cylinderBaseTile) ↔ _
  simp only [cylinderBaseTile, mem_prod, mem_univ, true_and]
  simpa only [zero_add] using (toIcoDiv_eq_iff (n := k) (a := 0) (b := p.2) Real.pi_pos).symm

private theorem cylinderAngleTile_disjoint {k j : ℤ} (hkj : k ≠ j) :
    Disjoint (cylinderAngleTile k) (cylinderAngleTile j) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact hkj (((mem_cylinderAngleTile_iff p k).mp hp).symm.trans
    ((mem_cylinderAngleTile_iff p j).mp hq))

theorem measurePreserving_cylinderAngularShift_to_tile (k : ℤ) :
    MeasurePreserving (cylinderAngularShift k) materialCylinderMeasure
      (volume.restrict (cylinderAngleTile k)) := by
  have hpre : cylinderAngularShift k ⁻¹' cylinderAngleTile k = cylinderBaseTile := by
    ext p
    change (cylinderAngularShift k).symm (cylinderAngularShift k p) ∈ cylinderBaseTile ↔ _
    rw [MeasurableEquiv.symm_apply_apply]
  have h := (measurePreserving_cylinderAngularShift k).restrict_preimage (measurableSet_cylinderAngleTile k)
  rwa [hpre, ← materialCylinderMeasure_eq_restrict_baseTile] at h

/-- The periodic extension using the unique representative in the half-open base tile. -/
def cylinderPeriodicExtension (u : CylinderL2) (p : PolarPoint) : ℝ :=
  u (p.1, toIcoMod Real.pi_pos 0 p.2)

theorem cylinderPeriodicExtension_periodic (u : CylinderL2) :
    Function.Periodic (cylinderPeriodicExtension u) (0, Real.pi) := by
  intro p
  change u (p.1 + 0, toIcoMod Real.pi_pos 0 (p.2 + Real.pi)) = _
  rw [add_zero, toIcoMod_add_right, cylinderPeriodicExtension]

private theorem cylinderPeriodicExtension_eq_of_mem_tile (u : CylinderL2) {p : PolarPoint} {k : ℤ}
    (hp : p ∈ cylinderAngleTile k) :
    cylinderPeriodicExtension u p = u ((cylinderAngularShift k).symm p) := by
  have hk := (mem_cylinderAngleTile_iff p k).mp hp
  change u (p.1, toIcoMod Real.pi_pos 0 p.2) = u (p.1, p.2 - k • Real.pi)
  rw [toIcoMod, hk]

private theorem cylinderPeriodicExtension_shift_eq (u : CylinderL2) {p : PolarPoint}
    (hp : p ∈ cylinderBaseTile) (k : ℤ) : cylinderPeriodicExtension u (cylinderAngularShift k p) = u p := by
  have hmod : toIcoMod Real.pi_pos 0 p.2 = p.2 :=
    (toIcoMod_eq_self Real.pi_pos).mpr (by simpa only [zero_add] using hp.2)
  change u (p.1, toIcoMod Real.pi_pos 0 (p.2 + k • Real.pi)) = u p
  rw [toIcoMod_add_zsmul, hmod]

theorem cylinderPeriodicExtension_ae (u : CylinderL2) :
    cylinderPeriodicExtension u =ᵐ[materialCylinderMeasure] (u : PolarPoint → ℝ) := by
  have hbase : ∀ᵐ p ∂materialCylinderMeasure, p ∈ cylinderBaseTile := by
    rw [materialCylinderMeasure_eq_restrict_baseTile]
    exact ae_restrict_mem measurableSet_cylinderBaseTile
  filter_upwards [hbase] with p hp
  have hmod : toIcoMod Real.pi_pos 0 p.2 = p.2 :=
    (toIcoMod_eq_self Real.pi_pos).mpr (by simpa only [zero_add] using hp.2)
  simp only [cylinderPeriodicExtension, hmod]

theorem memLp_cylinderPeriodicExtension_tile (u : CylinderL2) (k : ℤ) :
    MemLp (cylinderPeriodicExtension u) 2 (volume.restrict (cylinderAngleTile k)) := by
  have h := (Lp.memLp u).comp_measurePreserving
    (MeasurePreserving.symm (cylinderAngularShift k) (measurePreserving_cylinderAngularShift_to_tile k))
  apply MemLp.ae_eq _ h
  filter_upwards [ae_restrict_mem (measurableSet_cylinderAngleTile k)] with p hp
  exact (cylinderPeriodicExtension_eq_of_mem_tile u hp).symm

private theorem exists_cylinderAngularCutoff (R S : ℝ) :
    ∃ N : ℕ, ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → ∀ θ : ℝ,
      |θ| ≤ S → R < |θ + k • Real.pi| := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + S) / Real.pi)
  refine ⟨N, fun k hk θ hθ => ?_⟩
  have hbig : (N : ℝ) < |(k : ℝ)| := by
    apply lt_of_not_ge
    intro h
    have ha := abs_le.mp h
    apply hk
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast ha.1, by exact_mod_cast ha.2⟩
  have hN' := (div_lt_iff₀ Real.pi_pos).mp hN
  have hp := mul_lt_mul_of_pos_right hbig Real.pi_pos
  have he : (θ + (k : ℝ) * Real.pi) + -θ = (k : ℝ) * Real.pi := by ring
  have ht := abs_add_le (θ + (k : ℝ) * Real.pi) (-θ)
  rw [he, abs_neg, abs_mul, abs_of_pos Real.pi_pos] at ht
  rw [zsmul_eq_mul]
  linarith only [hp, hN', ht, hθ]

private theorem cylinderAngleTile_outside_cutoff {R : ℝ} {N : ℕ}
    (hN : ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → ∀ θ : ℝ,
      |θ| ≤ Real.pi → R < |θ + k • Real.pi|)
    {k : ℤ} (hk : k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) {p : PolarPoint}
    (hp : p ∈ cylinderAngleTile k) : R < |p.2| := by
  let q := (cylinderAngularShift k).symm p
  have hq : q ∈ cylinderBaseTile := hp
  have hθ : |q.2| ≤ Real.pi := by
    rw [abs_of_nonneg hq.2.1]
    exact hq.2.2.le
  have he : q.2 + k • Real.pi = p.2 :=
    congrArg Prod.snd ((cylinderAngularShift k).apply_symm_apply p)
  rw [← he]
  exact hN k hk q.2 hθ

private theorem cylinderAngleTile_indicator_sum_of_mem {S : Finset ℤ} {k : ℤ} {p : PolarPoint}
    (hk : k ∈ S) (hp : p ∈ cylinderAngleTile k) (f : PolarPoint → ℝ) :
    (∑ j ∈ S, (cylinderAngleTile j).indicator f p) = f p := by
  rw [Finset.sum_eq_single_of_mem k hk]
  · exact indicator_of_mem hp _
  · intro j _ hjk
    exact indicator_of_notMem (fun h => Set.disjoint_left.mp (cylinderAngleTile_disjoint hjk) h hp) _

/-- The actual periodic extension is square-integrable on each compact restriction. -/
theorem memLp_cylinderPeriodicExtension_restrict_compact (u : CylinderL2) {K : Set PolarPoint}
    (hK : IsCompact K) : MemLp (cylinderPeriodicExtension u) 2 (volume.restrict K) := by
  obtain ⟨R, hR⟩ := hK.bddAbove_image (continuous_norm.comp continuous_snd).continuousOn
  obtain ⟨N, hN⟩ := exists_cylinderAngularCutoff R Real.pi
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let g (p : PolarPoint) := ∑ k ∈ S, (cylinderAngleTile k).indicator (cylinderPeriodicExtension u) p
  have hg : MemLp g 2 volume := memLp_finsetSum S (fun k _ =>
    (memLp_indicator_iff_restrict (measurableSet_cylinderAngleTile k)).mpr
      (memLp_cylinderPeriodicExtension_tile u k))
  apply MemLp.ae_eq _ (hg.mono_measure Measure.restrict_le_self)
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with p hp
  let k := toIcoDiv Real.pi_pos 0 p.2
  have hpk : p ∈ cylinderAngleTile k := (mem_cylinderAngleTile_iff p k).mpr rfl
  have hple : |p.2| ≤ R := by
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hR ⟨p, hp, rfl⟩
  have hk : k ∈ S := by
    by_contra h
    exact (not_lt_of_ge hple) (cylinderAngleTile_outside_cutoff hN h hpk)
  exact cylinderAngleTile_indicator_sum_of_mem hk hpk _

private theorem exists_cylinderCompactSupportBounds {ψ : PolarPoint → ℝ} (hψ : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 < R ∧ (∀ p : PolarPoint, R ≤ |p.1| → ψ p = 0) ∧
      ∀ p : PolarPoint, R ≤ |p.2| → ψ p = 0 := by
  obtain ⟨M, hM⟩ := hψ.bddAbove_image continuous_norm.continuousOn
  let R := max 0 M + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (le_max_left _ _) zero_lt_one
  have hMR : M < R := (le_max_right _ _).trans_lt (lt_add_of_pos_right _ zero_lt_one)
  have he (p : PolarPoint) (hp : R ≤ ‖p‖) : ψ p = 0 := by
    by_contra h
    have hb := hM ⟨p, subset_tsupport ψ h, rfl⟩
    exact (not_lt_of_ge (hp.trans hb)) hMR
  refine ⟨R, hR, fun p hp => he p (hp.trans ?_), fun p hp => he p (hp.trans ?_)⟩
  · simpa only [Real.norm_eq_abs] using norm_fst_le p
  · simpa only [Real.norm_eq_abs] using norm_snd_le p

private theorem mixedDerivative_zero_of_angular_bound {ψ : PolarPoint → ℝ} {R : ℝ}
    (hzero : ∀ p : PolarPoint, R ≤ |p.2| → ψ p = 0) (a b : ℕ) (p : PolarPoint)
    (hp : R < |p.2|) : mixedDerivative a b ψ p = 0 := by
  have hn : ∀ᶠ θ : ℝ in 𝓝 p.2, R < |θ| :=
    continuousAt_const.eventually_lt continuous_abs.continuousAt hp
  have he : (fun r => iteratedDeriv b (fun θ => ψ (r, θ)) p.2) = (0 : ℝ → ℝ) := by
    funext r
    have hs : (fun θ : ℝ => ψ (r, θ)) =ᶠ[𝓝 p.2] (0 : ℝ → ℝ) := by
      filter_upwards [hn] with θ hθ
      exact hzero (r, θ) hθ.le
    simpa only [iteratedDeriv_const_zero, Pi.zero_apply] using hs.iteratedDeriv_eq b
  unfold mixedDerivative
  rw [he, iteratedDeriv_const_zero]

theorem hasCompactSupport_mixedDerivative {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (a b : ℕ) : HasCompactSupport (mixedDerivative a b ψ) := by
  obtain ⟨R, _, hx, hθ⟩ := exists_cylinderCompactSupportBounds hc
  let K : Set PolarPoint := Icc (-R) R ×ˢ Icc (-R) R
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro p hp
  refine ⟨abs_le.mp (le_of_not_gt fun h => hp ?_), abs_le.mp (le_of_not_gt fun h => hp ?_)⟩
  · exact mixedDerivative_zero_of_radial_support hψ hx a b p h.le
  · exact mixedDerivative_zero_of_angular_bound hθ a b p h

/-- Periodization of a planar test by actual integral angular translates. -/
def cylinderTestPeriodization (ψ : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  ∑' k : ℤ, ψ (cylinderAngularShift k p)

theorem cylinderTestPeriodization_periodic (ψ : PolarPoint → ℝ) :
    Function.Periodic (cylinderTestPeriodization ψ) (0, Real.pi) := by
  intro p
  have he (k : ℤ) : cylinderAngularShift k (p + (0, Real.pi)) = cylinderAngularShift (k + 1) p := by
    change (p.1 + 0, p.2 + Real.pi + k • Real.pi) = (p.1, p.2 + (k + 1) • Real.pi)
    rw [add_zero, add_zsmul, one_zsmul]
    congr 1
    ring
  simp only [cylinderTestPeriodization, he]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun k : ℤ => ψ (cylinderAngularShift k p))

private theorem cylinderTestPeriodization_eq_sum_on {ψ : PolarPoint → ℝ} {R S : ℝ} {N : ℕ}
    (hzero : ∀ p : PolarPoint, R < |p.2| → ψ p = 0)
    (hN : ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → ∀ θ : ℝ,
      |θ| ≤ S → R < |θ + k • Real.pi|) (p : PolarPoint) (hp : |p.2| ≤ S) :
    cylinderTestPeriodization ψ p = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ψ (cylinderAngularShift k p) := by
  unfold cylinderTestPeriodization
  apply tsum_eq_sum
  intro k hk
  exact hzero _ (hN k hk p.2 hp)

private theorem contDiff_cylinderAngularShift (k : ℤ) :
    ContDiff ℝ ∞ (cylinderAngularShift k : PolarPoint → PolarPoint) :=
  contDiff_fst.prodMk (contDiff_snd.add contDiff_const)

/-- Compact planar tests give actual smooth periodic cylinder tests. -/
theorem isCylinderTest_cylinderTestPeriodization {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) : IsCylinderTest (cylinderTestPeriodization ψ) := by
  obtain ⟨R, hR, hx, hθ⟩ := exists_cylinderCompactSupportBounds hc
  refine ⟨?_, cylinderTestPeriodization_periodic ψ, R, hR, fun p hp => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    obtain ⟨N, hN⟩ := exists_cylinderAngularCutoff R (|p.2| + 1)
    let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hs : ContDiff ℝ ∞ (fun q => ∑ k ∈ S, ψ (cylinderAngularShift k q)) :=
      ContDiff.sum (fun k _ => hψ.comp (contDiff_cylinderAngularShift k))
    apply hs.contDiffAt.congr_of_eventuallyEq
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, |q.2| < |p.2| + 1 :=
      (continuous_abs.comp continuous_snd).continuousAt.eventually_lt continuousAt_const
        (lt_add_of_pos_right _ zero_lt_one)
    filter_upwards [hnear] with q hq
    exact cylinderTestPeriodization_eq_sum_on (fun q h => hθ q h.le) hN q hq.le
  · unfold cylinderTestPeriodization
    have hz (k : ℤ) : ψ (cylinderAngularShift k p) = 0 := hx _ hp
    simp only [hz, tsum_zero]

private theorem mixedDerivative_congr_angular_window {f g : PolarPoint → ℝ} {S : ℝ}
    (he : ∀ p : PolarPoint, |p.2| ≤ S → f p = g p) (a b : ℕ) (p : PolarPoint)
    (hp : |p.2| < S) : mixedDerivative a b f p = mixedDerivative a b g p := by
  have hn : ∀ᶠ θ : ℝ in 𝓝 p.2, |θ| < S :=
    continuous_abs.continuousAt.eventually_lt continuousAt_const hp
  have hh : (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) =
      (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    funext r
    have hg : (fun θ : ℝ => f (r, θ)) =ᶠ[𝓝 p.2] (fun θ => g (r, θ)) := by
      filter_upwards [hn] with θ hθ
      exact he (r, θ) hθ.le
    exact hg.iteratedDeriv_eq b
  unfold mixedDerivative
  rw [hh]

private theorem mixedDerivative_sum {ι : Type*} {S : Finset ι} {f : ι → PolarPoint → ℝ}
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i)) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => ∑ i ∈ S, f i q) p = ∑ i ∈ S, mixedDerivative a b (f i) p := by
  have ha (r : ℝ) : iteratedDeriv b (fun θ => ∑ i ∈ S, f i (r, θ)) p.2 =
      ∑ i ∈ S, iteratedDeriv b (fun θ => f i (r, θ)) p.2 :=
    iteratedDeriv_fun_sum (fun i hi => ((hf i hi).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hs (i : ι) (hi : i ∈ S) : ContDiff ℝ ∞
      (fun r => iteratedDeriv b (fun θ => f i (r, θ)) p.2) := by
    have hslice : ContDiff ℝ ∞ (fun r : ℝ => (r, p.2)) := contDiff_id.prodMk contDiff_const
    have h := (contDiff_mixedDerivative (hf i hi) 0 b).comp hslice
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero] using h
  unfold mixedDerivative
  simp_rw [ha]
  exact iteratedDeriv_fun_sum (fun i hi => (hs i hi).contDiffAt.of_le (by simp))

private theorem mixedDerivative_cylinderAngularShift (ψ : PolarPoint → ℝ) (k : ℤ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => ψ (cylinderAngularShift k q)) p =
      mixedDerivative a b ψ (cylinderAngularShift k p) := by
  change iteratedDeriv a (fun r => iteratedDeriv b (fun θ => ψ (r, θ + k • Real.pi)) p.2) p.1 =
    iteratedDeriv a (fun r => iteratedDeriv b (fun θ => ψ (r, θ)) (p.2 + k • Real.pi)) p.1
  apply congrArg (fun d : ℝ → ℝ => iteratedDeriv a d p.1)
  funext r
  exact congrFun (iteratedDeriv_comp_add_const b (fun θ : ℝ => ψ (r, θ)) (k • Real.pi)) p.2

theorem mixedDerivative_cylinderTestPeriodization {ψ : PolarPoint → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (a b : ℕ) :
    mixedDerivative a b (cylinderTestPeriodization ψ) = cylinderTestPeriodization (mixedDerivative a b ψ) := by
  obtain ⟨R, _, _, hθ⟩ := exists_cylinderCompactSupportBounds hc
  funext p
  obtain ⟨N, hN⟩ := exists_cylinderAngularCutoff R (|p.2| + 1)
  have hp : |p.2| < |p.2| + 1 := lt_add_of_pos_right _ zero_lt_one
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have he (q : PolarPoint) (hq : |q.2| ≤ |p.2| + 1) :
      cylinderTestPeriodization ψ q = ∑ k ∈ S, ψ (cylinderAngularShift k q) :=
    cylinderTestPeriodization_eq_sum_on (fun q h => hθ q h.le) hN q hq
  rw [mixedDerivative_congr_angular_window he a b p hp,
    mixedDerivative_sum (f := fun k q => ψ (cylinderAngularShift k q))
      (fun k _ => hψ.comp (contDiff_cylinderAngularShift k))]
  simp_rw [mixedDerivative_cylinderAngularShift]
  exact (cylinderTestPeriodization_eq_sum_on (mixedDerivative_zero_of_angular_bound hθ a b) hN p hp.le).symm

/-- Splitting the plane into half-open angular tiles converts the integral pairing. -/
theorem integral_cylinderPeriodicExtension_mul (u : CylinderL2) {ψ : PolarPoint → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    (∫ p, cylinderPeriodicExtension u p * ψ p) =
      ∫ p, u p * cylinderTestPeriodization ψ p ∂materialCylinderMeasure := by
  obtain ⟨R, _, _, hθ⟩ := exists_cylinderCompactSupportBounds hc
  obtain ⟨N, hN⟩ := exists_cylinderAngularCutoff R Real.pi
  let S := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let F (p : PolarPoint) := cylinderPeriodicExtension u p * ψ p
  have hψLp : MemLp ψ 2 volume := hψ.memLp_of_hasCompactSupport hc
  have hi (k : ℤ) : Integrable F (volume.restrict (cylinderAngleTile k)) :=
    (memLp_cylinderPeriodicExtension_tile u k).integrable_mul
      (hψLp.mono_measure Measure.restrict_le_self)
  have hbase : ∀ᵐ p ∂materialCylinderMeasure, p ∈ cylinderBaseTile := by
    rw [materialCylinderMeasure_eq_restrict_baseTile]
    exact ae_restrict_mem measurableSet_cylinderBaseTile
  have hpart : F = fun p => ∑ k ∈ S, (cylinderAngleTile k).indicator F p := by
    funext p
    let k := toIcoDiv Real.pi_pos 0 p.2
    have hpk : p ∈ cylinderAngleTile k := (mem_cylinderAngleTile_iff p k).mpr rfl
    by_cases hk : k ∈ S
    · exact (cylinderAngleTile_indicator_sum_of_mem hk hpk F).symm
    · have hf0 : F p = 0 := by
        unfold F
        rw [hθ p (cylinderAngleTile_outside_cutoff hN hk hpk).le, mul_zero]
      rw [hf0]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      exact indicator_of_notMem (fun hpj => Set.disjoint_left.mp (cylinderAngleTile_disjoint hjk) hpj hpk) _
  have hshift (k : ℤ) : (F ∘ cylinderAngularShift k) =ᵐ[materialCylinderMeasure]
      (fun p => u p * ψ (cylinderAngularShift k p)) := by
    filter_upwards [hbase] with p hp
    change cylinderPeriodicExtension u (cylinderAngularShift k p) * ψ (cylinderAngularShift k p) = _
    rw [cylinderPeriodicExtension_shift_eq u hp]
  have hiShift (k : ℤ) : Integrable (fun p => u p * ψ (cylinderAngularShift k p)) materialCylinderMeasure :=
    (((measurePreserving_cylinderAngularShift_to_tile k).integrable_comp_emb
      (cylinderAngularShift k).measurableEmbedding).mpr (hi k)).congr (hshift k)
  change (∫ p, F p) = _
  calc
    (∫ p, F p) = ∫ p, ∑ k ∈ S, (cylinderAngleTile k).indicator F p :=
      congrArg (fun v : PolarPoint → ℝ => ∫ p, v p) hpart
    _ = ∑ k ∈ S, ∫ p, (cylinderAngleTile k).indicator F p :=
      integral_finsetSum S (fun k _ => (integrable_indicator_iff (measurableSet_cylinderAngleTile k)).mpr (hi k))
    _ = ∑ k ∈ S, ∫ p, u p * ψ (cylinderAngularShift k p) ∂materialCylinderMeasure := by
      apply Finset.sum_congr rfl
      intro k _
      rw [integral_indicator (measurableSet_cylinderAngleTile k),
        ← (measurePreserving_cylinderAngularShift_to_tile k).integral_comp' F]
      exact integral_congr_ae (hshift k)
    _ = ∫ p, ∑ k ∈ S, u p * ψ (cylinderAngularShift k p) ∂materialCylinderMeasure :=
      (integral_finsetSum S (fun k _ => hiShift k)).symm
    _ = ∫ p, u p * cylinderTestPeriodization ψ p ∂materialCylinderMeasure := by
      apply integral_congr_ae
      filter_upwards [hbase] with p hp
      have hple : |p.2| ≤ Real.pi := by
        rw [abs_of_nonneg hp.2.1]
        exact hp.2.2.le
      rw [cylinderTestPeriodization_eq_sum_on (fun q h => hθ q h.le) hN p hple, Finset.mul_sum]

/-- The cylinder weak identity gives the ordinary distribution identity for every
smooth compactly supported planar test, including tests crossing the angular seam. -/
theorem HasWeakMixedDerivative.periodicExtension_test {f g : CylinderL2} {a b : ℕ}
    (h : HasWeakMixedDerivative f g a b) {ψ : PolarPoint → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ p, cylinderPeriodicExtension g p * ψ p) =
      (-1 : ℝ) ^ (a + b) * ∫ p, cylinderPeriodicExtension f p * mixedDerivative a b ψ p := by
  rw [integral_cylinderPeriodicExtension_mul g hψ.continuous hc,
    integral_cylinderPeriodicExtension_mul f (contDiff_mixedDerivative hψ a b).continuous
      (hasCompactSupport_mixedDerivative hψ hc a b), ← mixedDerivative_cylinderTestPeriodization hψ hc]
  exact h _ (isCylinderTest_cylinderTestPeriodization hψ hc)

end ContinuousFlexibility.Statements
