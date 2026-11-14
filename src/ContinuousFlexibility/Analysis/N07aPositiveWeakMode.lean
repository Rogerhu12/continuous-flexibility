module

public import ContinuousFlexibility.Analysis.N07aPositiveUnitBounds
public import ContinuousFlexibility.Analysis.N07aIntervalWeakSecond

/-!
# Closing the positive mode estimate from its actual weak equation

The first weak derivative and the second-order test equation recover a
genuine second weak derivative. The cubic estimate then follows by smooth
approximation, with all coefficient constants supplied by primitive
reference geometry. No smooth representative or endpoint condition is used.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff Topology

private theorem n07a_mode_pairing_congr {f g φ : ℝ → ℝ}
    (he : f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] g)
    (hs : tsupport φ ⊆ Ioo (0 : ℝ) 1) :
    (∫ x, f x * φ x) = ∫ x, g x * φ x := by
  have h := (ae_restrict_iff' measurableSet_Ioo).mp he
  apply integral_congr_ae
  filter_upwards [h] with x hx
  by_cases hxi : x ∈ Ioo (0 : ℝ) 1
  · rw [hx hxi]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => hxi (hs ht)), mul_zero, mul_zero]

private theorem n07a_positive_mode_energy
    {a c V q : ℝ → ℝ} {J j : ℝ}
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1))
    (hc : ContDiffOn ℝ ∞ c (Ioo (0 : ℝ) 1))
    (hV : ContDiffOn ℝ ∞ V (Ioo (0 : ℝ) 1))
    (hq : ContDiffOn ℝ ∞ q (Ioo (0 : ℝ) 1)) (hJ : 1 ≤ J)
    (hab : ∀ x ∈ Ioo (0 : ℝ) 1, 1 / J ≤ a x ∧ a x ≤ J ∧ |deriv a x| ≤ J)
    (hcb : ∀ x ∈ Ioo (0 : ℝ) 1, cylinderWeight x / J ≤ c x ∧ |c x| ≤ J)
    (hVb : ∀ x ∈ Ioo (0 : ℝ) 1, |V x| ≤ J)
    (hqa : ∀ x ∈ Ioo (0 : ℝ) 1, c x = a x * q x)
    (hqb : ∀ x ∈ Ioo (0 : ℝ) 1, |deriv (deriv q) x| ≤ J)
    (u d F : N07aIntervalL2) (hud : HasIntervalWeakDerivative 0 1 u d)
    (heq : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x, u x * deriv (fun y => a y * deriv φ y) x) =
          ∫ x, (j ^ 2 * c x * u x + V x * u x - F x) * φ x) :
    ∃ dd : N07aIntervalL2, HasIntervalWeakDerivative 0 1 d dd ∧
      n07aCylinderEnergy j u d dd ≤ 16384 * J ^ 10 * (‖F‖ ^ 2 + ‖u‖ ^ 2) := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hJpos : 0 < J := zero_lt_one.trans_le hJ
  have hapos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < a x :=
    (one_div_pos.mpr hJpos).trans_le (hab x hx).1
  have hai (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : |(a x)⁻¹| ≤ J := by
    have h := (div_le_iff₀ hJpos).mp (hab x hx).1
    have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hapos x hx).le)
    simpa only [abs_of_pos (inv_pos.mpr (hapos x hx)), mul_one, ← mul_assoc,
      inv_mul_cancel₀ (hapos x hx).ne', one_mul] using hh
  have hcL : MemLp (fun x => c x * u x) 2 μ :=
    l2Multiplier_memLp μ (hc.continuousOn.aestronglyMeasurable measurableSet_Ioo)
      ((ae_restrict_mem measurableSet_Ioo).mono fun x hx => (hcb x hx).2) u
  have hvL : MemLp (fun x => V x * u x) 2 μ :=
    l2Multiplier_memLp μ (hV.continuousOn.aestronglyMeasurable measurableSet_Ioo)
      ((ae_restrict_mem measurableSet_Ioo).mono hVb) u
  let cu : N07aIntervalL2 := hcL.toLp (fun x => c x * u x)
  let vu : N07aIntervalL2 := hvL.toLp (fun x => V x * u x)
  let H : N07aIntervalL2 := j ^ 2 • cu + vu - F
  have hH : (H : ℝ → ℝ) =ᵐ[μ] fun x => j ^ 2 * c x * u x + V x * u x - F x := by
    filter_upwards [Lp.coeFn_sub (j ^ 2 • cu + vu) F,
      Lp.coeFn_add (j ^ 2 • cu) vu, Lp.coeFn_smul (j ^ 2) cu,
      hcL.coeFn_toLp, hvL.coeFn_toLp] with x hsub hadd hsmul hcu hvu
    dsimp only [H]
    rw [hsub, Pi.sub_apply, hadd, Pi.add_apply, hsmul, Pi.smul_apply,
      smul_eq_mul, hcu, hvu]
    ring
  have hflux : HasIntervalWeakDerivative 0 1 (fun x => a x * d x) H := by
    apply n07a_interval_weak_flux ha u d H hud
    intro φ hφ hφc hφs
    exact (heq φ hφ hφc hφs).trans (n07a_mode_pairing_congr hH hφs).symm
  obtain ⟨dd, hdd, hddae, _⟩ := n07a_interval_secondWeak_of_flux ha
    (fun x hx => (hapos x hx).ne') J hJpos.le hai
    (fun x hx => (hab x hx).2.2) d H hflux
  refine ⟨dd, hdd, ?_⟩
  apply n07a_open_weak_cubic_graph_bound ha hc hV hq hJ
    (fun x hx => (hab x hx).1) (fun x hx => (hab x hx).2.1)
    (fun x hx => (hab x hx).2.2) (fun x hx => (hcb x hx).1)
    (fun x hx => (hcb x hx).2) hVb hqa hqb u d dd F hud hdd
  filter_upwards [hddae, hH, ae_restrict_mem measurableSet_Ioo] with x hdx hHx hx
  rw [hdx, hHx]
  field_simp [(hapos x hx).ne']
  ring

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}

/-- Primitive geometry supplies a uniform positive-mode estimate once the
actual source and first weak derivative are written in unit coordinates. -/
theorem n07a_reference_positive_weak_mode
    (hJ : ReferenceJets D T S C L K) (hP : ReferencePrincipal T S C K)
    (hE : ∀ m, 0 < T.E0 (T.sample (K.cell m)))
    (hlen : ∀ m, K.left m < K.right m) :
    ∃ A P : ℝ, 0 < A ∧ 0 < P ∧ ∀ m, K.positive m = true → ∀ j : ℝ,
      ∀ u d F : N07aIntervalL2, HasIntervalWeakDerivative 0 1 u d →
      (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo (0 : ℝ) 1 →
        (∫ x, u x * deriv (fun y => n07aReferenceUnitAtom D T S C L K m .principalA y *
          deriv φ y) x) = ∫ x, (j ^ 2 * n07aReferenceUnitC D T S C L K m x * u x +
            n07aReferenceUnitV D T S C L K m x * u x - F x) * φ x) →
      ∃ dd : N07aIntervalL2, HasIntervalWeakDerivative 0 1 d dd ∧
        n07aCylinderEnergy j u d dd ≤
          16384 * (4 * (1 + A * T.E0 (T.sample (K.cell m)) ^ A +
            P * T.E0 (T.sample (K.cell m)) ^ P) ^ 5) ^ 10 * (‖F‖ ^ 2 + ‖u‖ ^ 2) := by
  obtain ⟨A, P, hA, hPpos, hb⟩ := n07a_reference_positive_unit_bounds hJ hP hE hlen
  refine ⟨A, P, hA, hPpos, ?_⟩
  intro m hm j u d F hud heq
  obtain ⟨hbound, hcoeff⟩ := hb m hm
  obtain ⟨hc, hv, hq⟩ := n07aReferenceUnit_scaled_contDiff hJ m
  exact n07a_positive_mode_energy (n07aReferenceUnitAtom_contDiff hJ m .principalA)
    hc hv hq hbound (fun x hx => ⟨(hcoeff x hx).1, (hcoeff x hx).2.1,
      (hcoeff x hx).2.2.1⟩)
    (fun x hx => ⟨(hcoeff x hx).2.2.2.1, (hcoeff x hx).2.2.2.2.1⟩)
    (fun x hx => (hcoeff x hx).2.2.2.2.2.1)
    (fun x hx => n07aReferenceUnitC_eq_A_mul_Q hP m (hlen m) hx)
    (fun x hx => (hcoeff x hx).2.2.2.2.2.2) u d F hud heq

end ContinuousFlexibility.Analysis
