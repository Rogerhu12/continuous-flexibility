module

public import ContinuousFlexibility.Radial.IntervalWeakPrimitive
public import Mathlib.Topology.Order.Compact

/-!
# Weak primitives using tests compactly inside the interval

These variants need only tests whose topological support lies in the open
interval. This permits multiplication by coefficients known smooth only
on that open interval.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open scoped Topology ContDiff

/-- A compact subset of an open real interval fits into a smaller open
interval whose closed interval still lies in the original interval. -/
theorem compact_subset_Ioo_enclosure
    {a b : ℝ} (hab : a < b) {K : Set ℝ}
    (hK : IsCompact K) (hKs : K ⊆ Ioo a b) :
    ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧ K ⊆ Ioo c d := by
  let K' : Set ℝ := K ∪ {(a + b) / 2}
  have hKc : IsCompact K' := hK.union isCompact_singleton
  have hKn : K'.Nonempty := ⟨(a + b) / 2, Or.inr (by simp)⟩
  have hKsub : K' ⊆ Ioo a b := by
    rintro x (hx | hx)
    · exact hKs hx
    · have he : x = (a + b) / 2 := mem_singleton_iff.mp hx
      subst x
      exact ⟨by linarith, by linarith⟩
  obtain ⟨l, hl⟩ := hKc.exists_isLeast hKn
  obtain ⟨r, hr⟩ := hKc.exists_isGreatest hKn
  have hal : a < l := (hKsub hl.1).1
  have hrb : r < b := (hKsub hr.1).2
  have hlr : l ≤ r := hl.2 hr.1
  refine ⟨(a + l) / 2, (r + b) / 2, by linarith,
    by linarith, by linarith, ?_⟩
  intro x hx
  have hlx : l ≤ x := hl.2 (Or.inl hx)
  have hxr : x ≤ r := hr.2 (Or.inl hx)
  exact ⟨by linarith, by linarith⟩

/-- A zero-integral smooth compact test has a smooth primitive compactly
supported inside the same open interval. -/
theorem compactPrimitive_tsupport_in_interval
    {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioo a b)
    (hgzero : (∫ x : ℝ, g x) = 0) :
    ∃ P : ℝ → ℝ,
      ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ Ioo a b ∧ deriv P = g := by
  obtain ⟨c, d, hac, hcd, hdb, hsub⟩ :=
    compact_subset_Ioo_enclosure hab hcg hgs
  obtain ⟨P, hP, hcP, hPs, hdP⟩ :=
    compactPrimitive_in_interval hcd hg ((subset_tsupport g).trans hsub) hgzero
  have hPt : tsupport P ⊆ Icc c d :=
    closure_minimal (hPs.trans Ioo_subset_Icc_self) isClosed_Icc
  refine ⟨P, hP, hcP, ?_, hdP⟩
  intro x hx
  exact ⟨hac.trans_le (hPt hx).1, (hPt hx).2.trans_lt hdb⟩

/-- A locally integrable function with zero weak derivative on an open
interval is constant almost everywhere on that interval. -/
theorem ae_constant_Ioo_of_weak_deriv_zero_tsupport
    {a b : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hF : LocallyIntegrable F volume)
    (hzero : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x : ℝ, F x * deriv φ x) = 0) :
    ∃ c : ℝ, F =ᵐ[volume.restrict (Ioo a b)] (fun _ => c) := by
  let B : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := B.normed volume
  have hη : ContDiff ℝ ∞ η := B.contDiff_normed
  have hcη : HasCompactSupport η := B.hasCompactSupport_normed
  have hηone : (∫ x : ℝ, η x) = 1 := B.integral_normed
  have hηs : tsupport η ⊆ Ioo a b := by
    intro x ht
    change x ∈ tsupport (B.normed volume) at ht
    rw [B.tsupport_normed_eq] at ht
    have hd := Metric.mem_closedBall.mp ht
    rw [Real.dist_eq] at hd
    change |x - (a + b) / 2| ≤ (b - a) / 4 at hd
    have hd' := abs_le.mp hd
    exact ⟨by linarith [hd'.1], by linarith [hd'.2]⟩
  let c : ℝ := ∫ x : ℝ, F x * η x
  have hk : LocallyIntegrable (fun x => F x - c) volume :=
    hF.sub (continuous_const : Continuous (fun _ : ℝ => c)).locallyIntegrable
  have hz : ∀ᵐ x ∂volume, x ∈ Ioo a b → F x - c = 0 := by
    apply (isOpen_Ioo : IsOpen (Ioo a b)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hk.locallyIntegrableOn (Ioo a b))
    intro φ hφ hcφ hφs
    let M : ℝ := ∫ x : ℝ, φ x
    let g (x : ℝ) : ℝ := φ x - M * η x
    have hg : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hη)
    have hcg : HasCompactSupport g :=
      hcφ.sub (hcη.mul_left (f := fun _ => M))
    have hgs : tsupport g ⊆ Ioo a b := by
      have hsub : Function.support g ⊆ tsupport φ ∪ tsupport η := by
        intro x hx
        by_contra hn
        have hφzero : φ x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hn (Or.inl ht))
        have hηzero : η x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun ht => hn (Or.inr ht))
        exact hx (by simp only [g, hφzero, hηzero, mul_zero, sub_zero])
      exact (closure_minimal hsub
        ((isClosed_tsupport φ).union (isClosed_tsupport η))).trans
          (union_subset hφs hηs)
    have hφI : Integrable φ volume :=
      hφ.continuous.integrable_of_hasCompactSupport hcφ
    have hηI : Integrable η volume :=
      hη.continuous.integrable_of_hasCompactSupport hcη
    have hgzero : (∫ x : ℝ, g x) = 0 := by
      change (∫ x : ℝ, φ x - M * η x) = 0
      rw [integral_sub hφI (hηI.const_mul M),
        integral_const_mul, hηone, mul_one]
      exact sub_self _
    obtain ⟨P, hP, hcP, hPs, hdP⟩ :=
      compactPrimitive_tsupport_in_interval hab hg hcg hgs hgzero
    have hPg := hzero P hP hcP hPs
    rw [hdP] at hPg
    have hFφ : Integrable (fun x => F x * φ x) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport hφ.continuous hcφ
    have hFη : Integrable (fun x => F x * η x) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport hη.continuous hcη
    have hsplit :
        (∫ x : ℝ, F x * g x) =
          (∫ x : ℝ, F x * φ x) - M * c := by
      calc
        _ = ∫ x : ℝ, F x * φ x - M * (F x * η x) := by
          apply integral_congr_ae
          apply Eventually.of_forall
          intro x
          dsimp only [g]
          ring
        _ = _ := by
          rw [integral_sub hFφ (hFη.const_mul M), integral_const_mul]
    rw [hsplit] at hPg
    have hmoment : (∫ x : ℝ, F x * φ x) = M * c :=
      sub_eq_zero.mp hPg
    calc
      (∫ x : ℝ, φ x • (F x - c))
          = ∫ x : ℝ, F x * φ x - c * φ x := by
            apply integral_congr_ae
            apply Eventually.of_forall
            intro x
            simp only [smul_eq_mul]
            ring
      _ = (∫ x : ℝ, F x * φ x) - c * (∫ x : ℝ, φ x) := by
        rw [integral_sub hFφ (hφI.const_mul c), integral_const_mul]
      _ = 0 := by
        rw [hmoment]
        dsimp only [M]
        ring
  refine ⟨c, ?_⟩
  exact (ae_restrict_iff' measurableSet_Ioo).mpr
    (hz.mono fun x hx hxi => sub_eq_zero.mp (hx hxi))

/-- An integrable weak derivative gives an actual integral representative
almost everywhere in the interval. No continuity of F is assumed. -/
theorem exists_ae_intervalPrimitive_of_weakDeriv_tsupport
    {a b : ℝ} (hab : a < b) {F f : ℝ → ℝ}
    (hF : IntervalIntegrable F volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hweak : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in a..b, F x * deriv φ x) =
        -(∫ x in a..b, f x * φ x)) :
    ∃ c : ℝ,
      F =ᵐ[volume.restrict (Ioo a b)]
        (fun x => c + ∫ t in a..x, f t) := by
  let P (x : ℝ) : ℝ := ∫ t in a..x, f t
  have hPac : AbsolutelyContinuousOnInterval P a b :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hPi : IntervalIntegrable P volume a b :=
    hPac.continuousOn.intervalIntegrable
  let H : ℝ → ℝ := (Icc a b).indicator (fun x => F x - P x)
  have hHi : Integrable H volume := by
    dsimp only [H]
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).mp (hF.sub hPi)
  have hHweak : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x : ℝ, H x * deriv φ x) = 0 := by
    intro φ hφ hcφ hφs
    have hφb : φ b = 0 := by
      by_contra hn
      have hb := hφs (subset_tsupport φ hn)
      exact (lt_irrefl b) hb.2
    have hφd : Continuous (deriv φ) :=
      (contDiff_infty_iff_deriv.mp hφ).2.continuous
    have hφone : ContDiffOn ℝ 1 φ (uIcc a b) :=
      (hφ.of_le (by simp)).contDiffOn
    have hPweak :
        (∫ x in a..b, P x * deriv φ x) =
          -(∫ x in a..b, f x * φ x) := by
      simpa only [P, hφb, mul_zero, zero_sub] using
        intervalPrimitive_integral_mul_deriv hf hφone
    have hindicator :
        (fun x => H x * deriv φ x) =
          (Icc a b).indicator (fun x => (F x - P x) * deriv φ x) := by
      funext x
      by_cases hx : x ∈ Icc a b <;> simp [H, hx]
    rw [hindicator, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le]
    simp only [sub_mul]
    rw [intervalIntegral.integral_sub
      (hF.mul_continuousOn hφd.continuousOn)
      (hPi.mul_continuousOn hφd.continuousOn),
      hweak φ hφ hcφ hφs, hPweak, sub_self]
  obtain ⟨c, hc⟩ :=
    ae_constant_Ioo_of_weak_deriv_zero_tsupport hab hHi.locallyIntegrable hHweak
  refine ⟨c, ?_⟩
  filter_upwards [hc, self_mem_ae_restrict measurableSet_Ioo] with x hxc hx
  have he : F x - P x = c := by
    simpa only [H, Set.indicator_of_mem (mem_Icc_of_Ioo hx)] using hxc
  change F x = c + P x
  linarith

/-- A continuous weak primitive agrees with its integral representative
at every point of the closed interval, including the two endpoints. -/
theorem eq_add_intervalIntegral_of_weakDeriv_tsupport
    {a b : ℝ} (hab : a < b) {F f : ℝ → ℝ}
    (hF : ContinuousOn F (Icc a b))
    (hf : IntervalIntegrable f volume a b)
    (hweak : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in a..b, F x * deriv φ x) =
        -(∫ x in a..b, f x * φ x)) :
    ∀ x ∈ Icc a b, F x = F a + ∫ t in a..x, f t := by
  obtain ⟨c, hc⟩ :=
    exists_ae_intervalPrimitive_of_weakDeriv_tsupport hab
      (hF.intervalIntegrable_of_Icc hab.le) hf hweak
  have hP :=
    hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hPc : ContinuousOn (fun x => ∫ t in a..x, f t) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hP.continuousOn
  have hrep :
      ContinuousOn (fun x => c + ∫ t in a..x, f t) (Icc a b) :=
    continuousOn_const.add hPc
  rw [restrict_Ioo_eq_restrict_Icc] at hc
  have hpoint :=
    Measure.eqOn_Icc_of_ae_eq volume hab.ne hc hF hrep
  have ha := hpoint ⟨le_rfl, hab.le⟩
  simp only [intervalIntegral.integral_same, add_zero] at ha
  intro x hx
  rw [hpoint hx, ha]

/-- Endpoint form of the weak fundamental theorem of calculus. -/
theorem intervalIntegral_eq_sub_of_weakDeriv_tsupport
    {a b : ℝ} (hab : a < b) {F f : ℝ → ℝ}
    (hF : ContinuousOn F (Icc a b))
    (hf : IntervalIntegrable f volume a b)
    (hweak : ∀ φ : ℝ → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      (∫ x in a..b, F x * deriv φ x) =
        -(∫ x in a..b, f x * φ x)) :
    (∫ x in a..b, f x) = F b - F a := by
  have h :=
    eq_add_intervalIntegral_of_weakDeriv_tsupport hab hF hf hweak b ⟨hab.le, le_rfl⟩
  linarith

end ContinuousFlexibility.Radial
