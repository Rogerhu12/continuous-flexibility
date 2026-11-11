import ContinuousFlexibility.Radial.BufferIntervalTrace

/-!
# Local primitives for positive-buffer regularity

Compact tests may be confined to one open interval. A zero weak derivative
then detects a constant on that interval, and subtracting an actual integral
primitive gives the local regularity statement needed by the ODE argument.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff RealInnerProductSpace InnerProductSpace

theorem bufferCompactPrimitive_in_interval {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo a b) (hzero : (∫ x : ℝ, g x) = 0) :
    ∃ P : ℝ → ℝ, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ Ioo a b ∧ deriv P = g := by
  by_cases hne : (tsupport g).Nonempty
  · obtain ⟨c, hcmin⟩ := hc.isCompact.exists_isLeast hne
    obtain ⟨d, hdmax⟩ := hc.isCompact.exists_isGreatest hne
    have hac : a < c := (hs hcmin.1).1
    have hdb : d < b := (hs hdmax.1).2
    have hcd : c ≤ d := hcmin.2 hdmax.1
    let a' : ℝ := (a + c) / 2
    let b' : ℝ := (d + b) / 2
    have haa' : a < a' := by dsimp [a']; linarith
    have ha'c : a' < c := by dsimp [a']; linarith
    have hdb' : d < b' := by dsimp [b']; linarith
    have hb'b : b' < b := by dsimp [b']; linarith
    have hgzero (x : ℝ) (hx : x ∉ Ioc a' b') : g x = 0 := by
      by_contra h
      have hxt : x ∈ tsupport g := subset_closure h
      exact hx ⟨ha'c.trans_le (hcmin.2 hxt), (hdmax.2 hxt).trans hdb'.le⟩
    let P (x : ℝ) := ∫ t in a'..x, g t
    have hP (x : ℝ) : HasDerivAt P (g x) x :=
      (hg.continuous.integral_hasStrictDerivAt a' x).hasDerivAt
    have hd : deriv P = g := funext (fun x => (hP x).deriv)
    have hPs : Function.support P ⊆ Icc a' b' := by
      intro x hx
      by_contra hxi
      have hPx : P x = 0 := by
        change (∫ t in a'..x, g t) = 0
        by_cases hxa : x < a'
        · have hI : (∫ t in Ioc x a', g t) = 0 := by
            calc
              _ = ∫ _ in Ioc x a', (0 : ℝ) := by
                apply setIntegral_congr_fun measurableSet_Ioc
                intro t ht
                exact hgzero t (fun hm => (not_lt_of_ge ht.2) hm.1)
              _ = _ := by simp
          rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hxa.le, hI, neg_zero]
        · have hax : a' ≤ x := le_of_not_gt hxa
          have hbx : b' < x := lt_of_not_ge (fun h => hxi ⟨hax, h⟩)
          have hout (t : ℝ) (ht : t ∉ Ioc a' x) : g t = 0 :=
            hgzero t (fun hm => ht ⟨hm.1, hm.2.trans hbx.le⟩)
          rw [intervalIntegral.integral_of_le hax]
          exact (setIntegral_eq_integral_of_forall_compl_eq_zero hout).trans hzero
      exact hx hPx
    have hPt : tsupport P ⊆ Icc a' b' := closure_minimal hPs isClosed_Icc
    refine ⟨P, contDiff_infty_iff_deriv.mpr ⟨fun x => (hP x).differentiableAt, hd.symm ▸ hg⟩,
      ?_, ?_, hd⟩
    · exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport P) hPt
    · intro x hx
      exact ⟨haa'.trans_le (hPt hx).1, (hPt hx).2.trans_lt hb'b⟩
  · have hgzero : g = fun _ => 0 := by
      funext x
      exact image_eq_zero_of_notMem_tsupport (fun hx => hne ⟨x, hx⟩)
    refine ⟨fun _ => 0, contDiff_const, ?_, ?_, ?_⟩
    · simp
    · simp
    · rw [hgzero]
      funext x
      exact deriv_const x 0

theorem buffer_ae_constant_of_local_weak_deriv_zero {F : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hF : LocallyIntegrable F volume)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x : ℝ, F x * deriv φ x) = 0) :
    ∃ c : ℝ, F =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  let bump : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8
      rOut := (b - a) / 4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let η : ℝ → ℝ := bump.normed volume
  have hη : ContDiff ℝ ∞ η := bump.contDiff_normed
  have hcη : HasCompactSupport η := bump.hasCompactSupport_normed
  have hη₁ : (∫ x : ℝ, η x) = 1 := bump.integral_normed
  have hsη : tsupport η ⊆ Ioo a b := by
    rw [show tsupport η = Metric.closedBall ((a + b) / 2) ((b - a) / 4) from
      bump.tsupport_normed_eq]
    intro x hx
    have hx' := Metric.mem_closedBall.mp hx
    rw [Real.dist_eq] at hx'
    have hx'' := abs_le.mp hx'
    constructor <;> linarith [hx''.1, hx''.2]
  let c : ℝ := ∫ x : ℝ, F x * η x
  have hpair (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
      (hsφ : tsupport φ ⊆ Ioo a b) : (∫ x : ℝ, F x * φ x) = (∫ x : ℝ, φ x) * c := by
    let M : ℝ := ∫ x : ℝ, φ x
    let g (x : ℝ) := φ x - M * η x
    have hg : ContDiff ℝ ∞ g := hφ.sub (contDiff_const.mul hη)
    have hcg : HasCompactSupport g := hcφ.sub (hcη.mul_left (f := fun _ => M))
    have hsg : tsupport g ⊆ Ioo a b := by
      have hsubset : tsupport g ⊆ tsupport φ ∪ tsupport η := by
        apply closure_minimal _ ((isClosed_tsupport φ).union (isClosed_tsupport η))
        intro x hx
        by_contra hn
        have hxφ : x ∉ tsupport φ := fun hm => hn (Or.inl hm)
        have hxη : x ∉ tsupport η := fun hm => hn (Or.inr hm)
        apply hx
        dsimp [g]
        rw [image_eq_zero_of_notMem_tsupport hxφ, image_eq_zero_of_notMem_tsupport hxη,
          mul_zero, sub_zero]
      exact hsubset.trans (union_subset hsφ hsη)
    have hφI : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hcφ
    have hηI : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hcη
    have hgzero : (∫ x : ℝ, g x) = 0 := by
      change (∫ x : ℝ, φ x - M * η x) = 0
      rw [integral_sub hφI (hηI.const_mul M), integral_const_mul, hη₁, mul_one]
      exact sub_self _
    obtain ⟨P, hP, hcP, hsP, hdP⟩ := bufferCompactPrimitive_in_interval hg hcg hsg hgzero
    have hPg := hzero P hP hcP hsP
    rw [hdP] at hPg
    have hFφ : Integrable (fun x => F x * φ x) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport hφ.continuous hcφ
    have hFη : Integrable (fun x => F x * η x) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport hη.continuous hcη
    have hsplit : (∫ x : ℝ, F x * g x) = (∫ x : ℝ, F x * φ x) - M * c := by
      calc
        _ = ∫ x : ℝ, F x * φ x - M * (F x * η x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [g]
          ring
        _ = _ := by rw [integral_sub hFφ (hFη.const_mul M), integral_const_mul]
    rw [hsplit] at hPg
    exact sub_eq_zero.mp hPg
  refine ⟨c, ?_⟩
  change ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), F x = c
  rw [ae_restrict_iff' measurableSet_Ioo]
  have htest : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x : ℝ, φ x • (F x - c)) = 0 := by
    intro φ hφ hcφ hsφ
    have hFφ : Integrable (fun x => F x * φ x) volume := by
      simpa only [smul_eq_mul] using
        hF.integrable_smul_right_of_hasCompactSupport hφ.continuous hcφ
    have hφI := hφ.continuous.integrable_of_hasCompactSupport hcφ
    calc
      (∫ x : ℝ, φ x • (F x - c)) =
          (∫ x : ℝ, F x * φ x) - (∫ x : ℝ, φ x) * c := by
        rw [← integral_mul_const, ← integral_sub hFφ (hφI.mul_const c)]
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [smul_eq_mul]
        ring
      _ = 0 := by rw [hpair φ hφ hcφ hsφ]; exact sub_self _
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hF.sub continuous_const.locallyIntegrable).locallyIntegrableOn (Ioo a b)) htest
  filter_upwards [hz] with x hx
  intro hxin
  exact sub_eq_zero.mp (hx hxin)

/-- The local test equation gives a continuous representative on the interval.
The derivative data are allowed to be merely locally integrable. -/
theorem buffer_localWeakDerivative_continuousRepresentative {u d : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : LocallyIntegrable u volume) (hd : LocallyIntegrable d volume)
    (hud : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ x : ℝ, u x * deriv φ x) = -(∫ x : ℝ, d x * φ x)) :
    ∃ U : ℝ → ℝ, Continuous U ∧ u =ᵐ[volume.restrict (Ioo a b)] U ∧
      (∀ x y : ℝ, U y - U x = ∫ t in x..y, d t) ∧
      (∀ᵐ x : ℝ, HasDerivAt U (d x) x) := by
  let P (x : ℝ) := ∫ t in (0 : ℝ)..x, d t
  have hP : Continuous P := bufferPrimitive_continuous hd 0
  let F (x : ℝ) := u x - P x
  have hF : LocallyIntegrable F volume := hu.sub hP.locallyIntegrable
  have hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → (∫ x : ℝ, F x * deriv φ x) = 0 := by
    intro φ hφ hcφ hsφ
    have hφ' := (contDiff_infty_iff_deriv.mp hφ).2
    have huI : Integrable (fun x => u x * deriv φ x) volume := by
      simpa only [smul_eq_mul] using
        hu.integrable_smul_right_of_hasCompactSupport hφ'.continuous hcφ.deriv
    have hPI : Integrable (fun x => P x * deriv φ x) volume :=
      (hP.mul hφ'.continuous).integrable_of_hasCompactSupport hcφ.deriv.mul_left
    calc
      _ = (∫ x : ℝ, u x * deriv φ x) - ∫ x : ℝ, P x * deriv φ x := by
        rw [← integral_sub huI hPI]
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [F]
        ring
      _ = 0 := by
        rw [hud φ hφ hcφ hsφ, bufferPrimitive_weak_derivative hd φ hφ hcφ]
        exact sub_self _
  obtain ⟨c, hc⟩ := buffer_ae_constant_of_local_weak_deriv_zero hab hF hzero
  let U (x : ℝ) := c + P x
  refine ⟨U, continuous_const.add hP, ?_, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    dsimp [F] at hx
    dsimp [U]
    linarith
  · intro x y
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (buffer_locallyIntegrable_intervalIntegrable hd 0 x)
      (buffer_locallyIntegrable_intervalIntegrable hd x y)
    dsimp [U, P]
    linarith
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hd] with x hx
    exact (hx 0).const_add c

/-- Once the weak derivative is continuous at a point, the continuous
representative has its classical derivative there. -/
theorem bufferPrimitiveRepresentative_hasDerivAt {U d : ℝ → ℝ}
    (hd : LocallyIntegrable d volume)
    (hprim : ∀ x y : ℝ, U y - U x = ∫ t in x..y, d t)
    {x : ℝ} (hcd : ContinuousAt d x) : HasDerivAt U (d x) x := by
  have hD := (intervalIntegral.integral_hasDerivAt_right
    (buffer_locallyIntegrable_intervalIntegrable hd x x)
    hd.aestronglyMeasurable.stronglyMeasurableAtFilter hcd).const_add (U x)
  apply hD.congr_of_eventuallyEq
  filter_upwards [] with y
  have hxy := hprim x y
  linarith

theorem buffer_localWeakDerivative_classicalRepresentative {u d : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : LocallyIntegrable u volume) (hd : LocallyIntegrable d volume)
    (hcd : ContinuousOn d (Ioo a b))
    (hud : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioo a b →
      (∫ x : ℝ, u x * deriv φ x) = -(∫ x : ℝ, d x * φ x)) :
    ∃ U : ℝ → ℝ, Continuous U ∧ u =ᵐ[volume.restrict (Ioo a b)] U ∧
      (∀ x y : ℝ, U y - U x = ∫ t in x..y, d t) ∧
      (∀ x ∈ Ioo a b, HasDerivAt U (d x) x) := by
  obtain ⟨U, hU, hue, hprim, -⟩ :=
    buffer_localWeakDerivative_continuousRepresentative hab hu hd hud
  refine ⟨U, hU, hue, hprim, ?_⟩
  intro x hx
  exact bufferPrimitiveRepresentative_hasDerivAt hd hprim
    (hcd.continuousAt (isOpen_Ioo.mem_nhds hx))

end ContinuousFlexibility.Radial
