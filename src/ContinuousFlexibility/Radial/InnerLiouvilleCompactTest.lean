module

public import ContinuousFlexibility.Radial.InnerLiouvilleEnergyDomain
public import ContinuousFlexibility.Radial.InnerWeakGreen

/-!
# Genuine compact physical tests and their normalized model tests

A physical compact test is pulled back on the retained interval and
extended by zero. Its support is proved compact and strictly inside
that interval using the actual inverse radius. The original
Schrodinger energy core is then populated by the resulting smooth
function and its actual derivative and potential coordinate.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

def innerLiouvilleTestPullback (R s : ℝ → ℝ) (a b lam : ℝ) (φ : ℝ → ℝ) : ℝ → ℝ :=
  (Ioo a b).indicator (fun x => Real.sqrt lam * s x * φ (R x))

theorem innerLiouvilleTestPullback_eventuallyEq (R s φ : ℝ → ℝ) (lam : ℝ)
    {a b x : ℝ} (hx : x ∈ Ioo a b) :
    innerLiouvilleTestPullback R s a b lam φ =ᶠ[𝓝 x]
      (fun y => Real.sqrt lam * s y * φ (R y)) := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact indicator_of_mem hy _

theorem innerLiouvilleTestPullback_compact {R s φ : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R)
    (hv : ∀ x ∈ Icc a b, 0 < deriv R x)
    (hc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioo (R a) (R b)) :
    HasCompactSupport (innerLiouvilleTestPullback R s a b lam φ) ∧
      tsupport (innerLiouvilleTestPullback R s a b lam φ) ⊆ Ioo a b := by
  let X := morseCellModelCoordinate R a b
  let K := X '' tsupport φ
  have hm := morseCell_strictMonoOn hR hv
  have hK : IsCompact K := hc.image_of_continuousOn
    ((innerLiouvilleIntervalCoordinate_continuousOn hab hR hv).mono hφs)
  have hKI : K ⊆ Ioo a b := by
    rintro _ ⟨r, hr, rfl⟩
    have hr' := hφs hr
    rw [← hR.continuous.continuousOn.image_Ioo_of_strictMonoOn hab hm] at hr'
    obtain ⟨x, hx, rfl⟩ := hr'
    dsimp only [X]
    rw [morseCellModelCoordinate_apply hm (Ioo_subset_Icc_self hx)]
    exact hx
  have hsupport : Function.support (innerLiouvilleTestPullback R s a b lam φ) ⊆ K := by
    intro x hx
    change innerLiouvilleTestPullback R s a b lam φ x ≠ 0 at hx
    have hi : x ∈ Ioo a b := by
      by_contra hout
      exact hx (indicator_of_notMem hout _)
    have hn : φ (R x) ≠ 0 := by
      intro hz
      apply hx
      rw [innerLiouvilleTestPullback, indicator_of_mem hi, hz, mul_zero]
    exact ⟨R x, subset_tsupport φ hn,
      morseCellModelCoordinate_apply hm (Ioo_subset_Icc_self hi)⟩
  have hsub : tsupport (innerLiouvilleTestPullback R s a b lam φ) ⊆ K :=
    closure_minimal hsupport hK.isClosed
  exact ⟨hK.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hKI⟩

theorem innerLiouvilleTestPullback_contDiff {R s φ : ℝ → ℝ} {a b lam : ℝ}
    (hab : a ≤ b) (hR : ContDiff ℝ ∞ R) (hs : ContDiff ℝ ∞ s)
    (hv : ∀ x ∈ Icc a b, 0 < deriv R x)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo (R a) (R b)) :
    ContDiff ℝ ∞ (innerLiouvilleTestPullback R s a b lam φ) := by
  have hsupport := (innerLiouvilleTestPullback_compact (s := s) (lam := lam) hab hR hv hc hφs).2
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ Ioo a b
  · exact ((contDiff_const.mul hs).mul (hφ.comp hR)).contDiffAt.congr_of_eventuallyEq
      (innerLiouvilleTestPullback_eventuallyEq R s φ lam hx)
  · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hsupport ht)))

theorem innerLiouvilleTestPullback_deriv {R s φ : ℝ → ℝ} {a b lam x : ℝ}
    (hR : DifferentiableAt ℝ R x) (hs : DifferentiableAt ℝ s x)
    (hφ : DifferentiableAt ℝ φ (R x)) (hx : x ∈ Ioo a b) :
    deriv (innerLiouvilleTestPullback R s a b lam φ) x =
      Real.sqrt lam * (deriv s x * φ (R x) + s x * deriv φ (R x) * deriv R x) := by
  have hprod := (hs.hasDerivAt.const_mul (Real.sqrt lam)).mul
    (hφ.hasDerivAt.comp x hR.hasDerivAt)
  have he := (hprod.congr_of_eventuallyEq
    (innerLiouvilleTestPullback_eventuallyEq R s φ lam hx)).deriv
  calc
    _ = (Real.sqrt lam * deriv s x) * φ (R x) +
        (Real.sqrt lam * s x) * (deriv φ (R x) * deriv R x) := he
    _ = _ := by ring

/-- The original three-coordinate core is populated by actual compact
smooth test classes, rather than postulated test vectors. -/
theorem exists_innerCompactModelEnergyCore {V φ : ℝ → ℝ} {a b : ℝ}
    (hV : Continuous V) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    ∃ q : RadialL2 × RadialL2 × RadialL2, q ∈ IntervalEnergyCore V a b ∧
      (q.1 : ℝ → ℝ) =ᵐ[volume] φ ∧ (q.2.1 : ℝ → ℝ) =ᵐ[volume] deriv φ := by
  have hv : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hc
  have hd : MemLp (deriv φ) 2 volume :=
    (hφ.continuous_deriv (by simp)).memLp_of_hasCompactSupport hc.deriv
  have hw : Continuous (fun x => Real.sqrt (1 + |V x|) * φ x) :=
    (continuous_const.add hV.abs).sqrt.mul hφ.continuous
  have hq : MemLp (fun x => Real.sqrt (1 + |V x|) * φ x) 2 volume :=
    hw.memLp_of_hasCompactSupport hc.mul_left
  let q : RadialL2 × RadialL2 × RadialL2 :=
    (hv.toLp φ, hd.toLp (deriv φ), hq.toLp (fun x => Real.sqrt (1 + |V x|) * φ x))
  refine ⟨q, ⟨⟨φ, hφ, hc, hv.coeFn_toLp, hd.coeFn_toLp, hq.coeFn_toLp⟩, ?_⟩,
    hv.coeFn_toLp, hd.coeFn_toLp⟩
  filter_upwards [ae_restrict_of_ae hv.coeFn_toLp,
    ae_restrict_mem measurableSet_Ioo.compl] with x hx hout
  exact hx.trans (image_eq_zero_of_notMem_tsupport (fun h => hout (hφs h)))

end ContinuousFlexibility.Radial
