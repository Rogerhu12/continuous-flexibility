import ContinuousFlexibility.Analysis.N06WeakCylinderPDE

/-!
# Calculus of the genuine unit-cylinder tests

The compact radial support makes multiplication by a coefficient smooth
on the open strip into a globally smooth test. No extension of the
coefficient through a degenerate endpoint is required.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open scoped ContDiff Topology
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

theorem n06UnitCanonicalTest.n06_mixedDerivative
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) (a b : ℕ) :
    n06UnitCanonicalTest (mixedDerivative a b φ) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  refine ⟨contDiff_mixedDerivative hφ.1 a b, ?_, J, hJ, hJK, ?_⟩
  · have hp (r : ℝ) : Function.Periodic (fun θ => φ (r, θ)) Real.pi := by
      intro θ
      simpa only [Prod.mk_add_mk, add_zero] using hφ.2.1 (r, θ)
    intro p
    change mixedDerivative a b φ (p.1 + 0, p.2 + Real.pi) = mixedDerivative a b φ p
    rw [add_zero]
    exact mixedDerivative_angular_periodic hp a b p.1 p.2
  · intro r hr θ
    have hnear : ∀ᶠ s : ℝ in 𝓝 r, s ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hr
    have he : (fun s : ℝ => iteratedDeriv b (fun t : ℝ => φ (s, t)) θ)
        =ᶠ[𝓝 r] (0 : ℝ → ℝ) := by
      filter_upwards [hnear] with s hs
      have hz : (fun t : ℝ => φ (s, t)) = (0 : ℝ → ℝ) := funext (hzero s hs)
      simp only [hz, iteratedDeriv_const_zero, Pi.zero_apply]
    simpa only [mixedDerivative, iteratedDeriv_const_zero, Pi.zero_apply] using
      he.iteratedDeriv_eq a

theorem n06UnitCanonicalTest.n06_radialPartial
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    n06UnitCanonicalTest (radialPartial φ) := by
  have heq : radialPartial φ = mixedDerivative 1 0 φ := by
    simpa only [spaces_mixedDerivative_zero, Nat.zero_add] using
      radialPartial_mixedDerivative hφ.1 0 0
  rw [heq]
  exact hφ.n06_mixedDerivative 1 0

theorem n06UnitCanonicalTest.n06_angularPartial
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ) :
    n06UnitCanonicalTest (angularPartial φ) := by
  rw [← n06_mixedAngular_one_eq_angularPartial hφ.1]
  exact hφ.n06_mixedDerivative 0 1

theorem n06UnitCanonicalTest.n06_zero_of_not_mem
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ)
    {p : PolarPoint} (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) : φ p = 0 := by
  obtain ⟨J, _, hJK, hzero⟩ := hφ.2.2
  have hpJ : p.1 ∉ J := fun h => hp ⟨hJK h, mem_univ p.2⟩
  exact hzero p.1 hpJ p.2

theorem n06UnitCanonicalTest.n06_eventually_zero_of_not_mem
    {φ : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ)
    {p : PolarPoint} (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  have hpJ : p.1 ∉ J := fun h => hp ⟨hJK h, mem_univ p.2⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝 p.1, r ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hpJ
  filter_upwards [(continuous_fst.tendsto p).eventually hnear] with q hq
  exact hzero q.1 hq q.2

theorem n06UnitCanonicalTest.n06_contDiff_mul_left
    {φ a : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ)
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ)) :
    ContDiff ℝ ∞ (fun p => a p * φ p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
  · exact (ha.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).mul hφ.1.contDiffAt
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [hφ.n06_eventually_zero_of_not_mem hp] with q hq
    change a q * φ q = 0
    change φ q = 0 at hq
    rw [hq, mul_zero]

theorem n06UnitCanonicalTest.n06_mul_left_of_contDiffOn
    {φ a : PolarPoint → ℝ} (hφ : n06UnitCanonicalTest φ)
    (ha : ContDiffOn ℝ ∞ a (Ioo (0 : ℝ) 1 ×ˢ univ))
    (hp : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ), a (p + (0, Real.pi)) = a p) :
    n06UnitCanonicalTest (fun p => a p * φ p) := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  refine ⟨hφ.n06_contDiff_mul_left ha, ?_, J, hJ, hJK, ?_⟩
  · intro p
    change a (p + (0, Real.pi)) * φ (p + (0, Real.pi)) = a p * φ p
    rw [hφ.2.1 p]
    by_cases hpU : p ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)
    · rw [hp p hpU]
    · rw [hφ.n06_zero_of_not_mem hpU, mul_zero, mul_zero]
  · intro r hr θ
    change a (r, θ) * φ (r, θ) = 0
    rw [hzero r hr θ, mul_zero]

theorem n06UnitCanonicalTest.n06_memLp {φ : PolarPoint → ℝ}
    (hφ : n06UnitCanonicalTest φ) : MemLp φ 2 (cylinderWindowMeasure 0) :=
  continuous_memLp_cylinderWindow hφ.1.continuous 0

end ContinuousFlexibility.Analysis
