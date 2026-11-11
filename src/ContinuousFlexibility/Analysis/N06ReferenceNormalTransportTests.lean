import ContinuousFlexibility.Analysis.N06CanonicalTestTransport
import ContinuousFlexibility.Radial.R11bRadialTests
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

/-!
# Radial weighted pullbacks of compact canonical tests

The multiplier is smooth only inside the physical piece. The compact
support of the original canonical test makes the actual zero extension
globally smooth. The radial coordinate can have either orientation; its
orientation is obtained from the actual injective chart.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open ContinuousFlexibility.Radial

set_option backward.isDefEq.respectTransparency false

def n06ReferenceWeightedTest (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (a : ℝ → ℝ)
    (φ : PolarPoint → ℝ) : PolarPoint → ℝ := by
  classical
  exact fun p => if p ∈ physicalPieceOpen S K m then
    a p.1 * φ (K.chart z m p) else 0

variable {D : ReferenceData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {base m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {a Y : ℝ → ℝ} {φ : PolarPoint → ℝ}

theorem n06ReferenceWeightedTest_of_mem {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n06ReferenceWeightedTest S K z m a φ p = a p.1 * φ (K.chart z m p) := by
  simp only [n06ReferenceWeightedTest, if_pos hp]

theorem n06ReferenceWeightedTest_of_not_mem {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K m) :
    n06ReferenceWeightedTest S K z m a φ p = 0 := by
  simp only [n06ReferenceWeightedTest, if_neg hp]

theorem n06ReferenceWeightedTest_germ {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n06ReferenceWeightedTest S K z m a φ =ᶠ[𝓝 p]
      (fun q => a q.1 * φ (K.chart z m q)) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact n06ReferenceWeightedTest_of_mem hq

theorem n06ReferenceWeightedTest_support
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    ∃ J : Set ℝ, IsCompact J ∧ J ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) ∧
      ∀ r, r ∉ J → ∀ θ, n06ReferenceWeightedTest S K z m a φ (r, θ) = 0 := by
  obtain ⟨J, hJ, hJI, hzero⟩ := n06CanonicalTestPullback_radialSupport hK hz hs hφ
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  refine ⟨J, hJ, hJI, fun r hr θ => ?_⟩
  by_cases hp : (r, θ) ∈ physicalPieceOpen S K m
  · have he := hzero r hr θ
    rw [n06CanonicalTestPullback_eq_of_mem hp] at he
    have hh : K.height z m (r, θ) ≠ 0 :=
      (hcharts.2.2.2.2.2.2.2 (r, θ) hp).1.ne'
    have hφzero : φ (K.chart z m (r, θ)) = 0 := (mul_eq_zero.mp he).resolve_left hh
    rw [n06ReferenceWeightedTest_of_mem hp, hφzero, mul_zero]
  · exact n06ReferenceWeightedTest_of_not_mem hp

theorem n06ReferenceWeightedTest_zero_germ
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K m) :
    n06ReferenceWeightedTest S K z m a φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  obtain ⟨J, hJ, hJI, hzero⟩ := n06ReferenceWeightedTest_support (a := a) hK hz hs hφ
  have hpJ : p.1 ∉ J := fun h => hp ⟨hJI h, mem_univ _⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝 p.1, r ∉ J := hJ.isClosed.isOpen_compl.mem_nhds hpJ
  filter_upwards [(continuous_fst.tendsto p).eventually hnear] with q hq
  exact hzero q.1 hq q.2

theorem n06ReferenceWeightedTest_contDiff
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ a (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hφ : CanonicalTest S K m φ) :
    ContDiff ℝ ∞ (n06ReferenceWeightedTest S K z m a φ) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ physicalPieceOpen S K m
  · have haAt := (ha.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).comp p contDiffAt_fst
    have hF := hcharts.2.2.2.2.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)
    exact (haAt.mul (hφ.1.contDiffAt.comp p hF)).congr_of_eventuallyEq
      (n06ReferenceWeightedTest_germ hp)
  · have hzero : ContDiffAt ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) p := contDiffAt_const
    exact hzero.congr_of_eventuallyEq
      (n06ReferenceWeightedTest_zero_germ hK hz hs hφ hp)

theorem n06ReferenceWeightedTest_periodic
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    Function.Periodic (n06ReferenceWeightedTest S K z m a φ) (0, Real.pi) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  intro p
  have hshift : p + (0, Real.pi) ∈ physicalPieceOpen S K m ↔
      p ∈ physicalPieceOpen S K m := by
    simp only [physicalPieceOpen, mem_prod, Prod.fst_add, add_zero, mem_univ, and_true]
  by_cases hp : p ∈ physicalPieceOpen S K m
  · rw [n06ReferenceWeightedTest_of_mem (hshift.mpr hp),
      n06ReferenceWeightedTest_of_mem hp,
      (hcharts.2.2.2.2.2.2.2 p hp).2.2.1, hφ.2.1 (K.chart z m p)]
    simp only [Prod.fst_add, add_zero]
  · rw [n06ReferenceWeightedTest_of_not_mem (mt hshift.mp hp),
      n06ReferenceWeightedTest_of_not_mem hp]

theorem n06ReferenceWeightedTest_radialTest
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ a (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hφ : CanonicalTest S K m φ) :
    RadialTest D (n06ReferenceWeightedTest S K z m a φ) := by
  obtain ⟨J, hJ, hJI, hzero⟩ := n06ReferenceWeightedTest_support (a := a) hK hz hs hφ
  have hp := n06ReferenceWeightedTest_periodic (a := a) hK hz hs hφ
  refine ⟨n06ReferenceWeightedTest_contDiff hK hz hs ha hφ, ?_,
    J, hJ, hJI.trans (hK.2.2.2.1 m).2.2, hzero⟩
  have hperiod : ((0 : ℝ), Real.pi) + (0, Real.pi) = (0, 2 * Real.pi) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, zero_add] <;> ring
  rw [← hperiod]
  exact hp.add_period hp

theorem n06ReferenceWeightedTest_radialPartial_zero
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K m) :
    radialPartial (n06ReferenceWeightedTest S K z m a φ) p = 0 := by
  have he := n06ReferenceWeightedTest_zero_germ (a := a) hK hz hs hφ hp
  unfold radialPartial
  rw [he.fderiv_eq (𝕜 := ℝ)]
  exact radialPartial_const (x := p) 0

theorem n06ReferenceWeightedTest_radialPartial
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (ha : ContDiffOn ℝ ∞ a (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ q ∈ physicalPieceOpen S K m, K.chart z m q = (Y q.1, q.2))
    (hφ : CanonicalTest S K m φ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    radialPartial (n06ReferenceWeightedTest S K z m a φ) p =
      deriv a p.1 * φ (K.chart z m p) +
        a p.1 * (deriv Y p.1 * radialPartial φ (K.chart z m p)) := by
  have ha' := (ha.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).differentiableAt (by simp)
  have hY' := (hY.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).differentiableAt (by simp)
  have hφ' := hasDerivAt_radialSlice
    (hφ.1.differentiable (by simp) (Y p.1, p.2))
  have hder := ha'.hasDerivAt.mul (hφ'.comp p.1 hY'.hasDerivAt)
  have he : (fun r => n06ReferenceWeightedTest S K z m a φ (r, p.2)) =ᶠ[𝓝 p.1]
      (fun r => a r * φ (Y r, p.2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with r hr
    rw [n06ReferenceWeightedTest_of_mem ⟨hr, mem_univ _⟩,
      hchart (r, p.2) ⟨hr, mem_univ _⟩]
  have hslice := hasDerivAt_radialSlice
    ((n06ReferenceWeightedTest_contDiff hK hz hs ha hφ).differentiable (by simp) p)
  have heq := hslice.unique (hder.congr_of_eventuallyEq he)
  rw [hchart p hp]
  simpa only [Function.comp_apply, mul_comm] using heq

/-- The actual planar Jacobian of a radial chart is its signed radial derivative. -/
theorem n06_reference_radial_jacobian
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ q ∈ physicalPieceOpen S K m, K.chart z m q = (Y q.1, q.2))
    {p : PolarPoint} (hp : p ∈ physicalPieceOpen S K m) :
    planeJacobian (K.chart z m) p = deriv Y p.1 := by
  have hd := (hY.contDiffAt (isOpen_Ioo.mem_nhds hp.1)).differentiableAt (by simp)
  have hFD : HasFDerivAt (fun q : PolarPoint => (Y q.1, q.2))
      (((ContinuousLinearMap.toSpanSingleton ℝ (deriv Y p.1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    (hd.hasDerivAt.hasFDerivAt.comp p hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have he : K.chart z m =ᶠ[𝓝 p] (fun q : PolarPoint => (Y q.1, q.2)) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact hchart q hq
  rw [planeJacobian, (hFD.congr_of_eventuallyEq he).fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    one_mul, zero_mul, mul_one, mul_zero, sub_zero]

/-- Injectivity and smoothness select one orientation for the whole actual piece. -/
theorem n06_reference_radial_orientation
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hY : ContDiffOn ℝ ∞ Y (Ioo (K.physicalLeft m) (K.physicalRight m)))
    (hchart : ∀ q ∈ physicalPieceOpen S K m, K.chart z m q = (Y q.1, q.2)) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ r ∈ Ioo (K.physicalLeft m) (K.physicalRight m), |deriv Y r| = σ * deriv Y r := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hs m
  have hinj : InjOn Y (Ioo (K.physicalLeft m) (K.physicalRight m)) := by
    intro r hr t ht he
    have hchartEq : K.chart z m (r, 0) = K.chart z m (t, 0) := by
      rw [hchart (r, 0) ⟨hr, mem_univ _⟩, hchart (t, 0) ⟨ht, mem_univ _⟩, he]
    exact congrArg Prod.fst ((hcharts.2.2.1 (r, 0) ⟨hr, mem_univ _⟩).symm.trans
      ((congrArg (K.inverseChart z m) hchartEq).trans
        (hcharts.2.2.1 (t, 0) ⟨ht, mem_univ _⟩)))
  rcases hY.continuousOn.strictMonoOn_of_injOn_Ioo (hK.2.2.2.1 m).1 hinj with hm | hm
  · refine ⟨1, Or.inl rfl, fun r hr => ?_⟩
    have hd : 0 ≤ deriv Y r := by
      simpa only [derivWithin_of_isOpen isOpen_Ioo hr] using
        (hm.monotoneOn.derivWithin_nonneg (x := r))
    rw [abs_of_nonneg hd, one_mul]
  · refine ⟨-1, Or.inr rfl, fun r hr => ?_⟩
    have hd : deriv Y r ≤ 0 := by
      simpa only [derivWithin_of_isOpen isOpen_Ioo hr] using
        (hm.antitoneOn.derivWithin_nonpos (x := r))
    rw [abs_of_nonpos hd, neg_one_mul]

end ContinuousFlexibility.Analysis
