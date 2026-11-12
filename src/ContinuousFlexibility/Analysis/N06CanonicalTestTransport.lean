import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import ContinuousFlexibility.Analysis.N06CanonicalProperties
import Mathlib.Algebra.Field.Periodic

/-!
# Compact canonical tests as genuine physical tests

The physical test is the height times the canonical test in the actual
chart, extended by zero off the selected physical piece. Its radial
support lies in the radial projection of the inverse image of one compact
canonical period, strictly inside the original annulus. At an actual
physical boundary the forward image leaves that compact canonical support,
so the zero extension is smooth even along a moving cut.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped ContDiff Topology
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint

set_option backward.isDefEq.respectTransparency false

/-- The exact physical pullback, with its original piece as the zero-extension domain. -/
def n06CanonicalTestPullback (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (φ : PolarPoint → ℝ) : PolarPoint → ℝ := by
  classical
  exact fun p => if p ∈ physicalPieceOpen S K z m then
    K.height z m p * φ (K.chart z m p) else 0

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}

theorem n06CanonicalTestPullback_eq_of_mem {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z m) :
    n06CanonicalTestPullback S K z m φ p = K.height z m p * φ (K.chart z m p) := by
  simp only [n06CanonicalTestPullback, if_pos hp]

theorem n06CanonicalTestPullback_eq_zero_of_not_mem {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K z m) :
    n06CanonicalTestPullback S K z m φ p = 0 := by
  simp only [n06CanonicalTestPullback, if_neg hp]

theorem n06CanonicalTestPullback_eventuallyEq_of_mem
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K z m) :
    n06CanonicalTestPullback S K z m φ =ᶠ[𝓝 p]
      fun q => K.height z m q * φ (K.chart z m q) := by
  filter_upwards [(hK.domains z hz hsector m).1.mem_nhds hp] with q hq
  exact n06CanonicalTestPullback_eq_of_mem hq

/-- One compact canonical angular period gives a compact radial support
inside the original annulus. The periodic inverse covers every lift. -/
theorem n06CanonicalTestPullback_radialSupport
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    ∃ Jp : Set ℝ, IsCompact Jp ∧ Jp ⊆ Ioo D.a D.b ∧
      ∀ r, r ∉ Jp → ∀ θ, n06CanonicalTestPullback S K z m φ (r, θ) = 0 := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  have hcharts := hK.charts z hz hsector m
  let Jp : Set ℝ :=
    (fun p : PolarPoint => (K.inverseChart z m p).1) '' (J ×ˢ Icc (0 : ℝ) Real.pi)
  have hJp : IsCompact Jp := (hJ.prod isCompact_Icc).image_of_continuousOn
    (hcharts.2.2.2.2.2.1.continuousOn.fst.mono
      (fun p hp => ⟨hJK hp.1, mem_univ _⟩))
  have hJpK : Jp ⊆ Ioo D.a D.b := by
    rintro r ⟨p, hp, rfl⟩
    exact ((hK.domains z hz hsector m).2.2.1
      (hcharts.2.1 ⟨hJK hp.1, mem_univ _⟩)).1
  have hGperiod (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      Function.Periodic (fun θ => (K.inverseChart z m (r, θ)).1) Real.pi := by
    intro θ
    have he := inverseChart_periodic_of_chart_periodic_on hcharts.2.1
      (fun q hq => ((hK.domains z hz hsector m).2.2.2.1 q).mpr hq) hcharts.2.2.1
      hcharts.2.2.2.1 (fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).2.2.1)
      (p := (r, θ)) ⟨hr, mem_univ _⟩
    simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero] using congrArg Prod.fst he
  refine ⟨Jp, hJp, hJpK, ?_⟩
  intro r hr θ
  by_cases hp : (r, θ) ∈ physicalPieceOpen S K z m
  · have hFJ : (K.chart z m (r, θ)).1 ∉ J := by
      intro hmem
      obtain ⟨η, hη, he⟩ := (hGperiod (K.chart z m (r, θ)).1
        (hcharts.1 hp).1).exists_mem_Ico₀ Real.pi_pos (K.chart z m (r, θ)).2
      apply hr
      refine ⟨((K.chart z m (r, θ)).1, η), ⟨hmem, hη.1, hη.2.le⟩, ?_⟩
      exact he.symm.trans (congrArg Prod.fst (hcharts.2.2.1 (r, θ) hp))
    have hzφ : φ (K.chart z m (r, θ)) = 0 :=
      hzero (K.chart z m (r, θ)).1 hFJ (K.chart z m (r, θ)).2
    rw [n06CanonicalTestPullback_eq_of_mem hp, hzφ, mul_zero]
  · exact n06CanonicalTestPullback_eq_zero_of_not_mem hp

/-- Compact support in the interior makes the extension identically zero
on a neighborhood of every point outside the physical piece. -/
theorem n06CanonicalTestPullback_eventually_zero_of_not_mem
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K z m) :
    n06CanonicalTestPullback S K z m φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  by_cases hpcl : p ∈ physicalPieceClosed S K z m
  · obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
    have hb := hK.boundary z hz hsector m
    have hFpJ : (K.chart z m p).1 ∉ J := by
      intro hmem
      have hFp : K.chart z m p ∈ canonicalOpen S K m :=
        ⟨hJK hmem, mem_univ _⟩
      have hinside := (hK.charts z hz hsector m).2.1 hFp
      rw [hb.2.2.1 p hpcl] at hinside
      exact hp hinside
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, (K.chart z m q).1 ∉ J :=
      ((hb.2.2.2.2.1 p hpcl).1.continuousAt.fst.tendsto).eventually
        (hJ.isClosed.isOpen_compl.mem_nhds hFpJ)
    filter_upwards [hnear] with q hq
    by_cases hqΩ : q ∈ physicalPieceOpen S K z m
    · rw [n06CanonicalTestPullback_eq_of_mem hqΩ,
        hzero (K.chart z m q).1 hq (K.chart z m q).2, mul_zero]
    · exact n06CanonicalTestPullback_eq_zero_of_not_mem hqΩ
  · have hnear : ∀ᶠ q : PolarPoint in 𝓝 p,
        q ∉ closure (physicalPieceOpen S K z m) :=
      isClosed_closure.isOpen_compl.mem_nhds hpcl
    filter_upwards [hnear] with q hq
    exact n06CanonicalTestPullback_eq_zero_of_not_mem
      (fun hmem => hq (subset_closure hmem))

theorem n06CanonicalTestPullback_contDiff
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    ContDiff ℝ ∞ (n06CanonicalTestPullback S K z m φ) := by
  have hcharts := hK.charts z hz hsector m
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hsector m).1
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ physicalPieceOpen S K z m
  · have hF := hcharts.2.2.2.2.1.contDiffAt (hU.mem_nhds hp)
    have hh := hcharts.2.2.2.2.2.2.1.contDiffAt (hU.mem_nhds hp)
    exact (hh.mul (hφ.1.contDiffAt.comp p hF)).congr_of_eventuallyEq
      (n06CanonicalTestPullback_eventuallyEq_of_mem hK hz hsector hp)
  · have hzero : ContDiffAt ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) p := contDiffAt_const
    exact hzero.congr_of_eventuallyEq
      (n06CanonicalTestPullback_eventually_zero_of_not_mem hK hz hsector hφ hp)

theorem n06CanonicalTestPullback_periodic
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    Function.Periodic (n06CanonicalTestPullback S K z m φ) (0, Real.pi) := by
  have hcharts := hK.charts z hz hsector m
  intro p
  have hshift : p + (0, Real.pi) ∈ physicalPieceOpen S K z m ↔ p ∈ physicalPieceOpen S K z m := by
    exact (hK.domains z hz hsector m).2.2.2.1 p
  by_cases hp : p ∈ physicalPieceOpen S K z m
  · rw [n06CanonicalTestPullback_eq_of_mem (hshift.mpr hp),
      n06CanonicalTestPullback_eq_of_mem hp,
      (hcharts.2.2.2.2.2.2.2 p hp).2.2.2,
      (hcharts.2.2.2.2.2.2.2 p hp).2.2.1, hφ.2.1 (K.chart z m p)]
  · rw [n06CanonicalTestPullback_eq_zero_of_not_mem (mt hshift.mp hp),
      n06CanonicalTestPullback_eq_zero_of_not_mem hp]

/-- The genuine reflected domain and chart preserve even physical tests.
The angular symmetry of the canonical test is explicit. -/
theorem n06CanonicalTestPullback_even
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : ∀ r θ, φ (r, -θ) = φ (r, θ)) :
    ∀ r θ, n06CanonicalTestPullback S K z m φ (r, -θ) =
      n06CanonicalTestPullback S K z m φ (r, θ) := by
  intro r θ
  have he : (r, -θ) ∈ physicalPieceOpen S K z m ↔
      (r, θ) ∈ physicalPieceOpen S K z m :=
    (hK.domains z hz hsector m).2.2.2.2.1 (r, θ)
  by_cases hp : (r, θ) ∈ physicalPieceOpen S K z m
  · have hreflection := hK.reflection z hz hsector m (r, θ) hp
    rw [n06CanonicalTestPullback_eq_of_mem (he.mpr hp),
      n06CanonicalTestPullback_eq_of_mem hp, hreflection.1, hreflection.2.1,
      hφ (K.chart z m (r, θ)).1 (K.chart z m (r, θ)).2]
  · rw [n06CanonicalTestPullback_eq_zero_of_not_mem (mt he.mp hp),
      n06CanonicalTestPullback_eq_zero_of_not_mem hp]

/-- This is a test in the exact full-period physical test class. -/
theorem n06CanonicalTestPullback_radialTest
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    RadialTest D (n06CanonicalTestPullback S K z m φ) := by
  obtain ⟨Jp, hJp, hJpK, hzero⟩ := n06CanonicalTestPullback_radialSupport hK hz hsector hφ
  have hp := n06CanonicalTestPullback_periodic hK hz hsector hφ
  refine ⟨n06CanonicalTestPullback_contDiff hK hz hsector hφ, ?_,
    Jp, hJp, hJpK, hzero⟩
  have hperiod : ((0 : ℝ), Real.pi) + (0, Real.pi) = (0, 2 * Real.pi) := by
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, zero_add] <;> ring
  rw [← hperiod]
  exact hp.add_period hp

/-- On the original canonical piece the height transform returns the
given test exactly, including its original representative. -/
theorem n06CanonicalTestPullback_canonicalHeight
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    canonicalHeight S K z m (n06CanonicalTestPullback S K z m φ) p = φ p := by
  have hcharts := hK.charts z hz hsector m
  have hGp := hcharts.2.1 hp
  have hh := (hcharts.2.2.2.2.2.2.2 (K.inverseChart z m p) hGp).1
  unfold canonicalHeight
  rw [n06CanonicalTestPullback_eq_of_mem hGp, hcharts.2.2.2.1 p hp]
  exact mul_div_cancel_left₀ _ hh.ne'

/-- The same actual N04 properties supply the transported physical test;
the coordinate witness and its piece are unchanged. -/
theorem n06_canonicalTest_transport
    (hN04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    RadialTest D (n06CanonicalTestPullback S K z m φ) ∧
      Function.Periodic (n06CanonicalTestPullback S K z m φ) (0, Real.pi) ∧
      ∀ p ∈ physicalPieceOpen S K z m,
        n06CanonicalTestPullback S K z m φ p = K.height z m p * φ (K.chart z m p) := by
  have hK := (n06_N04_qualitative_parts hN04).1
  exact ⟨n06CanonicalTestPullback_radialTest hK hz hsector hφ,
    n06CanonicalTestPullback_periodic hK hz hsector hφ,
    fun _ hp => n06CanonicalTestPullback_eq_of_mem hp⟩

end ContinuousFlexibility.Analysis
