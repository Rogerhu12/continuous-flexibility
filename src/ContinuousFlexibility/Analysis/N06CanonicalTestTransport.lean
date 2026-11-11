import ContinuousFlexibility.Analysis.CanonicalStripGeometry
import ContinuousFlexibility.Analysis.N06CanonicalProperties
import Mathlib.Algebra.Field.Periodic

/-!
# Compact canonical tests as genuine physical tests

The physical test is the height times the canonical test in the actual
chart, extended by zero off the selected physical piece. Its radial
support lies in the radial projection of the inverse image of one compact
canonical period. That projection stays strictly inside the physical
interval, so zero extension is smooth at both endpoints by a zero germ.
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
  exact fun p => if p ∈ physicalPieceOpen S K m then
    K.height z m p * φ (K.chart z m p) else 0

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss m : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}

theorem n06CanonicalTestPullback_eq_of_mem {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n06CanonicalTestPullback S K z m φ p = K.height z m p * φ (K.chart z m p) := by
  simp only [n06CanonicalTestPullback, if_pos hp]

theorem n06CanonicalTestPullback_eq_zero_of_not_mem {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K m) :
    n06CanonicalTestPullback S K z m φ p = 0 := by
  simp only [n06CanonicalTestPullback, if_neg hp]

theorem n06CanonicalTestPullback_eventuallyEq_of_mem {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n06CanonicalTestPullback S K z m φ =ᶠ[𝓝 p]
      fun q => K.height z m q * φ (K.chart z m q) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact n06CanonicalTestPullback_eq_of_mem hq

/-- One compact canonical angular period gives a compact physical radial
support. The same periodic radial component covers every angular lift. -/
theorem n06CanonicalTestPullback_radialSupport
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    ∃ Jp : Set ℝ, IsCompact Jp ∧ Jp ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) ∧
      ∀ r, r ∉ Jp → ∀ θ, n06CanonicalTestPullback S K z m φ (r, θ) = 0 := by
  obtain ⟨J, hJ, hJK, hzero⟩ := hφ.2.2
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  let Jp : Set ℝ :=
    (fun p : PolarPoint => (K.inverseChart z m p).1) '' (J ×ˢ Icc (0 : ℝ) Real.pi)
  have hJp : IsCompact Jp := (hJ.prod isCompact_Icc).image_of_continuousOn
    (hcharts.2.2.2.2.2.1.continuousOn.fst.mono
      (fun p hp => ⟨hJK hp.1, mem_univ _⟩))
  have hJpK : Jp ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) := by
    rintro r ⟨p, hp, rfl⟩
    exact (hcharts.2.1 ⟨hJK hp.1, mem_univ _⟩).1
  have hGperiod (r : ℝ) (hr : r ∈ Ioo (K.left m) (K.right m)) :
      Function.Periodic (fun θ => (K.inverseChart z m (r, θ)).1) Real.pi := by
    intro θ
    have he := inverseChart_periodic_of_chart_periodic hcharts.2.1 hcharts.2.2.1
      hcharts.2.2.2.1 (fun p hp => (hcharts.2.2.2.2.2.2.2 p hp).2.2.1)
      (p := (r, θ)) ⟨hr, mem_univ _⟩
    simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero] using congrArg Prod.fst he
  refine ⟨Jp, hJp, hJpK, ?_⟩
  intro r hr θ
  by_cases hp : (r, θ) ∈ physicalPieceOpen S K m
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
    (hp : p ∉ physicalPieceOpen S K m) :
    n06CanonicalTestPullback S K z m φ =ᶠ[𝓝 p] (0 : PolarPoint → ℝ) := by
  obtain ⟨Jp, hJp, hJpK, hzero⟩ := n06CanonicalTestPullback_radialSupport hK hz hsector hφ
  have hpJ : p.1 ∉ Jp := fun h => hp ⟨hJpK h, mem_univ _⟩
  have hnear : ∀ᶠ r : ℝ in 𝓝 p.1, r ∉ Jp := hJp.isClosed.isOpen_compl.mem_nhds hpJ
  filter_upwards [(continuous_fst.tendsto p).eventually hnear] with q hq
  exact hzero q.1 hq q.2

theorem n06CanonicalTestPullback_contDiff
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    ContDiff ℝ ∞ (n06CanonicalTestPullback S K z m φ) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  have hU : IsOpen (physicalPieceOpen S K m) := isOpen_Ioo.prod isOpen_univ
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p ∈ physicalPieceOpen S K m
  · have hF := hcharts.2.2.2.2.1.contDiffAt (hU.mem_nhds hp)
    have hh := hcharts.2.2.2.2.2.2.1.contDiffAt (hU.mem_nhds hp)
    exact (hh.mul (hφ.1.contDiffAt.comp p hF)).congr_of_eventuallyEq
      (n06CanonicalTestPullback_eventuallyEq_of_mem hp)
  · have hzero : ContDiffAt ℝ ∞ (fun _ : PolarPoint => (0 : ℝ)) p := contDiffAt_const
    exact hzero.congr_of_eventuallyEq
      (n06CanonicalTestPullback_eventually_zero_of_not_mem hK hz hsector hφ hp)

theorem n06CanonicalTestPullback_periodic
    (hK : N04PartA D S C K base ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (hφ : CanonicalTest S K m φ) :
    Function.Periodic (n06CanonicalTestPullback S K z m φ) (0, Real.pi) := by
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
  intro p
  have hshift : p + (0, Real.pi) ∈ physicalPieceOpen S K m ↔ p ∈ physicalPieceOpen S K m := by
    simp only [physicalPieceOpen, mem_prod, Prod.fst_add, add_zero, mem_univ, and_true]
  by_cases hp : p ∈ physicalPieceOpen S K m
  · rw [n06CanonicalTestPullback_eq_of_mem (hshift.mpr hp),
      n06CanonicalTestPullback_eq_of_mem hp,
      (hcharts.2.2.2.2.2.2.2 p hp).2.2.2,
      (hcharts.2.2.2.2.2.2.2 p hp).2.2.1, hφ.2.1 (K.chart z m p)]
  · rw [n06CanonicalTestPullback_eq_zero_of_not_mem (mt hshift.mp hp),
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
    Jp, hJp, hJpK.trans (hK.2.2.2.1 m).2.2, hzero⟩
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
  have hcharts := hK.2.2.2.2.2.2.2.1 z hz hsector m
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
      ∀ p ∈ physicalPieceOpen S K m,
        n06CanonicalTestPullback S K z m φ p = K.height z m p * φ (K.chart z m p) := by
  have hK := (n06_N04_qualitative_parts hN04).1
  exact ⟨n06CanonicalTestPullback_radialTest hK hz hsector hφ,
    n06CanonicalTestPullback_periodic hK hz hsector hφ,
    fun _ hp => n06CanonicalTestPullback_eq_of_mem hp⟩

end ContinuousFlexibility.Analysis
