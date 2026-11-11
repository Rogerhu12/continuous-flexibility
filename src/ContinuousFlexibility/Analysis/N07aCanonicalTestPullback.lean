import ContinuousFlexibility.Analysis.N07aCanonicalHalfStrip
import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Genuine compact physical tests for canonical weak equations

A compact canonical radial test has compact radial preimage under the
actual periodic strip diffeomorphism. Zero extension outside the physical
piece is therefore globally smooth and is a genuine physical test.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem n07a_strip_compact_radial_preimage {a b c d : ℝ}
    {F G : PolarPoint → PolarPoint}
    (hf : MapsTo F (Ioo a b ×ˢ (univ : Set ℝ)) (Ioo c d ×ˢ (univ : Set ℝ)))
    (hg : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) (Ioo a b ×ˢ (univ : Set ℝ)))
    (hgf : ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), G (F p) = p)
    (hGs : ContDiffOn ℝ ∞ G (Ioo c d ×ˢ (univ : Set ℝ)))
    (hGP : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p + (0, Real.pi)) = G p + (0, Real.pi))
    {J : Set ℝ} (hJ : IsCompact J) (hJU : J ⊆ Ioo c d) :
    ∃ A : Set ℝ, IsCompact A ∧ A ⊆ Ioo a b ∧
      ∀ p ∈ Ioo a b ×ˢ (univ : Set ℝ), (F p).1 ∈ J → p.1 ∈ A := by
  let A := (fun q : PolarPoint => (G q).1) '' (J ×ˢ Icc (0 : ℝ) Real.pi)
  have hAc : IsCompact A := (hJ.prod isCompact_Icc).image_of_continuousOn
    ((hGs.continuousOn.mono (fun q hq => ⟨hJU hq.1, mem_univ _⟩)).fst)
  have hAU : A ⊆ Ioo a b := by
    rintro r ⟨q, hq, rfl⟩
    exact (hg ⟨hJU hq.1, mem_univ _⟩).1
  refine ⟨A, hAc, hAU, ?_⟩
  intro p hp hJp
  let θ := toIocMod Real.pi_pos 0 (F p).2
  obtain ⟨hθ, k, hk⟩ := (toIocMod_eq_iff Real.pi_pos).mp
    (show toIocMod Real.pi_pos 0 (F p).2 = θ from rfl)
  simp only [zero_add] at hθ
  have hper : Function.Periodic (fun t : ℝ => (G ((F p).1, t)).1) Real.pi := by
    intro t
    have h := congrArg Prod.fst (hGP ((F p).1, t) ⟨(hf hp).1, mem_univ _⟩)
    simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero] using h
  have hreduced : (G (F p)).1 = (G ((F p).1, θ)).1 := by
    have h := hper.zsmul k θ
    rw [← hk] at h
    exact h
  refine ⟨((F p).1, θ), ⟨hJp, Ioc_subset_Icc_self hθ⟩, ?_⟩
  exact hreduced.symm.trans (congrArg Prod.fst (hgf p hp))

def n07aPhysicalTestPullback (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (W : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
  then K.height z m p * W (K.chart z m p) else 0

theorem n07aPhysicalTestPullback_germ {S : PhysicalSpacesData} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (W : PolarPoint → ℝ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    n07aPhysicalTestPullback S K z m W =ᶠ[𝓝 p]
      fun q => K.height z m q * W (K.chart z m q) := by
  filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
  exact ite_eq_left hq.1

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- The actual gauge pullback, extended by zero, is an admissible physical
test. Its support stays compactly inside this same physical piece. -/
theorem n07aPhysicalTestPullback_test
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    RadialTest D (n07aPhysicalTestPullback S K z m W) ∧
      Function.Periodic (n07aPhysicalTestPullback S K z m W) (0, Real.pi) ∧
      ∃ A : Set ℝ, IsCompact A ∧ A ⊆ Ioo (K.physicalLeft m) (K.physicalRight m) ∧
        ∀ r ∉ A, ∀ θ, n07aPhysicalTestPullback S K z m W (r, θ) = 0 := by
  rcases h04 with ⟨_, _, _, hinterval, _, _, _, hgeom, _⟩
  obtain ⟨hf, hg, hgf, hfg, hfs, hgs, hh, hgp⟩ := hgeom z hz hs m
  obtain ⟨hWs, hWp, J, hJ, hJU, hWzero⟩ := hW
  have hfp : ∀ p ∈ physicalPieceOpen S K m,
      K.chart z m (p + (0, Real.pi)) = K.chart z m p + (0, Real.pi) :=
    fun p hp => (hgp p hp).2.2.1
  obtain ⟨A, hAc, hAU, hpre⟩ := n07a_strip_compact_radial_preimage hf hg hgf hgs
    (n07a_strip_inverse_periodic hg hgf hfg hfp) hJ hJU
  have hzero (r : ℝ) (hr : r ∉ A) (θ : ℝ) :
      n07aPhysicalTestPullback S K z m W (r, θ) = 0 := by
    unfold n07aPhysicalTestPullback
    by_cases hri : r ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
    · rw [ite_eq_left hri]
      have hnot : (K.chart z m (r, θ)).1 ∉ J :=
        fun hj => hr (hpre (r, θ) ⟨hri, mem_univ _⟩ hj)
      rw [show W (K.chart z m (r, θ)) = 0 from hWzero _ hnot _, mul_zero]
    · exact ite_eq_right hri
  have hsmooth : ContDiff ℝ ∞ (n07aPhysicalTestPullback S K z m W) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ physicalPieceOpen S K m
    · have hnear := (isOpen_Ioo.prod isOpen_univ).mem_nhds hp
      exact ((hh.contDiffAt hnear).mul (hWs.contDiffAt.comp p (hfs.contDiffAt hnear))).congr_of_eventuallyEq
        (n07aPhysicalTestPullback_germ z m W hp)
    · have hpA : p.1 ∉ A := fun h => hp ⟨hAU h, mem_univ _⟩
      have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ A :=
        continuous_fst.continuousAt.eventually (hAc.isClosed.isOpen_compl.mem_nhds hpA)
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [hnear] with q hq
      exact hzero q.1 hq q.2
  have hperiod : Function.Periodic (n07aPhysicalTestPullback S K z m W) (0, Real.pi) := by
    intro p
    by_cases hp : p.1 ∈ Ioo (K.physicalLeft m) (K.physicalRight m)
    · simp only [n07aPhysicalTestPullback, Prod.fst_add, add_zero, ite_eq_left hp]
      rw [(hgp p ⟨hp, mem_univ _⟩).2.2.2, hfp p ⟨hp, mem_univ _⟩, hWp]
    · simp only [n07aPhysicalTestPullback, Prod.fst_add, add_zero, ite_eq_right hp]
  refine ⟨⟨hsmooth, ?_, A, hAc, hAU.trans (hinterval m).2.2, hzero⟩,
    hperiod, A, hAc, hAU, hzero⟩
  simpa only [Prod.mk_add_mk, zero_add, two_mul] using hperiod.add_period hperiod

/-- The actual divergence expression respects the unknown's germ. -/
theorem n07a_divergenceOperator_unknown_germ (A : SymmetricCoefficients)
    {u v : PolarPoint → ℝ} {p : PolarPoint} (huv : u =ᶠ[𝓝 p] v) :
    divergenceOperator A u p = divergenceOperator A v p := by
  have hd : fderiv ℝ u =ᶠ[𝓝 p] fderiv ℝ v := huv.fderiv
  have hr : (fun q => A.a q * radialPartial u q + A.b q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => A.a q * radialPartial v q + A.b q * angularPartial v q) := by
    filter_upwards [hd] with q hq
    simp only [radialPartial, angularPartial, hq]
  have ht : (fun q => A.b q * radialPartial u q + A.c q * angularPartial u q)
      =ᶠ[𝓝 p] (fun q => A.b q * radialPartial v q + A.c q * angularPartial v q) := by
    filter_upwards [hd] with q hq
    simp only [radialPartial, angularPartial, hq]
  unfold divergenceOperator
  exact congrArg₂ (fun r t : PolarPoint →L[ℝ] ℝ => r (1, 0) + t (0, 1))
    hr.fderiv_eq ht.fderiv_eq

end ContinuousFlexibility.Analysis
