module

public import ContinuousFlexibility.Analysis.N07aCurrentPhysicalGeometry
public import Mathlib.Algebra.Order.ToIntervalMod

/-!
# Genuine compact physical tests for canonical weak equations

A compact canonical radial test has compact radial preimage under the
actual periodic strip diffeomorphism. Zero extension outside the physical
piece is therefore globally smooth and is a genuine physical test.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology

private theorem n07a_domain_compact_radial_preimage {a b c d : ℝ}
    {Omega : Set PolarPoint} {F G : PolarPoint → PolarPoint}
    (hOmega : Omega ⊆ Ioo a b ×ˢ (univ : Set ℝ))
    (hf : MapsTo F Omega (Ioo c d ×ˢ (univ : Set ℝ)))
    (hg : MapsTo G (Ioo c d ×ˢ (univ : Set ℝ)) Omega)
    (hgf : ∀ p ∈ Omega, G (F p) = p)
    (hGs : ContDiffOn ℝ ∞ G (Ioo c d ×ˢ (univ : Set ℝ)))
    (hGP : ∀ p ∈ Ioo c d ×ˢ (univ : Set ℝ), G (p + (0, Real.pi)) = G p + (0, Real.pi))
    {J : Set ℝ} (hJ : IsCompact J) (hJU : J ⊆ Ioo c d) :
    ∃ A : Set ℝ, IsCompact A ∧ A ⊆ Ioo a b ∧
      ∀ p ∈ Omega, (F p).1 ∈ J → p.1 ∈ A := by
  let A := (fun q : PolarPoint => (G q).1) '' (J ×ˢ Icc (0 : ℝ) Real.pi)
  have hAc : IsCompact A := (hJ.prod isCompact_Icc).image_of_continuousOn
    ((hGs.continuousOn.mono (fun q hq => ⟨hJU hq.1, mem_univ _⟩)).fst)
  have hAU : A ⊆ Ioo a b := by
    rintro r ⟨q, hq, rfl⟩
    exact (hOmega (hg ⟨hJU hq.1, mem_univ _⟩)).1
  refine ⟨A, hAc, hAU, ?_⟩
  intro p hp hJp
  let theta := toIocMod Real.pi_pos 0 (F p).2
  obtain ⟨htheta, k, hk⟩ := (toIocMod_eq_iff Real.pi_pos).mp
    (show toIocMod Real.pi_pos 0 (F p).2 = theta from rfl)
  simp only [zero_add] at htheta
  have hper : Function.Periodic (fun t : ℝ => (G ((F p).1, t)).1) Real.pi := by
    intro t
    have h := congrArg Prod.fst (hGP ((F p).1, t) ⟨(hf hp).1, mem_univ _⟩)
    simpa only [Prod.mk_add_mk, Prod.fst_add, add_zero] using h
  have hreduced : (G (F p)).1 = (G ((F p).1, theta)).1 := by
    have h := hper.zsmul k theta
    rw [← hk] at h
    exact h
  refine ⟨((F p).1, theta), ⟨hJp, Ioc_subset_Icc_self htheta⟩, ?_⟩
  exact hreduced.symm.trans (congrArg Prod.fst (hgf p hp))

def n07aPhysicalTestPullback (S : PhysicalSpacesData) (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (W : PolarPoint → ℝ) (p : PolarPoint) : ℝ := by
  classical
  exact if p ∈ physicalPieceOpen S K z m
    then K.height z m p * W (K.chart z m p) else 0

theorem n07aPhysicalTestPullback_germ {S : PhysicalSpacesData} {K : CanonicalData S}
    (z : AnnularState S × ℝ) (m : ℕ) (W : PolarPoint → ℝ) {p : PolarPoint}
    (hOmega : IsOpen (physicalPieceOpen S K z m)) (hp : p ∈ physicalPieceOpen S K z m) :
    n07aPhysicalTestPullback S K z m W =ᶠ[𝓝 p]
      fun q => K.height z m q * W (K.chart z m q) := by
  filter_upwards [hOmega.mem_nhds hp] with q hq
  simp only [n07aPhysicalTestPullback, if_pos hq]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ} {m : ℕ}

/-- Compact canonical support gives a genuine zero germ at every point
outside the actual current domain, including its moving boundary. -/
theorem n07aPhysicalTestPullback_zero_germ
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) {p : PolarPoint}
    (hp : p ∉ physicalPieceOpen S K z m) :
    n07aPhysicalTestPullback S K z m W =ᶠ[𝓝 p] fun _ => 0 := by
  obtain ⟨_, _, J, hJ, hJU, hWzero⟩ := hW
  by_cases hpcl : p ∈ physicalPieceClosed S K z m
  · have hboundary := h04.1.boundary z hz hs m
    have hnot : K.chart z m p ∉ canonicalOpen S K m := by
      intro hcan
      have hin := (h04.1.charts z hz hs m).2.1 hcan
      rw [hboundary.2.2.1 p hpcl] at hin
      exact hp hin
    have hpJ : (K.chart z m p).1 ∉ J :=
      fun hj => hnot ⟨hJU hj, mem_univ _⟩
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, (K.chart z m q).1 ∉ J :=
      (hboundary.2.2.2.2.1 p hpcl).1.continuousAt.fst.eventually
        (hJ.isClosed.isOpen_compl.mem_nhds hpJ)
    filter_upwards [hnear] with q hq
    unfold n07aPhysicalTestPullback
    split_ifs
    · rw [show W (K.chart z m q) = 0 from hWzero _ hq _, mul_zero]
    · rfl
  · have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q ∉ physicalPieceClosed S K z m :=
      isClosed_closure.isOpen_compl.mem_nhds hpcl
    filter_upwards [hnear] with q hq
    simp only [n07aPhysicalTestPullback, if_neg (fun h => hq (subset_closure h))]

/-- The gauge pullback is a smooth physical test. Its radial support is
compact inside the annulus; the supporting physical piece may move. -/
theorem n07aPhysicalTestPullback_test
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {W : PolarPoint → ℝ} (hW : CanonicalTest S K m W) :
    RadialTest D (n07aPhysicalTestPullback S K z m W) ∧
      Function.Periodic (n07aPhysicalTestPullback S K z m W) (0, Real.pi) ∧
      ∃ A : Set ℝ, IsCompact A ∧ A ⊆ Ioo D.a D.b ∧
        ∀ r ∉ A, ∀ theta, n07aPhysicalTestPullback S K z m W (r, theta) = 0 := by
  have hdomain := h04.1.domains z hz hs m
  obtain ⟨hf, hg, hgf, hfg, hfs, hgs, hh, hgp⟩ := h04.1.charts z hz hs m
  obtain ⟨hWs, hWp, J, hJ, hJU, hWzero⟩ := hW
  obtain ⟨A, hAc, hAU, hpre⟩ := n07a_domain_compact_radial_preimage
    hdomain.2.2.1 hf hg hgf hgs
    (n07a_current_inverseChart_periodic h04 hz hs m) hJ hJU
  have hzero (r : ℝ) (hr : r ∉ A) (theta : ℝ) :
      n07aPhysicalTestPullback S K z m W (r, theta) = 0 := by
    unfold n07aPhysicalTestPullback
    by_cases hri : (r, theta) ∈ physicalPieceOpen S K z m
    · rw [ite_eq_left hri]
      have hnot : (K.chart z m (r, theta)).1 ∉ J :=
        fun hj => hr (hpre (r, theta) hri hj)
      rw [show W (K.chart z m (r, theta)) = 0 from hWzero _ hnot _, mul_zero]
    · exact ite_eq_right hri
  have hsmooth : ContDiff ℝ ∞ (n07aPhysicalTestPullback S K z m W) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p ∈ physicalPieceOpen S K z m
    · have hnear := hdomain.1.mem_nhds hp
      exact ((hh.contDiffAt hnear).mul (hWs.contDiffAt.comp p (hfs.contDiffAt hnear))).congr_of_eventuallyEq
        (n07aPhysicalTestPullback_germ z m W hdomain.1 hp)
    · exact contDiffAt_const.congr_of_eventuallyEq
        (n07aPhysicalTestPullback_zero_germ h04 hz hs
          ⟨hWs, hWp, J, hJ, hJU, hWzero⟩ hp)
  have hperiod : Function.Periodic (n07aPhysicalTestPullback S K z m W) (0, Real.pi) := by
    intro p
    by_cases hp : p ∈ physicalPieceOpen S K z m
    · have hps := (hdomain.2.2.2.1 p).mpr hp
      simp only [n07aPhysicalTestPullback, ite_eq_left hp, ite_eq_left hps]
      rw [(hgp p hp).2.2.2, (hgp p hp).2.2.1, hWp]
    · have hps : p + (0, Real.pi) ∉ physicalPieceOpen S K z m :=
        fun h => hp ((hdomain.2.2.2.1 p).mp h)
      simp only [n07aPhysicalTestPullback, ite_eq_right hp, ite_eq_right hps]
  refine ⟨⟨hsmooth, ?_, A, hAc, hAU, hzero⟩, hperiod, A, hAc, hAU, hzero⟩
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
