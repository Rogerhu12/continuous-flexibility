import ContinuousFlexibility.Analysis.N07aAngularPrimitiveLp
import ContinuousFlexibility.Scalar.WeightedAngularPrimitiveBounds

/-!
# Angular integration on the actual open annulus

Interior smoothness suffices for the angular primitive and all its material
jets. The material radius always lies in the open annulus, so the genuine
global cylinder calculation applies without a boundary smoothness premise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set MeasureTheory
open scoped ContDiff
open ContinuousFlexibility.Statements

variable {D : ReferenceData} {T : MaterialData} {f : PolarPoint → ℝ}

theorem n07a_scalarAngularPrimitive_contDiffOn
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    ContDiffOn ℝ ∞ (scalarAngularPrimitive f) (annularOpen D) := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have he : scalarAngularPrimitive f =
      fun p : PolarPoint => p.2 * ∫ t in (0 : ℝ)..1, f (p.1, p.2 * t) :=
    funext (scalarAngularPrimitive_eq_unitIntegral f)
  rw [he]
  apply contDiffOn_snd.mul
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_intervalIntegral_parameter
    (f := fun z : PolarPoint × ℝ => f (z.1.1, z.1.2 * z.2))
    (O := annularOpen D) hopen (by norm_num : (0 : ℝ) ≤ 1) (hp := hp)
  intro q hq t _
  have hqt : (q.1, q.2 * t) ∈ annularOpen D := ⟨hq.1, mem_univ _⟩
  have hfqt : ContDiffAt ℝ ∞ f (q.1, q.2 * t) := hf.contDiffAt (hopen.mem_nhds hqt)
  exact hfqt.comp (q, t)
    (contDiff_fst.fst.prodMk (contDiff_fst.snd.mul contDiff_snd)).contDiffAt

theorem n07a_scalarAngularPrimitive_periodic
    (hf : ∀ r : ℝ, Continuous (fun θ => f (r, θ)))
    (hodd : ∀ r θ, f (r, -θ) = -f (r, θ))
    (hp : Function.Periodic f (0, Real.pi)) :
    Function.Periodic (scalarAngularPrimitive f) (0, Real.pi) := by
  intro p
  have hs : Function.Periodic (fun t => f (p.1, t)) Real.pi := by
    intro t
    simpa only [Prod.mk_add_mk, add_zero] using hp (p.1, t)
  simp only [scalarAngularPrimitive, Prod.fst_add, Prod.snd_add, add_zero]
  rw [hs.intervalIntegral_add_eq_add 0 p.2
    (fun a b => (hf p.1).intervalIntegrable a b), zero_add,
    integral_odd_periodic_angular_eq_zero hodd hp, add_zero]

theorem n07a_angular_slice_continuous
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0) (r : ℝ) :
    Continuous (fun θ => f (r, θ)) := by
  by_cases hr : r ∈ Ioo D.a D.b
  · exact (hf.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun θ => ⟨hr, mem_univ _⟩)).continuous
  · have he : (fun θ => f (r, θ)) = fun _ => (0 : ℝ) :=
      funext fun θ => hzero (r, θ) (fun h => hr h.1)
    rw [he]
    exact continuous_const

theorem n07a_angularPartial_scalarAngularPrimitive_on
    (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    {p : PolarPoint} (hp : p ∈ annularOpen D) :
    angularPartial (scalarAngularPrimitive f) p = f p := by
  have hopen : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hs : Continuous (fun θ : ℝ => f (p.1, θ)) :=
    (hf.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun _ => ⟨hp.1, mem_univ _⟩)).continuous
  have hd : HasDerivAt (fun θ => scalarAngularPrimitive f (p.1, θ)) (f p) p.2 :=
    intervalIntegral.integral_hasDerivAt_right (hs.intervalIntegrable 0 p.2)
      hs.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuousAt
  have hP : DifferentiableAt ℝ (scalarAngularPrimitive f) p :=
    ((n07a_scalarAngularPrimitive_contDiffOn hf).contDiffAt
      (hopen.mem_nhds hp)).differentiableAt (by simp)
  exact (hasDerivAt_angular_slice hP).unique hd

theorem n07a_weightedPhysicalJet_scalarAngularPrimitive_zero
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (γ : ℝ) (a c : ℕ) :
    weightedPhysicalJet T γ a 0 c (scalarAngularPrimitive f) =
      scalarAngularPrimitive (weightedPhysicalJet T γ a 0 c f) := by
  have hg : ContDiff ℝ ∞ (materialPullback T γ f) := contDiff_materialPullback hT hf
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularPrimitive,
    mixedDerivative_scalarAngularPrimitive_zero hg, scalarAngularPrimitive,
    intervalIntegral.integral_const_mul]

theorem n07a_weightedPhysicalJet_scalarAngularPrimitive_succ
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (γ : ℝ) (a b c : ℕ) :
    weightedPhysicalJet T γ a (b + 1) c (scalarAngularPrimitive f) =
      weightedPhysicalJet T γ a b c f := by
  have hg : ContDiff ℝ ∞ (materialPullback T γ f) := contDiff_materialPullback hT hf
  funext p
  simp only [weightedPhysicalJet, materialPullback_scalarAngularPrimitive,
    mixedDerivative_scalarAngularPrimitive_succ hg]

theorem n07a_scalarAngularPrimitive_weightedJets_memLp
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    {γ : ℝ} (hjets : ∀ a b c : ℕ,
      MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure) (a b c : ℕ) :
    MemLp (weightedPhysicalJet T γ a b c (scalarAngularPrimitive f))
      2 materialCylinderMeasure := by
  cases b with
  | zero =>
      rw [n07a_weightedPhysicalJet_scalarAngularPrimitive_zero hT hf]
      exact (scalarAngularPrimitive_memLp_and_norm_le
        (contDiff_weightedPhysicalJet hT hf a 0 c) (hjets a 0 c)).1
  | succ b =>
      rw [n07a_weightedPhysicalJet_scalarAngularPrimitive_succ hT hf]
      exact hjets a b c

/-- The actual odd coefficient enters the original even height model
through its fixed angular primitive. -/
theorem n07a_scalarAngularPrimitive_heightMember
    (hT : IsMaterialData D T) (hf : ContDiffOn ℝ ∞ f (annularOpen D))
    (hodd : ∀ r θ, f (r, -θ) = -f (r, θ))
    (hperiod : Function.Periodic f (0, Real.pi))
    (hzero : ∀ p, p ∉ annularOpen D → f p = 0)
    {γ : ℝ} (hjets : ∀ a b c : ℕ,
      MemLp (weightedPhysicalJet T γ a b c f) 2 materialCylinderMeasure) :
    HeightMember D T γ (scalarAngularPrimitive f) :=
  ⟨n07a_scalarAngularPrimitive_contDiffOn hf, scalarAngularPrimitive_even hodd,
    n07a_scalarAngularPrimitive_periodic (n07a_angular_slice_continuous hf hzero) hodd hperiod,
    scalarAngularPrimitive_eq_zero_outside hzero,
    n07a_scalarAngularPrimitive_weightedJets_memLp hT hf hjets⟩

end ContinuousFlexibility.Analysis
