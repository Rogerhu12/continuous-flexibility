import ContinuousFlexibility.Analysis.CylinderSobolev
import ContinuousFlexibility.Analysis.CylinderMixedJets
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Uniform mixed jet bounds on the actual material cylinder

The actual pullback is smooth and inherits the angular period. A window is
the restriction of the material cylinder measure in its first coordinate.
The global jet integrability in `HeightMember` therefore controls the four
window norms needed for each pointwise mixed jet bound.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff ENNReal

set_option backward.isDefEq.respectTransparency false

theorem contDiff_materialPullback {D : ReferenceData} {T : MaterialData} {γ : ℝ}
    {f : PolarPoint → ℝ} (hT : IsMaterialData D T)
    (hf : ContDiffOn ℝ ∞ f (annularOpen D)) :
    ContDiff ℝ ∞ (materialPullback T γ f) := by
  obtain ⟨hsmooth, hpos, _, _, _, _, hr, hInv, _⟩ := hT
  have hrange (x : ℝ) : T.radius x ∈ Ioo D.a D.b := (hInv x).1
  have hH : ContDiffOn ℝ ∞ T.H (Ioo D.a D.b) := hsmooth T.H (by simp)
  have hcoord : ContDiff ℝ ∞ (fun p : PolarPoint => T.radius p.1) := hr.comp contDiff_fst
  have hHcomp : ContDiff ℝ ∞ (fun p : PolarPoint => T.H (T.radius p.1)) :=
    hH.comp_contDiff hcoord (fun p => hrange p.1)
  have hweight : ContDiff ℝ ∞ (fun p : PolarPoint => T.H (T.radius p.1) ^ (-γ)) :=
    hHcomp.rpow_const_of_ne (fun p => (hpos _ (hrange p.1)).2.1.ne')
  have hheight : ContDiff ℝ ∞ (fun p : PolarPoint => f (T.radius p.1, p.2)) :=
    hf.comp_contDiff (hcoord.prodMk contDiff_snd) (fun p => ⟨hrange p.1, mem_univ _⟩)
  exact hweight.mul hheight

theorem contDiff_mixedDerivative {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℕ) :
    ContDiff ℝ ∞ (mixedDerivative a b g) :=
  contDiffOn_univ.mp (contDiffOn_mixedDerivative isOpen_univ hg.contDiffOn a b)

theorem radialPartial_mixedDerivative {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℕ) :
    radialPartial (mixedDerivative a b g) = mixedDerivative (a + 1) b g := by
  funext p
  rcases p with ⟨x, θ⟩
  rw [← deriv_cylinder_radial_slice ((contDiff_mixedDerivative hg a b).differentiable (by simp)) x θ]
  simp only [mixedDerivative, iteratedDeriv_succ]

theorem angularPartial_mixedDerivative {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g) (a b : ℕ) :
    angularPartial (mixedDerivative a b g) = mixedDerivative a (b + 1) g := by
  induction a with
  | zero =>
    funext p
    rcases p with ⟨x, θ⟩
    rw [← deriv_cylinder_angular_slice ((contDiff_mixedDerivative hg 0 b).differentiable (by simp)) x θ]
    simp only [mixedDerivative, iteratedDeriv_zero, iteratedDeriv_succ]
  | succ a ih =>
    rw [← radialPartial_mixedDerivative hg a b]
    have hs := contDiff_mixedDerivative hg a b
    have hcomm : angularPartial (radialPartial (mixedDerivative a b g)) =
        radialPartial (angularPartial (mixedDerivative a b g)) := by
      funext p
      exact (radial_angular_commute ((hs.contDiffAt (x := p)).of_le (by simp))).symm
    rw [hcomm, ih, radialPartial_mixedDerivative hg a (b + 1)]

private theorem iteratedDeriv_preserves_periodic {f : ℝ → ℝ} {c : ℝ}
    (hf : Function.Periodic f c) (n : ℕ) : Function.Periodic (iteratedDeriv n f) c := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    intro t
    have he : (fun y => iteratedDeriv n f (y + c)) = iteratedDeriv n f := funext ih
    change deriv (iteratedDeriv n f) (t + c) = deriv (iteratedDeriv n f) t
    rw [← deriv_comp_add_const (iteratedDeriv n f) c t, he]

theorem mixedDerivative_angular_periodic {g : PolarPoint → ℝ} {c : ℝ}
    (hg : ∀ x : ℝ, Function.Periodic (fun θ : ℝ => g (x, θ)) c)
    (a b : ℕ) (x : ℝ) : Function.Periodic (fun θ => mixedDerivative a b g (x, θ)) c := by
  intro θ
  have he : (fun r => iteratedDeriv b (fun t => g (r, t)) (θ + c)) =
      fun r => iteratedDeriv b (fun t => g (r, t)) θ :=
    funext (fun r => iteratedDeriv_preserves_periodic (hg r) b θ)
  change iteratedDeriv a (fun r => iteratedDeriv b (fun t => g (r, t)) (θ + c)) x =
    iteratedDeriv a (fun r => iteratedDeriv b (fun t => g (r, t)) θ) x
  rw [he]

theorem materialPullback_angular_periodic {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : Function.Periodic f (0, Real.pi)) (x : ℝ) :
    Function.Periodic (fun θ => materialPullback T γ f (x, θ)) Real.pi := by
  intro θ
  have he := hf (T.radius x, θ)
  change f (T.radius x + 0, θ + Real.pi) = f (T.radius x, θ) at he
  rw [add_zero] at he
  change T.H (T.radius x) ^ (-γ) * f (T.radius x, θ + Real.pi) =
    T.H (T.radius x) ^ (-γ) * f (T.radius x, θ)
  rw [he]

theorem cylinderWindowMeasure_eq_materialCylinderRestrict (x : ℝ) :
    cylinderWindowMeasure x = materialCylinderMeasure.restrict (Ioc x (x + 1) ×ˢ (univ : Set ℝ)) :=
  cylinderWindowMeasure_eq_restrict_strip x

theorem cylinderWindowL2Norm_le_materialCylinder {g : PolarPoint → ℝ}
    (hg : MemLp g 2 materialCylinderMeasure) (x : ℝ) :
    cylinderWindowL2Norm x g ≤ (eLpNorm g 2 materialCylinderMeasure).toReal := by
  unfold cylinderWindowL2Norm
  rw [cylinderWindowMeasure_eq_materialCylinderRestrict]
  exact ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_measure g Measure.restrict_le_self)

/-- The uniform bound on a periodic cylinder from its four actual global norms. -/
theorem abs_le_materialCylinder_L2 {g : PolarPoint → ℝ} (hg : ContDiff ℝ ∞ g)
    (hperiodic : ∀ x : ℝ, Function.Periodic (fun θ => g (x, θ)) Real.pi)
    (h0 : MemLp g 2 materialCylinderMeasure)
    (h1 : MemLp (radialPartial g) 2 materialCylinderMeasure)
    (h2 : MemLp (angularPartial g) 2 materialCylinderMeasure)
    (h3 : MemLp (radialPartial (angularPartial g)) 2 materialCylinderMeasure) (x θ : ℝ) :
    |g (x, θ)| ≤ Real.sqrt Real.pi *
      ((eLpNorm g 2 materialCylinderMeasure).toReal +
        (eLpNorm (radialPartial g) 2 materialCylinderMeasure).toReal +
        (eLpNorm (angularPartial g) 2 materialCylinderMeasure).toReal +
        (eLpNorm (radialPartial (angularPartial g)) 2 materialCylinderMeasure).toReal) := by
  obtain ⟨t, ht, he⟩ := (hperiodic x).exists_mem_Ico₀ Real.pi_pos θ
  change g (x, θ) = g (x, t) at he
  rw [he]
  exact (abs_le_cylinderWindow_L2 hg x t ⟨ht.1, ht.2.le⟩).trans
    (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (add_le_add
        (cylinderWindowL2Norm_le_materialCylinder h0 x)
        (cylinderWindowL2Norm_le_materialCylinder h1 x))
        (cylinderWindowL2Norm_le_materialCylinder h2 x))
        (cylinderWindowL2Norm_le_materialCylinder h3 x)) (Real.sqrt_nonneg _))

theorem heightMember_materialPullback_mixedDerivative_memLp
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hf : HeightMember D T γ f) (a b : ℕ) :
    MemLp (mixedDerivative a b (materialPullback T γ f)) 2 materialCylinderMeasure := by
  have he : weightedPhysicalJet T γ a b 0 f = mixedDerivative a b (materialPullback T γ f) := by
    funext p
    simp only [weightedPhysicalJet, pow_zero, one_mul]
  rw [← he]
  exact hf.2.2.2.2 a b 0

/-- Every mixed material derivative of an actual height member is uniformly
bounded on the entire cylinder. -/
theorem heightMember_materialPullback_mixedDerivative_uniform_bound
    {D : ReferenceData} {T : MaterialData} {γ : ℝ} {f : PolarPoint → ℝ}
    (hT : IsMaterialData D T) (hf : HeightMember D T γ f) :
    ∀ a b : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ p : PolarPoint,
      |mixedDerivative a b (materialPullback T γ f) p| ≤ K := by
  intro a b
  let F := materialPullback T γ f
  let g := mixedDerivative a b F
  have hF : ContDiff ℝ ∞ F := contDiff_materialPullback hT hf.1
  have hg : ContDiff ℝ ∞ g := contDiff_mixedDerivative hF a b
  have hperiodic : ∀ x : ℝ, Function.Periodic (fun θ => g (x, θ)) Real.pi :=
    mixedDerivative_angular_periodic (g := F)
      (materialPullback_angular_periodic (T := T) (γ := γ) hf.2.2.1) a b
  have hx : radialPartial g = mixedDerivative (a + 1) b F := radialPartial_mixedDerivative hF a b
  have ht : angularPartial g = mixedDerivative a (b + 1) F := angularPartial_mixedDerivative hF a b
  have hxt : radialPartial (angularPartial g) = mixedDerivative (a + 1) (b + 1) F := by
    rw [ht, radialPartial_mixedDerivative hF a (b + 1)]
  have hm0 : MemLp g 2 materialCylinderMeasure :=
    heightMember_materialPullback_mixedDerivative_memLp hf a b
  have hm1 : MemLp (radialPartial g) 2 materialCylinderMeasure := by
    rw [hx]
    exact heightMember_materialPullback_mixedDerivative_memLp hf (a + 1) b
  have hm2 : MemLp (angularPartial g) 2 materialCylinderMeasure := by
    rw [ht]
    exact heightMember_materialPullback_mixedDerivative_memLp hf a (b + 1)
  have hm3 : MemLp (radialPartial (angularPartial g)) 2 materialCylinderMeasure := by
    rw [hxt]
    exact heightMember_materialPullback_mixedDerivative_memLp hf (a + 1) (b + 1)
  let K := Real.sqrt Real.pi *
    ((eLpNorm g 2 materialCylinderMeasure).toReal +
      (eLpNorm (radialPartial g) 2 materialCylinderMeasure).toReal +
      (eLpNorm (angularPartial g) 2 materialCylinderMeasure).toReal +
      (eLpNorm (radialPartial (angularPartial g)) 2 materialCylinderMeasure).toReal)
  refine ⟨K, ?_, ?_⟩
  · unfold K
    exact mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (add_nonneg (add_nonneg
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
  · rintro ⟨x, θ⟩
    exact abs_le_materialCylinder_L2 hg hperiodic hm0 hm1 hm2 hm3 x θ

end ContinuousFlexibility.Statements
