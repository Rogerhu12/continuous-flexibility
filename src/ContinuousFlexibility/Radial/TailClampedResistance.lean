import ContinuousFlexibility.Radial.TailSmoothResistanceStep
import ContinuousFlexibility.Statements.DeepTailOperator
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.IntermediateValue

/-!
# Resistance coordinates for a density defined on a closed tail edge

The original density is only smooth on the open tail. On each compact edge,
its constant extension at the two endpoints is globally continuous and positive.
This extension supplies the hypotheses of `TailResistanceTransport`, while its
mass integrals, resistance integrals and interior differential equation remain
those of the original density.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

theorem tailClampedDensity_apply (p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (x : ℝ) :
    tailClampedDensity p a b hab x = p (max a (min b x)) :=
  IccExtend_apply hab (fun y : Icc a b => p y) x

theorem tailClampedDensity_eq_of_mem {p : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) : tailClampedDensity p a b hab x = p x :=
  IccExtend_of_mem hab (fun y : Icc a b => p y) hx

theorem tailClampedDensity_continuous {p : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b)) :
    Continuous (tailClampedDensity p a b hab) :=
  hp.domRestrict.Icc_extend'

theorem tailClampedDensity_pos {p : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (x : ℝ) :
    0 < tailClampedDensity p a b hab x := by
  rw [tailClampedDensity_apply]
  exact hpos _ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

/-- The clamped extension has exactly the original mass on every subinterval. -/
theorem tailClampedDensity_integral {p : ℝ → ℝ} {a b l r : ℝ}
    (hab : a ≤ b) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    (∫ x in l..r, tailClampedDensity p a b hab x) = ∫ x in l..r, p x := by
  apply intervalIntegral.integral_congr
  intro x hx
  exact tailClampedDensity_eq_of_mem hab (uIcc_subset_Icc hl hr hx)

/-- The clamped extension has exactly the original resistance on every subinterval. -/
theorem tailClampedDensity_inv_integral {p : ℝ → ℝ} {a b l r : ℝ}
    (hab : a ≤ b) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    (∫ x in l..r, (tailClampedDensity p a b hab x)⁻¹) =
      ∫ x in l..r, (p x)⁻¹ := by
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [tailClampedDensity_eq_of_mem (p := p) hab (uIcc_subset_Icc hl hr hx)]

/-- The tail hypotheses supply the global transport assumptions on every compact edge. -/
theorem tailClampedDensity_of_deepTail {T : Statements.DeepTailData}
    (hT : Statements.DeepTailHypotheses T) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Ico T.entrance T.endpoint) :
    Continuous (tailClampedDensity T.p a b hab) ∧
      ∀ x, 0 < tailClampedDensity T.p a b hab x := by
  rcases hT with ⟨_, _, _, _, _, _, _, hp, hpos, _, _⟩
  exact ⟨tailClampedDensity_continuous hab (hp.continuousOn.mono hsub),
    tailClampedDensity_pos hab (fun x hx => hpos x (hsub hx))⟩

theorem hasDerivAt_tailClampedResistanceChart {p : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ y ∈ Icc a b, 0 < p y) (hx : x ∈ Icc a b) :
    HasDerivAt (tailResistanceChart (tailClampedDensity p a b hab) a) (p x)⁻¹ x := by
  simpa only [tailClampedDensity_eq_of_mem hab hx] using
    hasDerivAt_tailResistanceChart (tailClampedDensity_continuous hab hp)
      (tailClampedDensity_pos hab hpos) a x

theorem tailClampedResistanceChart_eq {p : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hx : x ∈ Icc a b) :
    tailResistanceChart (tailClampedDensity p a b hab) a x = ∫ y in a..x, (p y)⁻¹ :=
  tailClampedDensity_inv_integral hab ⟨le_rfl, hab⟩ hx

/-- Differences of resistance coordinates are the actual resistances of subedges. -/
theorem tailClampedResistanceChart_sub {p : ℝ → ℝ} {a b l r : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    tailResistanceChart (tailClampedDensity p a b hab) a r -
        tailResistanceChart (tailClampedDensity p a b hab) a l =
      ∫ x in l..r, (p x)⁻¹ := by
  have hi : Continuous (fun x => (tailClampedDensity p a b hab x)⁻¹) :=
    (tailClampedDensity_continuous hab hp).inv₀
      (fun x => (tailClampedDensity_pos hab hpos x).ne')
  exact (intervalIntegral.integral_interval_sub_left
    (hi.intervalIntegrable a r) (hi.intervalIntegrable a l)).trans
      (tailClampedDensity_inv_integral hab hl hr)

/-- Integration in resistance coordinates retains the original physical density. -/
theorem tailClampedResistance_mass_change {p V : ℝ → ℝ} {a b l r : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (hV : Continuous V)
    (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) :
    (∫ s in tailResistanceChart (tailClampedDensity p a b hab) a l..
        tailResistanceChart (tailClampedDensity p a b hab) a r,
      tailResistanceDensity (tailClampedDensity p a b hab) a s * V s) =
      ∫ x in l..r, p x * V (tailResistanceChart (tailClampedDensity p a b hab) a x) := by
  rw [tailResistance_mass_change (tailClampedDensity_continuous hab hp)
    (tailClampedDensity_pos hab hpos) hV]
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [tailClampedDensity_eq_of_mem (p := p) hab (uIcc_subset_Icc hl hr hx)]

theorem tailClampedResistanceDensity_chart {p : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ y ∈ Icc a b, 0 < p y) (hx : x ∈ Icc a b) :
    tailResistanceDensity (tailClampedDensity p a b hab) a
      (tailResistanceChart (tailClampedDensity p a b hab) a x) = p x ^ 2 := by
  dsimp only [tailResistanceDensity]
  rw [tailResistanceInverse_chart (tailClampedDensity_continuous hab hp)
    (tailClampedDensity_pos hab hpos), tailClampedDensity_eq_of_mem hab hx]

theorem tailClampedResistanceDensity_pos {p : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hpos : ∀ x ∈ Icc a b, 0 < p x) (s : ℝ) :
    0 < tailResistanceDensity (tailClampedDensity p a b hab) a s :=
  pow_pos (tailClampedDensity_pos hab hpos _) 2

theorem tailClampedResistanceDensity_continuousOn {p : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < p x) :
    ContinuousOn (tailResistanceDensity (tailClampedDensity p a b hab) a)
      (Icc (tailResistanceChart (tailClampedDensity p a b hab) a a)
        (tailResistanceChart (tailClampedDensity p a b hab) a b)) := by
  have hc := tailClampedDensity_continuous hab hp
  have hq := tailClampedDensity_pos hab hpos
  have hs : Continuous (tailResistanceChart (tailClampedDensity p a b hab) a) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_tailResistanceChart hc hq a x).continuousAt
  have hsub :
      Icc (tailResistanceChart (tailClampedDensity p a b hab) a a)
        (tailResistanceChart (tailClampedDensity p a b hab) a b) ⊆
        range (tailResistanceChart (tailClampedDensity p a b hab) a) := by
    rw [← hs.image_Icc_of_strictMono (tailResistanceChart_strictMono hc hq a)]
    exact image_subset_range _ _
  exact ((hc.comp_continuousOn (tailResistanceInverse_continuousOn hc hq a)).pow 2).mono hsub

/-- The flux at every point of the closed edge is the original physical flux. -/
theorem tailClampedResistance_flux {p V : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ y ∈ Icc a b, 0 < p y) (hV : Differentiable ℝ V) (hx : x ∈ Icc a b) :
    p x * deriv (V ∘ tailResistanceChart (tailClampedDensity p a b hab) a) x =
      deriv V (tailResistanceChart (tailClampedDensity p a b hab) a x) := by
  have h := congrFun (tailResistance_flux (tailClampedDensity_continuous hab hp)
    (tailClampedDensity_pos hab hpos) hV a) x
  simpa only [Function.comp_apply, tailClampedDensity_eq_of_mem hab hx] using h

/-- The transported equation is the actual radial equation in the interior of the edge. -/
theorem tailClampedResistance_equation {p V f : ℝ → ℝ} {a b x : ℝ}
    (hab : a ≤ b) (hp : ContinuousOn p (Icc a b))
    (hpos : ∀ y ∈ Icc a b, 0 < p y) (hV : Differentiable ℝ V) (Λ : ℝ)
    (hx : x ∈ Ioo a b)
    (hV₂ : DifferentiableAt ℝ (deriv V)
      (tailResistanceChart (tailClampedDensity p a b hab) a x)) :
    -deriv (fun y => p y * deriv
        (V ∘ tailResistanceChart (tailClampedDensity p a b hab) a) y) x / p x -
        Λ * (V ∘ tailResistanceChart (tailClampedDensity p a b hab) a) x = f x ↔
      -deriv (deriv V) (tailResistanceChart (tailClampedDensity p a b hab) a x) -
        Λ * tailResistanceDensity (tailClampedDensity p a b hab) a
          (tailResistanceChart (tailClampedDensity p a b hab) a x) *
          V (tailResistanceChart (tailClampedDensity p a b hab) a x) =
        tailResistanceDensity (tailClampedDensity p a b hab) a
          (tailResistanceChart (tailClampedDensity p a b hab) a x) * f x := by
  have heq : EqOn
      (fun y => p y * deriv (V ∘ tailResistanceChart (tailClampedDensity p a b hab) a) y)
      (fun y => tailClampedDensity p a b hab y *
        deriv (V ∘ tailResistanceChart (tailClampedDensity p a b hab) a) y) (Ioo a b) := by
    intro y hy
    dsimp only
    rw [tailClampedDensity_eq_of_mem (p := p) hab ⟨hy.1.le, hy.2.le⟩]
  rw [heq.deriv isOpen_Ioo hx,
    ← tailClampedDensity_eq_of_mem (p := p) hab ⟨hx.1.le, hx.2.le⟩]
  exact tailResistance_equation (tailClampedDensity_continuous hab hp)
    (tailClampedDensity_pos hab hpos) hV a Λ x hV₂

end ContinuousFlexibility.Radial
