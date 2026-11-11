import ContinuousFlexibility.Radial.TailClampedResistance
import ContinuousFlexibility.Radial.TailParameterFixedPoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Parameter continuity on a fixed physical edge

The resistance length varies with the density.  Keeping the physical
edge fixed avoids a parameter-dependent inverse coordinate: the Green
kernel is evaluated at the actual resistance integrals of its two
arguments.  Joint continuity then passes to the integral operator in the
supremum norm on the fixed physical interval.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory

section DensityFamily

variable {P : Type*} [TopologicalSpace P] {a b : ℝ}
  (p : P → ℝ → ℝ) (hab : a ≤ b)

/-- Jointly continuous densities on a closed edge have jointly continuous
constant extensions, with no assumptions outside that edge. -/
theorem continuous_tailClampedDensity_family
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2)) :
    Continuous (fun z : P × ℝ => tailClampedDensity (p z.1) a b hab z.2) := by
  exact hp.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))

/-- The forward resistance chart is jointly continuous in the density
parameter and the physical coordinate. -/
theorem continuous_tailClampedResistance_family
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
    (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x) :
    Continuous (fun z : P × ℝ =>
      tailResistanceChart (tailClampedDensity (p z.1) a b hab) a z.2) := by
  have hi : Continuous (fun z : P × ℝ =>
      (tailClampedDensity (p z.1) a b hab z.2)⁻¹) :=
    (continuous_tailClampedDensity_family p hab hp).inv₀
      (fun z => (tailClampedDensity_pos hab (hpos z.1) z.2).ne')
  exact intervalIntegral.continuous_parametric_primitive_of_continuous hi

end DensityFamily

/-- The unperturbed resistance Green kernel, expressed on the physical
edge.  Both occurrences of the coordinate are forward integrals. -/
def tailPhysicalGreenKernel (p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (x t : ℝ) : ℝ :=
  let R := tailResistanceChart (tailClampedDensity p a b hab) a
  tailEdgeGreen 0 (R b) (R x) (R t)

theorem continuous_tailPhysicalGreenKernel_family {P : Type*} [TopologicalSpace P]
    {a b : ℝ} (p : P → ℝ → ℝ) (hab : a < b)
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
    (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x) :
    Continuous (fun z : (P × ℝ) × ℝ =>
      tailPhysicalGreenKernel (p z.1.1) a b hab.le z.1.2 z.2) := by
  let R (σ : P) := tailResistanceChart (tailClampedDensity (p σ) a b hab.le) a
  have hR : Continuous (fun z : P × ℝ => R z.1 z.2) :=
    continuous_tailClampedResistance_family p hab.le hp hpos
  have hL : Continuous (fun z : (P × ℝ) × ℝ => R z.1.1 b) :=
    hR.comp (continuous_fst.fst.prodMk continuous_const)
  have hx : Continuous (fun z : (P × ℝ) × ℝ => R z.1.1 z.1.2) :=
    hR.comp continuous_fst
  have ht : Continuous (fun z : (P × ℝ) × ℝ => R z.1.1 z.2) :=
    hR.comp (continuous_fst.fst.prodMk continuous_snd)
  have hLpos (σ : P) : 0 < R σ b := by
    have hpσ : ContinuousOn (p σ) (Icc a b) := by
      apply continuousOn_iff_continuous_restrict.mpr
      exact hp.comp (continuous_const.prodMk continuous_id)
    have hm := tailResistanceChart_strictMono
      (tailClampedDensity_continuous hab.le hpσ)
      (tailClampedDensity_pos hab.le (hpos σ)) a hab
    simpa only [tailResistanceChart, intervalIntegral.integral_same] using hm
  change Continuous (fun z : (P × ℝ) × ℝ =>
    (min (R z.1.1 z.1.2) (R z.1.1 z.2) - 0) *
      (R z.1.1 b - max (R z.1.1 z.1.2) (R z.1.1 z.2)) / (R z.1.1 b - 0))
  exact (((hx.min ht).sub continuous_const).mul (hL.sub (hx.max ht))).div
    (hL.sub continuous_const) (fun z => by simpa only [sub_zero] using (hLpos z.1.1).ne')

/-- The Green insertion kernel includes the actual physical mass density. -/
def tailPhysicalGreenWeight (p : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (Λ x t : ℝ) : ℝ :=
  tailPhysicalGreenKernel p a b hab x t * (Λ * tailClampedDensity p a b hab t)

theorem continuous_tailPhysicalGreenWeight_family {P : Type*} [TopologicalSpace P]
    {a b : ℝ} (p : P → ℝ → ℝ) (hab : a < b) (Λ : P → ℝ)
    (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
    (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x) (hΛ : Continuous Λ) :
    Continuous (fun z : (P × ℝ) × ℝ =>
      tailPhysicalGreenWeight (p z.1.1) a b hab.le (Λ z.1.1) z.1.2 z.2) := by
  exact (continuous_tailPhysicalGreenKernel_family p hab hp hpos).mul
    ((hΛ.comp continuous_fst.fst).mul
      ((continuous_tailClampedDensity_family p hab.le hp).comp
        (continuous_fst.fst.prodMk continuous_snd)))

section IntegralOperator

variable {P : Type*} [TopologicalSpace P] {a b : ℝ} (hab : a ≤ b)
  (κ : P → ℝ → ℝ → ℝ)
  (hκ : Continuous (fun z : (P × ℝ) × ℝ => κ z.1.1 z.1.2 z.2))

/-- Integrate a continuous physical-edge kernel against a continuous edge
function, extending that function constantly outside the edge. -/
def tailContinuousKernelAction (σ : P) (u : C(Icc a b, ℝ)) : C(Icc a b, ℝ) where
  toFun x := ∫ t in a..b, κ σ x t * IccExtend hab u t
  continuous_toFun := by
    have hk : Continuous (fun z : ℝ × ℝ => κ σ z.1 z.2) :=
      hκ.comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    have hi : Continuous (fun z : ℝ × ℝ => κ σ z.1 z.2 * IccExtend hab u z.2) :=
      hk.mul (u.continuous.Icc_extend'.comp continuous_snd)
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hi a b).comp continuous_subtype_val

theorem tailContinuousKernelAction_apply (σ : P) (u : C(Icc a b, ℝ)) (x : Icc a b) :
    tailContinuousKernelAction hab κ hκ σ u x =
      ∫ t in a..b, κ σ x t * IccExtend hab u t := rfl

/-- Joint continuity of the kernel gives continuity of the actual integral
operator in both the parameter and its input, for the supremum norm. -/
theorem continuous_tailContinuousKernelAction :
    Continuous (fun z : P × C(Icc a b, ℝ) => tailContinuousKernelAction hab κ hκ z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hk : Continuous (fun z : ((P × C(Icc a b, ℝ)) × Icc a b) × ℝ =>
      κ z.1.1.1 z.1.2 z.2) :=
    hκ.comp ((continuous_fst.fst.fst.prodMk
      (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd)
  have hu : Continuous (fun z : ((P × C(Icc a b, ℝ)) × Icc a b) × ℝ =>
      IccExtend hab z.1.1.2 z.2) :=
    ContinuousMap.continuous_eval.comp
      (continuous_fst.fst.snd.prodMk (continuous_projIcc.comp continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (hk.mul hu) a b

/-- A uniformly contracting Green equation with continuous boundary data
has a continuous solution on the fixed physical edge. -/
theorem continuous_tailPhysicalIntegralSolution (K : ℝ≥0)
    (base u : P → C(Icc a b, ℝ)) (hb : Continuous base)
    (hcontract : ∀ σ, ContractingWith K
      (fun v => base σ + tailContinuousKernelAction hab κ hκ σ v))
    (hu : ∀ σ, u σ = base σ + tailContinuousKernelAction hab κ hκ σ (u σ)) :
    Continuous u := by
  apply continuous_tailFixedPoint K _ u hcontract
  · intro v
    exact hb.add ((continuous_tailContinuousKernelAction hab κ hκ).comp
      (continuous_id.prodMk continuous_const))
  · intro σ
    exact (hu σ).symm

end IntegralOperator

end ContinuousFlexibility.Radial
