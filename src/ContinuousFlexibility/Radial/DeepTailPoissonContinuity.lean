import ContinuousFlexibility.Radial.DeepTailPhysicalPoisson
import ContinuousFlexibility.Radial.TailPhysicalGreenContraction

/-!
# Continuous actual Poisson functions and their flux matrices

The physical integral equation identifies every Poisson bundle with the
unique fixed point on one fixed space of continuous edge functions.
The endpoint flux coefficients are then continuous scalar mass pairings.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory
open scoped NNReal

namespace TailPhysicalPoissonData

variable {p : ℝ → ℝ} {a b Λ η : ℝ} {hab : a ≤ b}

/-- Restrict an actual Poisson function to the fixed physical edge. -/
def onEdge (B : TailPhysicalPoissonData p a b Λ η hab) (right : Bool) : C(Icc a b, ℝ) :=
  ⟨fun x => B.u right x, (B.differentiable right).continuous.comp continuous_subtype_val⟩

theorem onEdge_apply (B : TailPhysicalPoissonData p a b Λ η hab)
    (right : Bool) (x : Icc a b) : B.onEdge right x = B.u right x := rfl

/-- The positive off-diagonal coefficient of the outward flux matrix. -/
def offDiagonal (B : TailPhysicalPoissonData p a b Λ η hab) : ℝ :=
  (tailResistanceChart (tailClampedDensity p a b hab) a b)⁻¹ +
    Λ * ∫ t in a..b, p t * tailPhysicalHeight p a b hab false t * B.u true t

def leftDiagonal (B : TailPhysicalPoissonData p a b Λ η hab) : ℝ :=
  (tailResistanceChart (tailClampedDensity p a b hab) a b)⁻¹ -
    Λ * ∫ t in a..b, p t * tailPhysicalHeight p a b hab false t * B.u false t

def rightDiagonal (B : TailPhysicalPoissonData p a b Λ η hab) : ℝ :=
  (tailResistanceChart (tailClampedDensity p a b hab) a b)⁻¹ -
    Λ * ∫ t in a..b, p t * tailPhysicalHeight p a b hab true t * B.u true t

theorem left_flux_false (B : TailPhysicalPoissonData p a b Λ η hab) :
    p a * deriv (B.u false) a = -B.leftDiagonal := by
  rw [B.left_flux]
  simp only [Bool.false_eq_true, ite_false, neg_div, one_div, leftDiagonal]
  ring

theorem left_flux_true (B : TailPhysicalPoissonData p a b Λ η hab) :
    p a * deriv (B.u true) a = B.offDiagonal := by
  simpa only [ite_true, one_div, offDiagonal] using B.left_flux true

theorem right_flux_true (B : TailPhysicalPoissonData p a b Λ η hab) :
    p b * deriv (B.u true) b = B.rightDiagonal := by
  simpa only [ite_true, one_div, rightDiagonal] using B.right_flux true

/-- Symmetry of the exact flux matrix follows from the weighted
Wronskian, including when the density is only regular on the closed edge. -/
theorem right_flux_false (B : TailPhysicalPoissonData p a b Λ η hab)
    (hlt : a < b) (hp : ContinuousOn p (Icc a b)) :
    p b * deriv (B.u false) b = -B.offDiagonal := by
  let W : ℝ → ℝ := fun x =>
    (p x * deriv (B.u false) x) * B.u true x -
      (p x * deriv (B.u true) x) * B.u false x
  have hW : ContinuousOn W (Icc a b) :=
    ((hp.mul (B.derivative_continuous false).continuousOn).mul
      (B.differentiable true).continuous.continuousOn).sub
      ((hp.mul (B.derivative_continuous true).continuousOn).mul
        (B.differentiable false).continuous.continuousOn)
  have hWD (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt W 0 x := by
    have hh := ((B.equation false x hx).mul ((B.differentiable true x).hasDerivAt)).sub
      ((B.equation true x hx).mul ((B.differentiable false x).hasDerivAt))
    convert hh using 1
    · funext y
      simp only [W, Pi.sub_apply]
    · ring
  obtain ⟨x, hx, hquot⟩ := exists_deriv_eq_slope W hlt hW
    (fun x hx => (hWD x hx).differentiableAt.differentiableWithinAt)
  rw [(hWD x hx).deriv] at hquot
  have hWeq : W b = W a := by
    have hh := (eq_div_iff (sub_pos.mpr hlt).ne').mp hquot
    linarith only [hh]
  have hflux : p b * deriv (B.u false) b = -(p a * deriv (B.u true) a) := by
    simpa [W, B.left_endpoint, B.right_endpoint] using hWeq
  rw [hflux, B.left_flux_true]

end TailPhysicalPoissonData

section Families

variable {P : Type*} [TopologicalSpace P] {a b : ℝ}
  (p : P → ℝ → ℝ) (hab : a < b) (Λ η : P → ℝ)
  (hp : Continuous (fun z : P × Icc a b => p z.1 z.2))
  (hpos : ∀ σ x, x ∈ Icc a b → 0 < p σ x)
  (hΛcont : Continuous Λ) (hΛ : ∀ σ, 0 ≤ Λ σ)
  (B : ∀ σ, TailPhysicalPoissonData (p σ) a b (Λ σ) (η σ) hab.le)

include hp hpos hΛcont hΛ

/-- The actual Poisson functions depend continuously on the parameter
in the supremum norm on the original physical edge. -/
theorem continuous_tailPhysicalPoissonOn (K : ℝ≥0) (hK : K < 1)
    (hsmall : ∀ σ, (∫ t in a..b,
      tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) t t) ≤ K)
    (right : Bool) : Continuous (fun σ => (B σ).onEdge right) := by
  let κ := fun σ x t => tailPhysicalGreenWeight (p σ) a b hab.le (Λ σ) x t
  have hκ := continuous_tailPhysicalGreenWeight_family p hab hp hpos hΛcont
  let base := tailPhysicalHeightFamily p hab hp hpos right
  apply continuous_tailPhysicalIntegralSolution hab.le κ hκ K base _
    (continuous_tailPhysicalHeightFamily p hab hp hpos right)
  · intro σ
    exact tailPhysicalGreenStep_contracting p hab Λ hp hpos hΛcont hΛ K hK hsmall σ (base σ)
  · intro σ
    ext x
    change (B σ).u right x = tailPhysicalHeight (p σ) a b hab.le right x +
      tailContinuousKernelAction hab.le κ hκ σ ((B σ).onEdge right) x
    rw [(B σ).integral right x x.property, tailContinuousKernelAction_apply]
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    intro t ht
    rw [IccExtend_of_mem hab.le ((B σ).onEdge right) ht,
      TailPhysicalPoissonData.onEdge_apply]
    rfl

/-- Original-coordinate mass pairings for the Poisson functions are
continuous once the physical-edge restrictions are continuous. -/
theorem continuous_tailPhysicalPoissonPairing
    (hB : ∀ right, Continuous (fun σ => (B σ).onEdge right)) (left right : Bool) :
    Continuous (fun σ => ∫ t in a..b,
      p σ t * tailPhysicalHeight (p σ) a b hab.le left t * (B σ).u right t) := by
  have hh := continuous_tailPhysicalMassPairing p hab.le hp
    (tailPhysicalHeightFamily p hab hp hpos left) (fun σ => (B σ).onEdge right)
    (continuous_tailPhysicalHeightFamily p hab hp hpos left) (hB right)
  apply hh.congr
  intro σ
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab.le]
  intro t ht
  rw [tailClampedDensity_eq_of_mem hab.le ht,
    IccExtend_of_mem hab.le (tailPhysicalHeightFamily p hab hp hpos left σ) ht,
    IccExtend_of_mem hab.le ((B σ).onEdge right) ht,
    tailPhysicalHeightFamily_apply, TailPhysicalPoissonData.onEdge_apply]

/-- All three coefficients of the actual edge flux matrix vary
continuously; the dependence of the resistance length is included. -/
theorem continuous_tailPhysicalPoissonCoefficients
    (hB : ∀ right, Continuous (fun σ => (B σ).onEdge right)) :
    Continuous (fun σ => (B σ).offDiagonal) ∧
      Continuous (fun σ => (B σ).leftDiagonal) ∧
      Continuous (fun σ => (B σ).rightDiagonal) := by
  have hL : Continuous (fun σ => tailResistanceChart
      (tailClampedDensity (p σ) a b hab.le) a b) :=
    (continuous_tailClampedResistance_family p hab.le hp hpos).comp
      (continuous_id.prodMk continuous_const)
  have hLne (σ : P) : tailResistanceChart (tailClampedDensity (p σ) a b hab.le) a b ≠ 0 := by
    apply (tailClampedResistanceLength_pos hab _ (hpos σ)).ne'
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hp.comp (continuous_const.prodMk continuous_id)
  have hi := hL.inv₀ hLne
  have hm (left right : Bool) :=
    continuous_tailPhysicalPoissonPairing p hab Λ η hp hpos hΛcont hΛ B hB left right
  exact ⟨hi.add (hΛcont.mul (hm false true)),
    hi.sub (hΛcont.mul (hm false false)), hi.sub (hΛcont.mul (hm true true))⟩

end Families

end ContinuousFlexibility.Radial
