module

public import ContinuousFlexibility.Analysis.N07bDirectionChain
public import ContinuousFlexibility.Analysis.N07bFiniteRadialGreen

/-!
# The actual reference differential expression under a coordinate change

The two reference coordinate derivatives become two explicitly computed
vector fields on the current physical piece. The identities use genuine
inverse relations and actual derivatives of the transition. In particular,
the second-order reference expression is a sum of words of lengths one
and two, to which the source-independent material expansion applies.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology

/-- A reference coordinate direction, expressed at a current physical
point through the actual transition and its actual inverse. -/
def n07bReferenceDirection (τ Θ : PolarPoint → PolarPoint)
    (e x : PolarPoint) : PolarPoint :=
  fderiv ℝ τ (Θ x) e

theorem n07bReferenceDirection_contDiffOn
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {τ Θ : PolarPoint → PolarPoint}
    (hτ : ContDiffOn ℝ ∞ τ V) (hΘ : ContDiffOn ℝ ∞ Θ U)
    (hmap : MapsTo Θ U V) (e : PolarPoint) :
    ContDiffOn ℝ ∞ (n07bReferenceDirection τ Θ e) U := by
  intro x hx
  have ht : ContDiffAt ℝ ∞ τ (Θ x) :=
    (hτ (Θ x) (hmap hx)).contDiffAt (hV.mem_nhds (hmap hx))
  have ht' : ContDiffAt ℝ ∞ (fun y => fderiv ℝ τ y e) (Θ x) :=
    (ht.fderiv_right (by simp)).clm_apply (contDiffAt_const (c := e))
  exact (ht'.comp x ((hΘ x hx).contDiffAt (hU.mem_nhds hx))).contDiffWithinAt

/-- First-order coordinate transport, derived from the ordinary chain
rule and the actual inverse identity at this point. -/
theorem n07b_referenceDirection_comp
    {τ Θ : PolarPoint → PolarPoint} {f : PolarPoint → ℝ} {y : PolarPoint}
    (hτ : DifferentiableAt ℝ τ y) (hf : DifferentiableAt ℝ f (τ y))
    (hinv : Θ (τ y) = y) (e : PolarPoint) :
    n07bDirectionalDerivative (fun _ => e) (f ∘ τ) y =
      n07bDirectionalDerivative (n07bReferenceDirection τ Θ e) f (τ y) := by
  rw [n07bDirectionalDerivative_eq_fderiv, n07bDirectionalDerivative_eq_fderiv,
    fderiv_comp y hf hτ, ContinuousLinearMap.comp_apply]
  change fderiv ℝ f (τ y) (fderiv ℝ τ y e) =
    fderiv ℝ f (τ y) (fderiv ℝ τ (Θ (τ y)) e)
  rw [hinv]

/-- Every word in one reference direction is the corresponding actual
word in the transported geometric field. Equality is on the whole open
piece before the next derivative is taken. -/
theorem n07b_referenceDirection_iterate
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {τ Θ : PolarPoint → PolarPoint}
    (hτ : ContDiffOn ℝ ∞ τ V) (hΘ : ContDiffOn ℝ ∞ Θ U)
    (hτmap : MapsTo τ V U) (hΘmap : MapsTo Θ U V)
    (hinv : ∀ y ∈ V, Θ (τ y) = y)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (e : PolarPoint) (j : ℕ) {y : PolarPoint} (hy : y ∈ V) :
    n07bDirectionIterate (fun _ _ => e) (f ∘ τ) j y =
      n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ e) f j (τ y) := by
  have hX : ContDiffOn ℝ ∞ (n07bReferenceDirection τ Θ e) U :=
    n07bReferenceDirection_contDiffOn hU hV hτ hΘ hΘmap e
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
      have heq : n07bDirectionIterate (fun _ _ => e) (f ∘ τ) j =ᶠ[𝓝 y]
          (n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ e) f j ∘ τ) := by
        filter_upwards [hV.mem_nhds hy] with y' hy'
        exact ih hy'
      have hdf : DifferentiableAt ℝ
          (n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ e) f j) (τ y) :=
        (n07bDirectionIterate_contDiffAt
          (fun _ => (hX (τ y) (hτmap hy)).contDiffAt (hU.mem_nhds (hτmap hy)))
          ((hf (τ y) (hτmap hy)).contDiffAt (hU.mem_nhds (hτmap hy))) j).differentiableAt
            (by simp)
      exact (n07bDirectionalDerivative_congr (fun _ => e) heq).trans
        (n07b_referenceDirection_comp
          (((hτ y hy).contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp))
          hdf (hinv y hy) e)

theorem n07bDirectionIterate_radial_one (f : PolarPoint → ℝ) (x : PolarPoint) :
    n07bDirectionIterate (fun _ _ => (1, 0)) f 1 x = radialPartial f x := by
  simp [n07bDirectionIterate, n07bDirectionalDerivative]

theorem n07bDirectionIterate_radial_two (f : PolarPoint → ℝ) (x : PolarPoint) :
    n07bDirectionIterate (fun _ _ => (1, 0)) f 2 x =
      radialPartial (radialPartial f) x := by
  have hfirst : n07bDirectionIterate (fun _ _ => (1, 0)) f 1 =
      radialPartial f := funext (n07bDirectionIterate_radial_one f)
  change n07bDirectionalDerivative (fun _ => (1, 0))
    (n07bDirectionIterate (fun _ _ => (1, 0)) f 1) x = _
  rw [hfirst]
  simp only [n07bDirectionalDerivative, one_mul, zero_mul, add_zero]

theorem n07bDirectionIterate_angular_two (f : PolarPoint → ℝ) (x : PolarPoint) :
    n07bDirectionIterate (fun _ _ => (0, 1)) f 2 x =
      angularPartial (angularPartial f) x := by
  have hfirst : n07bDirectionIterate (fun _ _ => (0, 1)) f 1 =
      angularPartial f := by
    funext y
    simp only [n07bDirectionIterate, n07bDirectionalDerivative,
      zero_mul, one_mul, zero_add]
  change n07bDirectionalDerivative (fun _ => (0, 1))
    (n07bDirectionIterate (fun _ _ => (0, 1)) f 1) x = _
  rw [hfirst]
  simp only [n07bDirectionalDerivative, zero_mul, one_mul, zero_add]

/-- The exact reference radial expression at the corresponding reference
point. This uses actual coefficient values and actual transported
directions, not an assumed second-derivative transformation formula. -/
theorem n07b_referencePDE_pullback
    {U V : Set PolarPoint} (hU : IsOpen U) (hV : IsOpen V)
    {τ Θ : PolarPoint → PolarPoint}
    (hτ : ContDiffOn ℝ ∞ τ V) (hΘ : ContDiffOn ℝ ∞ Θ U)
    (hτmap : MapsTo τ V U) (hΘmap : MapsTo Θ U V)
    (hinv : ∀ y ∈ V, Θ (τ y) = y) (hleft : ∀ x ∈ U, τ (Θ x) = x)
    {f : PolarPoint → ℝ} (hf : ContDiffOn ℝ ∞ f U)
    {w : ℝ → ℝ} {x : PolarPoint} (hx : x ∈ U)
    (hw : DifferentiableAt ℝ w (Θ x).1) :
    radialPDE w (fun r θ => (f ∘ τ) (r, θ)) (Θ x).1 (Θ x).2 =
      deriv w (Θ x).1 *
        n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (1, 0)) f 1 x +
      w (Θ x).1 *
        n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (1, 0)) f 2 x +
      deriv w (Θ x).1 / (Θ x).1 *
        n07bDirectionIterate (fun _ => n07bReferenceDirection τ Θ (0, 1)) f 2 x := by
  have hy : Θ x ∈ V := hΘmap hx
  have hg : ContDiffAt ℝ 2 (f ∘ τ) (Θ x) :=
    (((hf.comp hτ hτmap) (Θ x) hy).contDiffAt (hV.mem_nhds hy)).of_le (by simp)
  have hr₁ := n07b_referenceDirection_iterate hU hV hτ hΘ hτmap hΘmap
    hinv hf (1, 0) 1 hy
  have hr₂ := n07b_referenceDirection_iterate hU hV hτ hΘ hτmap hΘmap
    hinv hf (1, 0) 2 hy
  have hθ₂ := n07b_referenceDirection_iterate hU hV hτ hΘ hτmap hΘmap
    hinv hf (0, 1) 2 hy
  rw [n07bDirectionIterate_radial_one, hleft x hx] at hr₁
  rw [n07bDirectionIterate_radial_two, hleft x hx] at hr₂
  rw [n07bDirectionIterate_angular_two, hleft x hx] at hθ₂
  rw [n07b_c2_radialPDE_eq_polar_jets hw hg, hr₁, hr₂, hθ₂]

end ContinuousFlexibility.Analysis
