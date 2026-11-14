module

public import ContinuousFlexibility.Analysis.N06CubicMultipliers
public import ContinuousFlexibility.Scalar.WeightedDifferentiationSupport

/-!
# Local regularity and reflection signs of the five cubic multipliers

The divided diagonal coefficients are even and the mixed coefficient is
odd. Their actual first partials give the signs [even, odd, even, even,
odd] for the five graph multipliers. All differentiability is required
only inside the canonical strip, where the radial weight is positive.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- Local translation invariance passes to both actual partials. -/
theorem n06_coordinatePartials_periodicOn_strip
    {l r : ℝ} {f : PolarPoint → ℝ}
    (hperiod : ∀ p : PolarPoint, p.1 ∈ Ioo l r → f (p + (0, Real.pi)) = f p)
    (p : PolarPoint) (hp : p.1 ∈ Ioo l r) :
    radialPartial f (p + (0, Real.pi)) = radialPartial f p ∧
      angularPartial f (p + (0, Real.pi)) = angularPartial f p := by
  have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∈ Ioo l r :=
    continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hp)
  have he : (fun q : PolarPoint => f (q + (0, Real.pi))) =ᶠ[𝓝 p] f := by
    filter_upwards [hnear] with q hq
    exact hperiod q hq
  have hderiv : fderiv ℝ f (p + (0, Real.pi)) = fderiv ℝ f p := by
    rw [← fderiv_comp_add_right (0, Real.pi)]
    exact he.fderiv_eq
  exact ⟨congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) hderiv,
    congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) hderiv⟩

/-- A radial partial preserves the sign of angular reflection and an
angular partial reverses it. The equality is used only in the open strip. -/
theorem n06_coordinatePartials_reflectionOn_strip
    {l r σ : ℝ} {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioo l r ×ˢ (univ : Set ℝ)))
    (hpar : ∀ p : PolarPoint, p.1 ∈ Ioo l r → f (p.1, Real.pi - p.2) = σ * f p)
    (p : PolarPoint) (hp : p.1 ∈ Ioo l r) :
    radialPartial f (p.1, Real.pi - p.2) = σ * radialPartial f p ∧
      angularPartial f (p.1, Real.pi - p.2) = -σ * angularPartial f p := by
  rcases p with ⟨x, θ⟩
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hx : x ∈ Ioo l r := hp
  have hd (η : ℝ) : DifferentiableAt ℝ f (x, η) := by
    have hη : (x, η) ∈ Ioo l r ×ˢ (univ : Set ℝ) := ⟨hx, mem_univ η⟩
    exact (hf.contDiffAt (x := (x, η)) (hU.mem_nhds hη)).differentiableAt (by simp)
  constructor
  · have he : (fun s : ℝ => f (s, Real.pi - θ)) =ᶠ[𝓝 x]
        fun s => σ * f (s, θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hp] with s hs
      exact hpar (s, θ) hs
    calc
      radialPartial f (x, Real.pi - θ) = deriv (fun s => f (s, Real.pi - θ)) x :=
        (hasDerivAt_radial_slice (hd (Real.pi - θ))).deriv.symm
      _ = deriv (fun s => σ * f (s, θ)) x := he.deriv_eq
      _ = σ * radialPartial f (x, θ) :=
        ((hasDerivAt_radial_slice (hd θ)).const_mul σ).deriv
  · have hleft : HasDerivAt (fun η : ℝ => f (x, Real.pi - η))
        (-angularPartial f (x, Real.pi - θ)) θ := by
      simpa only [Function.comp_def, zero_sub, mul_neg_one] using
        (hasDerivAt_angular_slice (hd (Real.pi - θ))).comp θ
          ((hasDerivAt_const θ Real.pi).sub (hasDerivAt_id' θ))
    have hright : HasDerivAt (fun η : ℝ => σ * f (x, η))
        (σ * angularPartial f (x, θ)) θ :=
      (hasDerivAt_angular_slice (hd θ)).const_mul σ
    have he : (fun η : ℝ => f (x, Real.pi - η)) = fun η => σ * f (x, η) :=
      funext (fun η => hpar (x, η) hp)
    rw [he] at hleft
    have heq := hleft.unique hright
    linarith only [heq]

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set
open scoped ContDiff
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

def n06CubicGraphParity : Fin 5 → ℝ := ![1, -1, 1, 1, -1]

theorem n06CubicGraphParity_sq (i : Fin 5) : n06CubicGraphParity i ^ 2 = 1 := by
  fin_cases i <;> norm_num [n06CubicGraphParity]

/-- Square-root factors are smooth on the original open strip because
the radial graph weight is strictly positive there. -/
theorem n06CubicGraphMultipliers_contDiffOn_strip
    {l r : ℝ} {d e : ℝ → ℝ}
    (hd : ContDiffOn ℝ ∞ d (Ioo l r)) (he : ContDiffOn ℝ ∞ e (Ioo l r))
    (hdpos : ∀ x ∈ Ioo l r, 0 < d x)
    {A B C : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo l r ×ˢ (univ : Set ℝ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo l r ×ˢ (univ : Set ℝ)))
    (hC : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ (univ : Set ℝ))) (i : Fin 5) :
    ContDiffOn ℝ ∞ (n06CubicGraphMultipliers d e A B C i)
      (Ioo l r ×ˢ (univ : Set ℝ)) := by
  have hd' : ContDiffOn ℝ ∞ (fun p : PolarPoint => d p.1) (Ioo l r ×ˢ (univ : Set ℝ)) :=
    hd.comp contDiffOn_fst (fun _ hp => hp.1)
  have he' : ContDiffOn ℝ ∞ (fun p : PolarPoint => e p.1) (Ioo l r ×ˢ (univ : Set ℝ)) :=
    he.comp contDiffOn_fst (fun _ hp => hp.1)
  have hsqrt := hd'.sqrt (fun p hp => (hdpos p.1 hp.1).ne')
  have hU : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hAr := scalar_contDiffOn_radialPartial hU hA
  have hBt := scalar_contDiffOn_angularPartial hU hB
  have hBr := scalar_contDiffOn_radialPartial hU hB
  have hCt := scalar_contDiffOn_angularPartial hU hC
  fin_cases i <;> simp only [n06CubicGraphMultipliers, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq]
  · exact hd'.mul hA
  · exact (contDiffOn_const.mul hsqrt).mul hB
  · exact hC
  · exact hd'.mul ((((contDiffOn_const.mul he').mul hA).add (hd'.mul hAr)).add (hd'.mul hBt))
  · exact hsqrt.mul ((((contDiffOn_const.mul he').mul hB).add (hd'.mul hBr)).add (hd'.mul hCt))

theorem n06CubicGraphMultipliers_periodicOn_strip
    {l r : ℝ} (d e : ℝ → ℝ) {A B C : PolarPoint → ℝ}
    (hA : ∀ p : PolarPoint, p.1 ∈ Ioo l r → A (p + (0, Real.pi)) = A p)
    (hB : ∀ p : PolarPoint, p.1 ∈ Ioo l r → B (p + (0, Real.pi)) = B p)
    (hC : ∀ p : PolarPoint, p.1 ∈ Ioo l r → C (p + (0, Real.pi)) = C p)
    (i : Fin 5) (p : PolarPoint) (hp : p.1 ∈ Ioo l r) :
    n06CubicGraphMultipliers d e A B C i (p + (0, Real.pi)) =
      n06CubicGraphMultipliers d e A B C i p := by
  have hAr := (n06_coordinatePartials_periodicOn_strip hA p hp).1
  have hBt := (n06_coordinatePartials_periodicOn_strip hB p hp).2
  have hBr := (n06_coordinatePartials_periodicOn_strip hB p hp).1
  have hCt := (n06_coordinatePartials_periodicOn_strip hC p hp).2
  fin_cases i <;> simp only [n06CubicGraphMultipliers, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', id_eq,
    Prod.fst_add, add_zero, hA p hp, hB p hp, hC p hp, hAr, hBt, hBr, hCt]

/-- The mixed coefficient is odd; the diagonal coefficients are even.
The five resulting multiplier signs agree with those of the graph fields. -/
theorem n06CubicGraphMultipliers_reflectionOn_strip
    {l r : ℝ} (d e : ℝ → ℝ) {A B C : PolarPoint → ℝ}
    (hA : ContDiffOn ℝ ∞ A (Ioo l r ×ˢ (univ : Set ℝ)))
    (hB : ContDiffOn ℝ ∞ B (Ioo l r ×ˢ (univ : Set ℝ)))
    (hC : ContDiffOn ℝ ∞ C (Ioo l r ×ˢ (univ : Set ℝ)))
    (hAe : ∀ p : PolarPoint, p.1 ∈ Ioo l r → A (p.1, Real.pi - p.2) = A p)
    (hBo : ∀ p : PolarPoint, p.1 ∈ Ioo l r → B (p.1, Real.pi - p.2) = -B p)
    (hCe : ∀ p : PolarPoint, p.1 ∈ Ioo l r → C (p.1, Real.pi - p.2) = C p)
    (i : Fin 5) (p : PolarPoint) (hp : p.1 ∈ Ioo l r) :
    n06CubicGraphMultipliers d e A B C i (p.1, Real.pi - p.2) =
      n06CubicGraphParity i * n06CubicGraphMultipliers d e A B C i p := by
  have hAr : radialPartial A (p.1, Real.pi - p.2) = radialPartial A p := by
    simpa only [one_mul] using (n06_coordinatePartials_reflectionOn_strip hA
      (σ := 1) (fun q hq => by simpa only [one_mul] using hAe q hq) p hp).1
  have hBt : angularPartial B (p.1, Real.pi - p.2) = angularPartial B p := by
    simpa only [neg_neg, one_mul] using (n06_coordinatePartials_reflectionOn_strip hB
      (σ := -1) (fun q hq => by simpa only [neg_one_mul] using hBo q hq) p hp).2
  have hBr : radialPartial B (p.1, Real.pi - p.2) = -radialPartial B p := by
    simpa only [neg_one_mul] using (n06_coordinatePartials_reflectionOn_strip hB
      (σ := -1) (fun q hq => by simpa only [neg_one_mul] using hBo q hq) p hp).1
  have hCt : angularPartial C (p.1, Real.pi - p.2) = -angularPartial C p := by
    simpa only [neg_one_mul] using (n06_coordinatePartials_reflectionOn_strip hC
      (σ := 1) (fun q hq => by simpa only [one_mul] using hCe q hq) p hp).2
  fin_cases i <;> simp only [n06CubicGraphMultipliers, n06CubicGraphParity,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ',
    id_eq, hAe p hp, hBo p hp, hCe p hp, hAr, hBt, hBr, hCt] <;> ring

end ContinuousFlexibility.Analysis
