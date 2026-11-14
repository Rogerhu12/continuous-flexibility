import ContinuousFlexibility.Analysis.ParameterizedScalarInverse
import ContinuousFlexibility.Analysis.N01cCoefficientJetCalculus
import ContinuousFlexibility.Analysis.CircleSmoothDirectionsOperations

/-!
# Actual inverses of finite coefficient scalar families

The radial collar is a smooth function of finitely many actual endpoint
coefficients.  Its inverse therefore only needs a finite dimensional
implicit function theorem, even when those coefficients depend on the
original nonnormable state space.  Positivity and surjectivity are hypotheses
on the forward scalar family.  No continuity or differentiability of its
chosen `invFun` is assumed.

The last constructor composes the resulting ordinary smooth inverse with
the original coefficient tower.  Its displayed partition formula gives
all state derivatives of the literal inverse and is available for uniform
estimates.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff BigOperators

private theorem scalarSlope_isInvertible {d : ℝ} (hd : d ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
  · ext x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      ContinuousLinearMap.id_apply]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  · ext x
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      ContinuousLinearMap.id_apply]
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]

section NormedCoefficientSpace

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {V : Set P} {F : P × ℝ → ℝ}

/-- The actual scalar inverse is jointly smooth on any open coefficient
domain on which the forward family has positive scalar derivative and is
onto.  Its regularity is obtained from the implicit function theorem and
uniqueness of the scalar solution. -/
theorem n04PositiveGeometry_scalarInverse_contDiffOn
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (hpositive : ∀ a ∈ V, ∀ r, 0 < deriv (fun t => F (a, t)) r)
    (hsurj : ∀ a ∈ V, Function.Surjective (fun t => F (a, t))) :
    ContDiffOn ℝ ∞
      (fun q : P × ℝ => Function.invFun (fun t => F (q.1, t)) q.2)
      (V ×ˢ univ) := by
  let G : P × ℝ → ℝ := fun q => Function.invFun (fun t => F (q.1, t)) q.2
  have hright (q : P × ℝ) (hq : q.1 ∈ V) : F (q.1, G q) = q.2 :=
    Function.rightInverse_invFun (hsurj q.1 hq) q.2
  intro q hq
  let H : (P × ℝ) × ℝ → ℝ := fun z => F (z.1.1, z.2) - z.1.2
  have hFq : ContDiffAt ℝ ∞ F (q.1, G q) :=
    hF.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hq.1, mem_univ _⟩)
  have hprojection : ContDiffAt ℝ ∞
      (fun z : (P × ℝ) × ℝ => (z.1.1, z.2)) (q, G q) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have hvalue : ContDiffAt ℝ ∞ (fun z : (P × ℝ) × ℝ => z.1.2) (q, G q) :=
    contDiffAt_fst.snd
  have hc : ContDiffAt ℝ ∞ H (q, G q) :=
    (hFq.comp (q, G q) hprojection).sub hvalue
  let d : ℝ := deriv (fun t => F (q.1, t)) (G q)
  have hd : d ≠ 0 := (hpositive q.1 hq.1 (G q)).ne'
  have ha : HasDerivAt (fun t => F (q.1, t)) d (G q) :=
    (differentiableAt_of_deriv_ne_zero hd).hasDerivAt
  have hs : HasFDerivAt (fun t => H (q, t))
      (ContinuousLinearMap.toSpanSingleton ℝ d) (G q) := by
    simpa only [H] using (ha.sub_const q.2).hasFDerivAt
  have hp : HasFDerivAt (fun t => H (q, t))
      ((fderiv ℝ H (q, G q)).comp (ContinuousLinearMap.inr ℝ (P × ℝ) ℝ)) (G q) := by
    have hh := (hc.differentiableAt (by simp)).hasFDerivAt.comp (G q)
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q (G q))
    simpa only [Function.comp_def] using hh
  have hi : ((fderiv ℝ H (q, G q)).comp
      (ContinuousLinearMap.inr ℝ (P × ℝ) ℝ)).IsInvertible := by
    rw [hp.unique hs]
    exact scalarSlope_isInvertible hd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ : P × ℝ → ℝ := hc.implicitFunction hn hi
  have hψ : ContDiffAt ℝ ∞ ψ q := hc.contDiffAt_implicitFunction hn hi
  have hsol : ∀ᶠ z in 𝓝 q, H (z, ψ z) = H (q, G q) :=
    hc.eventually_apply_implicitFunction hn hi
  have hzero : H (q, G q) = 0 := sub_eq_zero.mpr (hright q hq.1)
  have hmem : ∀ᶠ z : P × ℝ in 𝓝 q, z.1 ∈ V :=
    continuous_fst.continuousAt.eventually (hV.mem_nhds hq.1)
  have heq : G =ᶠ[𝓝 q] ψ := by
    filter_upwards [hsol, hmem] with z hz hzV
    rw [hzero] at hz
    change F (z.1, ψ z) - z.2 = 0 at hz
    apply (strictMono_of_deriv_pos (f := fun t : ℝ => F (z.1, t))
      (fun t => hpositive z.1 hzV t)).injective
    exact (hright z hzV).trans (sub_eq_zero.mp hz).symm
  exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt

end NormedCoefficientSpace

section OriginalParameterSpace

variable {E P : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {U : Set E} {V : Set P} {F : P × ℝ → ℝ} {a : E → P × ℝ}

/-- An actual inverse tower on the original state space, constructed from
the forward finite coefficient family and its coefficient tower. -/
def n04PositiveGeometry_finiteCoefficient_inverseDirections
    (J : SmoothDirections U a)
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (hpositive : ∀ c ∈ V, ∀ r, 0 < deriv (fun t => F (c, t)) r)
    (hsurj : ∀ c ∈ V, Function.Surjective (fun t => F (c, t)))
    (hmap : MapsTo a U (V ×ˢ univ)) :
    SmoothDirections U
      (fun x => Function.invFun (fun t => F ((a x).1, t)) (a x).2) :=
  smoothDirections_contDiff_comp J (hV.prod isOpen_univ)
    (n04PositiveGeometry_scalarInverse_contDiffOn hV hF hpositive hsurj) hmap

/-- The tower uses the ordinary Fréchet jets of the actual scalar inverse,
with the precise ordered partition formula.  This is the formula used by
the subsequent finite coefficient and one-high estimates. -/
theorem n04PositiveGeometry_finiteCoefficient_inverseDirections_apply
    (J : SmoothDirections U a)
    (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F (V ×ˢ univ))
    (hpositive : ∀ c ∈ V, ∀ r, 0 < deriv (fun t => F (c, t)) r)
    (hsurj : ∀ c ∈ V, Function.Surjective (fun t => F (c, t)))
    (hmap : MapsTo a U (V ×ˢ univ))
    (n : ℕ) (x : E) (v : Fin n → E) :
    (n04PositiveGeometry_finiteCoefficient_inverseDirections
      J hV hF hpositive hsurj hmap).D n x v =
      ∑ c : OrderedFinpartition n,
        iteratedFDeriv ℝ c.length
          (fun q : P × ℝ => Function.invFun (fun t => F (q.1, t)) q.2)
          (a x) (fun i => J.D (c.partSize i) x (v ∘ c.emb i)) :=
  smoothDirections_contDiff_comp_D_apply J (hV.prod isOpen_univ)
    (n04PositiveGeometry_scalarInverse_contDiffOn hV hF hpositive hsurj)
    hmap n x v

end OriginalParameterSpace

end ContinuousFlexibility.Analysis
