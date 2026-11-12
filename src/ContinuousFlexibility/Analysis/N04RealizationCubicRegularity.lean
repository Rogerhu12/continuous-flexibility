import ContinuousFlexibility.Analysis.N01cMixedPowerBounds
import ContinuousFlexibility.Analysis.CanonicalTwoEndpointCubicMixed

/-!
# Genuine mixed towers for fixed cubic factors

Division by a fixed nonvanishing spatial factor preserves the actual
parameter tower on the open cylinder. Translation and reflection use the
existing mixed derivative identities. These operations do not shrink the
parameter set or prescribe any quantitative estimate for the quotient.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {Ω : Set PolarPoint} {f g : E → PolarPoint → ℝ}

/-- A fixed scalar multiple identifies every genuine directional jet. -/
theorem n04Realization_smoothDirections_D_const_mul
    {f g : E → ℝ} (J : SmoothDirections U f) (Q : SmoothDirections U g)
    (c : ℝ) (heq : ∀ x ∈ U, g x = c * f x)
    (k : ℕ) {x : E} (hx : x ∈ U) (v : Fin k → E) :
    Q.D k x v = c * J.D k x v := by
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  let K : SmoothDirections U g := (smoothDirections_postcompCLM J L).congr
    (fun y hy => by
      simpa only [L, Function.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul] using (heq y hy).symm)
  have h := HasProjectiveJetsOn.unique Q.open_domain
    Q.hasProjectiveJetsOn K.hasProjectiveJetsOn k x hx
  calc
    Q.D k x v = K.D k x v :=
      congrArg (fun A : E [×k]→L[ℝ] ℝ => A v) h
    _ = L (J.D k x v) := smoothDirections_postcompCLM_D_apply J L k x v
    _ = c * J.D k x v := by
      simp only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]

/-- The quotient's mixed tower is constructed from the numerator and
the fixed reciprocal factor on the original open spatial domain. -/
def n04Realization_mixedJetRegularity_of_staticFactorization
    (F : MixedJetRegularity U Ω f) (hU : IsOpen U) (hΩ : IsOpen Ω)
    {d : PolarPoint → ℝ} (hd : ContDiffOn ℝ ∞ d Ω)
    (hne : ∀ q ∈ Ω, d q ≠ 0)
    (hfactor : ∀ x ∈ U, ∀ q ∈ Ω, f x q = d q * g x q) :
    MixedJetRegularity U Ω g := by
  let W : MixedJetRegularity U Ω (fun (_ : E) q => (d q)⁻¹) :=
    { spatial := fun _ _ => hd.inv hne
      parameter := fun a b q _ =>
        smoothDirections_constant hU (mixedDerivative a b (fun q => (d q)⁻¹) q) }
  let P := F.mul W hU hΩ
  have heq : ∀ x ∈ U, EqOn (fun q => f x q * (d q)⁻¹) (g x) Ω := by
    intro x hx q hq
    rw [hfactor x hx q hq]
    field_simp [hne q hq] <;> ring
  exact P.congr hΩ
    (fun x hx => (P.spatial x hx).congr (fun q hq => (heq x hx q hq).symm)) heq

/-- Reflection maps the same open cylinder to itself. -/
theorem n04Realization_reflect_mem_cylinder {R : ℝ} {p : PolarPoint}
    (hp : p ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) :
    (R - p.1, p.2) ∈ Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ) := by
  exact ⟨⟨sub_pos.mpr hp.1.2, sub_lt_self R hp.1.1⟩, mem_univ _⟩

/-- Reflection transports the existing spatial and parameter towers. -/
def n04Realization_mixedJetRegularity_reflect {R : ℝ}
    (F : MixedJetRegularity U (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) f) :
    MixedJetRegularity U (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ))
      (fun x => reflectRadialField R (f x)) where
  spatial x hx := (F.spatial x hx).comp
    ((contDiff_const.sub contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ hp => n04Realization_reflect_mem_cylinder hp)
  parameter a b q hq :=
    (smoothDirections_postcompCLM
      (F.parameter a b (R - q.1, q.2) (n04Realization_reflect_mem_cylinder hq))
      ((-1 : ℝ) ^ a • ContinuousLinearMap.id ℝ ℝ)).congr (fun x _ => by
        simp only [Function.comp_apply, smul_apply,
          ContinuousLinearMap.id_apply, smul_eq_mul]
        exact (mixedDerivative_reflectRadialField R (f x) a b q).symm)

/-- Translation introduces no mixed derivative multiplier. -/
def n04Realization_mixedJetRegularity_translate {l r : ℝ}
    (F : MixedJetRegularity U (Ioo l r ×ˢ (univ : Set ℝ)) f) :
    MixedJetRegularity U (Ioo (0 : ℝ) (r - l) ×ˢ (univ : Set ℝ))
      (fun x => translateRadialField l (f x)) where
  spatial x hx := (F.spatial x hx).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
    (fun _ hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩)
  parameter a b q hq :=
    (F.parameter a b (l + q.1, q.2)
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩).congr
      (fun x _ => (mixedDerivative_translateRadialField l (f x) a b q).symm)

end ContinuousFlexibility.Analysis
