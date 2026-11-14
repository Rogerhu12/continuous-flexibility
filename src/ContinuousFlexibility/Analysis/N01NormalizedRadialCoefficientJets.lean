module

public import ContinuousFlexibility.Analysis.N01RadialCoefficientRootJets

/-!
# The actual radial coefficient in normalized root coordinates

The physical radial coordinate is `r + σ δ x`. The coefficient used by
the normalized root height is the physical radial coefficient divided
by δ. This exact function inherits the original N01 derivative loss;
all powers of the fixed affine norm and δ belong to numerical constants
chosen before the state.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

def rootScaledRadialCoefficient (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (z : AnnularState S × ℝ) (r σ δ : ℝ)
    (q : PolarPoint) : ℝ :=
  (originalCoefficients D S C z).a (r + (σ * δ) * q.1, q.2) / δ

private def rootRadialScaleLinear (σ δ : ℝ) : PolarPoint →L[ℝ] PolarPoint :=
  ((σ * δ) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem rootRadialScaleLinear_apply (σ δ : ℝ) (q : PolarPoint) :
    rootRadialScaleLinear σ δ q = ((σ * δ) * q.1, q.2) := by
  simp only [rootRadialScaleLinear, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]

private theorem scaledRadialCoefficient_material_bound
    {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) {loss : ℕ}
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) (r σ δ : ℝ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧ ∀ z : E, ∀ f : PolarPoint → ℝ, ∀ θ : ℝ,
      ContDiffAt ℝ ∞ f (r, θ) → PointwiseMaterialJetBound p loss A z f (r, θ) →
      ContDiffAt ℝ ∞ (fun q => f (r + (σ * δ) * q.1, q.2) / δ) (0, θ) ∧
        PointwiseMaterialJetBound p loss B z
          (fun q => f (r + (σ * δ) * q.1, q.2) / δ) (0, θ) := by
  let L := rootRadialScaleLinear σ δ
  let B : ℕ → ℝ := fun n => (1 + |δ⁻¹|) * (1 + ‖L‖ ^ n) * A n
  have hB (n : ℕ) : 0 < B n :=
    mul_pos (mul_pos (add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _))
      (add_pos_of_pos_of_nonneg zero_lt_one (pow_nonneg (norm_nonneg L) n))) (hA n)
  refine ⟨B, hB, ?_⟩
  intro z f θ hf hb
  have hLapply (q : PolarPoint) : L q = ((σ * δ) * q.1, q.2) :=
    rootRadialScaleLinear_apply σ δ q
  have hpoint : (r, (0 : ℝ)) + L (0, θ) = (r, θ) := by
    rw [hLapply]
    simp only [mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  have hf' : ContDiffAt ℝ ∞ f ((r, (0 : ℝ)) + L (0, θ)) := by rw [hpoint]; exact hf
  have hb' : PointwiseMaterialJetBound p loss A z f ((r, (0 : ℝ)) + L (0, θ)) := by
    rw [hpoint]
    exact hb
  have hcomp := PointwiseMaterialJetBound.affine_comp L (r, 0) hf' hb'
  have hcompSmooth : ContDiffAt ℝ ∞ (fun q => f ((r, 0) + L q)) (0, θ) :=
    hf'.comp (0, θ) (contDiffAt_const.add L.contDiff.contDiffAt)
  have hscaled := hcomp.const_mul hcompSmooth δ⁻¹
  have he : (fun q => δ⁻¹ * f ((r, 0) + L q)) =
      (fun q => f (r + (σ * δ) * q.1, q.2) / δ) := by
    funext q
    rw [hLapply]
    simp only [Prod.mk_add_mk, zero_add, div_eq_mul_inv]
    exact mul_comm _ _
  rw [he] at hscaled
  have hsmooth : ContDiffAt ℝ ∞ (fun q => δ⁻¹ * f ((r, 0) + L q)) (0, θ) :=
    contDiffAt_const.mul hcompSmooth
  rw [he] at hsmooth
  have hconstant (n : ℕ) : |δ⁻¹| * (‖L‖ ^ n * A n) ≤ B n := by
    have hn : 0 ≤ ‖L‖ ^ n := pow_nonneg (norm_nonneg L) n
    calc
      _ = (|δ⁻¹| * ‖L‖ ^ n) * A n := by ring
      _ ≤ ((1 + |δ⁻¹|) * (1 + ‖L‖ ^ n)) * A n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (le_add_of_nonneg_left zero_le_one)
            (le_add_of_nonneg_left zero_le_one) hn
            (add_nonneg zero_le_one (abs_nonneg _))) (hA n).le
      _ = B n := rfl
  exact ⟨hsmooth, hscaled.mono hp le_rfl
    (fun n => mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg (norm_nonneg L) n) (hA n).le))
    hconstant⟩

def N01ScaledRadialCoefficientRootJetBound
    (D : ReferenceData) (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (base loss : ℕ) (ε r σ δ : ℝ) (B : ℕ → ℝ) : Prop :=
  ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 → ∀ θ : ℝ,
    ContDiffAt ℝ ∞ (rootScaledRadialCoefficient D S C z r σ δ) (0, θ) ∧
      PointwiseMaterialJetBound (pairGrading (stateGrading S) realGrading) loss B
        (z - (C.referenceState, 0)) (rootScaledRadialCoefficient D S C z r σ δ) (0, θ)

theorem n01_scaledRadialCoefficient_root_fixed_loss
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε r : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) (hr : r ∈ Ioo D.a D.b) (σ δ : ℝ) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      N01ScaledRadialCoefficientRootJetBound D S C base loss ε r σ δ B := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  obtain ⟨A, hA, hroot⟩ := n01_radialCoefficient_root_fixed_loss hS hT hN hr
  obtain ⟨B, hB, hb⟩ := scaledRadialCoefficient_material_bound hp A hA r σ δ
  refine ⟨B, hB, ?_⟩
  intro z hz hs θ
  exact hb (z - (C.referenceState, 0)) (originalCoefficients D S C z).a θ
    (hroot z hz hs θ).1 (hroot z hz hs θ).2

end ContinuousFlexibility.Analysis
