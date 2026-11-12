import ContinuousFlexibility.Analysis.N07aAngularFrequency
import ContinuousFlexibility.Analysis.N07aAngularSobolev
import ContinuousFlexibility.Analysis.AngularHilbertScale
import ContinuousFlexibility.Analysis.AngularRealInverseEstimate

/-!
# Applying the real angular inverse theorem to the actual canonical graph

The coordinates in this theorem are the proved onto decomposition of
the prescribed source graph. The analytic commutator hypotheses are
stated for actual source operators, and the conclusion constructs an
actual higher-level source. This is the transport step used after the
relative operator and its commutator estimates have been proved.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

/-- Transport through a proved onto isometry, keeping the frequency action explicit. -/
private theorem n07aAngular_inverse_tame_isometry
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
    (e : H ≃ₗᵢ[ℝ] lp E 2) (Λ : H → H)
    (hΛ : ∀ u, e (Λ u) = angularDerivative (𝕜 := ℝ) (e u))
    (R Q B : H →L[ℝ] H) (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p u, MemAngularSobolev (𝕜 := ℝ) p (e u) →
      MemAngularSobolev (𝕜 := ℝ) p (e (R u)))
    (hQ : ∀ p u, MemAngularSobolev (𝕜 := ℝ) p (e u) →
      MemAngularSobolev (𝕜 := ℝ) p (e (Q u)) ∧
      angularSobolevNorm (𝕜 := ℝ) p (e (Q u)) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℝ) p (e u) + (c p : ℝ) * ‖u‖)
    (hcomm : ∀ u, e u ∈ angularFrequencyDomain (𝕜 := ℝ) → Λ (R u) = R (Λ u) + Q u)
    (hleft : ∀ u, B (u + R u) = u) (hright : ∀ u, B u + R (B u) = u) :
    (∀ p u, MemAngularSobolev (𝕜 := ℝ) p (e u) →
      MemAngularSobolev (𝕜 := ℝ) p (e (B u))) ∧
    (∀ p, 1 ≤ p → ∀ u, MemAngularSobolev (𝕜 := ℝ) p (e u) →
      angularSobolevNorm (𝕜 := ℝ) p (e (B u)) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (angularSobolevNorm (𝕜 := ℝ) p (e u) + (1 + (c (p - 1) : ℝ)) * ‖u‖)) := by
  have hRC : ∀ p v, MemAngularSobolev (𝕜 := ℝ) p v →
      MemAngularSobolev (𝕜 := ℝ) p (angularConjugate e R v) := by
    intro p v hv
    simpa only [angularConjugate_apply, e.apply_symm_apply] using
      hR p (e.symm v) (by simpa only [e.apply_symm_apply] using hv)
  have hQC : ∀ p v, MemAngularSobolev (𝕜 := ℝ) p v →
      MemAngularSobolev (𝕜 := ℝ) p (angularConjugate e Q v) ∧
      angularSobolevNorm (𝕜 := ℝ) p (angularConjugate e Q v) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℝ) p v + (c p : ℝ) * ‖v‖ := by
    intro p v hv
    simpa only [angularConjugate_apply, e.apply_symm_apply, e.symm.norm_map] using
      hQ p (e.symm v) (by simpa only [e.apply_symm_apply] using hv)
  have hΛ' (v : lp E 2) : Λ (e.symm v) = e.symm (angularDerivative (𝕜 := ℝ) v) := by
    apply e.injective
    simpa only [e.apply_symm_apply] using hΛ (e.symm v)
  have hcommC : ∀ v, v ∈ angularFrequencyDomain (𝕜 := ℝ) →
      angularDerivative (𝕜 := ℝ) (angularConjugate e R v) =
        angularConjugate e R (angularDerivative (𝕜 := ℝ) v) + angularConjugate e Q v := by
    intro v hv
    have h := congrArg e (hcomm (e.symm v) (by simpa only [e.apply_symm_apply] using hv))
    simpa only [map_add, hΛ, hΛ', angularConjugate_apply] using h
  have hleftC : ∀ v, angularConjugate e B (v + angularConjugate e R v) = v := by
    intro v
    simpa only [angularConjugate_apply, map_add, e.apply_symm_apply, e.symm_apply_apply]
      using congrArg e (hleft (e.symm v))
  have hrightC : ∀ v, angularConjugate e B v +
      angularConjugate e R (angularConjugate e B v) = v := by
    intro v
    simpa only [angularConjugate_apply, map_add, e.apply_symm_apply, e.symm_apply_apply]
      using congrArg e (hright (e.symm v))
  obtain ⟨hreg, hnorm⟩ := angular_inverse_tame_real
    (angularConjugate e R) (angularConjugate e Q) (angularConjugate e B)
    a c ha hc hRC (fun p v hv => (hQC p v hv).1) (fun p v hv => (hQC p v hv).2)
    hcommC hleftC hrightC
  constructor
  · intro p u hu
    simpa only [angularConjugate_apply_coordinates] using hreg p (e u) hu
  · intro p hp u hu
    simpa only [angularConjugate_apply_coordinates, norm_angularConjugate, e.norm_map]
      using hnorm p hp (e u) hu

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hK : ∀ m, K.left m < K.right m) (b : ℕ)

local instance n07aInverseLevelGroup (s : ℕ) : NormedAddCommGroup (V.level γ w s) := Submodule.normedAddCommGroup _
local instance n07aInverseLevelSpace (s : ℕ) : NormedSpace ℝ (V.level γ w s) := Submodule.normedSpace _
local instance n07aInverseLevelInner (s : ℕ) : InnerProductSpace ℝ (V.level γ w s) := Submodule.innerProductSpace _
local instance n07aInverseBandGroup (n : ℕ) : NormedAddCommGroup (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.normedAddCommGroup _
local instance n07aInverseBandSpace (n : ℕ) : NormedSpace ℝ (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.normedSpace _
local instance n07aInverseBandInner (n : ℕ) : InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.innerProductSpace _
local instance n07aInverseLpGroup : NormedAddCommGroup
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.normedAddCommGroup
local instance n07aInverseLpSpace : NormedSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.instNormedSpace
local instance n07aInverseLpInner : InnerProductSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.instInnerProductSpace

/-- The established real angular theorem on the actual canonical source space. -/
theorem n07aAngular_inverse_tame
    (R Q B : V.level γ w b →L[ℝ] V.level γ w b)
    (a c : ℕ → ℝ≥0) (ha : Monotone a) (hc : Monotone c)
    (hR : ∀ p u, MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (R u)))
    (hQ : ∀ p u, MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (Q u)) ∧
      angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (Q u)) ≤
        (a p : ℝ) * angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) +
          (c p : ℝ) * ‖u‖)
    (hcomm : ∀ u, n07aAngularHilbertEquiv hV γ w hK b u ∈ angularFrequencyDomain (𝕜 := ℝ) →
      n07aAngularLambda hV γ w hK b (R u) = R (n07aAngularLambda hV γ w hK b u) + Q u)
    (hleft : ∀ u, B (u + R u) = u) (hright : ∀ u, B u + R (B u) = u) :
    (∀ p u, MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (B u))) ∧
    (∀ p, 1 ≤ p → ∀ u,
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (B u)) ≤
        angularInverseTameConstant p (a (p - 1)) (c 0) ‖B‖ *
          (angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) +
            (1 + (c (p - 1) : ℝ)) * ‖u‖)) := by
  let : CompleteSpace (V.level γ w b) := n07aAngularLevelComplete hV γ w b
  exact n07aAngular_inverse_tame_isometry (n07aAngularHilbertEquiv hV γ w hK b)
    (n07aAngularLambda hV γ w hK b) (n07aAngularLambda_coordinates hV γ w hK b)
    R Q B a c ha hc hR hQ hcomm hleft hright

/-- The spectral estimate reconstructs the actual inverse in the higher graph. -/
theorem n07aAngular_inverse_lift_of_estimate
    (B : V.level γ w b →L[ℝ] V.level γ w b) (p : ℕ) (A C : ℝ)
    (hA : 0 ≤ A)
    (hreg : ∀ u, MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (B u)))
    (hbound : ∀ u, MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) →
      angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (B u)) ≤
        A * (angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) + C * ‖u‖))
    (f : V.level γ w (b + p)) :
    ∃ u : V.level γ w (b + p),
      n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) u =
        B (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) f) ∧
      ‖u‖ ≤ n07aAngularLiftConstant p * A *
        (‖f‖ + C * ‖n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) f‖) := by
  let f₀ := n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) f
  have hf := n07aAngularTruncate_memSobolev hV γ w hK b p f
  obtain ⟨u, hu, hnorm⟩ := n07aAngularSobolev_exists_lift hV γ w hK b p (B f₀) (hreg f₀ hf)
  refine ⟨u, hu, hnorm.trans ?_⟩
  calc
    n07aAngularLiftConstant p *
        angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (B f₀)) ≤
        n07aAngularLiftConstant p * (A *
          (angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b f₀) +
            C * ‖f₀‖)) :=
      mul_le_mul_of_nonneg_left (hbound f₀ hf) (n07aAngularLiftConstant_nonneg p)
    _ ≤ n07aAngularLiftConstant p * (A * (‖f‖ + C * ‖f₀‖)) := by
      apply mul_le_mul_of_nonneg_left _ (n07aAngularLiftConstant_nonneg p)
      apply mul_le_mul_of_nonneg_left _ hA
      exact add_le_add (n07aAngularTruncate_sobolevNorm_le hV γ w hK b p f) le_rfl
    _ = _ := by ring

end ContinuousFlexibility.Statements
