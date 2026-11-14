module

public import ContinuousFlexibility.Analysis.N01aComponentCountingHosts
public import ContinuousFlexibility.Analysis.N01aWeightedEnumerationBounds

/-!
# A quantitatively ordered enumeration of the negative components

The physical lower distance bound places all components of bounded host
index in one compact interior set. Their host weights are therefore
proper. Actual good-point decay then gives a bijection whose host indices
grow at most linearly.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Real
open scoped ContDiff

theorem n01a_component_host_sublevel_finite {D : ReferenceData} {C : ℕ → ℝ}
    (hD : AccumulatingProfileBounds D C)
    (host : N01aNegativeComponent D → ℕ)
    (hhost : ∀ J, J.interval ⊆ D.cells (host J)) (N : ℕ) :
    {J : N01aNegativeComponent D | D.cellIndex (host J) ≤ N}.Finite := by
  have hC : 0 < C 0 := hD.2.2.1 0
  let δ : ℝ := (C 0)⁻¹ * exp (-((N : ℝ) + 1) ^ 2)
  have hδ : 0 < δ := mul_pos (inv_pos.mpr hC) (exp_pos _)
  let K : Set ℝ := Icc (D.a + δ) (D.b - δ)
  have hK : K ⊆ radialCore D := by
    intro r hr
    constructor <;> linarith only [hr.1, hr.2, hδ]
  apply (N01aNegativeComponent.finite_inter_compact hD.1 isCompact_Icc hK).subset
  intro J hJ
  let r : ℝ := (J.left + J.right) / 2
  have hr : r ∈ J.interval := by
    constructor <;> dsimp only [r] <;> linarith only [J.left_lt_right]
  have hdist := (hD.2.2.2.2.2.2.1 (host J) r (hhost J hr)).1
  have hindex : (D.cellIndex (host J) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hJ
  have hsquare : ((D.cellIndex (host J) : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    linarith only [hindex]
  have hsmall : δ ≤ (C 0)⁻¹ * exp (-((D.cellIndex (host J) : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hsquare)) (inv_nonneg.mpr hC.le)
  have hmin := hsmall.trans hdist
  have hl := hmin.trans (min_le_left _ _)
  have hh := hmin.trans (min_le_right _ _)
  exact ⟨r, hr, by constructor <;> linarith only [hl, hh]⟩

theorem exists_n01a_component_enumeration_linear_of_good_points {D : ReferenceData}
    (hD : IsAccumulatingProfile D) (hR : RadialReturnMargins D)
    {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hJ : ∀ r ∈ radialCore D, Radial.radialJacobi 4 D.w u r = 0)
    {p : ℝ} (hp : p ∈ radialCore D) (henergy : 0 < n01aJacobiEnergy u p)
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (host : N01aNegativeComponent D → ℕ)
    (hhost : ∀ J, J.interval ⊆ D.cells (host J)) {N₀ : ℝ}
    (hgood : ∀ N : ℝ, N₀ ≤ N → ∃ r : ℝ, r ∈ radialCore D ∧ p ≤ r ∧
      r ≤ D.b - (1 / 2 : ℝ) * exp (-N ^ 2) ∧
      n01aJacobiEnergy u r ≤ A * exp (-c * N ^ 3)) :
    ∃ e : ℕ ≃ N01aNegativeComponent D, ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (D.cellIndex (host (e n)) : ℝ) ≤ B * (1 + (n : ℝ)) := by
  classical
  obtain ⟨C, hC⟩ := hD
  letI := N01aNegativeComponent.infinite hC.1 hR
  let f : N01aNegativeComponent D → ℕ := fun J => D.cellIndex (host J)
  have hf : ∀ N : ℕ, {J | f J ≤ N}.Finite :=
    n01a_component_host_sublevel_finite hC host hhost
  obtain ⟨d, H, hd, hH, hwitness⟩ :=
    exists_n01a_component_density_witnesses hC hR hu hJ hp henergy hA hc host hhost hgood
  obtain ⟨B, hB, hb⟩ := exists_n01aWeightEnumeration_linear_bound f hf hd hH hwitness
  refine ⟨n01aWeightEquiv f hf, B, hB, ?_⟩
  intro n
  exact hb n

end ContinuousFlexibility.Statements
