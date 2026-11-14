module

public import ContinuousFlexibility.Analysis.N06NormalizerDomain

/-!
# Every original weighted estimate survives normalizer reselection

The correction direction is obtained from one canonical source sequence.
Its membership in every source level lets the old global inverse provide
the required weighted height of that direction. The new output is the
old output plus its compatibility scalar times this fixed direction.
The original three exponents and every material and angular order are
retained.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

private theorem n06_normalizer_norm_and_cost
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (W v : Y) {c s s' q : ℝ} (hq : 0 ≤ q)
    (hc : |c| ≤ s) (hs' : s' ≤ s + |c| * q) :
    ‖W + c • v‖ + s' ≤ (1 + ‖v‖ + q) * (‖W‖ + s) := by
  have hn : ‖W + c • v‖ ≤ ‖W‖ + |c| * ‖v‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le W (c • v)
  have hqv : 0 ≤ ‖v‖ + q := add_nonneg (norm_nonneg _) hq
  calc
    ‖W + c • v‖ + s' ≤ (‖W‖ + |c| * ‖v‖) + (s + |c| * q) :=
      add_le_add hn hs'
    _ = ‖W‖ + s + |c| * (‖v‖ + q) := by ring
    _ ≤ ‖W‖ + s + s * (‖v‖ + q) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hqv)
    _ ≤ (1 + ‖v‖ + q) * (‖W‖ + s) := by
      nlinarith only [mul_nonneg (norm_nonneg W) hqv]

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

/-- The weighted clause of N05, with its selected global inverse exposed. -/
def N06CanonicalInverseBound (V : VolumeModelData S K)
    (J : CanonicalSequence S K → CanonicalUnknown S K)
    (loss γ t : ℝ) (s : ℕ) : Prop :=
  ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ F : V.level γ t s,
    ∃ W : V.level γ (t - loss) s,
      V.forget γ (t - loss) s W = (fun m => (J (V.forget γ t s F)).1 m) ∧
      ‖W‖ + canonicalUnknownScalars S K (J (V.forget γ t s F)) ≤ C₀ * ‖F‖

theorem n06_canonicalUnknownScalars_nonneg (U : CanonicalUnknown S K) :
    0 ≤ canonicalUnknownScalars S K U :=
  add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

theorem n06_normalizer_lambda_le_scalars (U : CanonicalUnknown S K) :
    |U.2.2.2| ≤ canonicalUnknownScalars S K U :=
  le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))

theorem n06_normalizer_scalars_add_smul (U v : CanonicalUnknown S K) (c : ℝ) :
    canonicalUnknownScalars S K (U + c • v) ≤
      canonicalUnknownScalars S K U + |c| * canonicalUnknownScalars S K v := by
  change |U.2.1 + c * v.2.1| + |U.2.2.1 + c * v.2.2.1| +
      |U.2.2.2 + c * v.2.2.2| ≤
    (|U.2.1| + |U.2.2.1| + |U.2.2.2|) +
      |c| * (|v.2.1| + |v.2.2.1| + |v.2.2.2|)
  calc
    _ ≤ (|U.2.1| + |c * v.2.1|) + (|U.2.2.1| + |c * v.2.2.1|) +
        (|U.2.2.2| + |c * v.2.2.2|) :=
      add_le_add (add_le_add (abs_add_le _ _) (abs_add_le _ _)) (abs_add_le _ _)
    _ = _ := by simp only [abs_mul]; ring

theorem n06NormalizerUnknownShear_height (v U : CanonicalUnknown S K) :
    (fun m => (n06NormalizerUnknownShear (n06NormalizerLambda S K) v U).1 m) =
      (fun m => U.1 m) + U.2.2.2 • (fun m => v.1 m) := by
  rw [n06NormalizerUnknownShear_apply, n06NormalizerLambda_apply]
  rfl

/-- On a graph source, the old selected global inverse is the same graph
element, not an independently chosen solution. -/
theorem n06N05_globalInverse_graph_source
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (v : B.Space) :
    B.globalInverse (V.forget (3 / 4 : ℝ) 0 b v.val.2) = v.val.1 := by
  have hg := h05.2.2.2.2.2.2.2.2.2.1 v.val.2
  have hi := congrArg (fun x : B.Space => x.val.1) (h05.2.2.2.2.2.2.2.2.1 v)
  exact hg.symm.trans hi

/-- A fixed weighted direction changes only the constant in the old
weighted estimate. All sources are represented in the original level. -/
theorem n06Normalizer_weighted_bound
    {J : CanonicalSequence S K → CanonicalUnknown S K}
    {d : CanonicalSequence S K} {v : CanonicalUnknown S K}
    {loss γ t : ℝ} {s : ℕ}
    (hd : VolumeMember S K V γ t s d) (hv : J d = v)
    (hbound : N06CanonicalInverseBound V J loss γ t s) :
    N06CanonicalInverseBound V
      (fun F => n06NormalizerUnknownShear (n06NormalizerLambda S K) v (J F))
      loss γ t s := by
  obtain ⟨C₀, hC₀, hb⟩ := hbound
  obtain ⟨D₀, hD₀⟩ := hd
  obtain ⟨Wv, hWv, _⟩ := hb D₀
  have hWv' : V.forget γ (t - loss) s Wv = fun m => v.1 m := by
    rw [hD₀, hv] at hWv
    exact hWv
  let A : ℝ := 1 + ‖Wv‖ + canonicalUnknownScalars S K v
  have hA : 0 < A := by
    dsimp only [A]
    have hs := n06_canonicalUnknownScalars_nonneg v
    positivity
  refine ⟨A * C₀, mul_pos hA hC₀, ?_⟩
  intro F
  obtain ⟨W, hW, hnorm⟩ := hb F
  let U : CanonicalUnknown S K := J (V.forget γ t s F)
  refine ⟨W + U.2.2.2 • Wv, ?_, ?_⟩
  · rw [map_add, map_smul, hW, hWv']
    exact (n06NormalizerUnknownShear_height v U).symm
  · have hs := n06_normalizer_scalars_add_smul U v U.2.2.2
    have hn := n06_normalizer_norm_and_cost W Wv
      (n06_canonicalUnknownScalars_nonneg v) (n06_normalizer_lambda_le_scalars U) hs
    have he : n06NormalizerUnknownShear (n06NormalizerLambda S K) v U =
        U + U.2.2.2 • v := by
      rw [n06NormalizerUnknownShear_apply, n06NormalizerLambda_apply]
    change ‖W + U.2.2.2 • Wv‖ +
      canonicalUnknownScalars S K (n06NormalizerUnknownShear (n06NormalizerLambda S K) v U) ≤
        A * C₀ * ‖F‖
    rw [he]
    exact hn.trans (by
      change A * (‖W‖ + canonicalUnknownScalars S K U) ≤ A * C₀ * ‖F‖
      calc
        _ ≤ A * (C₀ * ‖F‖) := mul_le_mul_of_nonneg_left hnorm hA.le
        _ = _ := (mul_assoc _ _ _).symm)

theorem n06NormalizerDomain_weighted_bound
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    {γ t : ℝ} {s : ℕ}
    (hd : VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2))
    (hbound : N06CanonicalInverseBound V B.globalInverse B.lossMaterial γ t s) :
    N06CanonicalInverseBound (n06NormalizerVolume V ψ)
      (n06NormalizerDomain B ψ v hv).globalInverse
      (n06NormalizerDomain B ψ v hv).lossMaterial γ t s := by
  change N06CanonicalInverseBound V
    (fun F => n06NormalizerUnknownShear (n06NormalizerLambda S K) v.val.1 (B.globalInverse F))
    B.lossMaterial γ t s
  exact n06Normalizer_weighted_bound hd (n06N05_globalInverse_graph_source h05 v) hbound

/-- The old delta, all three height exponents, and every material and
angular order are retained by the actual transported global inverse. -/
theorem n06NormalizerDomain_three_weights
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (hd : ∀ γ t : ℝ, ∀ s : ℕ,
      VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (1 / 4 : ℝ) ∧ ∀ γ : ℝ,
      (γ = (3 / 4 : ℝ) - δ ∨ γ = (3 / 4 : ℝ) ∨ γ = (3 / 4 : ℝ) + δ) →
      ∀ t : ℝ, ∀ s : ℕ,
        N06CanonicalInverseBound (n06NormalizerVolume V ψ)
          (n06NormalizerDomain B ψ v hv).globalInverse
          (n06NormalizerDomain B ψ v hv).lossMaterial γ t s := by
  obtain ⟨δ, hδ, hδ', hb⟩ := h05.2.2.2.2.2.2.2.2.2.2.2.1
  exact ⟨δ, hδ, hδ', fun γ hγ t s =>
    n06NormalizerDomain_weighted_bound h05 ψ v hv (hd γ t s) (hb γ hγ t s)⟩

theorem n06NormalizerDomain_central_weights
    {B : CanonicalDomainData S K V b} (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space) (v : B.Space)
    (hv : n06NormalizerLambda S K v.val.1 = 0)
    (hd : ∀ γ t : ℝ, ∀ s : ℕ,
      VolumeMember S K V γ t s (V.forget (3 / 4 : ℝ) 0 b v.val.2)) :
    ∀ t : ℝ, ∀ s : ℕ,
      N06CanonicalInverseBound (n06NormalizerVolume V ψ)
        (n06NormalizerDomain B ψ v hv).globalInverse
        (n06NormalizerDomain B ψ v hv).lossMaterial (3 / 4 : ℝ) t s := by
  intro t s
  exact n06NormalizerDomain_weighted_bound h05 ψ v hv (hd (3 / 4 : ℝ) t s)
    (h05.2.2.2.2.2.2.2.2.2.2.2.2.1 t s)

end ContinuousFlexibility.Statements
