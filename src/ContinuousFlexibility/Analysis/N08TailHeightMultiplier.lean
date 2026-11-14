module

public import ContinuousFlexibility.Analysis.N08TailCutoffCoefficients
public import ContinuousFlexibility.Analysis.N08RadialMultiplierFamily
public import ContinuousFlexibility.Scalar.WeightedReferenceMaterialJets

/-!
# Actual height localizations with arbitrary sample-envelope decay

The cutoff operator is fixed independently of the requested decay power
and grading. A fixed extra number of input orders pays for each requested
sample-envelope power, uniformly over the complete cell family.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

section Scaling

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

private def n08_scaledOperator (a : ℝ) (L : E →L[ℝ] E) : E →L[ℝ] E := a • L

private theorem n08_scaledOperator_seminorm (p : Seminorm ℝ E)
    {a : ℝ} (ha : 0 ≤ a) (L : E →L[ℝ] E) (u : E) :
    p (n08_scaledOperator a L u) = a * p (L u) := by
  change p (a • L u) = _
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ha]

private theorem n08_scaledOperator_decode {P : Type*}
    (decode : E →ₗ[ℝ] (P → ℝ)) (a : ℝ) (L : E →L[ℝ] E) (u : E) (p : P) :
    decode (n08_scaledOperator a L u) p = a * decode (L u) p := by
  change decode (a • L u) p = _
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

end Scaling

variable {D : ReferenceData} {T : MaterialData} {W : SobolevModelData} {γ : ℝ}

def n08CellLayerMultiplier (hT : IsMaterialData D T) (hW : IsSobolevModel D T γ W)
    (A : ℝ) (m : ℕ) : W.Space →L[ℝ] W.Space :=
  SobolevModelData.radialMultiplierCLM hT hW
    (n08CellLayerCutoff_contDiff D A m).contDiffOn
    (materialSubpower_comp_radius_of_contDiff hT (n08CellLayerCutoff_contDiff D A m))

theorem n08CellLayerMultiplier_decode (hT : IsMaterialData D T) (hW : IsSobolevModel D T γ W)
    (A : ℝ) (m : ℕ) (u : W.Space) (p : PolarPoint) :
    W.decode (n08CellLayerMultiplier hT hW A m u) p =
      n08CellLayerCutoff D A m p.1 * W.decode u p := by
  rw [n08CellLayerMultiplier, SobolevModelData.decode_radialMultiplierCLM]

theorem n08CellLayerMultiplier_decode_germ
    (hT : IsMaterialData D T) (hW : IsSobolevModel D T γ W)
    {A : ℝ} (hA : 0 < A) (m : ℕ) (u : W.Space) {p : PolarPoint}
    (hp : n08CellLayerInner A (D.cellIndex m) < endpointDistance D p.1 ∧
      endpointDistance D p.1 < n08CellLayerOuter A (D.cellIndex m)) :
    W.decode (n08CellLayerMultiplier hT hW A m u) =ᶠ[𝓝 p] W.decode u := by
  have hnear : {q : PolarPoint | n08CellLayerCutoff D A m q.1 = 1} ∈ 𝓝 p :=
    continuous_fst.continuousAt.preimage_mem_nhds
      (n08CellLayerCutoff_eventually_one hA m hp)
  filter_upwards [hnear] with q hq
  rw [n08CellLayerMultiplier_decode, hq, one_mul]

theorem n08CellLayerMultiplier_tail_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T) (hW : IsSobolevModel D T γ W)
    {A : ℝ} (hA : 1 ≤ A) (N : ℝ) :
    ∃ loss : ℕ, ∀ s : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ m (u : W.Space),
      W.grading s (n08CellLayerMultiplier hT hW A m u) ≤
        K * (T.M (T.sample m) ^ N)⁻¹ * W.grading (s + loss) u := by
  obtain ⟨loss, hb⟩ := n08ScaledCellCutoff_material_bound hD hT hA N
  obtain ⟨B, hB⟩ := hD
  have hsample (m : ℕ) : 0 < T.M (T.sample m) ^ N :=
    Real.rpow_pos_of_pos
      (zero_lt_one.trans_le (hT.2.1 _ (materialSample_mem_radialCore hT hB.2.1 m)).2.2.2) N
  let F (m : ℕ) : W.Space →L[ℝ] W.Space :=
    n08_scaledOperator (T.M (T.sample m) ^ N) (n08CellLayerMultiplier hT hW A m)
  have hdecode (m : ℕ) (u : W.Space) (p : PolarPoint) :
      W.decode (F m u) p = n08ScaledCellCutoff D T A N m p.1 * W.decode u p := by
    change W.decode (n08_scaledOperator (T.M (T.sample m) ^ N)
      (n08CellLayerMultiplier hT hW A m) u) p = _
    rw [n08_scaledOperator_decode, n08CellLayerMultiplier_decode]
    dsimp only [n08ScaledCellCutoff]
    ring
  have hsmooth (m : ℕ) : ContDiff ℝ ∞ (fun x => n08ScaledCellCutoff D T A N m (T.radius x)) :=
    (n08ScaledCellCutoff_contDiff D T A N m).comp hT.2.2.2.2.2.2.1
  refine ⟨loss, fun s => ?_⟩
  obtain ⟨K, hK, hKb⟩ := n08_radialMultiplier_family_grading_bound hT hW
    (n08ScaledCellCutoff D T A N) F hdecode hsmooth loss hb s
  refine ⟨K, hK, fun m u => ?_⟩
  have hbound := hKb m u
  change W.grading s (n08_scaledOperator (T.M (T.sample m) ^ N)
    (n08CellLayerMultiplier hT hW A m) u) ≤ _ at hbound
  rw [n08_scaledOperator_seminorm (W.grading s) (hsample m).le] at hbound
  have hdiv : W.grading s (n08CellLayerMultiplier hT hW A m u) ≤
      (K * W.grading (s + loss) u) / T.M (T.sample m) ^ N :=
    (le_div_iff₀ (hsample m)).mpr (by simpa only [mul_comm] using hbound)
  exact hdiv.trans_eq (by ring)

end ContinuousFlexibility.Statements
