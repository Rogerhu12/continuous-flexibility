module

public import ContinuousFlexibility.Analysis.N05CanonicalSampleBlockWeights
public import ContinuousFlexibility.Analysis.N05CanonicalFiniteBlockSums
public import ContinuousFlexibility.Analysis.N05ActualWeightKernelSums
public import ContinuousFlexibility.Analysis.N05SchurMembership

/-!
# The weighted L² output of the actual global inverse

Finite source truncations have the exact block sums of the fixed global
inverse. Their coordinates converge to its actual output by the continuous
source-level restriction. The Schur membership theorem is then applied to
that very output sequence, before any weighted membership is assumed.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped BigOperators Topology

/-- The actual zero-coordinate output has material loss four. The bound
is chosen before the angular order and the source. The output is identified
coordinate by coordinate with the already fixed global inverse. -/
theorem n05CanonicalGlobalInverse_weighted_l2_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ γ δ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    (hγ : |γ - β| ≤ δ) (hmargin : δ < ρ) {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G) (t : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℕ,
      ∀ v : (n05CanonicalVolumeModel T S K).level γ t s,
      ∃ w : CanonicalL2Sequence S K,
        (∀ k, w k = (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
          (n05CanonicalGlobalInverse D S C K G
            ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 k) ∧
        ‖w‖ ≤ B * ‖v‖ := by
  have hgap : β - ρ < γ := by
    have hh := (abs_le.mp hγ).1
    linarith only [hh, hmargin]
  obtain ⟨Cb, c, hCb, hblock⟩ := n05_canonicalInverseBlock_weighted_bound
    hD hT hS h hcoordinates hminus hplus hγ hGminus hGplus t
  obtain ⟨b, hb, _, hfiber, _⟩ := hcoordinates.2
  obtain ⟨B0, hB0, hnon, hrow, hcol⟩ := n05_actualWeightKernel_sums
    hD.1 hT K.cell hb.le hfiber t c (ρ - δ) (sub_pos.mpr hmargin)
  let a : ℕ → ℕ → ℝ := fun k m => Cb * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m
  let B : ℝ := Cb * B0
  have hB : 0 < B := mul_pos hCb hB0
  have ha (k m : ℕ) : 0 ≤ a k m := mul_nonneg hCb.le (hnon k m)
  have hrowa (k : ℕ) : Summable (fun m => a k m) ∧ (∑' m, a k m) ≤ B := by
    refine ⟨(hrow k).1.mul_left Cb, ?_⟩
    change (∑' m, Cb * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m) ≤ Cb * B0
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hrow k).2 hCb.le
  have hcola (m : ℕ) : Summable (fun k => a k m) ∧ (∑' k, a k m) ≤ B := by
    refine ⟨(hcol m).1.mul_left Cb, ?_⟩
    change (∑' k, Cb * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m) ≤ Cb * B0
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hcol m).2 hCb.le
  refine ⟨B, hB, fun s v => ?_⟩
  let hone : ∀ m : ℕ, ‖(fun _ : ℕ => (1 : ℝ)) m‖ ≤ 1 := fun _ => by norm_num
  let x : CanonicalL2Sequence S K :=
    n05CanonicalWeightedZeroMap S K s (fun _ => 1) 1 zero_le_one hone v
  have hx (m : ℕ) : x m = v.val m 0 := by
    simpa only [one_smul] using
      n05CanonicalWeightedZeroMap_apply S K s (fun _ => 1) 1 zero_le_one hone v m
  have hxn : ‖x‖ ≤ ‖v‖ := by
    change ‖n05CanonicalWeightedZeroMap S K s (fun _ => 1) 1 zero_le_one hone v‖ ≤
      ‖(show n05CanonicalClosedSubmodule S K s from v)‖
    exact (n05CanonicalWeightedZeroMap_bound S K s (fun _ => 1) 1 zero_le_one hone v).trans_eq
      (one_mul _)
  let y : CanonicalSequence S K := fun k =>
    (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 k
  have hsum (k : ℕ) : Summable (fun m => a k m * ‖x m‖) :=
    ((hrowa k).1.mul_right ‖x‖).of_nonneg_of_le
      (fun m => mul_nonneg (ha k m) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num) x m) (ha k m))
  have hy (k : ℕ) : ‖y k‖ ≤ ∑' m, a k m * ‖x m‖ := by
    have ht := (n05CanonicalGlobalInverse_finite_coordinate_tendsto
      hD hT hS h hcoordinates hminus hgap hGminus t s v k).const_smul
        (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹
    apply le_of_tendsto' ht.norm
    intro q
    change ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
      (n05CanonicalGlobalInverse D S C K G
        ((n05CanonicalVolumeModel T S K).forget γ t s
          (n05CanonicalFiniteTruncate S K s q v))).1 k‖ ≤ _
    rw [n05CanonicalGlobalInverse_finite_block_sum
      hD hT hS h hcoordinates hminus hgap hGminus t s v q k, Finset.smul_sum]
    calc
      _ ≤ ∑ m ∈ q, ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
          n05CanonicalInverseBlock D S C K G k m
            (n05CanonicalSampleWeight T S K γ t m • v.val m 0)‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ q, a k m * ‖x m‖ := by
        apply Finset.sum_le_sum
        intro m hm
        simpa only [a, hx] using hblock k m (v.val m 0)
      _ ≤ ∑' m, a k m * ‖x m‖ :=
        Summable.sum_le_tsum q (fun m _ => mul_nonneg (ha k m) (norm_nonneg _)) (hsum k)
  have hymem : Memℓp y 2 := n05_schur_memℓp a hB.le hB.le ha hrowa hcola x y hy
  let w : CanonicalL2Sequence S K := ⟨y, hymem⟩
  have hn : ‖w‖ ≤ Real.sqrt (B * B) * ‖x‖ :=
    n05_schur_lp_norm a hB.le hB.le ha hrowa hcola x w hy
  rw [← sq B, Real.sqrt_sq hB.le] at hn
  exact ⟨w, fun _ => rfl, hn.trans (mul_le_mul_of_nonneg_left hxn hB.le)⟩

end ContinuousFlexibility.Statements
