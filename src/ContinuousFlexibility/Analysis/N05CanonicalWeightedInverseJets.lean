module

public import ContinuousFlexibility.Analysis.N05CanonicalWeightedAngularBlock
public import ContinuousFlexibility.Analysis.N05CanonicalInverseJetLinearity
public import ContinuousFlexibility.Analysis.N05ActualWeightKernelSums
public import ContinuousFlexibility.Analysis.N05SchurMembership

/-!
# Schur membership for the genuine fixed inverse jets

Each weighted output is defined from the already fixed global inverse.
Its actual finite source truncations converge to that very jet, through
the continuous linear restriction proved from weak derivative uniqueness.
Schur then proves membership of this actual weighted sequence.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped BigOperators Topology

theorem n05CanonicalGlobalInverse_weighted_jet_bound
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {base loss : ℕ} {ε : ℝ}
    (hD : IsRadialReference D) (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough04 D T S C R L K base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    {β ρ γ δ M0 M1 : ℝ} (hminus : 0 < β - ρ) (hplus : 0 < β + ρ)
    (hγ : |γ - β| ≤ δ) (hmargin : δ < ρ) {G : RadialSource → RadialUnknown}
    (hGminus : ReferenceInverseProperties D (β - ρ) M0 M1 G)
    (hGplus : ReferenceInverseProperties D (β + ρ) M0 M1 G) (t : ℝ) (s : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (v : (n05CanonicalVolumeModel T S K).level γ t s) (j : Fin (s + 1)),
      ∃ w : CanonicalL2Sequence S K,
        (∀ k, w k = (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
          n05CanonicalAngularJetSequence S K
            (n05CanonicalGlobalInverse D S C K G
              ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 j.val k) ∧
        ‖w‖ ≤ B * ‖v‖ := by
  have hgap : β - ρ < γ := by
    have hh := (abs_le.mp hγ).1
    linarith only [hh, hmargin]
  obtain ⟨c, hblocks⟩ := n05_canonicalAngularInverseBlock_weighted_bound
    hD hT hS h hcoordinates hminus hplus hγ hGminus hGplus t
  obtain ⟨Cb, hCb, hblock⟩ := hblocks s
  obtain ⟨b, hb, _, hfiber, _⟩ := hcoordinates.2
  obtain ⟨B0, hB0, hnon, hrow, hcol⟩ := n05_actualWeightKernel_sums
    hD.1 hT K.cell hb.le hfiber t c (ρ - δ) (sub_pos.mpr hmargin)
  let a : ℕ → ℕ → ℝ := fun k m => Cb * n05ActualWeightKernel D T K.cell t c (ρ - δ) k m
  let B := Cb * B0
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
  refine ⟨B, hB, fun v j => ?_⟩
  let x : CanonicalVolumeJets S K s := v.val
  let y : CanonicalSequence S K := fun k =>
    (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
      n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s v)).1 j.val k
  have hsum (k : ℕ) : Summable (fun m => a k m * ‖x m‖) :=
    ((hrowa k).1.mul_right ‖x‖).of_nonneg_of_le
      (fun m => mul_nonneg (ha k m) (norm_nonneg _))
      (fun m => mul_le_mul_of_nonneg_left
        (lp.norm_apply_le_norm (by norm_num) x m) (ha k m))
  have hy (k : ℕ) : ‖y k‖ ≤ ∑' m, a k m * ‖x m‖ := by
    have ht := (n05CanonicalGlobalInverse_finite_jet_tendsto
      hD hT hS h hcoordinates hminus hGminus hgap t s v j k).const_smul
        (n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹
    apply le_of_tendsto' ht.norm
    intro q
    change ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
      n05CanonicalAngularJetSequence S K
        (n05CanonicalGlobalInverse D S C K G
          ((n05CanonicalVolumeModel T S K).forget γ t s
            (n05CanonicalFiniteTruncate S K s q v))).1 j.val k‖ ≤
      ∑' m, a k m * ‖x m‖
    rw [n05CanonicalGlobalInverse_finite_jet_sum
      hD hT hS h hcoordinates hminus hGminus hgap t s v q j k, Finset.smul_sum]
    calc
      _ ≤ ∑ m ∈ q, ‖(n05CanonicalSampleWeight T S K γ (t - 4) k)⁻¹ •
          n05CanonicalAngularJetSequence S K
            (n05CanonicalGlobalInverse D S C K G
              (Pi.single m (n05CanonicalSampleWeight T S K γ t m • v.val m 0))).1 j.val k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ m ∈ q, a k m * ‖x m‖ := by
        apply Finset.sum_le_sum
        intro m hm
        exact hblock k m v j
      _ ≤ ∑' m, a k m * ‖x m‖ :=
        Summable.sum_le_tsum q (fun m _ => mul_nonneg (ha k m) (norm_nonneg _)) (hsum k)
  have hymem : Memℓp y 2 := n05_schur_memℓp a hB.le hB.le ha hrowa hcola x y hy
  let w : CanonicalL2Sequence S K := ⟨y, hymem⟩
  have hn : ‖w‖ ≤ Real.sqrt (B * B) * ‖x‖ :=
    n05_schur_lp_norm a hB.le hB.le ha hrowa hcola x w hy
  rw [← sq B, Real.sqrt_sq hB.le] at hn
  refine ⟨w, fun _ => rfl, ?_⟩
  simpa only [x, Submodule.norm_coe] using hn

end ContinuousFlexibility.Statements
