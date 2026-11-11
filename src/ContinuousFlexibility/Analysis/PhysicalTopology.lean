import ContinuousFlexibility.Analysis.ReturnCorrectionSource
import ContinuousFlexibility.Analysis.ProjectiveDifferential

/-!
# Physical norms detect the actual height and source topologies

The supplied norm identities identify convergence in every projective
coordinate with convergence of the actual weighted physical norms.
The source carries the induced topology of the existing compatibility
kernel, so the same criterion applies there without a new completion.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Filter ContinuousFlexibility.Analysis
open scoped Topology

variable {D : ReferenceData} {T : MaterialData} {γ : ℝ} {H : SobolevModelData}

def heightRealize (hH : IsSobolevModel D T γ H) (f : PolarPoint → ℝ)
    (hf : HeightMember D T γ f) : H.Space :=
  (hH.2.2.2.2.1 f hf).choose

theorem heightRealize_decode (hH : IsSobolevModel D T γ H) (f : PolarPoint → ℝ)
    (hf : HeightMember D T γ f) : H.decode (heightRealize hH f hf) = f :=
  (hH.2.2.2.2.1 f hf).choose_spec

theorem height_tendsto_iff_physicalNorm (hH : IsSobolevModel D T γ H)
    {α : Type*} {l : Filter α} (u : α → H.Space) (v : H.Space) :
    Tendsto u l (𝓝 v) ↔
      ∀ s, Tendsto (fun a => physicalNorm T γ s (H.decode (u a - v))) l (𝓝 0) := by
  have hn : ∀ w : H.Space, ∀ s, ‖w.val s‖ = physicalNorm T γ s (H.decode w) :=
    hH.2.2.2.2.2.2.2
  have hsub (a : α) (s : ℕ) : (u a - v).val s = (u a).val s - v.val s := by
    simpa only [projectiveCoordinate_apply] using
      (projectiveCoordinate (fun s => H.level s) H.bond s).map_sub (u a) v
  rw [tendsto_projectiveLimit_iff]
  constructor
  · intro h s
    have hs := tendsto_iff_norm_sub_tendsto_zero.mp (h s)
    simpa only [← hn, hsub] using hs
  · intro h s
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [← hn, hsub] using h s

theorem height_hasProjectiveCurveDerivAt_iff_physicalNorm
    (hH : IsSobolevModel D T γ H) (c : ℝ → H.Space) (dc : H.Space) (t : ℝ) :
    HasProjectiveCurveDerivAt c dc t ↔
      ∀ s, Tendsto (fun h : ℝ => physicalNorm T γ s
        (H.decode (h⁻¹ • (c (t + h) - c t) - dc))) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
  height_tendsto_iff_physicalNorm hH (fun h : ℝ => h⁻¹ • (c (t + h) - c t)) dc

variable {S : PhysicalSpacesData}

def physicalSourceRealize (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ)
    (hf : HeightMember D T (3 / 4 : ℝ) f) (hzero : physicalSourceIntegral D f = 0) :
    S.Source :=
  ((physicalSourceDecode_mem_range_iff hS f).mpr ⟨hf, hzero⟩).choose

theorem physicalSourceRealize_decode (hS : IsPhysicalSpaces D T S) (f : PolarPoint → ℝ)
    (hf : HeightMember D T (3 / 4 : ℝ) f) (hzero : physicalSourceIntegral D f = 0) :
    physicalSourceDecode S (physicalSourceRealize hS f hf hzero) = f :=
  ((physicalSourceDecode_mem_range_iff hS f).mpr ⟨hf, hzero⟩).choose_spec

theorem source_tendsto_iff_physicalNorm (hS : IsPhysicalSpaces D T S)
    {α : Type*} {l : Filter α} (u : α → S.Source) (v : S.Source) :
    Tendsto u l (𝓝 v) ↔
      ∀ s, Tendsto (fun a => physicalNorm T (3 / 4 : ℝ) s
        (physicalSourceDecode S (u a - v))) l (𝓝 0) := by
  rw [tendsto_subtype_rng]
  exact height_tendsto_iff_physicalNorm (hS.1 (3 / 4 : ℝ)) (fun a => (u a).val) v.val

theorem source_hasProjectiveCurveDerivAt_iff_height
    (c : ℝ → S.Source) (dc : S.Source) (t : ℝ) :
    HasProjectiveCurveDerivAt c dc t ↔
      HasProjectiveCurveDerivAt (fun a => (c a).val) dc.val t := by
  unfold HasProjectiveCurveDerivAt
  exact tendsto_subtype_rng

theorem source_hasProjectiveCurveDerivAt_iff_physicalNorm
    (hS : IsPhysicalSpaces D T S) (c : ℝ → S.Source) (dc : S.Source) (t : ℝ) :
    HasProjectiveCurveDerivAt c dc t ↔
      ∀ s, Tendsto (fun h : ℝ => physicalNorm T (3 / 4 : ℝ) s
        (physicalSourceDecode S (h⁻¹ • (c (t + h) - c t) - dc)))
          (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
  source_tendsto_iff_physicalNorm hS (fun h : ℝ => h⁻¹ • (c (t + h) - c t)) dc

end ContinuousFlexibility.Statements
