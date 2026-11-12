import ContinuousFlexibility.Analysis.N06NormalizerRetype
import ContinuousFlexibility.Analysis.N06NormalizerGraphShear
import ContinuousFlexibility.Analysis.N06CompatibilityFourierSource

/-!
# The source shear is exactly the new physical reference relation

The shifted graph is characterized by the literal reference equation
with the new normalizer. The physical source changes by
lambda times the old-minus-new normalizer, so the compatible source in
ReferenceGraph is unchanged. The underlying height representation and
all material parameters are the original ones.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency true

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {K : CanonicalData S}
  {V : VolumeModelData S K} {b : ℕ}

def n06NormalizerLambda (S : PhysicalSpacesData) (K : CanonicalData S) :
    CanonicalUnknown S K →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (CanonicalL2Sequence S K) (ℝ × ℝ × ℝ)))

theorem n06NormalizerLambda_apply (U : CanonicalUnknown S K) :
    n06NormalizerLambda S K U = U.2.2.2 := by
  simp only [n06NormalizerLambda, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd']

private theorem n06_normalizer_source_add_cancel
    (ψ : (S.height (3 / 4 : ℝ)).Space) (f : PolarPoint → ℝ) (c : ℝ) :
    (fun p => (f p + c * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p) -
      c * (S.height (3 / 4 : ℝ)).decode S.psi p) =
      fun p => f p - c * (S.height (3 / 4 : ℝ)).decode ψ p := by
  funext p
  simp only [map_sub, Pi.sub_apply]
  ring

private theorem n06_normalizer_source_sub_cancel
    (ψ : (S.height (3 / 4 : ℝ)).Space) (f : PolarPoint → ℝ) (c : ℝ) :
    (fun p => (f p - c * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p) -
      c * (S.height (3 / 4 : ℝ)).decode ψ p) =
      fun p => f p - c * (S.height (3 / 4 : ℝ)).decode S.psi p := by
  funext p
  simp only [map_sub, Pi.sub_apply]
  ring

/-- The shift is an equality of the original physical relation, not a
new definition of that relation in terms of a proposed solution map. -/
theorem n06_normalizer_referenceRelation_iff
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (d : V.level (3 / 4 : ℝ) 0 b)
    (hd : ∀ m, (V.forget (3 / 4 : ℝ) 0 b d m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ)))
    (γ M₀ M₁ loss : ℝ) (U : CanonicalUnknown S K)
    (F : V.level (3 / 4 : ℝ) 0 b) :
    ReferenceCanonicalRelation D T (n06WithNormalizer S ψ)
        (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) (n06NormalizerVolume V ψ)
        γ M₀ M₁ loss U ((n06NormalizerVolume V ψ).forget (3 / 4 : ℝ) 0 b F) ↔
      ReferenceCanonicalRelation D T S C K V γ M₀ M₁ loss U
        (V.forget (3 / 4 : ℝ) 0 b (F + U.2.2.2 • d)) := by
  constructor
  · rintro ⟨hmember, η, f, hrep, hgraph⟩
    refine ⟨hmember, η,
      (fun p => f p + U.2.2.2 * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p),
      ⟨hrep.1, ?_⟩, ?_⟩
    · intro m
      exact n06Volume_forget_source_add_smul_ae F d U.2.2.2 (C.referenceState, 0) m
        (hrep.2 m) (hd m)
    · change ReferenceGraph D γ M₀ M₁ (η, U.2.2.1)
        ((fun p => (f p + U.2.2.2 * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p) -
          U.2.2.2 * (S.height (3 / 4 : ℝ)).decode S.psi p), 0)
      rw [n06_normalizer_source_add_cancel]
      exact hgraph
  · rintro ⟨hmember, η, f, hrep, hgraph⟩
    refine ⟨hmember, η,
      (fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p),
      ⟨hrep.1, ?_⟩, ?_⟩
    · intro m
      have hh := n06Volume_forget_source_sub_smul_ae
        (F + U.2.2.2 • d) d U.2.2.2 (C.referenceState, 0) m (hrep.2 m) (hd m)
      have hc : F + U.2.2.2 • d - U.2.2.2 • d = F :=
        add_sub_cancel_right F (U.2.2.2 • d)
      change (V.forget (3 / 4 : ℝ) 0 b F m : PolarPoint → ℝ)
        =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
          (fun p => f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p)
      simpa only [hc] using hh
    · change ReferenceGraph D γ M₀ M₁ (η, U.2.2.1)
        ((fun p => (f p - U.2.2.2 * (S.height (3 / 4 : ℝ)).decode (S.psi - ψ) p) -
          U.2.2.2 * (S.height (3 / 4 : ℝ)).decode ψ p), 0)
      rw [n06_normalizer_source_sub_cancel]
      exact hgraph

theorem n06_normalizer_graph_iff_referenceRelation
    {B : CanonicalDomainData S K V b}
    (h05 : N05Properties D T S C K V b B)
    (ψ : (S.height (3 / 4 : ℝ)).Space)
    (d : V.level (3 / 4 : ℝ) 0 b)
    (hd : ∀ m, (V.forget (3 / 4 : ℝ) 0 b d m : PolarPoint → ℝ)
      =ᵐ[canonicalMeasure S K m] canonicalSource S K (C.referenceState, 0) m
        ((S.height (3 / 4 : ℝ)).decode (S.psi - ψ)))
    (x : CanonicalUnknown S K × V.level (3 / 4 : ℝ) 0 b) :
    x ∈ n06NormalizerGraph B.graph (n06NormalizerLambda S K) d ↔
      ReferenceCanonicalRelation D T (n06WithNormalizer S ψ)
        (n06NormalizerGeometry C ψ) (n06NormalizerCanonical K ψ) (n06NormalizerVolume V ψ)
        B.weakExponent B.sourceMaterial B.outputMaterial B.lossMaterial x.1
        ((n06NormalizerVolume V ψ).forget (3 / 4 : ℝ) 0 b x.2) := by
  rw [n06NormalizerGraph_mem, n06NormalizerLambda_apply]
  exact (h05.2.2.2.2.2.2.1 _).trans
    (n06_normalizer_referenceRelation_iff ψ d hd
      B.weakExponent B.sourceMaterial B.outputMaterial B.lossMaterial x.1 x.2).symm

end ContinuousFlexibility.Statements
