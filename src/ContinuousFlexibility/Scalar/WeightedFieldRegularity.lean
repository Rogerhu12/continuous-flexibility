module

public import ContinuousFlexibility.Scalar.WeightedStateFlatness
public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise

/-!
# Regularity of the even/odd scalar field encoding

The odd summand is the actual angular derivative of an even decoded height.
It inherits global smoothness and every flat jet, and it vanishes outside
the same radial interval, including both endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open scoped ContDiff

theorem mixedDerivative_add_of_contDiff {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f q + g q) p =
      mixedDerivative a b f p + mixedDerivative a b g p := by
  have hs (r : ℝ) :
      iteratedDeriv b (fun θ => f (r, θ) + g (r, θ)) p.2 =
        iteratedDeriv b (fun θ => f (r, θ)) p.2 +
          iteratedDeriv b (fun θ => g (r, θ)) p.2 :=
    iteratedDeriv_fun_add
      ((hf.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
      ((hg.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by simp))
  have hf' : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => f (r, θ)) p.2) := by
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      (contDiff_mixedDerivative hf 0 b).comp (contDiff_id.prodMk contDiff_const)
  have hg' : ContDiff ℝ ∞ (fun r => iteratedDeriv b (fun θ => g (r, θ)) p.2) := by
    simpa only [Function.comp_def, mixedDerivative, iteratedDeriv_zero, id_eq] using
      (contDiff_mixedDerivative hg 0 b).comp (contDiff_id.prodMk contDiff_const)
  unfold mixedDerivative
  simp_rw [hs]
  exact iteratedDeriv_fun_add (hf'.contDiffAt.of_le (by simp)) (hg'.contDiffAt.of_le (by simp))

theorem UniformFlatJets.add {D : ReferenceData} {f g : PolarPoint → ℝ}
    (hf : UniformFlatJets D f) (hg : UniformFlatJets D g)
    (hcf : ContDiff ℝ ∞ f) (hcg : ContDiff ℝ ∞ g) :
    UniformFlatJets D (fun p => f p + g p) := by
  intro a b k ε hε
  obtain ⟨δf, hδf, hfb⟩ := hf a b k (ε / 2) (half_pos hε)
  obtain ⟨δg, hδg, hgb⟩ := hg a b k (ε / 2) (half_pos hε)
  refine ⟨min δf δg, lt_min hδf hδg, fun r θ hr hθ hnear => ?_⟩
  rw [mixedDerivative_add_of_contDiff hcf hcg, mul_add]
  calc
    _ ≤ |endpointDistance D r ^ (-(k : ℤ)) * mixedDerivative a b f (r, θ)| +
        |endpointDistance D r ^ (-(k : ℤ)) * mixedDerivative a b g (r, θ)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (hfb r θ hr hθ (hnear.trans_le (min_le_left _ _)))
      (hgb r θ hr hθ (hnear.trans_le (min_le_right _ _)))
    _ = ε := by ring

theorem UniformFlatJets.angularPartial {D : ReferenceData} {f : PolarPoint → ℝ}
    (hf : UniformFlatJets D f) (hcf : ContDiff ℝ ∞ f) :
    UniformFlatJets D (angularPartial f) := by
  intro a b k ε hε
  obtain ⟨δ, hδ, hb⟩ := hf a (b + 1) k ε hε
  refine ⟨δ, hδ, fun r θ hr hθ hnear => ?_⟩
  rw [mixedDerivative_angularPartial isOpen_univ hcf.contDiffOn a b (mem_univ _)]
  exact hb r θ hr hθ hnear

theorem scalarFieldDecode_contDiff_and_flatJets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarFieldSpace S) :
    ContDiff ℝ ∞ (scalarFieldDecode S u) ∧ UniformFlatJets D (scalarFieldDecode S u) := by
  obtain ⟨he, hfe⟩ := scalarHeight_decode_contDiff_and_flatJets hT hS u.1
  obtain ⟨ho, hfo⟩ := scalarHeight_decode_contDiff_and_flatJets hT hS u.2
  have hθ : ContDiff ℝ ∞ (angularPartial ((S.height scalarBeta).decode u.2)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_angularPartial ho.contDiffAt (by simp)
  exact ⟨he.add hθ, hfe.add (hfo.angularPartial ho) he hθ⟩

theorem scalarFieldDecode_eq_zero_outside
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (u : ScalarFieldSpace S) {p : PolarPoint} (hp : p ∉ annularOpen D) :
    scalarFieldDecode S u p = 0 := by
  have he := ((hS.1 scalarBeta).2.2.2.1 u.1).2.2.2.1 p hp
  have ho := ((hS.1 scalarBeta).2.2.2.1 u.2).2.2.2.1
  have hc := (scalarHeight_decode_contDiff_and_flatJets hT hS u.2).1
  have hs : (fun θ => (S.height scalarBeta).decode u.2 (p.1, θ)) = fun _ => 0 := by
    funext θ
    apply ho
    intro h
    exact hp ⟨h.1, mem_univ _⟩
  have hd := Radial.hasDerivAt_angularSlice (hc.differentiable (by simp) p)
  rw [hs] at hd
  have hθ : angularPartial ((S.height scalarBeta).decode u.2) p = 0 :=
    hd.unique (hasDerivAt_const p.2 (0 : ℝ))
  simp only [scalarFieldDecode, he, hθ, add_zero]

end ContinuousFlexibility.Statements
