module

public import ContinuousFlexibility.Scalar.WeightedFieldRegularity

/-!
# Global regularity of the actual weighted scalar coefficients

The decoded coefficients are differences from the two radial backgrounds
`w` and `w' / r`.  The second background is globally smooth: the positive
inner radius places the apparent division by zero inside an open region
where the numerator vanishes identically.  Both backgrounds have every
uniform flat jet at the actual radial endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

/-- Division by the radial coordinate preserves a smooth profile supported
away from zero, including its totalized value at zero. -/
theorem EndpointFlat.div_id {f : ℝ → ℝ} (hf : EndpointFlat D f) (ha : 0 < D.a) :
    EndpointFlat D (fun r => f r / r) := by
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
      filter_upwards [eventually_lt_nhds ha] with t ht
      simp only [hf.2 t (Or.inl ht.le), zero_div]
    · exact hf.1.contDiffAt.div contDiffAt_id hr
  · intro r hr
    change f r / r = 0
    rw [hf.2 r hr, zero_div]

theorem referenceProfile_deriv_div_radius_endpointFlat (hD : IsAccumulatingProfile D) :
    EndpointFlat D (fun r => deriv D.w r / r) := by
  have hw : EndpointFlat D D.w := hD.choose_spec.1.2.2.1
  have hd : EndpointFlat D (deriv D.w) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hw.iteratedDeriv 1
  exact hd.div_id hD.choose_spec.1.1

theorem scalarStateAB_eq_of_coefficient_decode
    (x : ScalarWeightedState S) (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p) :
    scalarStateA D S x = (fun p => scalarFieldDecode S (c 0) p + D.w p.1) ∧
      scalarStateB D S x = scalarFieldDecode S (c 1) := by
  constructor
  · funext p
    have h := hc 0 p
    change scalarFieldDecode S (c 0) p = scalarStateA D S x p - D.w p.1 at h
    linarith only [h]
  · funext p
    exact (hc 1 p).symm

theorem scalarStateCorrectedC_eq_of_coefficient_decode
    (x : ScalarWeightedState S) (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p) :
    scalarStateCorrectedC D S x =
      (fun p => scalarFieldDecode S (c 2) p + deriv D.w p.1 / p.1) := by
  funext p
  have h := hc 2 p
  change scalarFieldDecode S (c 2) p = scalarStateCorrectedC D S x p - deriv D.w p.1 / p.1 at h
  linarith only [h]

theorem scalarStateAB_contDiff_and_flatJets_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p) :
    (ContDiff ℝ ∞ (scalarStateA D S x) ∧ UniformFlatJets D (scalarStateA D S x)) ∧
      (ContDiff ℝ ∞ (scalarStateB D S x) ∧ UniformFlatJets D (scalarStateB D S x)) := by
  obtain ⟨hA, hB⟩ := scalarStateAB_eq_of_coefficient_decode x c hc
  have h₀ := scalarFieldDecode_contDiff_and_flatJets hT hS (c 0)
  have h₁ := scalarFieldDecode_contDiff_and_flatJets hT hS (c 1)
  have hw : EndpointFlat D D.w := hD.choose_spec.1.2.2.1
  have hcw : ContDiff ℝ ∞ (fun p : PolarPoint => D.w p.1) := hw.1.comp contDiff_fst
  rw [hA, hB]
  exact ⟨⟨h₀.1.add hcw, h₀.2.add hw.uniformFlatJets h₀.1 hcw⟩, h₁⟩

theorem scalarStateCorrectedC_contDiff_and_flatJets_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p) :
    ContDiff ℝ ∞ (scalarStateCorrectedC D S x) ∧
      UniformFlatJets D (scalarStateCorrectedC D S x) := by
  have h₂ := scalarFieldDecode_contDiff_and_flatJets hT hS (c 2)
  have href := referenceProfile_deriv_div_radius_endpointFlat hD
  have hcr : ContDiff ℝ ∞ (fun p : PolarPoint => deriv D.w p.1 / p.1) :=
    href.1.comp contDiff_fst
  rw [scalarStateCorrectedC_eq_of_coefficient_decode x c hc]
  exact ⟨h₂.1.add hcr, h₂.2.add href.uniformFlatJets h₂.1 hcr⟩

/-- The exact three-coefficient regularity clause in `IsWeightedS05` follows
from physical decoding; no additional regularity premise is required. -/
theorem scalarStateCoefficients_contDiff_and_flatJets_of_decode
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (x : ScalarWeightedState S)
    (c : Fin 3 → ScalarFieldSpace S)
    (hc : ∀ i p, scalarFieldDecode S (c i) p = scalarCoefficientComponent D S x i p) :
    ∀ coefficient ∈ ({scalarStateA D S x, scalarStateB D S x,
      scalarStateCorrectedC D S x} : Set (PolarPoint → ℝ)),
      ContDiff ℝ ∞ coefficient ∧ UniformFlatJets D coefficient := by
  intro coefficient hcoefficient
  simp only [mem_insert_iff, mem_singleton_iff] at hcoefficient
  obtain ⟨hA, hB⟩ := scalarStateAB_contDiff_and_flatJets_of_decode hD hT hS x c hc
  rcases hcoefficient with rfl | rfl | rfl
  · exact hA
  · exact hB
  · exact scalarStateCorrectedC_contDiff_and_flatJets_of_decode hD hT hS x c hc

end ContinuousFlexibility.Statements
