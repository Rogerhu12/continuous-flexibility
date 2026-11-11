import ContinuousFlexibility.Analysis.PeriodicGermCollar
import ContinuousFlexibility.Analysis.N04bFieldRegularity
import ContinuousFlexibility.Analysis.N04bRootCoefficientGerms
import ContinuousFlexibility.Scalar.GreenIdentity

/-!
# A genuine uniform collar for the corrected coefficient germs

N03 gives equality with the original coefficients on a neighborhood of
each point of a physical root circle. The actual coefficient periodicity
reduces these neighborhoods to one compact angular period. The resulting
single radial collar is valid at every real angle, for the fixed state
and root under consideration.

No uniformity over states or over distinct roots is asserted here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped Topology ContDiff

/-- The actual state height inherits angular periodicity from the decoded
physical height space; its radial summands do not affect the period. -/
theorem n04b_stateHeight_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) :
    Function.Periodic (stateHeight D S C z) (0, Real.pi) := by
  have hm := (hS.1 (3 / 4 : ℝ)).2.2.2.1 z.1.1.1
  have hp := hm.2.2.1
  intro p
  simp only [stateHeight, stateU, heightPairField, Prod.fst_add, add_zero, hp p]

/-- The original actual coefficient functions are periodic before any
corrected coefficient regularity is used. -/
theorem n04b_originalCoefficients_periodic
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hS : IsPhysicalSpaces D T S)
    (z : AnnularState S × ℝ) (r : ℝ) :
    Function.Periodic (fun θ => (originalCoefficients D S C z).a (r, θ)) Real.pi ∧
      Function.Periodic (fun θ => (originalCoefficients D S C z).b (r, θ)) Real.pi ∧
      Function.Periodic (fun θ => (originalCoefficients D S C z).c (r, θ)) Real.pi := by
  have hp := periodic_heightCorrectedCoefficients
    (stateProfile D S C z.1) (n04b_stateHeight_periodic (C := C) hS z)
  refine ⟨?_, ?_, ?_⟩ <;> intro θ
  · simpa only [originalCoefficients, Prod.mk_add_mk, add_zero] using hp.1 (r, θ)
  · simpa only [originalCoefficients, Prod.mk_add_mk, add_zero] using hp.2.1 (r, θ)
  · simpa only [originalCoefficients, Prod.mk_add_mk, add_zero] using hp.2.2 (r, θ)

/-- A full two-sided radial collar, common to every angle, on which all
three corrected coefficients equal the actual original coefficients. -/
theorem n04b_through03_root_coefficient_collar
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    (hL : N04bFieldRegularity D S C L base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo D.a D.b)
    (hroot : deriv D.w r₀ = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r θ : ℝ, |r - r₀| < δ →
      r ∈ Ioo D.a D.b ∧
      (L.coefficients z).a (r, θ) = (originalCoefficients D S C z).a (r, θ) ∧
      (L.coefficients z).b (r, θ) = (originalCoefficients D S C z).b (r, θ) ∧
      (L.coefficients z).c (r, θ) = (originalCoefficients D S C z).c (r, θ) := by
  let Q : PolarPoint → Prop := fun p =>
    r₀ + p.1 ∈ Ioo D.a D.b ∧
      (L.coefficients z).b (r₀ + p.1, p.2) =
        (originalCoefficients D S C z).b (r₀ + p.1, p.2) ∧
      (L.coefficients z).c (r₀ + p.1, p.2) =
        (originalCoefficients D S C z).c (r₀ + p.1, p.2)
  have hperiod : ∀ t θ, Q (t, θ + Real.pi) ↔ Q (t, θ) := by
    intro t θ
    by_cases ht : r₀ + t ∈ Ioo D.a D.b
    · have hl := hL.periodic_coefficients z hz hs (r₀ + t) ht
      have ho := n04b_originalCoefficients_periodic (C := C) hS z (r₀ + t)
      simp only [Q, hl.2.1 θ, hl.2.2 θ, ho.2.1 θ, ho.2.2 θ]
    · simp only [Q, ht, false_and]
  have hlocal : ∀ θ : ℝ, ∀ᶠ p in 𝓝 (0, θ), Q p := by
    intro θ
    have hg := h03.2.2.2.1 z hz hs (r₀, θ) ⟨hr₀, mem_univ _⟩ hroot
    have hmem : ∀ᶠ p in 𝓝 (r₀, θ), p ∈ annularOpen D :=
      (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hr₀, mem_univ _⟩
    have hshift : Continuous (fun p : PolarPoint => (r₀ + p.1, p.2)) :=
      (continuous_const.add continuous_fst).prodMk continuous_snd
    have ht : Tendsto (fun p : PolarPoint => (r₀ + p.1, p.2))
        (𝓝 (0, θ)) (𝓝 (r₀, θ)) := by
      simpa only [add_zero] using (hshift.continuousAt (x := (0, θ))).tendsto
    filter_upwards [ht.eventually (hmem.and (hg.1.and hg.2))] with p hp
    exact ⟨hp.1.1, hp.2.1, hp.2.2⟩
  obtain ⟨δ, hδ, hc⟩ :=
    exists_uniform_periodic_collar_of_local Real.pi_ne_zero hperiod hlocal
  refine ⟨δ, hδ, ?_⟩
  intro r θ hr
  have hp := hc (r - r₀) θ hr
  have hshift : r₀ + (r - r₀) = r := by ring
  have he : r ∈ Ioo D.a D.b ∧
      (L.coefficients z).b (r, θ) = (originalCoefficients D S C z).b (r, θ) ∧
      (L.coefficients z).c (r, θ) = (originalCoefficients D S C z).c (r, θ) := by
    simpa only [Q, hshift] using hp
  exact ⟨he.1, h03.2.1 z hz hs (r, θ), he.2⟩

end ContinuousFlexibility.Analysis
