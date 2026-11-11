import ContinuousFlexibility.Statements.N07aCanonicalGeometry

/-!
# One normal form for the actual root and cut first jets

This is extracted from the primitive forward-chart data. The number
`jump` is zero at a root and `-(2 * cutRadius)⁻¹` at a middle cut.
The same numbers work at the reference state and at every current state.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements CanonicalGeometry

structure N07aInterfaceJetData (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (K : CanonicalData S) (base : ℕ) (ε : ℝ) (i j : ℕ) where
  endpointLeft : ℝ
  endpointRight : ℝ
  orientationLeft : ℝ
  orientationRight : ℝ
  jump : ℝ
  orientationLeft_ne : orientationLeft ≠ 0
  orientationRight_ne : orientationRight ≠ 0
  jets : ∀ z, TransmissionParameter S C base ε z → ∀ θ : ℝ,
    let p : PolarPoint := (K.physicalRight i, θ)
    let Fi := endpointAlignedChart K z i endpointLeft orientationLeft
    let Fj := endpointAlignedChart K z j endpointRight orientationRight
    (Fi p).1 = 0 ∧ Fi p = Fj p ∧
    fderiv ℝ Fi p = fderiv ℝ Fj p ∧
    K.height z i p = K.height z j p ∧
    fderiv ℝ (K.height z j) p - fderiv ℝ (K.height z i) p =
      (jump * K.height z i p) • fderiv ℝ (fun q => (K.chart z i q).1) p

theorem n07a_interfaceJetData_exists {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (h : TransmissionGeometry D S C K base ε) {i j : ℕ}
    (hij : i ≠ j) (hboundary : K.physicalRight i = K.physicalLeft j) :
    Nonempty (N07aInterfaceJetData S C K base ε i j) := by
  rcases h.1 i j hij hboundary with hroot | ⟨k, hk⟩
  · obtain ⟨ei, ej, si, sj, _, _, hsi, hsj, hjets⟩ :=
      h.2.1 i j hij hboundary hroot
    refine ⟨⟨ei, ej, si, sj, 0, ?_, ?_, ?_⟩⟩
    · rcases hsi with rfl | rfl <;> norm_num
    · rcases hsj with rfl | rfl <;> norm_num
    · intro z hz θ
      obtain ⟨h0, hv, hd, hh, hdh⟩ := hjets z hz θ
      refine ⟨h0, hv, hd, hh, ?_⟩
      simp only [hdh, sub_self, zero_mul, zero_smul]
  · refine ⟨⟨K.cutRadius k, K.cutRadius k, 1, -1,
      -(2 * K.cutRadius k)⁻¹, one_ne_zero, by norm_num, ?_⟩⟩
    intro z hz θ
    have hcut := h.2.2 k z hz θ
    simp only [hk] at hcut
    refine ⟨hcut.1, hcut.2.1, hcut.2.2.1, hcut.2.2.2.1, ?_⟩
    have hscalar : -(K.height z i (K.physicalRight i, θ) / (2 * K.cutRadius k)) =
        -(2 * K.cutRadius k)⁻¹ * K.height z i (K.physicalRight i, θ) := by
      ring
    simpa only [hscalar] using hcut.2.2.2.2

end ContinuousFlexibility.Analysis
