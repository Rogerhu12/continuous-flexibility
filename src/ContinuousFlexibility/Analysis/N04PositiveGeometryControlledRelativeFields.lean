import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledFiniteCalculus
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledRootFields
import ContinuousFlexibility.Analysis.CanonicalRootFiniteEndpointBounds

/-!
# Polynomial finite bounds for the actual relative root fields

The actual inverse-chart germs and exact root images turn the original
physical chart and height bounds into the relative endpoint data. Both
relative coordinate directions are estimated, so the positive diagonal
lower bound is derived from the true inverse first derivative.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

private theorem controlled_relative_envelope_identity (K M : ℝ) (d N : ℕ) :
    (2 : ℝ) ^ (N + 1) *
        (K * (K * (K * M ^ (d + 1)) ^ (N + 1)) ^ (N + 1)) ^ 2 =
      ((2 : ℝ) ^ (N + 1) * (K * (K * K ^ (N + 1)) ^ (N + 1)) ^ 2) *
        M ^ (((d + 1) * (N + 1) * (N + 1)) * 2) := by
  simp only [mul_pow, ← pow_mul, Nat.mul_assoc, mul_assoc]

private theorem controlled_rootBetween_radial
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    {z₀ z₁ : AnnularState S × ℝ}
    (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
    (hz₁ : z₁ ∈ stateNeighborhood S C base ε) (hs₁ : stateSector S z₁.1)
    (m : ℕ) (side : Bool) (θ : ℝ) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := n01ComponentRoot C m side
    (K.inverseChart z₁ i (K.chart z₀ i (r, θ))).1 = r := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  have hroot := canonicalCutRoot_mem_closed_and_zero hA hcut hz₀ hs₀ m side θ
  have hzero : K.inverseChart z₁ i '' ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) =
      ({r} ×ˢ (univ : Set ℝ)) := by
    cases side
    · exact (hcut.2 z₁ hz₁ hs₁ m).2.2.2.2.1
    · exact (hcut.2 z₁ hz₁ hs₁ m).2.2.2.2.2
  have hmem := mem_image_of_mem (K.inverseChart z₁ i)
    (show K.chart z₀ i (r, θ) ∈ ({(0 : ℝ)} ×ˢ (univ : Set ℝ)) from
      ⟨hroot.2, mem_univ _⟩)
  rw [hzero] at hmem
  exact hmem.1

/-- One polynomial, selected before all geometry and states, controls all
six actual endpoint input clauses from the finite original root fields. -/
theorem n04PositiveGeometry_exists_actual_relative_root_polynomial (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ degree : ℕ,
      ∀ {D : ReferenceData} {S : PhysicalSpacesData}
      {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ},
      CanonicalGeometry D S C K base ε → CanonicalCutGeometry S C K base ε →
      (C.referenceState, 0) ∈ stateNeighborhood S C base ε →
      stateSector S C.referenceState →
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
      ∀ m : ℕ, ∀ side : Bool, ∀ M : ℝ, 1 ≤ M →
      let i := if side then (K.cutPair m).2 else (K.cutPair m).1
      let r := n01ComponentRoot C m side
      N04PositiveGeometryFiniteRootFields (n + 2)
        (K.chart (C.referenceState, 0) i) (K.height (C.referenceState, 0) i) r M →
      N04PositiveGeometryFiniteRootFields (n + 2) (K.chart z i) (K.height z i) r M →
      RootEndpointJetBounds n (canonicalCurrentPoint C K z i)
        (n04CoordinatesCurrentHeightRatio C K z i) r
        (A * M ^ degree)⁻¹ (A * M ^ degree) (A * M ^ degree) := by
  let N := n + 2
  obtain ⟨CI, hCI, dI, hInv⟩ := n04PositiveGeometry_exists_planarInverse_prefix_polynomial N
  obtain ⟨CC, hCC, hComp⟩ := n04PositiveGeometry_exists_composition_prefix_polynomial
    (X := PolarPoint) (Y := PolarPoint) (Z := PolarPoint) N
  obtain ⟨CH, hCH, hHeightComp⟩ := n04PositiveGeometry_exists_composition_prefix_polynomial
    (X := PolarPoint) (Y := PolarPoint) (Z := ℝ) N
  let K₀ : ℝ := CI + CC + CH + 2
  have hK : 1 ≤ K₀ := by dsimp only [K₀]; linarith
  have hIK : CI ≤ K₀ := by dsimp only [K₀]; linarith
  have hCK : CC ≤ K₀ := by dsimp only [K₀]; linarith
  have hHK : CH ≤ K₀ := by dsimp only [K₀]; linarith
  let A : ℝ := (2 : ℝ) ^ (N + 1) * (K₀ * (K₀ * K₀ ^ (N + 1)) ^ (N + 1)) ^ 2
  let degree : ℕ := ((dI + 1) * (N + 1) * (N + 1)) * 2
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK
      (one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hK)))))
  refine ⟨A, hA, degree, ?_⟩
  intro D S C K base ε hgeometry hcut href hsref z hz hs m side M hM i r hraw₀ hraw
  let U : ℝ := K₀ * M ^ (dI + 1)
  let R : ℝ := K₀ * U ^ (N + 1)
  let Q : ℝ := K₀ * R ^ (N + 1)
  let V : ℝ := (2 : ℝ) ^ (N + 1) * Q ^ 2
  have grow {x : ℝ} (hx : 1 ≤ x) (k : ℕ) : x ≤ K₀ * x ^ (k + 1) := by
    calc
      x ≤ x ^ (k + 1) := by
        simpa only [pow_one] using pow_le_pow_right₀ hx (by omega : 1 ≤ k + 1)
      _ ≤ K₀ * x ^ (k + 1) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hK
          (pow_nonneg (zero_le_one.trans hx) _)
  have hMU : M ≤ U := grow hM dI
  have hU : 1 ≤ U := hM.trans hMU
  have hUR : U ≤ R := grow hU N
  have hR : 1 ≤ R := hU.trans hUR
  have hRQ : R ≤ Q := grow hR N
  have hQ : 1 ≤ Q := hR.trans hRQ
  have hQV : Q ≤ V := by
    calc
      Q ≤ Q ^ 2 := by
        simpa only [pow_one] using pow_le_pow_right₀ hQ (by decide : 1 ≤ 2)
      _ ≤ (2 : ℝ) ^ (N + 1) * Q ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) (sq_nonneg Q)
  have hV : 1 ≤ V := hQ.trans hQV
  have hMR : M ≤ R := hMU.trans hUR
  have hMQ : M ≤ Q := hMR.trans hRQ
  have hRV : R ≤ V := hRQ.trans hQV
  have hVeq : V = A * M ^ degree := controlled_relative_envelope_identity K₀ M dI N
  have hbetween (z₀ z₁ : AnnularState S × ℝ)
      (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
      (hz₁ : z₁ ∈ stateNeighborhood S C base ε) (hs₁ : stateSector S z₁.1)
      (hF₀ : N04PositiveGeometryFiniteRootFields N (K.chart z₀ i) (K.height z₀ i) r M)
      (hF₁ : N04PositiveGeometryFiniteRootFields N (K.chart z₁ i) (K.height z₁ i) r M)
      (θ : ℝ) :
      ContDiffAt ℝ ∞ (K.inverseChart z₁ i ∘ K.chart z₀ i) (r, θ) ∧
        ∀ k, 1 ≤ k → k ≤ N →
          ‖iteratedFDeriv ℝ k (K.inverseChart z₁ i ∘ K.chart z₀ i) (r, θ)‖ ≤ R := by
    have hc : (r, θ) ∈ physicalPieceClosed S K z₀ i :=
      (canonicalCutRoot_mem_closed_and_zero hgeometry hcut hz₀ hs₀ m side θ).1
    have hcanon : K.chart z₀ i (r, θ) ∈ canonicalClosed S K i :=
      (hgeometry.boundary z₀ hz₀ hs₀ i).1 hc
    let y := K.inverseChart z₁ i (K.chart z₀ i (r, θ))
    have hy : y = (r, y.2) := Prod.ext
      (controlled_rootBetween_radial hgeometry hcut hz₀ hs₀ hz₁ hs₁ m side θ) rfl
    have hyclosed : y ∈ physicalPieceClosed S K z₁ i :=
      (hgeometry.boundary z₁ hz₁ hs₁ i).2.1 hcanon
    have hFy := (hgeometry.boundary z₁ hz₁ hs₁ i).2.2.2.2.1 y hyclosed
    have hF0 := ((hgeometry.boundary z₀ hz₀ hs₀ i).2.2.2.2.1 (r, θ) hc).1
    have hG := n04b_inverseChart_contDiffAt_closed hgeometry hz₁ hs₁ i hcanon
    have hgerms := canonicalClosed_inverse_germs hgeometry hz₁ hs₁ i hcanon
    have hfirst : |planeJacobian (K.chart z₁ i) y|⁻¹ ≤ M := by
      rw [hy]
      exact hF₁.inverse_jacobian y.2
    have hjets : ∀ k, 1 ≤ k → k ≤ max 1 N →
        ‖iteratedFDeriv ℝ k (K.chart z₁ i) y‖ ≤ M := by
      intro k hk hkN
      rw [hy]
      exact hF₁.chart_jets y.2 k hk (by dsimp only [N] at hkN ⊢; omega)
    have hinverse := hInv hM (K.chart z₁ i) (K.inverseChart z₁ i)
      (K.chart z₀ i (r, θ)) hFy.1 hG hgerms.2 hgerms.1 hFy.2.2.1 hfirst hjets
    have hIM : CI * M ^ dI ≤ U := mul_le_mul hIK
      (pow_le_pow_right₀ hM (Nat.le_succ dI))
      (pow_nonneg (zero_le_one.trans hM) _) (zero_le_one.trans hK)
    refine ⟨hG.comp (r, θ) hF0, ?_⟩
    intro k hk hkN
    exact (hComp hU (K.inverseChart z₁ i) (K.chart z₀ i) (r, θ) hG hF0
      (fun j hj hjN => (hinverse j hj hjN).trans hIM)
      (fun j hj hjN => (hF₀.chart_jets θ j hj hjN).trans hMU) k hk hkN).trans
      (mul_le_mul_of_nonneg_right hCK (pow_nonneg (zero_le_one.trans hU) _))
  have hforward (θ : ℝ) := hbetween (C.referenceState, 0) z href hsref hz hs hraw₀ hraw θ
  have hinverse (θ : ℝ) := hbetween z (C.referenceState, 0) hz hs href hsref hraw hraw₀ θ
  let τ := canonicalCurrentPoint C K z i
  let q := n04CoordinatesCurrentHeightRatio C K z i
  have hscalar (f : PolarPoint → ℝ) (θ : ℝ)
      (hf : ContDiffAt ℝ ∞ f (τ (r, θ)))
      (hfj : ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k f (τ (r, θ))‖ ≤ M) :
      ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k (f ∘ τ) (r, θ)‖ ≤ Q := by
    intro k hkN
    by_cases hk : k = 0
    · subst k
      simpa only [norm_iteratedFDeriv_zero, Function.comp_apply] using
        (hfj 0 (Nat.zero_le N)).trans hMQ
    · exact (hHeightComp hR f τ (r, θ) hf (hforward θ).1
        (fun j _ hj => (hfj j hj).trans hMR)
        (fun j hj hjN => (hforward θ).2 j hj hjN) k (by omega) hkN).trans
        (mul_le_mul_of_nonneg_right hHK (pow_nonneg (zero_le_one.trans hR) _))
  have hheights (θ : ℝ) :
      (∀ k, k ≤ N → ‖iteratedFDeriv ℝ k q (r, θ)‖ ≤ V) ∧
      (∀ k, k ≤ N → ‖iteratedFDeriv ℝ k (fun p => (q p)⁻¹) (r, θ)‖ ≤ V) := by
    have hc := (canonicalCutRoot_mem_closed_and_zero hgeometry hcut href hsref m side θ).1
    have hreg0 := (hgeometry.boundary _ href hsref i).2.2.2.2.1 (r, θ) hc
    have hy : τ (r, θ) = (r, (τ (r, θ)).2) := Prod.ext
      (canonicalCurrentPoint_root_radial hgeometry hcut href hsref hz hs m side θ) rfl
    have hcy : τ (r, θ) ∈ physicalPieceClosed S K z i :=
      (hgeometry.boundary z hz hs i).2.1 ((hgeometry.boundary _ href hsref i).1 hc)
    have hreg := (hgeometry.boundary z hz hs i).2.2.2.2.1 (τ (r, θ)) hcy
    have hjcurrent (k : ℕ) (hk : k ≤ N) :
        ‖iteratedFDeriv ℝ k (K.height z i) (τ (r, θ))‖ ≤ M := by
      rw [hy]
      exact hraw.height_jets _ k hk
    have hjinverse (k : ℕ) (hk : k ≤ N) :
        ‖iteratedFDeriv ℝ k (fun p => (K.height z i p)⁻¹) (τ (r, θ))‖ ≤ M := by
      rw [hy]
      exact hraw.inverse_height_jets _ k hk
    have hcH := hscalar (K.height z i) θ hreg.2.1 hjcurrent
    have hcI := hscalar (fun p => (K.height z i p)⁻¹) θ
      (hreg.2.1.inv hreg.2.2.2.ne') hjinverse
    have hproduct {f g : PolarPoint → ℝ}
        (hf : ContDiffAt ℝ ∞ f (r, θ)) (hg : ContDiffAt ℝ ∞ g (r, θ))
        (hfj : ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k f (r, θ)‖ ≤ Q)
        (hgj : ∀ k, k ≤ N → ‖iteratedFDeriv ℝ k g (r, θ)‖ ≤ Q)
        {k : ℕ} (hk : k ≤ N) :
        ‖iteratedFDeriv ℝ k (fun p => f p * g p) (r, θ)‖ ≤ V :=
      (n04PositiveGeometry_product_prefix_bound (zero_le_one.trans hQ) hf hg hfj hgj hk).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ N)) (sq_nonneg Q))
    constructor
    · intro k hk
      have hb := hproduct hreg0.2.1
        ((hreg.2.1.inv hreg.2.2.2.ne').comp (r, θ) (hforward θ).1)
        (fun j hj => (hraw₀.height_jets θ j hj).trans hMQ) hcI hk
      have he : q = (fun p => K.height (C.referenceState, 0) i p *
          (K.height z i (τ p))⁻¹) := by
        funext p
        exact div_eq_mul_inv _ _
      exact (congrArg (fun f : PolarPoint → ℝ =>
        ‖iteratedFDeriv ℝ k f (r, θ)‖ ≤ V) he).mpr hb
    · intro k hk
      have hb := hproduct (hreg0.2.1.inv hreg0.2.2.2.ne')
        (hreg.2.1.comp (r, θ) (hforward θ).1)
        (fun j hj => (hraw₀.inverse_height_jets θ j hj).trans hMQ) hcH hk
      have he : (fun p => (q p)⁻¹) =
          (fun p => (K.height (C.referenceState, 0) i p)⁻¹ * K.height z i (τ p)) := by
        funext p
        change (_ / _)⁻¹ = _
        rw [inv_div, div_eq_mul_inv, mul_comm]
      rw [he]
      exact hb
  have hdiag (θ : ℝ) :
      V⁻¹ ≤ radialPartial (fun p => (τ p).1) (r, θ) ∧
        V⁻¹ ≤ angularPartial (fun p => (τ p).2) (r, θ) := by
    apply canonicalCurrentPoint_root_diagonal_lower hgeometry hcut href hsref hz hs
      m side θ (zero_lt_one.trans_le hV)
    have hy : τ (r, θ) = (r, (τ (r, θ)).2) := Prod.ext
      (canonicalCurrentPoint_root_radial hgeometry hcut href hsref hz hs m side θ) rfl
    change ‖fderiv ℝ (canonicalReferencePoint C K z i) (τ (r, θ))‖ ≤ V
    rw [hy]
    have hb : ‖fderiv ℝ (K.inverseChart (C.referenceState, 0) i ∘ K.chart z i)
        (r, (τ (r, θ)).2)‖ ≤ V := by
      simpa only [norm_iteratedFDeriv_one] using
        ((hinverse (τ (r, θ)).2).2 1 le_rfl (by dsimp only [N]; omega)).trans hRV
    have he : K.inverseChart (C.referenceState, 0) i ∘ K.chart z i =
        canonicalReferencePoint C K z i := rfl
    exact (congrArg (fun f : PolarPoint → PolarPoint =>
      ‖fderiv ℝ f (r, (τ (r, θ)).2)‖ ≤ V) he).mp hb
  have hout : RootEndpointJetBounds n τ q r V⁻¹ V V :=
    { radial_lower := fun θ => (hdiag θ).1
      angular_lower := fun θ => (hdiag θ).2
      coordinate_jets := fun k hk hkN θ => ((hforward θ).2 k hk hkN).trans hRV
      height_value := fun θ => (le_abs_self _).trans (by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
          (hheights θ).1 0 (Nat.zero_le N))
      height_inverse := fun θ => (le_abs_self _).trans (by
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
          (hheights θ).2 0 (Nat.zero_le N))
      height_jets := fun k _ hk θ => (hheights θ).1 k (by dsimp only [N]; omega) }
  exact (congrArg (fun B : ℝ => RootEndpointJetBounds n τ q r B⁻¹ B B) hVeq).mp hout

end ContinuousFlexibility.Analysis
