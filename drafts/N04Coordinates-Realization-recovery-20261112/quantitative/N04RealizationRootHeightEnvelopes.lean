import ContinuousFlexibility.Analysis.N04RealizationRootBetweenEnvelopes

/-!
# Material envelopes for the actual root height ratio

The two signs use the original reference and current height powers.
The relative map is the stored inverse composed with the stored chart.
All envelopes use the same host sample and original root circle.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff

theorem n04Realization_rootHeight_material_envelope
    {X : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {N base : ℕ} {ε K₀ C0 B : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    (hB : 1 ≤ B) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hraw : N04RealizationRootMaterialPrefix D T S C K N base ε K₀ C0 B)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    (z : X → AnnularState S × ℝ) (m j : X → ℕ)
    (side : X → Bool) (θ : X → ℝ)
    (hz : ∀ x, z x ∈ stateNeighborhood S C base ε)
    (hs : ∀ x, stateSector S (z x).1)
    (hhost : ∀ x, Ioo (C.left (m x)) (C.right (m x)) ⊆ D.cells (j x))
    (hopt : ∀ x, ∀ r ∈ Ioo (C.left (m x)) (C.right (m x)),
      K₀⁻¹ * T.E0 (T.sample (j x)) ^ (-K₀) *
        min (r - C.left (m x)) (C.right (m x) - r) ≤
          -deriv D.w r / (r * D.w r))
    (sign : Bool) {n : ℕ} (hnN : n ≤ N) :
    HasPositiveEnvelope (fun x => C0 * T.E0 (T.sample (j x)))
      (fun x =>
        let i : ℕ := if side x then (K.cutPair (m x)).2 else (K.cutPair (m x)).1
        ‖iteratedFDeriv ℝ n
          (fun p => n04CoordinatesCurrentHeightRatio C K (z x) i p ^
            (if sign then (-1 : ℝ) else 1))
          (n01ComponentRoot C (m x) (side x), θ x)‖) := by
  let i : X → ℕ := fun x =>
    if side x then (K.cutPair (m x)).2 else (K.cutPair (m x)).1
  let r : X → ℝ := fun x => n01ComponentRoot C (m x) (side x)
  let p : X → PolarPoint := fun x => (r x, θ x)
  let W : X → ℝ := fun x => C0 * T.E0 (T.sample (j x))
  let τ : X → PolarPoint → PolarPoint := fun x => canonicalCurrentPoint C K (z x) (i x)
  let γ : Bool → ℝ := fun b => if b then -1 else 1
  let H₀ : Bool → X → PolarPoint → ℝ := fun b x q =>
    K.height (C.referenceState, 0) (i x) q ^ γ b
  let H₁ : Bool → X → PolarPoint → ℝ := fun b x q =>
    K.height (z x) (i x) q ^ γ b
  have hW (x : X) : 1 ≤ W x := hfloor (j x)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hy (x : X) : τ x (p x) = (r x, (τ x (p x)).2) :=
    Prod.ext (canonicalCurrentPoint_root_radial hA hcut href hsref
      (hz x) (hs x) (m x) (side x) (θ x)) rfl
  have hroot₀ (x : X) := hraw (C.referenceState, 0) href hsref
    (m x) (j x) (hhost x) (hopt x) (side x) (θ x)
  have hroot₁ (x : X) := hraw (z x) (hz x) (hs x)
    (m x) (j x) (hhost x) (hopt x) (side x) (τ x (p x)).2
  have hτ (x : X) : ContDiffAt ℝ ∞ (τ x) (p x) :=
    n04Coordinates_currentPoint_contDiffAt_closed hA href hsref
      (hz x) (hs x) (i x) (hroot₀ x).1
  have hH₀ (b : Bool) (x : X) : ContDiffAt ℝ ∞ (H₀ b x) (p x) :=
    (((hA.boundary _ href hsref (i x)).2.2.2.2.1 _ (hroot₀ x).1).2.1).rpow_const_of_ne
      (hroot₀ x).2.1.ne'
  have hH₁ (b : Bool) (x : X) : ContDiffAt ℝ ∞ (H₁ b x) (τ x (p x)) := by
    rw [hy x]
    exact (((hA.boundary (z x) (hz x) (hs x) (i x)).2.2.2.2.1 _
      (hroot₁ x).1).2.1).rpow_const_of_ne (hroot₁ x).2.1.ne'
  have hH₀j (b : Bool) (k : ℕ) (hkn : k ≤ n) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (H₀ b x) (p x)‖) :=
    ⟨B, B, hBpos, hBpos, fun x => (hroot₀ x).2.2.2.1 b k (hkn.trans hnN)⟩
  have hH₁j (b : Bool) (k : ℕ) (hkn : k ≤ n) :
      HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ k (H₁ b x) (τ x (p x))‖) := by
    refine ⟨B, B, hBpos, hBpos, fun x => ?_⟩
    rw [hy x]
    exact (hroot₁ x).2.2.2.1 b k (hkn.trans hnN)
  have hτj (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (τ x) (p x)‖) :=
    n04Realization_rootBetween_material_envelope hA hcut hB hfloor hraw
      (fun _ => (C.referenceState, 0)) z m j side θ
      (fun _ => href) (fun _ => hsref) hz hs hhost hopt hk (hkn.trans hnN)
  have hcomp (b : Bool) (k : ℕ) (hkn : k ≤ n) :
      HasPositiveEnvelope W
        (fun x => ‖iteratedFDeriv ℝ k (H₁ b x ∘ τ x) (p x)‖) :=
    n04Realization_envelope_comp_jets hW p (H₁ b) τ (hH₁ b) hτ k
      (fun a ha => hH₁j b a (ha.trans hkn))
      (fun a ha hak => hτj a ha (hak.trans hkn))
  have hproduct := n04Realization_envelope_mul_jets hW p (H₀ sign)
    (fun x => H₁ (!sign) x ∘ τ x) (hH₀ sign)
    (fun x => (hH₁ (!sign) x).comp (p x) (hτ x)) n
    (hH₀j sign) (hcomp (!sign))
  have heq (x : X) :
      (fun q => H₀ sign x q * (H₁ (!sign) x ∘ τ x) q) =
      (fun q => n04CoordinatesCurrentHeightRatio C K (z x) (i x) q ^ γ sign) := by
    funext q
    cases sign <;>
      simp only [H₀, H₁, γ, Bool.not_true, Bool.not_false, Bool.false_eq_true,
        ↓reduceIte, Real.rpow_one, Real.rpow_neg_one, Function.comp_apply,
        n04CoordinatesCurrentHeightRatio, div_eq_mul_inv, mul_inv_rev, inv_inv]
    exact mul_comm _ _
  exact hproduct.mono (fun x => le_of_eq (congrArg
    (fun f : PolarPoint → ℝ => ‖iteratedFDeriv ℝ n f (p x)‖) (heq x).symm))

end ContinuousFlexibility.Analysis
