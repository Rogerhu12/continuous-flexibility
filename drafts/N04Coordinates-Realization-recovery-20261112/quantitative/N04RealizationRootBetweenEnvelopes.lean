import ContinuousFlexibility.Analysis.N04RealizationRootMaterialPrefix
import ContinuousFlexibility.Analysis.CanonicalRootFiniteEndpointBounds

/-!
# Sample envelopes for the actual relative root maps

The two states below are supplied, not selected. Both inverse directions
are covered by the same theorem, using the same root and host sample.
Only positive coordinate jets enter the composition estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

private theorem rootBetween_radial
    {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    {z₀ z₁ : AnnularState S × ℝ}
    (hz₀ : z₀ ∈ stateNeighborhood S C base ε) (hs₀ : stateSector S z₀.1)
    (hz₁ : z₁ ∈ stateNeighborhood S C base ε) (hs₁ : stateSector S z₁.1)
    (m : ℕ) (side : Bool) (θ : ℝ) :
    let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r : ℝ := n01ComponentRoot C m side
    (K.inverseChart z₁ i (K.chart z₀ i (r, θ))).1 = r := by
  let i : ℕ := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r : ℝ := n01ComponentRoot C m side
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

theorem n04Realization_rootBetween_material_envelope
    {X : Type*} {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S}
    {N base : ℕ} {ε K₀ C0 B : ℝ}
    (hA : N04PartA D S C K base ε) (hcut : CanonicalCutGeometry S C K base ε)
    (hB : 1 ≤ B) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j))
    (hraw : N04RealizationRootMaterialPrefix D T S C K N base ε K₀ C0 B)
    (z₀ z₁ : X → AnnularState S × ℝ) (m j : X → ℕ)
    (side : X → Bool) (θ : X → ℝ)
    (hz₀ : ∀ x, z₀ x ∈ stateNeighborhood S C base ε)
    (hs₀ : ∀ x, stateSector S (z₀ x).1)
    (hz₁ : ∀ x, z₁ x ∈ stateNeighborhood S C base ε)
    (hs₁ : ∀ x, stateSector S (z₁ x).1)
    (hhost : ∀ x, Ioo (C.left (m x)) (C.right (m x)) ⊆ D.cells (j x))
    (hopt : ∀ x, ∀ r ∈ Ioo (C.left (m x)) (C.right (m x)),
      K₀⁻¹ * T.E0 (T.sample (j x)) ^ (-K₀) *
        min (r - C.left (m x)) (C.right (m x) - r) ≤
          -deriv D.w r / (r * D.w r))
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    HasPositiveEnvelope (fun x => C0 * T.E0 (T.sample (j x)))
      (fun x =>
        let i : ℕ := if side x then (K.cutPair (m x)).2 else (K.cutPair (m x)).1
        ‖iteratedFDeriv ℝ n (K.inverseChart (z₁ x) i ∘ K.chart (z₀ x) i)
          (n01ComponentRoot C (m x) (side x), θ x)‖) := by
  let i : X → ℕ := fun x =>
    if side x then (K.cutPair (m x)).2 else (K.cutPair (m x)).1
  let r : X → ℝ := fun x => n01ComponentRoot C (m x) (side x)
  let p : X → PolarPoint := fun x => (r x, θ x)
  let W : X → ℝ := fun x => C0 * T.E0 (T.sample (j x))
  let F₀ : X → PolarPoint → PolarPoint := fun x => K.chart (z₀ x) (i x)
  let F₁ : X → PolarPoint → PolarPoint := fun x => K.chart (z₁ x) (i x)
  let G₁ : X → PolarPoint → PolarPoint := fun x => K.inverseChart (z₁ x) (i x)
  let q : X → PolarPoint := fun x => F₀ x (p x)
  let y : X → PolarPoint := fun x => G₁ x (q x)
  have hW (x : X) : 1 ≤ W x := hfloor (j x)
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hy (x : X) : y x = (r x, (y x).2) :=
    Prod.ext (rootBetween_radial hA hcut (hz₀ x) (hs₀ x) (hz₁ x) (hs₁ x)
      (m x) (side x) (θ x)) rfl
  have hroot₀ (x : X) := hraw (z₀ x) (hz₀ x) (hs₀ x)
    (m x) (j x) (hhost x) (hopt x) (side x) (θ x)
  have hroot₁ (x : X) := hraw (z₁ x) (hz₁ x) (hs₁ x)
    (m x) (j x) (hhost x) (hopt x) (side x) (y x).2
  have hq (x : X) : q x ∈ canonicalClosed S K (i x) :=
    (hA.boundary (z₀ x) (hz₀ x) (hs₀ x) (i x)).1 (hroot₀ x).1
  have hF₀ (x : X) : ContDiffAt ℝ ∞ (F₀ x) (p x) :=
    ((hA.boundary (z₀ x) (hz₀ x) (hs₀ x) (i x)).2.2.2.2.1 _ (hroot₀ x).1).1
  have hF₁ (x : X) : ContDiffAt ℝ ∞ (F₁ x) (y x) := by
    rw [hy x]
    exact ((hA.boundary (z₁ x) (hz₁ x) (hs₁ x) (i x)).2.2.2.2.1 _
      (hroot₁ x).1).1
  have hG₁ (x : X) : ContDiffAt ℝ ∞ (G₁ x) (q x) :=
    n04b_inverseChart_contDiffAt_closed hA (hz₁ x) (hs₁ x) (i x) (hq x)
  have heq (x : X) : F₁ x (y x) = q x :=
    (hA.boundary (z₁ x) (hz₁ x) (hs₁ x) (i x)).2.2.2.1 _ (hq x)
  have hF₀j (k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (F₀ x) (p x)‖) :=
    ⟨B, B, hBpos, hBpos, fun x => (hroot₀ x).2.2.1 k hk hkN⟩
  have hF₁j (k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (F₁ x) (y x)‖) := by
    refine ⟨B, B, hBpos, hBpos, fun x => ?_⟩
    rw [hy x]
    exact (hroot₁ x).2.2.1 k hk hkN
  have hJ : HasPositiveEnvelope W (fun x => |planeJacobian (F₁ x) (y x)|⁻¹) := by
    refine ⟨B, B, hBpos, hBpos, fun x => ?_⟩
    rw [hy x]
    exact (hroot₁ x).2.2.2.2
  have hfirstF : HasPositiveEnvelope W (fun x => ‖fderiv ℝ (F₁ x) (y x)‖) := by
    simpa only [norm_iteratedFDeriv_one] using hF₁j 1 (by omega) (by omega)
  have hfirstG : HasPositiveEnvelope W (fun x => ‖fderiv ℝ (G₁ x) (q x)‖) := by
    apply (((hasPositiveEnvelope_const W hW 2).mul hW hfirstF
      (fun _ => norm_nonneg _)).mul hW hJ
      (fun _ => inv_nonneg.mpr (abs_nonneg _))).mono
    intro x
    have hpoint := (hA.boundary (z₁ x) (hz₁ x) (hs₁ x) (i x)).2.1 (hq x)
    have hnonzero :=
      ((hA.boundary (z₁ x) (hz₁ x) (hs₁ x) (i x)).2.2.2.2.1 _ hpoint).2.2.1
    have hGat : DifferentiableAt ℝ (G₁ x) (F₁ x (y x)) := by
      rw [heq x]
      exact (hG₁ x).differentiableAt (by simp)
    simpa only [heq x] using n04Realization_inverse_first_norm_le
      ((hF₁ x).differentiableAt (by simp)) hGat
      (canonicalClosed_inverse_germs hA (hz₁ x) (hs₁ x) (i x) (hq x)).1 hnonzero
  have hGj (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
      HasPositiveEnvelope W (fun x => ‖iteratedFDeriv ℝ k (G₁ x) (q x)‖) :=
    n04Realization_envelope_inverse_positive_jets hW q F₁ G₁ hF₁ hG₁
      (fun x => (canonicalClosed_inverse_germs hA (hz₁ x) (hs₁ x) (i x) (hq x)).2)
      (fun x => (canonicalClosed_inverse_fderiv hA (hz₁ x) (hs₁ x) (i x) (hq x)).1)
      hfirstG hk (fun j hj hjk => hF₁j j (by omega) (hjk.trans (hkn.trans hnN)))
  exact n04Realization_envelope_comp_positive_jets hW p G₁ F₀ hG₁ hF₀ hn
    hGj (fun k hk hkn => hF₀j k hk (hkn.trans hnN))

end ContinuousFlexibility.Analysis
