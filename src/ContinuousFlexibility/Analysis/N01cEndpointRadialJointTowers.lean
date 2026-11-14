module

public import ContinuousFlexibility.Analysis.N01cGradedJetContinuity
public import ContinuousFlexibility.Analysis.N01cEndpointCosineTower
public import ContinuousFlexibility.Analysis.N01cOrdinarySpeedFiniteAffine

/-!
# Genuine joint state-angle towers for physical radial jets

At a fixed interior radius the positive endpoint weight can be divided
out of the raw mixed estimate. This supplies consecutive grading-unit
bounds for every angular derivative. The resulting state-angle tower
uses the actual radial derivatives and the original topological state
space throughout.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff Topology

variable {X ι : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]

/-- Schwarz commutation identifies the angular derivative of the actual
radial jet on its original open smooth domain. -/
theorem angularIterate_mixedDerivative_radialZero
    {I : Set ℝ} (hI : IsOpen I) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (I ×ˢ (univ : Set ℝ)))
    (a b : ℕ) {r : ℝ} (hr : r ∈ I) (θ : ℝ) :
    iteratedDeriv b (fun η => mixedDerivative a 0 f (r, η)) θ =
      mixedDerivative a b f (r, θ) := by
  simpa only [mixedDerivative, iteratedDeriv_zero] using
    (iteratedDeriv_swap_of_contDiffOn (hI.prod isOpen_univ) hf a b
      (show (r, θ) ∈ I ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ _⟩)).symm

def MixedJetRegularity.radialAngularStateJets
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U (I ×ˢ univ) f) (hI : IsOpen I)
    (a b : ℕ) (r : ℝ) (hr : r ∈ I) (θ : ℝ) :
    SmoothDirections U
      (fun x => iteratedDeriv b (fun η => mixedDerivative a 0 (f x) (r, η)) θ) :=
  (R.parameter a b (r, θ) ⟨hr, mem_univ _⟩).congr
    (fun x hx => (angularIterate_mixedDerivative_radialZero hI
      (R.spatial x hx) a b hr θ).symm)

theorem MixedJetRegularity.radialAngularStateJets_D_apply
    {U : Set X} {I : Set ℝ} {f : X → PolarPoint → ℝ}
    (R : MixedJetRegularity U (I ×ˢ univ) f) (hI : IsOpen I)
    (a b k : ℕ) (r : ℝ) (hr : r ∈ I) (θ : ℝ) (x : X) (v : Fin k → X) :
    (R.radialAngularStateJets hI a b r hr θ).D k x v =
      (R.parameter a b (r, θ) ⟨hr, mem_univ _⟩).D k x v := rfl

/-- The endpoint-weighted estimate gives ordinary grading-unit bounds at
each fixed interior radius, uniformly over all angles. -/
theorem EndpointMixedPowerBounds.radialAngular_unit_bound
    {p : ℕ → Seminorm ℝ X} {center : X} {base loss : ℕ}
    {U : Set X} {I : ι → Set ℝ} {δ : ι → ℝ → ℝ} {H E : ι → ℝ}
    {f : ι → X → PolarPoint → ℝ}
    (hf : EndpointMixedPowerBounds p center base loss U (fun m => I m ×ˢ univ)
      (fun m q => δ m q.1) (fun m _ => H m) (fun m _ => E m) f)
    (hp : Monotone p) (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (m : ι) (hI : IsOpen (I m)) (RF : MixedJetRegularity U (I m ×ˢ univ) (f m))
    (r : ℝ) (hr : r ∈ I m) (hδ : 0 < δ m r) (hE : 1 ≤ E m) (a b K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, k ≤ K → ∀ θ : ℝ,
      ∀ J : SmoothDirections U
        (fun x => iteratedDeriv b (fun η => mixedDerivative a 0 (f m x) (r, η)) θ),
      ∀ x ∈ U, ∀ R : ℝ, 1 ≤ R → p (max base (a + b + loss)) (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p (max base (a + b + loss)) (v i) < 1) →
        |J.D k x v| ≤ B * R := by
  obtain ⟨C, A, hC, hA, hb⟩ := hf K (a + b)
  let C₀ : ℝ := C * E m ^ A * max 1 (H m)
  have hCE : 0 ≤ C * E m ^ A :=
    mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have hC₀ : 0 ≤ C₀ := mul_nonneg hCE (zero_le_one.trans (le_max_left _ _))
  have hd : 0 < δ m r ^ a := pow_pos hδ a
  refine ⟨C₀ / δ m r ^ a, div_nonneg hC₀ hd.le, ?_⟩
  intro k hk θ J x hx R hR hxR v hv
  let J₀ : SmoothDirections U (fun y => mixedDerivative a b (f m y) (r, θ)) :=
    J.congr (fun y hy => angularIterate_mixedDerivative_radialZero hI
      (RF.spatial y hy) a b hr θ)
  have hvl (i : Fin k) : p base (v i) ≤ 1 :=
    ((hp (le_max_left base (a + b + loss))) (v i)).trans (hv i).le
  have hxh : p (a + b + loss) (x - center) ≤ R :=
    ((hp (le_max_right base (a + b + loss))) (x - center)).trans hxR
  have hvh (i : Fin k) : p (a + b + loss) (v i) ≤ R :=
    (((hp (le_max_right base (a + b + loss))) (v i)).trans (hv i).le).trans hR
  have hraw : δ m r ^ a * |J.D k x v| ≤
      C * E m ^ A * parameterHeightWeight (H m) k *
        R ^ (((a + b : ℕ) : ℝ) / (((a + b : ℕ) : ℝ) + 1)) := by
    simpa only [Real.norm_eq_abs, J₀, SmoothDirections.congr] using
      hb m k hk a b le_rfl (r, θ) ⟨hr, mem_univ _⟩ J₀
        x hx (hlow x hx) v hvl R hR hxh hvh
  have hW : parameterHeightWeight (H m) k ≤ max 1 (H m) := by
    unfold parameterHeightWeight
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hcoef : C * E m ^ A * parameterHeightWeight (H m) k ≤ C₀ :=
    mul_le_mul_of_nonneg_left hW hCE
  have hweighted : δ m r ^ a * |J.D k x v| ≤ C₀ * R :=
    hraw.trans (mul_le_mul hcoef
      (Real.rpow_le_self_of_one_le hR (spatialOrder_fraction_le_one (le_refl (a + b))))
      (Real.rpow_nonneg (zero_le_one.trans hR) _) hC₀)
  calc
    |J.D k x v| = (δ m r ^ a * |J.D k x v|) / δ m r ^ a := by
      field_simp [hd.ne']
    _ ≤ (C₀ * R) / δ m r ^ a := div_le_div_of_nonneg_right hweighted hd.le
    _ = (C₀ / δ m r ^ a) * R := by ring

/-- The actual radial jet has a genuine joint state-angle tower on the
same state domain; the fixed physical radius introduces no new state
hypothesis or order-dependent neighbourhood. -/
def jointSmoothDirections_of_endpointRadialJet
    (p : ℕ → Seminorm ℝ X) (hp : Monotone p) (hcp : ∀ n, Continuous (p n))
    (center : X) (base loss : ℕ)
    {U : Set X} (hU : IsOpen U) (hconv : Convex ℝ U)
    (hlow : ∀ x ∈ U, p base (x - center) ≤ 1)
    (I : ι → Set ℝ) (δ : ι → ℝ → ℝ) (H E : ι → ℝ)
    (f : ι → X → PolarPoint → ℝ)
    (hf : EndpointMixedPowerBounds p center base loss U (fun m => I m ×ˢ univ)
      (fun m q => δ m q.1) (fun m _ => H m) (fun m _ => E m) f)
    (m : ι) (hI : IsOpen (I m)) (RF : MixedJetRegularity U (I m ×ˢ univ) (f m))
    (a : ℕ) (r : ℝ) (hr : r ∈ I m) (hδ : 0 < δ m r) (hE : 1 ≤ E m)
    (hfinite : IsFiniteAffineTimeSmooth U (fun y : X × PolarPoint =>
      mixedDerivative a 0 (f m y.1) (r, y.2.2))) :
    SmoothDirections (U ×ˢ (univ : Set ℝ))
      (fun y : X × ℝ => mixedDerivative a 0 (f m y.1) (r, y.2)) := by
  let J (b : ℕ) (q : PolarPoint) := RF.radialAngularStateJets hI a b r hr q.2
  have hjets : ∀ b K : ℕ, ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℕ, k ≤ K → ∀ q : PolarPoint, ∀ x ∈ U,
      ∀ R : ℝ, 1 ≤ R → p N (x - center) ≤ R →
      ∀ v : Fin k → X, (∀ i, p N (v i) < 1) →
        |(J b q).D k x v| ≤ C * R := by
    intro b K
    obtain ⟨C, hC, hb⟩ :=
      hf.radialAngular_unit_bound hp hlow m hI RF r hr hδ hE a b K
    exact ⟨max base (a + b + loss), C, hC,
      fun k hk q x hx R hR hxR v hv => hb k hk q.2 (J b q) x hx R hR hxR v hv⟩
  exact (continuousTimeSpeedTower_of_graded_stateAngularJets
    p hcp center hU hconv hfinite J hjets).jet 0

end ContinuousFlexibility.Analysis
