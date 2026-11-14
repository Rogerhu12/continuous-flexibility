module

public import ContinuousFlexibility.Analysis.N06NuSpatialPacket

/-!
# Fixed-seminorm bounds for all spatial jets of the actual nu coordinates

The five polar entries are the derivatives of the actual decoded state
height. Their Fréchet jets through order n are controlled by the original
state grading at order n+4, uniformly over the physical annulus. The
estimate is for the actual coordinate packet, with no independently
assigned jets.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff BigOperators Topology

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem n06_actualNuJetCoordinates_sub_eq_spatialPacket
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (z w : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    n06ActualNuJetCoordinates D S z p - n06ActualNuJetCoordinates D S w p =
      n06NuSpatialLinearPacket (fun x => stateU S z.1 x - stateU S w.1 x)
        (z.2 - w.2) (z.1.2.1 - w.1.2.1) p := by
  have hU : IsOpen {x : PolarPoint | x.1 ≠ 0} := isOpen_ne_fun continuous_fst continuous_const
  have h := n06_polar_height_jet_sub hU
    (neighborhood_stateU_contDiff hT hS z.1).contDiffOn
    (neighborhood_stateU_contDiff hT hS w.1).contDiffOn (fun _ hx => hx) hr
  funext i
  fin_cases i
  · change p.1 - p.1 = 0
    exact sub_self _
  · change D.w p.1 - D.w p.1 = 0
    exact sub_self _
  · change deriv D.w p.1 - deriv D.w p.1 = 0
    exact sub_self _
  · change D.chi p.1 - D.chi p.1 = 0
    exact sub_self _
  · change deriv D.chi p.1 - deriv D.chi p.1 = 0
    exact sub_self _
  · exact h.1.symm
  · exact h.2.1.symm
  · exact h.2.2.1.symm
  · exact h.2.2.2.1.symm
  · exact h.2.2.2.2.symm
  · rfl
  · rfl

private theorem n06_spatial_difference_of_mixed
    {U : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hU : IsOpen U) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (n : ℕ) {R : ℝ} (hR : 0 ≤ R) {p : PolarPoint} (hp : p ∈ U)
    (hbound : ∀ a b, a + b ≤ n →
      ‖mixedDerivative a b f p - mixedDerivative a b g p‖ ≤ R)
    (k : ℕ) (hk : k ≤ n) :
    ‖iteratedFDeriv ℝ k (fun q => f q - g q) p‖ ≤ (2 : ℝ) ^ n * R := by
  have h := norm_iteratedFDeriv_le_of_mixedDerivative hU (hf.sub hg).contDiffOn k hp hR
    (fun a b hab => by
      rw [n06_mixedDerivative_sub hf hg]
      exact hbound a b (by omega))
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk) hR)

private theorem n06_stateU_spatial_difference_bound
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hjet : N06StateHeightFiniteJetDifferenceBound D S (n + 2) L)
    (x y : AnnularState S) {p : PolarPoint} (hp : p ∈ annularOpen D)
    (k : ℕ) (hk : k ≤ n + 2) :
    ‖iteratedFDeriv ℝ k (fun q => stateU S x q - stateU S y q) p‖ ≤
      ((2 : ℝ) ^ (n + 2) * L) * stateGrading S (n + 4) (x - y) := by
  have hx := neighborhood_stateU_contDiff hT hS x
  have hy := neighborhood_stateU_contDiff hT hS y
  have hP : 0 ≤ stateGrading S (n + 4) (x - y) := apply_nonneg _ _
  have hbound (a b : ℕ) (hab : a + b ≤ n + 2) :
      ‖mixedDerivative a b (stateU S x) p - mixedDerivative a b (stateU S y) p‖ ≤
        L * stateGrading S (n + 4) (x - y) := by
    change |mixedDerivative a b (stateU S x) p - mixedDerivative a b (stateU S y) p| ≤ _
    exact hjet a b hab x y p hp
  have h := n06_spatial_difference_of_mixed (isOpen_Ioo.prod isOpen_univ)
    hx hy (n + 2) (mul_nonneg hL hP) hp hbound k hk
  exact h.trans_eq
    (mul_assoc ((2 : ℝ) ^ (n + 2)) L (stateGrading S (n + 4) (x - y))).symm

def N06NuSpatialCoordinateDifferenceBound (D : ReferenceData) (S : PhysicalSpacesData)
    (n : ℕ) (L : ℝ) : Prop :=
  ∀ (z w : AnnularState S × ℝ) k, k ≤ n → ∀ p ∈ annularOpen D,
    ‖iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S z) p -
      iteratedFDeriv ℝ k (n06ActualNuJetCoordinates D S w) p‖ ≤
        L * (stateGrading S (n + 4) (z.1 - w.1) + |z.2 - w.2|)

/-- All actual spatial packet jets have a common, fixed, linear state
difference bound at the same order n+4 as the pure angular estimate. -/
theorem n06_actualNuJetCoordinates_spatial_difference_bound
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hS : IsPhysicalSpaces D T S) (hχ : ContDiff ℝ ∞ D.chi) (n : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ N06NuSpatialCoordinateDifferenceBound D S n L := by
  obtain ⟨J, hJ, hjet⟩ := n06_stateU_mixedDerivative_finite_difference_bound hD hT hS (n + 2)
  have ha : 0 < D.a := hD.choose_spec.1.1
  have hi : ContDiffOn ℝ ∞ (fun r : ℝ => r⁻¹) (Ioi 0) :=
    contDiffOn_id.inv (fun _ hr => ne_of_gt hr)
  obtain ⟨B, hB, hrecip⟩ := n06_radialLift_finite_frechet_bound (b := D.b) ha hi (n + 1)
  let A : ℝ := 1 + (2 : ℝ) ^ (n + 2) * J
  let E : ℝ := 1 + (2 : ℝ) ^ (n + 1) * B
  have hA : 1 ≤ A := le_add_of_nonneg_right (mul_nonneg (by positivity) hJ)
  have hE : 0 ≤ E := add_nonneg zero_le_one (mul_nonneg (by positivity) hB)
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  refine ⟨1 + E * A, le_add_of_nonneg_right (mul_nonneg hE hA₀), ?_⟩
  intro z w k hk p hp
  let P : ℝ := stateGrading S (n + 4) (z.1 - w.1)
  let δ : ℝ := P + |z.2 - w.2|
  have hP : 0 ≤ P := apply_nonneg _ _
  have hδ : 0 ≤ δ := add_nonneg hP (abs_nonneg _)
  have hPδ : P ≤ δ := le_add_of_nonneg_right (abs_nonneg _)
  have hδA : δ ≤ A * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hδ
  have hsmallHeight (j : ℕ) (hj : j ≤ n + 2) :
      ‖iteratedFDeriv ℝ j (fun q => stateU S z.1 q - stateU S w.1 q) p‖ ≤ A * δ := by
    have h := n06_stateU_spatial_difference_bound hT hS n hJ hjet z.1 w.1 hp j hj
    have hJA : (2 : ℝ) ^ (n + 2) * J ≤ A := le_add_of_nonneg_left zero_le_one
    exact h.trans ((mul_le_mul_of_nonneg_left hPδ (mul_nonneg (by positivity) hJ)).trans
      (mul_le_mul_of_nonneg_right hJA hδ))
  have hq : |z.2 - w.2| ≤ A * δ :=
    (le_add_of_nonneg_left hP).trans hδA
  have hν : |z.1.2.1 - w.1.2.1| ≤ A * δ :=
    (((neighborhoodStateGrading_controls_le S (n + 4) (z.1 - w.1)).1).trans hPδ).trans hδA
  have hU : IsOpen (annularOpen D) := isOpen_Ioo.prod isOpen_univ
  have hr (x : PolarPoint) (hx : x ∈ annularOpen D) : x.1 ≠ 0 :=
    (ha.trans hx.1.1).ne'
  have hheight : ContDiffOn ℝ ∞ (fun q => stateU S z.1 q - stateU S w.1 q) (annularOpen D) :=
    ((neighborhood_stateU_contDiff hT hS z.1).sub
      (neighborhood_stateU_contDiff hT hS w.1)).contDiffOn
  have hpacket := n06NuSpatialLinearPacket_frechet_bound hU hheight hr n hp hB
    (mul_nonneg hA₀ hδ) (fun j hj => hrecip j hj p ⟨hp.1.1.le, hp.1.2.le⟩)
    hsmallHeight hq hν k hk
  have hcz := n06_actualNuJetCoordinates_contDiffAt hT hS
    hD.choose_spec.1.2.2.1.1 hχ z (hr p hp)
  have hcw := n06_actualNuJetCoordinates_contDiffAt hT hS
    hD.choose_spec.1.2.2.1.1 hχ w (hr p hp)
  have he := iteratedFDeriv_sub_apply (hcz.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
    (hcw.of_le (by simp : (k : ℕ∞ω) ≤ ∞))
  have hnear : (n06ActualNuJetCoordinates D S z - n06ActualNuJetCoordinates D S w) =ᶠ[𝓝 p]
      n06NuSpatialLinearPacket (fun q => stateU S z.1 q - stateU S w.1 q)
        (z.2 - w.2) (z.1.2.1 - w.1.2.1) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact n06_actualNuJetCoordinates_sub_eq_spatialPacket hT hS z w (hr x hx)
  calc
    _ = ‖iteratedFDeriv ℝ k
        (n06ActualNuJetCoordinates D S z - n06ActualNuJetCoordinates D S w) p‖ :=
      congrArg norm he.symm
    _ = ‖iteratedFDeriv ℝ k
        (n06NuSpatialLinearPacket (fun q => stateU S z.1 q - stateU S w.1 q)
          (z.2 - w.2) (z.1.2.1 - w.1.2.1)) p‖ :=
      congrArg norm ((hnear.iteratedFDeriv ℝ k).eq_of_nhds)
    _ ≤ E * (A * δ) := hpacket
    _ = (E * A) * δ := (mul_assoc E A δ).symm
    _ ≤ (1 + E * A) * δ :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hδ

end ContinuousFlexibility.Statements
