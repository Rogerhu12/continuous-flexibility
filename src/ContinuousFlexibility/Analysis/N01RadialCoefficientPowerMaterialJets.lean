import ContinuousFlexibility.Analysis.N01OriginalCoefficientOrdinaryGlobalJets
import ContinuousFlexibility.Analysis.N01RadialCoefficientMaterialInverse
import ContinuousFlexibility.Analysis.PositivePowerPolynomialMaterialJets
import ContinuousFlexibility.Analysis.MaterialGlobalEndpointModels
import ContinuousFlexibility.Analysis.CanonicalStateInterpolation

/-!
# Material jets of every real power of the actual radial coefficient

The original N01 ratios and inverse profile estimate supply the positive
value and its reciprocal on each genuinely hosted closed component.
The global ordinary coefficient tower supplies all positive jets. The
same material data are retained; only a fixed scalar multiplies E0 so
that its envelope is at least one. No optical root lower is used.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

/-- The pointwise power estimate for an arbitrary graded state space. All
grading manipulations happen here, away from the actual state spaces. -/
private theorem rpow_jet_bound_generic {E : Type} [AddCommGroup E] [Module ℝ E]
    {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (x : E) {powerLow loss outLoss low : ℕ}
    (hpowerLow : powerLow ≤ low) (hloss : loss ≤ low) (hx : p low x ≤ 1)
    {A B : ℕ → ℝ} (hA : ∀ k, 1 ≤ A k) {K W γ : ℝ} (hK : 1 ≤ K) (hAK : 2 * A 0 ≤ K)
    (hW : 1 ≤ W) {f : PolarPoint → ℝ} {q : PolarPoint} (hf : ContDiffAt ℝ ∞ f q)
    (hpos : 0 < f q) (hinv : (f q)⁻¹ ≤ K * W ^ K)
    (hjet : ∀ k, ‖iteratedFDeriv ℝ k f q‖ ≤ A k * (1 + p (k + loss) x))
    (hbound : ∀ z : E, p powerLow z ≤ 1 → ∀ W : ℝ, 1 ≤ W →
      ∀ g : PolarPoint → ℝ, ∀ y : PolarPoint, ContDiffAt ℝ ∞ g y →
        0 < g y → g y ≤ K * W ^ K → (g y)⁻¹ ≤ K * W ^ K →
        (∀ k, 1 ≤ k → ‖iteratedFDeriv ℝ k g y‖ ≤
          A k * W ^ (A k) * (1 + p (k + loss) z)) →
        ∀ k, ‖iteratedFDeriv ℝ k (fun y => g y ^ γ) y‖ ≤
          B k * W ^ (B k) * (1 + p (k + outLoss) z))
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f y ^ γ) q‖ ≤
      B n * W ^ (B n) * (1 + p (n + outLoss) x) := by
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hsmall : p loss x ≤ 1 := (hp hloss x).trans hx
  have hvalue0 : f q ≤ 2 * A 0 := by
    have h0 := hjet 0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.zero_add] at h0
    have h1 := mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hsmall)
      (zero_le_one.trans (hA 0))
    linarith only [le_abs_self (f q), h0, h1]
  have hvalue : f q ≤ K * W ^ K :=
    (hvalue0.trans hAK).trans (le_mul_of_one_le_right hKnonneg
      (Real.one_le_rpow hW hKnonneg))
  refine hbound x ((hp hpowerLow x).trans hx) W hW f q hf hpos hvalue hinv ?_ n
  intro k _hk
  have ha : A k ≤ A k * W ^ (A k) := le_mul_of_one_le_right
    (zero_le_one.trans (hA k)) (Real.one_le_rpow hW (zero_le_one.trans (hA k)))
  exact (hjet k).trans (mul_le_mul_of_nonneg_right ha
    (add_nonneg zero_le_one (apply_nonneg _ _)))

theorem n01_radialCoefficient_rpow_component_material_jets
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε) :
    ∃ C0 : ℝ, ∃ low outLoss : ℕ, 1 ≤ C0 ∧
      (∀ j, 1 ≤ C0 * T.E0 (T.sample j)) ∧
      ∀ γ : ℝ, ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧
      ∀ z ∈ stateNeighborhood S C base ε, stateSector S z.1 →
        pairGrading (stateGrading S) realGrading low (z - (C.referenceState, 0)) ≤ 1 →
      ∀ m j : ℕ, Ioo (C.left m) (C.right m) ⊆ D.cells j →
      ∀ q : PolarPoint, q.1 ∈ Icc (C.left m) (C.right m) → ∀ n : ℕ,
        ‖iteratedFDeriv ℝ n (fun x => (originalCoefficients D S C z).a x ^ γ) q‖ ≤
          B n * (C0 * T.E0 (T.sample j)) ^ (B n) *
            (1 + pairGrading (stateGrading S) realGrading (n + outLoss)
              (z - (C.referenceState, 0))) := by
  have hp : Monotone (pairGrading (stateGrading S) realGrading) :=
    tamePairGrading_monotone (stateGrading_monotone S) (fun _ _ _ => le_rfl)
  have hI : HasInterpolation (pairGrading (stateGrading S) realGrading) :=
    coordinate_hasInterpolation_pair (stateGrading_monotone S)
      (fun _ _ _ => le_rfl) (coordinate_hasInterpolation_stateGrading hS)
      coordinate_hasInterpolation_realGrading
  refine (positivePower_polynomial_material_bound (X := PolarPoint) hp hI loss).elim ?_
  intro powerLow hpowerEx
  refine hpowerEx.elim ?_
  intro outLoss hpower
  refine (originalCoefficient_ordinary_global_bound_of_n01 hS hT hN).elim ?_
  intro A hAraw
  have hA := hAraw.1
  have hraw := hAraw.2
  refine (hN.originalRadialCoefficient_inverse_component_material_bound hT).elim ?_
  intro K0 hK0ex
  refine hK0ex.elim ?_
  intro P hK0P
  have hK0 := hK0P.1
  have hP := hK0P.2.1
  have hinverse := hK0P.2.2
  refine (material_E0_uniform_scaled_lower hT hN.1.1).elim ?_
  intro C0 hC0floor
  have hC0 := hC0floor.1
  have hfloor := hC0floor.2
  let K : ℝ := max 1 (max (2 * A 0) (max K0 P))
  have hK : 1 ≤ K := le_max_left _ _
  have hAK : 2 * A 0 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK0K : K0 ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hPK : P ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hsample (j : ℕ) : 1 ≤ C0 * T.E0 (T.sample j) :=
    hfloor _ (materialSample_mem_interval hN.1.1 hT j)
  refine ⟨C0, max powerLow loss, outLoss, hC0, hsample, ?_⟩
  intro γ
  refine (hpower γ K hK A hA).elim ?_
  intro B hBb
  have hB := hBb.1
  have hbound := hBb.2
  refine ⟨B, hB, ?_⟩
  intro z hz hs hzlow m j hhost q hq n
  have hcomp := n01Properties_negativeRadialComponent hN m
  have hqD : q ∈ annularOpen D :=
    ⟨⟨hcomp.1.trans_le hq.1, hq.2.trans_lt hcomp.2.2.1⟩, mem_univ _⟩
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hsample j
  have hE : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hN.1.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC0 hE.le
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hKnonneg : 0 ≤ K := zero_le_one.trans hK
  have hw : 0 < D.w q.1 := hN.1.1.choose_spec.1.2.2.2.2.1 q.1 hqD.1
  have hpositive : 0 < (originalCoefficients D S C z).a q :=
    (div_pos hw (by norm_num : (0 : ℝ) < 16)).trans_le
      (hN.originalRadialCoefficient_ge_sixteenth_profile hz hs hqD)
  have hcomp0 : canonicalCoefficientComponent 0 (originalCoefficients D S C z) =
      (originalCoefficients D S C z).a := by
    unfold canonicalCoefficientComponent
    exact if_pos rfl
  have hinv : ((originalCoefficients D S C z).a q)⁻¹ ≤ K * W ^ K := by
    calc
      _ ≤ K0 * T.E0 (T.sample j) ^ P := hinverse z hz hs m j hhost q hq
      _ ≤ K0 * W ^ P := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hE.le hEW hP) hK0.le
      _ ≤ K * W ^ K := mul_le_mul hK0K
        (Real.rpow_le_rpow_of_exponent_le hW hPK)
        (Real.rpow_nonneg hW0 _) hKnonneg
  have hf : ContDiffOn ℝ ∞ (originalCoefficients D S C z).a (annularOpen D) := by
    rw [← hcomp0]
    exact contDiffOn_originalCoefficientComponent_of_n01 hS hT hN hz hs (0 : Fin 3)
  have hnorm (k : ℕ) : ‖iteratedFDeriv ℝ k
      (canonicalCoefficientComponent 0 (originalCoefficients D S C z)) q‖ =
        ‖iteratedFDeriv ℝ k (originalCoefficients D S C z).a q‖ := by
    rw [hcomp0]
  exact rpow_jet_bound_generic hp (z - (C.referenceState, 0)) (le_max_left _ _)
    (le_max_right _ _) hzlow hA hK hAK hW
    (hf.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds hqD)) hpositive hinv
    (fun k => (hnorm k).symm.trans_le (hraw z hz hs (0 : Fin 3) k q hqD)) hbound n

end ContinuousFlexibility.Analysis
