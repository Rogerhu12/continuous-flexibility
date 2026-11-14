module

public import ContinuousFlexibility.Analysis.N07aAngularSobolev
public import ContinuousFlexibility.Analysis.AngularInverseEstimate

/-!
# Converting actual level estimates to the spectral inverse interface

The analytic relative-operator estimates may be proved entirely in the
prescribed weak graph norms.  The already proved onto Fourier/Sobolev
identification converts those estimates to the spectral norms required
by `angular_inverse_tame_real`.  Finite prefix sums make the constants
monotone without creating a second high state factor.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal NNReal BigOperators

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hK : ∀ m, K.left m < K.right m) (b : ℕ)

local instance n07aSpectralBoundsLevelGroup (s : ℕ) :
    NormedAddCommGroup (V.level γ w s) := Submodule.normedAddCommGroup _

local instance n07aSpectralBoundsLevelSpace (s : ℕ) :
    NormedSpace ℝ (V.level γ w s) := Submodule.normedSpace _

local instance n07aSpectralBoundsLevelInner (s : ℕ) :
    InnerProductSpace ℝ (V.level γ w s) := Submodule.innerProductSpace _

local instance n07aSpectralBoundsBandGroup (n : ℕ) :
    NormedAddCommGroup (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.normedAddCommGroup _

local instance n07aSpectralBoundsBandSpace (n : ℕ) :
    NormedSpace ℝ (n07aAngularBandSpace hV γ w hK b n) := Submodule.normedSpace _

local instance n07aSpectralBoundsBandInner (n : ℕ) :
    InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.innerProductSpace _

local instance n07aSpectralBoundsLpGroup :
    NormedAddCommGroup (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) :=
  lp.normedAddCommGroup

local instance n07aSpectralBoundsLpSpace :
    NormedSpace ℝ (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) :=
  lp.instNormedSpace

local instance n07aSpectralBoundsLpInner :
    InnerProductSpace ℝ (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) :=
  lp.instInnerProductSpace

/-- The norm conversion is ordinary algebra once the actual lift and its
forgetful map have been constructed. Keeping this step independent of the
nested canonical graph prevents repeated typeclass normalization. -/
private theorem n07a_spectral_bound_via_lift
    {H G : Type*} [NormedAddCommGroup H] [NormedAddCommGroup G]
    (D : H → Prop) (N : H → ℝ) (i : G → H) (A : H → H)
    {L a c : ℝ} (ha : 0 ≤ a)
    (hlift : ∀ u, D u → ∃ U : G, i U = u ∧ ‖U‖ ≤ L * N u)
    (htruncate : ∀ W : G, D (i W) ∧ N (i W) ≤ ‖W‖)
    (hlevel : ∀ U : G, ∃ W : G,
      i W = A (i U) ∧ ‖W‖ ≤ a * ‖U‖ + c * ‖i U‖)
    (u : H) (hu : D u) :
    D (A u) ∧ N (A u) ≤ (a * L) * N u + c * ‖u‖ := by
  obtain ⟨U, hU, hUnorm⟩ := hlift u hu
  obtain ⟨W, hW, hWnorm⟩ := hlevel U
  have hWbase : i W = A u := hW.trans (congrArg A hU)
  refine ⟨hWbase ▸ (htruncate W).1, ?_⟩
  calc
    N (A u) ≤ ‖W‖ := hWbase ▸ (htruncate W).2
    _ ≤ a * ‖U‖ + c * ‖u‖ := by simpa only [hU] using hWnorm
    _ ≤ a * (L * N u) + c * ‖u‖ :=
      add_le_add (mul_le_mul_of_nonneg_left hUnorm ha) le_rfl
    _ = _ := by ring

/-- A genuine higher-level output and its actual norm bound supply exactly
the Sobolev-domain and one-high hypotheses of the angular inverse theorem. -/
theorem n07aAngular_sobolev_bound_of_level
    (A : V.level γ w b →L[ℝ] V.level γ w b) (p : ℕ)
    {a c : ℝ} (ha : 0 ≤ a)
    (hlevel : ∀ U : V.level γ w (b + p),
      ∃ W : V.level γ w (b + p),
        V.forget γ w (b + p) W =
          V.forget γ w b (A (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U)) ∧
        ‖W‖ ≤ a * ‖U‖ + c * ‖n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p) U‖)
    (u : V.level γ w b)
    (hu : MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u)) :
    MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (A u)) ∧
      angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b (A u)) ≤
        (a * n07aAngularLiftConstant p) *
          angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b u) + c * ‖u‖ := by
  apply n07a_spectral_bound_via_lift
    (fun v => MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b v))
    (fun v => angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ w hK b v))
    (n07aAngularLevelTruncate hV γ w (Nat.le_add_right b p)) A ha
    (n07aAngularSobolev_exists_lift hV γ w hK b p) ?_ ?_ u hu
  · intro W
    exact ⟨n07aAngularTruncate_memSobolev hV γ w hK b p W,
      n07aAngularTruncate_sobolevNorm_le hV γ w hK b p W⟩
  · intro U
    obtain ⟨W, hW, hWnorm⟩ := hlevel U
    refine ⟨W, ?_, hWnorm⟩
    apply hV.2.2.1 γ w b
    rw [n07aAngularLevelTruncate_forget]
    exact hW

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open scoped NNReal BigOperators

/-- A finite monotone majorant, retaining the original order-zero constant. -/
def n07aAngularMonotoneEnvelope (a : ℕ → ℝ≥0) (p : ℕ) : ℝ≥0 :=
  ∑ j ∈ Finset.range (p + 1), a j

theorem n07aAngularMonotoneEnvelope_ge (a : ℕ → ℝ≥0) (p : ℕ) :
    a p ≤ n07aAngularMonotoneEnvelope a p :=
  Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_self p))

theorem n07aAngularMonotoneEnvelope_mono (a : ℕ → ℝ≥0) :
    Monotone (n07aAngularMonotoneEnvelope a) := by
  intro p q hpq
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hpq)) (fun _ _ _ => zero_le)

@[simp] theorem n07aAngularMonotoneEnvelope_zero (a : ℕ → ℝ≥0) :
    n07aAngularMonotoneEnvelope a 0 = a 0 := by
  simp only [n07aAngularMonotoneEnvelope, zero_add, Finset.sum_range_one]

/-- Taking a monotone envelope of the coefficient constants still leaves
only one factor of the highest state size. -/
theorem n07aAngularMonotoneEnvelope_oneHigh
    (a N : ℕ → ℝ≥0) (hN : Monotone N) (p : ℕ) :
    n07aAngularMonotoneEnvelope (fun j => a j * N j) p ≤
      n07aAngularMonotoneEnvelope a p * N p := by
  unfold n07aAngularMonotoneEnvelope
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hN (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    zero_le

/-- The explicit inverse constant can be made uniform by replacing its
three low-order arguments by uniform bounds.  No high error enters it. -/
theorem n07aAngularInverseTameConstant_mono (p : ℕ)
    {a c b A C B : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (haA : a ≤ A) (hcC : c ≤ C) (hbB : b ≤ B) :
    angularInverseTameConstant p a c b ≤ angularInverseTameConstant p A C B := by
  have hA0 : 0 ≤ A := ha.trans haA
  have hC0 : 0 ≤ C := hc.trans hcC
  have hB0 : 0 ≤ B := hb.trans hbB
  have hpre : angularInversePreConstant p a c b ≤ angularInversePreConstant p A C B := by
    unfold angularInversePreConstant
    gcongr
  have hpre0 := (angularInversePreConstant_pos p ha hc hb).le
  have hpre1 := (angularInversePreConstant_pos p hA0 hC0 hB0).le
  unfold angularInverseTameConstant angularAbsorptionConstant
  gcongr

end ContinuousFlexibility.Analysis
