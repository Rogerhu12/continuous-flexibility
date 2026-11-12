import ContinuousFlexibility.Analysis.N07aAngularInverse
import ContinuousFlexibility.Analysis.N07aAngularSpectralBounds

/-!
# Uniform inverse constants from the actual one-high graph estimates

Only the order-zero state size enters the inverse constant. A finite
monotone envelope preserves the single high state factor, and the output
is the same bounded inverse in the actual higher source graph.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

local instance n07aUniformInverseLevelGroup (γ : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ 0 s) := Submodule.normedAddCommGroup _
local instance n07aUniformInverseLevelSpace (γ : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ 0 s) := Submodule.normedSpace _
local instance n07aUniformInverseLevelInner (γ : ℝ) (s : ℕ) :
    InnerProductSpace ℝ (V.level γ 0 s) := Submodule.innerProductSpace _
local instance n07aUniformInverseBandGroup (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b n : ℕ) :
    NormedAddCommGroup (n07aAngularBandSpace hV γ 0 hI b n) := Submodule.normedAddCommGroup _
local instance n07aUniformInverseBandSpace (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b n : ℕ) :
    NormedSpace ℝ (n07aAngularBandSpace hV γ 0 hI b n) := Submodule.normedSpace _
local instance n07aUniformInverseBandInner (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b n : ℕ) :
    InnerProductSpace ℝ (n07aAngularBandSpace hV γ 0 hI b n) := Submodule.innerProductSpace _
local instance n07aUniformInverseLpGroup (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b : ℕ) :
    NormedAddCommGroup (lp (fun n => n07aAngularBandSpace hV γ 0 hI b n) 2) :=
  lp.normedAddCommGroup
local instance n07aUniformInverseLpSpace (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b : ℕ) :
    NormedSpace ℝ (lp (fun n => n07aAngularBandSpace hV γ 0 hI b n) 2) := lp.instNormedSpace
local instance n07aUniformInverseLpInner (hV : IsVolumeModel T S K V)
    (γ : ℝ) (hI : ∀ m, K.left m < K.right m) (b : ℕ) :
    InnerProductSpace ℝ (lp (fun n => n07aAngularBandSpace hV γ 0 hI b n) 2) :=
  lp.instInnerProductSpace

private theorem n07a_uniformAngularSpectralBounds
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ) (a c : ℕ → ℝ≥0)
    (R Q : V.level γ 0 b →L[ℝ] V.level γ 0 b) (N : ℕ → ℝ≥0)
    (hlevel : ∀ q (commute : Bool) (U : V.level γ 0 (b + q)),
      ∃ W : V.level γ 0 (b + q),
        V.forget γ 0 (b + q) W = V.forget γ 0 b
          ((if commute then Q else R)
            (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b q) U)) ∧
        ‖W‖ ≤ (a q : ℝ) * ‖U‖ + (c q : ℝ) * (N q : ℝ) *
          ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b q) U‖) :
    (∀ q u,
      MemAngularSobolev (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b u) →
      MemAngularSobolev (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b (R u))) ∧
    (∀ q u,
      MemAngularSobolev (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b u) →
      MemAngularSobolev (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b (Q u)) ∧
        angularSobolevNorm (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b (Q u)) ≤
          (n07aAngularMonotoneEnvelope (fun j => a j *
            ⟨n07aAngularLiftConstant j, n07aAngularLiftConstant_nonneg j⟩) q : ℝ) *
              angularSobolevNorm (𝕜 := ℝ) q (n07aAngularHilbertEquiv hV γ 0 hI b u) +
          (n07aAngularMonotoneEnvelope (fun j => c j * N j) q : ℝ) * ‖u‖) := by
  constructor
  · intro q u hu
    exact (n07aAngular_sobolev_bound_of_level hV γ 0 hI b R q
      (a q).coe_nonneg (fun U => by
        simpa only [Bool.false_eq_true, ite_false] using hlevel q false U) u hu).1
  · intro q u hu
    have h := n07aAngular_sobolev_bound_of_level hV γ 0 hI b Q q
      (a q).coe_nonneg (fun U => by simpa only [ite_true] using hlevel q true U) u hu
    have ha' : (a q : ℝ) * n07aAngularLiftConstant q ≤
        (n07aAngularMonotoneEnvelope (fun j => a j *
          ⟨n07aAngularLiftConstant j, n07aAngularLiftConstant_nonneg j⟩) q : ℝ) := by
      exact_mod_cast n07aAngularMonotoneEnvelope_ge
        (fun j => a j * ⟨n07aAngularLiftConstant j, n07aAngularLiftConstant_nonneg j⟩) q
    have hc' : (c q : ℝ) * (N q : ℝ) ≤
        (n07aAngularMonotoneEnvelope (fun j => c j * N j) q : ℝ) := by
      exact_mod_cast n07aAngularMonotoneEnvelope_ge (fun j => c j * N j) q
    exact ⟨h.1, h.2.trans (add_le_add
      (mul_le_mul_of_nonneg_right ha'
        (angularSobolevNorm_nonneg (𝕜 := ℝ) q _))
      (mul_le_mul_of_nonneg_right hc' (norm_nonneg u)))⟩

private theorem n07a_uniformAngularLift
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ)
    (B : V.level γ 0 b →L[ℝ] V.level γ 0 b) (p : ℕ) (A : ℝ) (C : ℝ≥0)
    (hA : 0 ≤ A)
    (hreg : ∀ u, MemAngularSobolev (𝕜 := ℝ) p
      (n07aAngularHilbertEquiv hV γ 0 hI b u) →
      MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b (B u)))
    (hbound : ∀ u, MemAngularSobolev (𝕜 := ℝ) p
      (n07aAngularHilbertEquiv hV γ 0 hI b u) →
      angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b (B u)) ≤
        A * (angularSobolevNorm (𝕜 := ℝ) p
          (n07aAngularHilbertEquiv hV γ 0 hI b u) + (C : ℝ) * ‖u‖))
    (f : V.level γ 0 (b + p)) :
    ∃ u : V.level γ 0 (b + p),
      n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) u =
        B (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) f) ∧
      ‖u‖ ≤ (1 + n07aAngularLiftConstant p * A) *
        (‖f‖ + (C : ℝ) * ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) f‖) := by
  obtain ⟨u, hu, hn⟩ := n07aAngular_inverse_lift_of_estimate hV γ 0 hI b B p A C
    hA hreg hbound f
  have hsize : 0 ≤ ‖f‖ + (C : ℝ) *
      ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) f‖ :=
    add_nonneg (norm_nonneg f) (mul_nonneg C.coe_nonneg (norm_nonneg _))
  have hconstant : n07aAngularLiftConstant p * A ≤
      1 + n07aAngularLiftConstant p * A := le_add_of_nonneg_left zero_le_one
  exact ⟨u, hu, hn.trans (mul_le_mul_of_nonneg_right hconstant hsize)⟩

theorem n07a_uniformAngularInverse
    (hV : IsVolumeModel T S K V) (γ : ℝ)
    (hI : ∀ m, K.left m < K.right m) (b : ℕ) (a c : ℕ → ℝ≥0) :
    ∀ p : ℕ, ∃ Cₚ : ℝ, 0 < Cₚ ∧
      ∀ (R Q B : V.level γ 0 b →L[ℝ] V.level γ 0 b) (N : ℕ → ℝ≥0),
      Monotone N → (∀ q, 1 ≤ (N q : ℝ)) → (N 0 : ℝ) ≤ 2 →
      (∀ q (commute : Bool) (U : V.level γ 0 (b + q)),
        ∃ W : V.level γ 0 (b + q),
          V.forget γ 0 (b + q) W = V.forget γ 0 b
            ((if commute then Q else R)
              (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b q) U)) ∧
          ‖W‖ ≤ (a q : ℝ) * ‖U‖ + (c q : ℝ) * (N q : ℝ) *
            ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b q) U‖) →
      (∀ u, n07aAngularHilbertEquiv hV γ 0 hI b u ∈ angularFrequencyDomain (𝕜 := ℝ) →
        n07aAngularLambda hV γ 0 hI b (R u) =
          R (n07aAngularLambda hV γ 0 hI b u) + Q u) →
      (∀ u, B (u + R u) = u) → (∀ u, B u + R (B u) = u) → ‖B‖ ≤ 2 →
      ∀ f : V.level γ 0 (b + p), ∃ u : V.level γ 0 (b + p),
        n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) u =
          B (n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) f) ∧
        ‖u‖ ≤ Cₚ * (‖f‖ + (N p : ℝ) *
          ‖n07aAngularLevelTruncate hV γ 0 (Nat.le_add_right b p) f‖) := by
  let A : ℕ → ℝ≥0 := n07aAngularMonotoneEnvelope
    (fun q => a q * ⟨n07aAngularLiftConstant q, n07aAngularLiftConstant_nonneg q⟩)
  let C : ℕ → ℝ≥0 := n07aAngularMonotoneEnvelope c
  intro p
  by_cases hp : p = 0
  · subst p
    refine ⟨2, by norm_num, fun R Q B N hN hN₁ hN₀ hlevel hcomm hleft hright hB f => ?_⟩
    refine ⟨B f, ?_, ?_⟩
    · simp only [Nat.add_zero, n07aAngularLevelTruncate_refl]
    · have h := (B.le_opNorm f).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg f))
      simpa only [Nat.add_zero, n07aAngularLevelTruncate_refl] using
        h.trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg (N 0).coe_nonneg (norm_nonneg f)))
          (by norm_num : (0 : ℝ) ≤ 2))
  · have hp₁ : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp
    let k : ℝ := angularInverseTameConstant p (A (p - 1)) (2 * (c 0 : ℝ)) 2
    have hk : 0 < k := angularInverseTameConstant_pos p
      (A (p - 1)).coe_nonneg (mul_nonneg (by norm_num) (c 0).coe_nonneg) (by norm_num)
    let k' : ℝ := k * (1 + (C (p - 1) : ℝ))
    have hk' : 0 ≤ k' := mul_nonneg hk.le (by positivity)
    refine ⟨1 + n07aAngularLiftConstant p * k',
      add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (n07aAngularLiftConstant_nonneg p) hk'),
      fun R Q B N hN hN₁ hN₀ hlevel hcomm hleft hright hB f => ?_⟩
    let CN : ℕ → ℝ≥0 := n07aAngularMonotoneEnvelope (fun q => c q * N q)
    obtain ⟨hR, hQ⟩ := n07a_uniformAngularSpectralBounds hV γ hI b a c R Q N hlevel
    obtain ⟨hreg, hnorm⟩ := n07aAngular_inverse_tame hV γ 0 hI b R Q B A CN
      (n07aAngularMonotoneEnvelope_mono _) (n07aAngularMonotoneEnvelope_mono _)
      hR hQ hcomm hleft hright
    have hc₀ : (CN 0 : ℝ) ≤ 2 * (c 0 : ℝ) := by
      simp only [CN, n07aAngularMonotoneEnvelope_zero, NNReal.coe_mul]
      exact (mul_le_mul_of_nonneg_left hN₀ (c 0).coe_nonneg).trans_eq (mul_comm _ _)
    have hcₚ : (CN (p - 1) : ℝ) ≤ (C (p - 1) : ℝ) * (N p : ℝ) := by
      have h := (n07aAngularMonotoneEnvelope_oneHigh c N hN (p - 1)).trans
        (mul_le_mul_of_nonneg_left (hN (Nat.sub_le p 1))
          (zero_le : (0 : ℝ≥0) ≤ C (p - 1)))
      exact_mod_cast h
    have hcoef : 1 + (CN (p - 1) : ℝ) ≤ (1 + (C (p - 1) : ℝ)) * (N p : ℝ) := by
      nlinarith only [hcₚ, hN₁ p]
    have hbound : ∀ u,
        MemAngularSobolev (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b u) →
        angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b (B u)) ≤
          k' * (angularSobolevNorm (𝕜 := ℝ) p
            (n07aAngularHilbertEquiv hV γ 0 hI b u) + (N p : ℝ) * ‖u‖) := by
      intro u hu
      have hkbound := n07aAngularInverseTameConstant_mono p
        (A (p - 1)).coe_nonneg (CN 0).coe_nonneg (norm_nonneg B) le_rfl hc₀ hB
      have hinside :
          angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b u) +
            (1 + (CN (p - 1) : ℝ)) * ‖u‖ ≤
          (1 + (C (p - 1) : ℝ)) *
            (angularSobolevNorm (𝕜 := ℝ) p (n07aAngularHilbertEquiv hV γ 0 hI b u) +
              (N p : ℝ) * ‖u‖) := by
        have hs := angularSobolevNorm_nonneg (𝕜 := ℝ) p
          (n07aAngularHilbertEquiv hV γ 0 hI b u)
        have hmul := mul_le_mul_of_nonneg_right hcoef (norm_nonneg u)
        nlinarith only [hmul, mul_nonneg (C (p - 1)).coe_nonneg hs]
      exact (hnorm p hp₁ u hu).trans
        ((mul_le_mul hkbound hinside
          (add_nonneg (angularSobolevNorm_nonneg (𝕜 := ℝ) p _)
            (mul_nonneg (add_nonneg zero_le_one (CN (p - 1)).coe_nonneg)
              (norm_nonneg u))) hk.le).trans_eq (by dsimp only [k']; ring))
    exact n07a_uniformAngularLift hV γ hI b B p k' (N p) hk' (hreg p) hbound f

end ContinuousFlexibility.Analysis
