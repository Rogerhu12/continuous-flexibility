import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseLabelPositiveWords

/-!
# Sample conversion and common budgets for a label and its slope

The prefix arithmetic uses only a graded parameter space and scalar
sample costs. Keeping it separate avoids unfolding the actual atlas
while aligning the two angular horizons.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements

variable {E I : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem n04PositiveGeometry_labelPair_sample_prefix
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (U : Set E)
    (α : Bool → ℕ → E × ℝ → ℝ) (rel : I → Bool → ℕ → Prop)
    (sourceH : ℕ → ℝ) (sampleE sampleH : I → ℝ)
    (hE : ∀ i, 1 ≤ sampleE i) (hH : ∀ i, 0 ≤ sampleH i) (base : ℕ)
    (Jδ : ∀ side m θ, SmoothDirections U (fun x => α side m (x, θ) - θ))
    (hdefect : ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ u : ℕ, u ≤ s → ∀ b : ℕ, b ≤ u + 5 →
      ∀ side m θ, ∀ J : SmoothDirections U
        (fun x => iteratedDeriv b (fun η => α side m (x, η) - η) θ),
      ∀ x ∈ U, p low x ≤ 1 → ∀ v : Fin k → E,
      (∀ j, p low (v j) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) x ≤ R →
      (∀ j, p (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * sourceH m *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)))
    (hslope : ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ k : ℕ, k ≤ K → ∀ d : ℕ, d ≤ 4 → ∀ u : ℕ, u ≤ s →
      ∀ side m θ, ∀ J : SmoothDirections U
        (fun x => iteratedDeriv (u + d) (deriv (fun η => α side m (x, η))) θ),
      ∀ x ∈ U, p low x ≤ 1 → ∀ v : Fin k → E,
      (∀ j, p low (v j) ≤ 1) → ∀ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) x ≤ R →
      (∀ j, p (low + s + shift * K + 1) (v j) ≤ R) →
      |J.D k x v| ≤ A * parameterHeightWeight (sourceH m) k *
        R ^ (((u + shift * k : ℕ) : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)))
    (hsample : ∀ A : ℝ, 1 ≤ A → ∃ B : ℝ, 1 ≤ B ∧
      ∀ i side m, rel i side m → ∀ k,
      A * parameterHeightWeight (sourceH m) k ≤
        B * sampleE i ^ B * parameterHeightWeight (sampleH i) k) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i side m, rel i side m →
      ∀ Ja : SmoothDirections (U ×ˢ univ) (α (!side) m),
      ∀ Jb : SmoothDirections (U ×ˢ univ)
        (fun y => deriv (fun η => α (!side) m (y.1, η)) y.2),
      ∀ z ∈ U, p low z ≤ 1 → ∀ θ : ℝ, ∀ R : ℝ, 1 ≤ R →
      p (low + s + shift * K + 1) z ≤ R →
      let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
      let M := A * sampleE i ^ A
      let H := sampleH i
      let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
      N04BoundaryPositiveWordBounds Ja K s 1 z θ P M H t shift ∧
        N04BoundaryWordBounds Jb K s 1 z θ P M H t shift := by
  obtain ⟨Bd, hBd, pd⟩ := hdefect
  obtain ⟨Bb, _, pb⟩ := hslope
  let low := Bd + Bb
  have hdl : Bd ≤ low := by dsimp only [low]; omega
  have hbl : Bb ≤ low := by dsimp only [low]; omega
  refine ⟨low, hBd.trans hdl, fun K => ?_⟩
  obtain ⟨cd, pdc⟩ := pd K
  obtain ⟨cb, pbc⟩ := pb K
  let shift := cd + cb
  have hcd : cd ≤ shift := by dsimp only [shift]; omega
  have hcb : cb ≤ shift := by dsimp only [shift]; omega
  refine ⟨shift, fun s => ?_⟩
  let sd := s + (shift - cd) * K
  let sb := s + (shift - cb) * K
  obtain ⟨Ad, hAd, hd⟩ := pdc sd
  obtain ⟨Ab, hAb, hb⟩ := pbc sb
  obtain ⟨Cd, hCd, htd⟩ := hsample Ad hAd
  obtain ⟨Cb, hCb, htb⟩ := hsample Ab hAb
  let A := Cd + Cb + 1
  have hA : 1 ≤ A := by dsimp only [A]; linarith only [hCd, hCb]
  have hCdA : Cd ≤ A := by dsimp only [A]; linarith only [hCb]
  have hCbA : Cb ≤ A := by dsimp only [A]; linarith only [hCd]
  refine ⟨A, hA, ?_⟩
  intro i side m hm Ja Jb z hz hzlow θ R hR hzR
  let M := A * sampleE i ^ A
  let H := sampleH i
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  let P := fun v => p low v ≤ 1 ∧ p (low + s + shift * K + 1) v ≤ R
  have hM : 0 ≤ M := mul_nonneg (zero_le_one.trans hA)
    (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {B : ℝ} (hBA : B ≤ A) : B * sampleE i ^ B ≤ M :=
    mul_le_mul hBA (Real.rpow_le_rpow_of_exponent_le (hE i) hBA)
      (Real.rpow_nonneg (zero_le_one.trans (hE i)) _) (zero_le_one.trans hA)
  have hden (c : ℕ) (hc : c ≤ shift) :
      (s + (shift - c) * K) + c * K = s + shift * K := by
    calc
      _ = s + ((shift - c) + c) * K := by ring
      _ = _ := by rw [Nat.sub_add_cancel hc]
  have hhigh (l c : ℕ) (hl : l ≤ low) (hc : c ≤ shift) :
      l + (s + (shift - c) * K) + c * K + 1 ≤ low + s + shift * K + 1 := by
    have he := hden c hc
    omega
  have htpow (a : ℕ) : t ^ a =
      R ^ ((a : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  have hfinish {c u k : ℕ} {Z v : ℝ} (hc : c ≤ shift)
      (hZ : Z ≤ M * parameterHeightWeight H k)
      (hv : ‖v‖ ≤ Z * R ^ (((u + c * k : ℕ) : ℝ) /
        ((((s + (shift - c) * K) + c * K : ℕ) : ℝ) + 1))) :
      ‖v‖ ≤ M * parameterHeightWeight H k * t ^ (u + shift * k) := by
    have hpow : R ^ (((u + c * k : ℕ) : ℝ) /
        ((((s + (shift - c) * K) + c * K : ℕ) : ℝ) + 1)) ≤
        t ^ (u + shift * k) := by
      rw [hden c hc, ← htpow (u + c * k)]
      exact pow_le_pow_right₀ ht (Nat.add_le_add_left (Nat.mul_le_mul_right k hc) u)
    exact hv.trans (mul_le_mul hZ hpow (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (mul_nonneg hM (parameterHeightWeight_nonneg (hH i) k)))
  have hmatb (k : ℕ) : Ab * parameterHeightWeight (sourceH m) k ≤
      M * parameterHeightWeight H k :=
    (htb i side m hm k).trans (mul_le_mul_of_nonneg_right
      (hcost hCbA) (parameterHeightWeight_nonneg (hH i) k))
  have hmatd (k : ℕ) (hk : 0 < k) : Ad * sourceH m ≤
      M * parameterHeightWeight H k := by
    have h := (htd i side m hm k).trans (mul_le_mul_of_nonneg_right
      (hcost hCdA) (parameterHeightWeight_nonneg (hH i) k))
    simpa only [parameterHeightWeight, if_neg (Nat.ne_of_gt hk)] using h
  have hb' (k : ℕ) (hk : k ≤ K) (u : ℕ) (hu : u ≤ s) (d : ℕ) (hd' : d ≤ 1)
      (J : SmoothDirections U
        (fun x => iteratedDeriv (u + d) (deriv (fun η => α (!side) m (x, η))) θ))
      (v : Fin k → E) (hv : ∀ j, P (v j)) :
      ‖J.D k z v‖ ≤ M * parameterHeightWeight H k * t ^ (u + shift * k) := by
    have h := hb k hk d (by omega) u (by dsimp only [sb]; omega) (!side) m θ J z hz
      ((hp hbl z).trans hzlow) v (fun j => (hp hbl (v j)).trans (hv j).1) R hR
      ((hp (hhigh Bb cb hbl hcb) z).trans hzR)
      (fun j => (hp (hhigh Bb cb hbl hcb) (v j)).trans (hv j).2)
    exact hfinish hcb (hmatb k) (by simpa only [Real.norm_eq_abs] using h)
  have hd' (k : ℕ) (hkpos : 0 < k) (hk : k ≤ K)
      (v : Fin k → E) (hv : ∀ j, P (v j)) :
      ‖(Jδ (!side) m θ).D k z v‖ ≤
        M * parameterHeightWeight H k * t ^ (shift * k) := by
    have h := hd k hk 0 (Nat.zero_le _) 0 (by omega) (!side) m θ (Jδ (!side) m θ) z hz
      ((hp hdl z).trans hzlow) v (fun j => (hp hdl (v j)).trans (hv j).1) R hR
      ((hp (hhigh Bd cd hdl hcd) z).trans hzR)
      (fun j => (hp (hhigh Bd cd hdl hcd) (v j)).trans (hv j).2)
    simpa only [Nat.zero_add] using
      hfinish (u := 0) hcd (hmatd k hkpos) (by simpa only [Real.norm_eq_abs] using h)
  constructor
  · exact n04PositiveGeometry_inverseLabel_positive_words Ja Jb K s z hz θ P
      (Jδ (!side) m θ) M H t shift hd'
      (fun k hk u hu v hv => by
        simpa only [Nat.add_zero] using hb' k hk u hu 0 (by omega)
          (smoothDirections_angularStateSlice Jb (u + 0) θ) v hv)
  · apply n04PositiveGeometry_boundaryWord_of_angular Jb
      (smoothDirections_angularStateSlice Jb) K s 1 z hz θ P M H t shift
    intro k hk u hu d hd' v hv
    exact hb' k hk u hu d hd' (smoothDirections_angularStateSlice Jb (u + d) θ) v hv

end ContinuousFlexibility.Analysis
