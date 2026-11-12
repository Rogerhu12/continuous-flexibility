import ContinuousFlexibility.Analysis.N01cWeightAbsorption

/-!
# The polynomial envelope of the forcing head

Tame circle composition contributes a high outer-speed norm and a
fixed low outer norm times the derivative defect. If the defect has a
fixed additive loss, this is one requested-order aggregate times one
fixed-order aggregate. The original material weight is retained.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

/-- Keep the additive offset outside the spatial-order quantifier while
transporting an opaque indexed bound. -/
theorem n01c_transport_offset_bounds
    (P Q : ℕ → ℕ → ℝ → Prop)
    (hP : ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ P d s B)
    (hstep : ∀ d s B, 0 < B → P d s B → Q d s B) :
    ∃ d : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ Q d s B := by
  obtain ⟨d, hd⟩ := hP
  refine ⟨d, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := hd s
  exact ⟨B, hB, hstep d s B hB hb⟩

theorem n01c_headComposition_envelope {I : Type*}
    (head outer defect R : ℕ → I → ℝ) (H E : I → ℝ)
    (K : ℕ → ℝ) (loss qoffset : ℕ)
    (hH : ∀ i, 0 ≤ H i) (hE : ∀ i, 1 ≤ E i)
    (hR : ∀ n i, 1 ≤ R n i)
    (hRmono : ∀ a b, a ≤ b → ∀ i, R a i ≤ R b i)
    (hK : ∀ s, 0 ≤ K s)
    (hdefectNonneg : ∀ s i, 0 ≤ defect s i)
    (hcomp : ∀ s i,
      head s i ≤ K s * (outer s i + outer 3 i * defect (s - 1) i))
    (houter : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i,
      outer s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B * R (s + loss + offset) i)
    (hdefect : ∀ s : ℕ, ∃ Q : ℝ, 0 < Q ∧ ∀ i,
      defect s i ≤ Q * R (s + qoffset) i) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i,
      head s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + offset) i * R offset i := by
  obtain ⟨o, ho⟩ := houter
  obtain ⟨B₃, hB₃, hb₃⟩ := ho 3
  let offset : ℕ := 3 + loss + o + qoffset
  refine ⟨offset, fun s => ?_⟩
  obtain ⟨Bₛ, hBₛ, hbₛ⟩ := ho s
  obtain ⟨Q, hQ, hq⟩ := hdefect (s - 1)
  let A : ℝ := max Bₛ B₃
  obtain ⟨B, hB, habsorb⟩ := exists_sameConstant_materialWeight_bound
    (K s * (Bₛ + B₃ * Q)) A (3 / 4 : ℝ)
  refine ⟨B, hB, fun i => ?_⟩
  let W : ℝ := H i ^ (3 / 4 : ℝ) * E i ^ A
  let U : ℝ := R (s + offset) i
  let R₀ : ℝ := R offset i
  have hU : 0 ≤ U := zero_le_one.trans (hR _ i)
  have hR₀ : 1 ≤ R₀ := hR _ i
  have hW : 0 ≤ W := mul_nonneg (Real.rpow_nonneg (hH i) _)
    (Real.rpow_nonneg (zero_le_one.trans (hE i)) _)
  have hweight (C : ℝ) (hC : 0 ≤ C) (hCA : C ≤ A) :
      C * H i ^ (3 / 4 : ℝ) * E i ^ C ≤ C * W := by
    have hp := Real.rpow_le_rpow_of_exponent_le (hE i) hCA
    simpa only [W, mul_assoc] using
      mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Real.rpow_nonneg (hH i) _))
  have hOs : outer s i ≤ Bₛ * W * U :=
    (hbₛ i).trans (mul_le_mul
      (hweight Bₛ hBₛ.le (le_max_left _ _))
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) (mul_nonneg hBₛ.le hW))
  have hO₃ : outer 3 i ≤ B₃ * W * R₀ :=
    (hb₃ i).trans (mul_le_mul
      (hweight B₃ hB₃.le (le_max_right _ _))
      (hRmono _ _ (by dsimp only [offset]; omega) i)
      (zero_le_one.trans (hR _ i)) (mul_nonneg hB₃.le hW))
  have hQbound : defect (s - 1) i ≤ Q * U :=
    (hq i).trans (mul_le_mul_of_nonneg_left
      (hRmono _ _ (by dsimp only [offset]; omega) i) hQ.le)
  have hsource : outer s i + outer 3 i * defect (s - 1) i ≤
      (Bₛ + B₃ * Q) * W * U * R₀ := by
    have hfirst : outer s i ≤ Bₛ * W * U * R₀ :=
      hOs.trans (le_mul_of_one_le_right (by positivity) hR₀)
    have hsecond : outer 3 i * defect (s - 1) i ≤
        (B₃ * W * R₀) * (Q * U) :=
      mul_le_mul hO₃ hQbound (hdefectNonneg _ i) (by positivity)
    calc
      _ ≤ Bₛ * W * U * R₀ + (B₃ * W * R₀) * (Q * U) :=
        add_le_add hfirst hsecond
      _ = _ := by ring
  calc
    head s i ≤ K s * (outer s i + outer 3 i * defect (s - 1) i) := hcomp s i
    _ ≤ K s * ((Bₛ + B₃ * Q) * W * U * R₀) :=
      mul_le_mul_of_nonneg_left hsource (hK s)
    _ = (K s * (Bₛ + B₃ * Q)) * H i ^ (3 / 4 : ℝ) * E i ^ A *
        (U * R₀) := by dsimp only [W]; ring
    _ ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B * (U * R₀) :=
      habsorb _ _ _ (hH i) (hE i) (mul_nonneg hU (zero_le_one.trans hR₀))
    _ = _ := by ring

/-- Global material absorption is used only for factors which do not
carry the retained material weight of the forcing head. -/
theorem n01c_productEnvelope_absorb {I : Type*}
    (F R : ℕ → I → ℝ) (H E : I → ℝ)
    (hR : ∀ n i, 0 ≤ R n i)
    (hweight : ∀ A : ℝ, ∃ Q : ℝ, 0 < Q ∧ ∀ i,
      H i ^ (3 / 4 : ℝ) * E i ^ A ≤ Q)
    (hF : ∃ offset : ℕ, ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ i,
      F s i ≤ B * H i ^ (3 / 4 : ℝ) * E i ^ B *
        R (s + offset) i * R offset i) :
    ∃ offset : ℕ, ∀ s : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i,
      F s i ≤ C * R (s + offset) i * R offset i := by
  obtain ⟨offset, ho⟩ := hF
  refine ⟨offset, fun s => ?_⟩
  obtain ⟨B, hB, hb⟩ := ho s
  obtain ⟨Q, hQ, hq⟩ := hweight B
  refine ⟨B * Q, mul_pos hB hQ, fun i => ?_⟩
  have hw : B * H i ^ (3 / 4 : ℝ) * E i ^ B ≤ B * Q := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hq i) hB.le
  exact (hb i).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hw (hR _ i)) (hR _ i))

end ContinuousFlexibility.Analysis
