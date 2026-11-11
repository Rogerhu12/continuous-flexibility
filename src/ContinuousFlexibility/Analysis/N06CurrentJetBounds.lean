import ContinuousFlexibility.Analysis.N06Neighborhood
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Small current coefficient jets from the N01 directional estimates

The order-zero estimate in N01 contains a constant term.  Smallness of the
actual coefficient difference instead follows from its vanishing at the
reference state and the genuine first derivative along the state segment.
The argument retains the factor `H^(3/4)` and the fixed coefficient power.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

section ScalarDifference

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  {U : Set E} {f : E → ℝ}

/-- A genuine directional tower gives the scalar mean-value bound on any
affine segment contained in its domain. -/
theorem n06_smoothDirections_difference_le (J : SmoothDirections U f)
    (x₀ x : E) {M : ℝ}
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |J.D 1 (x₀ + t • (x - x₀)) (Fin.cons (x - x₀) Fin.elim0)| ≤ M) :
    |f x - f x₀| ≤ M := by
  let g : ℝ → ℝ := fun t => J.D 0 (x₀ + t • (x - x₀)) Fin.elim0
  let dg : ℝ → ℝ := fun t =>
    J.D 1 (x₀ + t • (x - x₀)) (Fin.cons (x - x₀) Fin.elim0)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (dg t) t := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    simpa only [g, dg, HasProjectiveLineDerivAt, HasProjectiveCurveDerivAt,
      zero_add, zero_smul, add_zero, add_smul, add_assoc] using
      (J.derivative 0 (x₀ + t • (x - x₀)) (hsegment t ht) Fin.elim0 (x - x₀))
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖dg t‖ ≤ M := by
    simpa only [dg, Real.norm_eq_abs] using hbound t ht
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
    (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  have he : x₀ + (x - x₀) = x := by abel
  have hx₀ : x₀ ∈ U := by
    simpa only [zero_smul, add_zero] using hsegment 0 (by simp)
  have hx : x ∈ U := by
    simpa only [one_smul, he] using hsegment 1 (by simp)
  simpa only [g, one_smul, zero_smul, add_zero, he, J.zero x hx, J.zero x₀ hx₀,
    sub_zero, norm_one, mul_one, Real.norm_eq_abs] using hm

theorem n06_oneHighVariationWeight_one (p : ℕ → Seminorm ℝ E)
    (base high : ℕ) (x h : E) :
    oneHighVariationWeight p base high x (Fin.cons h Fin.elim0) =
      (1 + p high x) * p base h + p high h := by
  simpa only [tameJetSize, oneHighVariationWeight, Nat.zero_add, Fin.cons_zero] using
    (tameJetSize_one p 0 high base x (Fin.cons h Fin.elim0))

/-- One low smallness bound converts the first one-high-factor estimate
into a linear bound in one fixed, possibly higher, seminorm. -/
theorem n06_oneHighVariationWeight_segment_le
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (base high : ℕ)
    (x₀ x : E) (hlow : p base (x - x₀) ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    oneHighVariationWeight p base high (x₀ + t • (x - x₀) - x₀)
      (Fin.cons (x - x₀) Fin.elim0) ≤ 3 * p (max base high) (x - x₀) := by
  let h := x - x₀
  let N := max base high
  have hbase : p base h ≤ p N h := hp (le_max_left base high) h
  have hhigh : p high h ≤ p N h := hp (le_max_right base high) h
  have hnonneg : 0 ≤ p base h := apply_nonneg _ _
  have hNnonneg : 0 ≤ p N h := apply_nonneg _ _
  have hradial : p high (x₀ + t • (x - x₀) - x₀) ≤ p N h := by
    have he : x₀ + t • (x - x₀) - x₀ = t • h := by dsimp only [h]; abel
    rw [he, map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    have hscale : t * p high h ≤ p high h := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right ht.2 (apply_nonneg (p high) h))
    exact hscale.trans hhigh
  have hproduct : p N h * p base h ≤ p N h := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlow hNnonneg
  rw [n06_oneHighVariationWeight_one]
  have hfirst := mul_le_mul_of_nonneg_right (add_le_add le_rfl hradial) hnonneg
  change (1 + p high (x₀ + t • (x - x₀) - x₀)) * p base h + p high h ≤ 3 * p N h
  nlinarith only [hfirst, hproduct, hbase, hhigh]

theorem n06_smoothDirections_oneHigh_difference_le
    (J : SmoothDirections U f) (p : ℕ → Seminorm ℝ E) (hp : Monotone p)
    (base high : ℕ) (x₀ x : E) {K : ℝ} (hK : 0 ≤ K)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ U)
    (hlow : p base (x - x₀) ≤ 1)
    (hbound : ∀ y ∈ U, ∀ v : Fin 1 → E,
      |J.D 1 y v| ≤ K * oneHighVariationWeight p base high (y - x₀) v) :
    |f x - f x₀| ≤ 3 * K * p (max base high) (x - x₀) := by
  apply n06_smoothDirections_difference_le J x₀ x hsegment
  intro t ht
  exact (hbound _ (hsegment t ht) _).trans
    ((mul_le_mul_of_nonneg_left
      (n06_oneHighVariationWeight_segment_le p hp base high x₀ x hlow t ht) hK).trans_eq
        (by ring))

private theorem n06_currentCoefficientFamily_bound
    (p : ℕ → Seminorm ℝ E) (hp : Monotone p) (base loss : ℕ)
    (x₀ : E) (H E₀ : ℕ → ℝ) (cells : ℕ → Set ℝ)
    (family : Fin 3 → ℕ → ℕ → PolarPoint → E → ℝ)
    (hH : ∀ m, 0 < H m) (hE : ∀ m, 0 < E₀ m)
    (hzero : ∀ i a b y, family i a b y x₀ = 0)
    (hsegment : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, x₀ + t • (x - x₀) ∈ U)
    (hfamily : ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b y,
      a + b ≤ s → y.1 ∈ cells m →
      ∃ J : SmoothDirections U (family i a b y),
        ∀ z ∈ U, ∀ v : Fin 1 → E,
          |J.D 1 z v| ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B *
            oneHighVariationWeight p base (s + loss) (z - x₀) v) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m i a b y,
      a + b ≤ s → y.1 ∈ cells m → ∀ z ∈ U, p base (z - x₀) ≤ 1 →
      |family i a b y z| ≤
        3 * (B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B) * p (max base (s + loss)) (z - x₀) := by
  intro s
  obtain ⟨B, hB, hJ⟩ := hfamily s
  refine ⟨B, hB, ?_⟩
  intro m i a b y hab hy z hz hlow
  obtain ⟨J, hbound⟩ := hJ m i a b y hab hy
  have hK : 0 ≤ B * H m ^ (3 / 4 : ℝ) * E₀ m ^ B :=
    mul_nonneg (mul_nonneg hB.le (Real.rpow_pos_of_pos (hH m) _).le)
      (Real.rpow_pos_of_pos (hE m) _).le
  have hm := n06_smoothDirections_oneHigh_difference_le J p hp base (s + loss)
    x₀ z hK (hsegment z hz) hlow hbound
  simpa only [hzero i a b y, sub_zero] using hm

end ScalarDifference

theorem n06_stateParameterGrading_sub_reference (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (s : ℕ) (z : AnnularState S × ℝ) :
    pairGrading (stateGrading S) realGrading s (z - (C.referenceState, 0)) =
      stateGrading S s (z.1 - C.referenceState) + |z.2| := by
  simp only [pairGrading, realGrading, add_apply, Seminorm.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, Prod.fst_sub, Prod.snd_sub,
    sub_zero, coe_normSeminorm, Real.norm_eq_abs]

/-- The actual common state neighborhood contains the full affine segment
from the reference state to any of its points. -/
theorem n06_stateNeighborhood_segment {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base : ℕ} {ε : ℝ}
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (C.referenceState, 0) + t • (z - (C.referenceState, 0)) ∈
      stateNeighborhood S C base ε := by
  constructor
  · have he : ((C.referenceState, (0 : ℝ)) +
        t • (z - (C.referenceState, 0))).1 - C.referenceState =
        t • (z.1 - C.referenceState) := by
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub]
      abel
    rw [he, map_smul_eq_mul, Real.norm_of_nonneg ht.1]
    have hscale : t * stateGrading S base (z.1 - C.referenceState) ≤
        stateGrading S base (z.1 - C.referenceState) := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right ht.2
          (apply_nonneg (stateGrading S base) (z.1 - C.referenceState)))
    exact hscale.trans_lt hz.1
  · have he : ((C.referenceState, (0 : ℝ)) +
        t • (z - (C.referenceState, 0))).2 = t * z.2 := by
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, sub_zero, zero_add,
        smul_eq_mul]
    rw [he, abs_mul, abs_of_nonneg ht.1]
    have hscale : t * |z.2| ≤ |z.2| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (abs_nonneg z.2)
    exact hscale.trans_lt hz.2

theorem n06_coefficientFamily_reference (D : ReferenceData) (S : PhysicalSpacesData)
    (C : NonlinearGeometryData S) (i : Fin 3) (a b : ℕ) (p : PolarPoint) :
    coefficientFamily D S C i a b p (C.referenceState, 0) = 0 := by
  simp only [coefficientFamily, sub_self, mixedDerivative, iteratedDeriv_const_zero]

/-- The N01 first variation estimate yields a genuinely small coefficient
difference, including all spatial mixed derivatives up to the fixed order. -/
theorem n06_N01_currentCoefficient_bound {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ m (i : Fin 3) a b p,
      a + b ≤ s → p.1 ∈ D.cells m → ∀ z ∈ stateNeighborhood S C base ε,
      stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1 →
      |coefficientFamily D S C i a b p z| ≤
        3 * (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) *
          (stateGrading S (max base (s + loss)) (z.1 - C.referenceState) + |z.2|) := by
  rcases h with ⟨hRef, _, _, _, _, _, _, _, _, _, _, hcoefficient, _⟩
  obtain ⟨_, hprofile⟩ := hRef.1
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 m
  have hpair : Monotone (pairGrading (stateGrading S) realGrading) :=
    pairGrading_monotone (solve_stateGrading_monotone S) (fun _ _ _ _ => le_rfl)
  have hH (m : ℕ) : 0 < T.H (T.sample m) := (hT.2.1 _ (hsample m)).2.1
  have hE (m : ℕ) : 0 < T.E0 (T.sample m) := (hT.2.1 _ (hsample m)).2.2.1
  have hresult := n06_currentCoefficientFamily_bound
    (E := AnnularState S × ℝ) (U := stateNeighborhood S C base ε)
    (pairGrading (stateGrading S) realGrading) hpair base loss (C.referenceState, 0)
    (fun m => T.H (T.sample m)) (fun m => T.E0 (T.sample m)) D.cells
    (coefficientFamily D S C) hH hE (n06_coefficientFamily_reference D S C)
    (fun z hz => n06_stateNeighborhood_segment hz) (fun s => hcoefficient 1 s)
  simpa only [n06_stateParameterGrading_sub_reference] using hresult

/-- At any fixed jet order, a sufficiently high common low order makes
the coefficient difference linear in the final neighborhood radius. -/
theorem n06_N01_currentCoefficient_small {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (h : N01Properties D T S C base loss ε) :
    ∀ s : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, δ ≤ ε → δ ≤ (1 / 2 : ℝ) →
      ∀ m (i : Fin 3) a b p, a + b ≤ s → p.1 ∈ D.cells m →
      ∀ z ∈ stateNeighborhood S C (max base (s + loss)) δ,
      |coefficientFamily D S C i a b p z| ≤
        6 * (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) * δ := by
  obtain ⟨_, hprofile⟩ := h.1.1
  have hsample (m : ℕ) : T.sample m ∈ Ioo D.a D.b :=
    materialSample_mem_radialCore hT hprofile.2.1 m
  intro s
  obtain ⟨B, hB, hbound⟩ := n06_N01_currentCoefficient_bound hT h s
  refine ⟨B, hB, ?_⟩
  intro δ hδε hδ m i a b p hab hp z hz
  have hzold := n06_stateNeighborhood_mono (C := C) (le_max_left base (s + loss)) hδε hz
  have hlow : stateGrading S base (z.1 - C.referenceState) + |z.2| ≤ 1 := by
    have hb := solve_stateGrading_monotone S (le_max_left base (s + loss))
      (z.1 - C.referenceState)
    have h₁ := hz.1
    have h₂ := hz.2
    linarith only [hb, h₁, h₂, hδ]
  have hm := hbound m i a b p hab hp z hzold hlow
  have hsum : stateGrading S (max base (s + loss)) (z.1 - C.referenceState) +
      |z.2| ≤ 2 * δ := by
    have h₁ := hz.1
    have h₂ := hz.2
    linarith only [h₁, h₂]
  have hH := (hT.2.1 _ (hsample m)).2.1
  have hE := (hT.2.1 _ (hsample m)).2.2.1
  have hK : 0 ≤ 3 * (B * T.H (T.sample m) ^ (3 / 4 : ℝ) * T.E0 (T.sample m) ^ B) :=
    mul_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg hB.le (Real.rpow_pos_of_pos hH _).le)
      (Real.rpow_pos_of_pos hE _).le)
  exact hm.trans ((mul_le_mul_of_nonneg_left hsum hK).trans_eq (by ring))

end ContinuousFlexibility.Statements
