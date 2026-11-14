module

public import ContinuousFlexibility.Radial.TailNodeUniqueness
public import ContinuousFlexibility.Radial.TailNodeProducts

/-!
# Mass and resistance bounds for the natural node line

The exact edge coefficients need only satisfy a lower diagonal bound and
an upper coupling bound. The two neighboring mass--resistance inequalities
then give the continued-fraction smallness conditions, the physical node
decay, and summability in the weighted mass norm of exponent one.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

/-- A large mass--resistance product makes the edge coupling small compared
with either adjacent mass. -/
theorem tailNode_coupling_le_eighth_mass {Λ K μ R c : ℝ}
    (hR : 0 < R) (hK : 32 ≤ K) (hlarge : K ≤ Λ * μ * R)
    (hc : c ≤ 2 / R) : c ≤ Λ * μ / 8 := by
  apply (mul_le_mul_iff_right₀ hR).mp
  have hcR : c * R ≤ 2 := (le_div_iff₀ hR).mp hc
  nlinarith only [hcR, hK, hlarge]

/-- Two mass bounds give the corresponding bound in square-root mass
coordinates. This is the normalization used in the node Hilbert space. -/
theorem tailNode_coupling_le_sqrt_mass {a μ ν c : ℝ}
    (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hc : 0 ≤ c)
    (hleft : c ≤ a * μ) (hright : c ≤ a * ν) :
    c ≤ a * (Real.sqrt μ * Real.sqrt ν) := by
  apply (sq_le_sq₀ hc
    (mul_nonneg ha (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))).mp
  calc
    c ^ 2 = c * c := by ring
    _ ≤ (a * μ) * (a * ν) :=
      mul_le_mul hleft hright hc (mul_nonneg ha hμ)
    _ = (a * (Real.sqrt μ * Real.sqrt ν)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hμ, Real.sq_sqrt hν]
      ring

/-- The normalized couplings are uniformly bounded, as required by the
Casoratian uniqueness theorem. -/
theorem tailNaturalNode_normalized_coupling_bound {c μ R : ℕ → ℝ} {Λ K : ℝ}
    (hc : ∀ n, 0 ≤ c n) (hμ : ∀ n, 0 < μ n) (hR : ∀ n, 0 < R n)
    (hΛ : 0 < Λ) (hK : 32 ≤ K)
    (hupper : ∀ n, c n ≤ 2 / R n)
    (hleft : ∀ n, K ≤ Λ * μ n * R n)
    (hright : ∀ n, K ≤ Λ * μ (n + 1) * R n) :
    ∀ n, |c n| ≤ (Λ / 8) * (Real.sqrt (μ n) * Real.sqrt (μ (n + 1))) := by
  intro n
  rw [abs_of_nonneg (hc n)]
  apply tailNode_coupling_le_sqrt_mass
    (div_nonneg hΛ.le (by norm_num)) (hμ n).le (hμ (n + 1)).le (hc n)
  · simpa only [div_mul_eq_mul_div] using
      tailNode_coupling_le_eighth_mass (hR n) hK (hleft n) (hupper n)
  · simpa only [div_mul_eq_mul_div] using
      tailNode_coupling_le_eighth_mass (hR n) hK (hright n) (hupper n)

/-- The coefficient assumptions of the deep tail imply both quantitative
hypotheses used to construct the positive natural node solution. -/
theorem tailNaturalNode_coefficient_conditions {b c μ R : ℕ → ℝ} {Λ K : ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n)
    (hμ : ∀ n, 0 < μ n) (hR : ∀ n, 0 < R n)
    (hΛ : 0 < Λ) (hK : 32 ≤ K)
    (hlower : ∀ n, Λ * μ n / 2 ≤ b n)
    (hupper : ∀ n, c n ≤ 2 / R n)
    (hleft : ∀ n, K ≤ Λ * μ n * R n)
    (hright : ∀ n, K ≤ Λ * μ (n + 1) * R n) :
    (∀ n, c n ^ 2 / (b n * b (n + 1)) ∈ Icc 0 (1 / 8)) ∧
    (∀ n, Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) ≤
      (1 / 4 : ℝ) * Real.sqrt (μ n)) := by
  have hL (n : ℕ) : c n ≤ Λ * μ n / 8 :=
    tailNode_coupling_le_eighth_mass (hR n) hK (hleft n) (hupper n)
  have hU (n : ℕ) : c n ≤ Λ * μ (n + 1) / 8 :=
    tailNode_coupling_le_eighth_mass (hR n) hK (hright n) (hupper n)
  constructor
  · intro n
    have hc₀ : c n ≤ b n / 4 := by linarith only [hL n, hlower n]
    have hc₁ : c n ≤ b (n + 1) / 4 := by
      linarith only [hU n, hlower (n + 1)]
    have hprod := mul_le_mul hc₀ hc₁ (hc n).le
      (div_nonneg (hb n).le (by norm_num : (0 : ℝ) ≤ 4))
    refine ⟨div_nonneg (sq_nonneg _) (mul_pos (hb n) (hb (n + 1))).le, ?_⟩
    apply (div_le_iff₀ (mul_pos (hb n) (hb (n + 1)))).mpr
    nlinarith only [hprod, mul_pos (hb n) (hb (n + 1))]
  · intro n
    have hroot : c n ≤ (Λ / 8) *
        (Real.sqrt (μ n) * Real.sqrt (μ (n + 1))) :=
      tailNode_coupling_le_sqrt_mass
        (div_nonneg hΛ.le (by norm_num)) (hμ n).le (hμ (n + 1)).le (hc n).le
        (by simpa only [div_mul_eq_mul_div] using hL n)
        (by simpa only [div_mul_eq_mul_div] using hU n)
    have hnum : Real.sqrt (μ (n + 1)) * c n ≤
        ((1 / 4 : ℝ) * Real.sqrt (μ n)) * b (n + 1) := by
      calc
        Real.sqrt (μ (n + 1)) * c n ≤
            Real.sqrt (μ (n + 1)) *
              ((Λ / 8) * (Real.sqrt (μ n) * Real.sqrt (μ (n + 1)))) :=
          mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
        _ = (Λ / 8) * Real.sqrt (μ n) * Real.sqrt (μ (n + 1)) ^ 2 := by ring
        _ = (Λ * μ (n + 1) / 8) * Real.sqrt (μ n) := by
          rw [Real.sq_sqrt (hμ (n + 1)).le]
          ring
        _ ≤ (b (n + 1) / 4) * Real.sqrt (μ n) :=
          mul_le_mul_of_nonneg_right (by linarith only [hlower (n + 1)])
            (Real.sqrt_nonneg _)
        _ = ((1 / 4 : ℝ) * Real.sqrt (μ n)) * b (n + 1) := by ring
    calc
      Real.sqrt (μ (n + 1)) * (c n / b (n + 1)) =
          (Real.sqrt (μ (n + 1)) * c n) / b (n + 1) := by ring
      _ ≤ _ := (div_le_iff₀ (hb (n + 1))).mpr hnum

/-- The unnormalized coupling-to-diagonal ratio has the physical
mass--resistance bound. -/
theorem tailNode_ratio_le_mass_resistance {Λ μ R b c : ℝ}
    (hΛ : 0 < Λ) (hμ : 0 < μ) (hR : 0 < R) (hb : 0 < b)
    (hlower : Λ * μ / 2 ≤ b) (hupper : c ≤ 2 / R) :
    c / b ≤ 4 / (Λ * μ * R) := by
  apply (div_le_iff₀ hb).mpr
  calc
    c ≤ 2 / R := hupper
    _ = (4 / (Λ * μ * R)) * (Λ * μ / 2) := by
      field_simp [hΛ.ne', hμ.ne', hR.ne'] <;> ring
    _ ≤ (4 / (Λ * μ * R)) * b :=
      mul_le_mul_of_nonneg_left hlower (by positivity)

/-- The same physical decay factor contracts the mass-weighted values.
Only the mass--resistance bound on the preceding mass is needed here. -/
theorem tailNode_decay_mass_factor {Λ K μ ν R : ℝ}
    (hΛ : 0 < Λ) (hK : 0 < K) (hν : 0 < ν) (hR : 0 < R)
    (hlarge : K ≤ Λ * μ * R) :
    ν * (8 / (Λ * ν * R)) ≤ (8 / K) * μ := by
  calc
    ν * (8 / (Λ * ν * R)) = 8 / (Λ * R) := by
      field_simp [hΛ.ne', hν.ne', hR.ne'] <;> ring
    _ ≤ (8 * μ) / K := by
      apply (div_le_div_iff₀ (mul_pos hΛ hR) hK).mpr
      nlinarith only [hlarge]
    _ = (8 / K) * μ := by ring

/-- A constant one-step contraction gives geometric decay from every
starting node. -/
theorem tailNode_geometric_bound {v : ℕ → ℝ} {q : ℝ}
    (hv : ∀ n, 0 < v n) (hq : 0 ≤ q)
    (hstep : ∀ n, v (n + 1) ≤ q * v n) {m n : ℕ} (hmn : m ≤ n) :
    v n ≤ q ^ (n - m) * v m := by
  have h := tailNode_ratio_le_prod hv (fun _ => hq) hstep hmn
  have hp : (∏ k ∈ Finset.Ico m n, q) = q ^ (n - m) := by simp
  rw [hp] at h
  exact (div_le_iff₀ (hv m)).mp h

theorem tailNode_summable_of_step {v : ℕ → ℝ} {q : ℝ}
    (hv : ∀ n, 0 < v n) (hq : 0 ≤ q) (hq₁ : q < 1)
    (hstep : ∀ n, v (n + 1) ≤ q * v n) : Summable v := by
  have hgeo := (summable_geometric_of_lt_one hq hq₁).mul_right (v 0)
  apply Summable.of_nonneg_of_le (fun n => (hv n).le) ?_ hgeo
  intro n
  simpa only [Nat.sub_zero] using tailNode_geometric_bound hv hq hstep (Nat.zero_le n)

/-- The natural node line has physical one-step decay, geometric decay of
the mass-weighted values, and both weighted square and absolute summability.
The product estimate keeps every individual mass and resistance factor. -/
theorem exists_tailNaturalNodeLine_bounds {b c μ R : ℕ → ℝ} {Λ K : ℝ}
    (hb : ∀ n, 0 < b n) (hc : ∀ n, 0 < c n)
    (hμ : ∀ n, 0 < μ n) (hR : ∀ n, 0 < R n)
    (hΛ : 0 < Λ) (hK : 32 ≤ K)
    (hlower : ∀ n, Λ * μ n / 2 ≤ b n)
    (hupper : ∀ n, c n ≤ 2 / R n)
    (hleft : ∀ n, K ≤ Λ * μ n * R n)
    (hright : ∀ n, K ≤ Λ * μ (n + 1) * R n) :
    ∃ y : ℕ → ℝ,
      y 0 = 1 ∧ (∀ n, 0 < y n) ∧
      (∀ n, b (n + 1) * y (n + 1) =
        c n * y n + c (n + 1) * y (n + 2)) ∧
      Summable (fun n => μ n * y n ^ 2) ∧
      (∀ n, |y (n + 1)| ≤ (8 / (Λ * μ (n + 1) * R n)) * |y n|) ∧
      (∀ n, μ (n + 1) * |y (n + 1)| ≤ (8 / K) * (μ n * |y n|)) ∧
      (∀ m n, m ≤ n → μ n * |y n| ≤ (8 / K) ^ (n - m) * (μ m * |y m|)) ∧
      Summable (fun n => μ n * |y n|) ∧
      ∀ m n, m ≤ n →
        |y n| ≤ |y m| * ∏ k ∈ Finset.Ico m n, 8 / (Λ * μ (k + 1) * R k) := by
  obtain ⟨hε, hr⟩ := tailNaturalNode_coefficient_conditions hb hc hμ hR hΛ hK
    hlower hupper hleft hright
  obtain ⟨y, hy₀, hypos, hyratio, hyrec, _, hysum⟩ :=
    exists_tailNaturalNodeLine hb hc hμ hε hr
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hK
  have hq : 0 ≤ (8 : ℝ) / K := div_nonneg (by norm_num) hKpos.le
  have hq₁ : (8 : ℝ) / K < 1 := by
    apply (div_lt_iff₀ hKpos).mpr
    linarith only [hK]
  have hstep (n : ℕ) : |y (n + 1)| ≤
      (8 / (Λ * μ (n + 1) * R n)) * |y n| := by
    rw [abs_of_pos (hypos (n + 1)), abs_of_pos (hypos n)]
    apply (div_le_iff₀ (hypos n)).mp
    rw [hyratio n]
    have ht := tailFractionLimit_mem (fun k => c k ^ 2 / (b k * b (k + 1))) hε n
    have hcoeff := tailNode_ratio_le_mass_resistance hΛ (hμ (n + 1)) (hR n)
      (hb (n + 1)) (hlower (n + 1)) (hupper n)
    calc
      c n / b (n + 1) * tailFractionLimit
          (fun k => c k ^ 2 / (b k * b (k + 1))) hε n ≤
          (4 / (Λ * μ (n + 1) * R n)) * 2 :=
        mul_le_mul hcoeff ht.2 (zero_le_one.trans ht.1)
          (div_nonneg (by norm_num) (mul_pos (mul_pos hΛ (hμ (n + 1))) (hR n)).le)
      _ = 8 / (Λ * μ (n + 1) * R n) := by ring
  have hmassstep (n : ℕ) : μ (n + 1) * |y (n + 1)| ≤
      (8 / K) * (μ n * |y n|) := by
    calc
      μ (n + 1) * |y (n + 1)| ≤
          μ (n + 1) * ((8 / (Λ * μ (n + 1) * R n)) * |y n|) :=
        mul_le_mul_of_nonneg_left (hstep n) (hμ (n + 1)).le
      _ = (μ (n + 1) * (8 / (Λ * μ (n + 1) * R n))) * |y n| := by ring
      _ ≤ ((8 / K) * μ n) * |y n| :=
        mul_le_mul_of_nonneg_right
          (tailNode_decay_mass_factor hΛ hKpos (hμ (n + 1)) (hR n) (hleft n))
          (abs_nonneg _)
      _ = (8 / K) * (μ n * |y n|) := by ring
  have hmasspos (n : ℕ) : 0 < μ n * |y n| :=
    mul_pos (hμ n) (abs_pos.mpr (hypos n).ne')
  refine ⟨y, hy₀, hypos, hyrec, hysum, hstep, hmassstep, ?_,
    tailNode_summable_of_step hmasspos hq hq₁ hmassstep, ?_⟩
  · intro m n hmn
    exact tailNode_geometric_bound hmasspos hq hmassstep hmn
  · intro m n hmn
    have hyabs (k : ℕ) : 0 < |y k| := abs_pos.mpr (hypos k).ne'
    have hfactor (k : ℕ) : 0 ≤ 8 / (Λ * μ (k + 1) * R k) :=
      div_nonneg (by norm_num) (mul_pos (mul_pos hΛ (hμ (k + 1))) (hR k)).le
    have hprod := tailNode_ratio_le_prod hyabs hfactor hstep hmn
    have hmul := (div_le_iff₀ (hyabs m)).mp hprod
    simpa only [mul_comm] using hmul

end ContinuousFlexibility.Radial
