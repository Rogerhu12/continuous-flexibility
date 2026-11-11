import ContinuousFlexibility.Analysis.AngularWeightedInterpolation
import ContinuousFlexibility.Analysis.AngularWeightBounds

/-!
# Interpolation with an additive high-order error

The endpoint error `c * ‖v‖` is incorporated in the diagonal graph weight
`sqrt (w² + (1+c)²)`.  Three-lines interpolation then costs only
`(1+c)^theta * ‖v‖`, with a prefactor independent of `c`.  The final
theorem specializes this argument to the exact Japanese-bracket angular
Sobolev scale, with no restriction on the spectral multiplicities.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ENNReal

/-- The diagonal weight of the Hilbert graph norm. -/
def angularGraphWeight (w : ℕ → ℝ) (A : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (w n ^ 2 + A ^ 2)

theorem angularGraphWeight_nonneg (w : ℕ → ℝ) (A : ℝ) (n : ℕ) :
    0 ≤ angularGraphWeight w A n := Real.sqrt_nonneg _

theorem le_angularGraphWeight_left (w : ℕ → ℝ) (A : ℝ) (n : ℕ) :
    w n ≤ angularGraphWeight w A n :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))

theorem le_angularGraphWeight_right (w : ℕ → ℝ) (A : ℝ) (n : ℕ) :
    A ≤ angularGraphWeight w A n :=
  Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

/-- A fractional graph weight is bounded by the sum of the fractional
principal weight and the fractional error coefficient. -/
theorem angular_sqrt_rpow_le_add {x y theta : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (htheta : 0 ≤ theta) (htheta' : theta ≤ 1) :
    Real.sqrt (x ^ 2 + y ^ 2) ^ theta ≤ x ^ theta + y ^ theta := by
  have hhalf : 0 ≤ theta / 2 := by positivity
  have hhalf' : theta / 2 ≤ 1 := by linarith
  have hexp : (1 / (2 : ℝ)) * theta = theta / 2 := by ring
  have htwo : (2 : ℝ) * (theta / 2) = theta := by ring
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (add_nonneg (sq_nonneg x) (sq_nonneg y)), hexp]
  calc
    (x ^ 2 + y ^ 2) ^ (theta / 2) ≤
        (x ^ 2) ^ (theta / 2) + (y ^ 2) ^ (theta / 2) :=
      Real.rpow_add_le_add_rpow (sq_nonneg x) (sq_nonneg y) hhalf hhalf'
    _ = x ^ theta + y ^ theta := by
      rw [← Real.rpow_natCast_mul hx 2, ← Real.rpow_natCast_mul hy 2]
      simp only [Nat.cast_ofNat, htwo]

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

/-- The graph-weight form of interpolation.  The constant in front of the
estimate is independent of the high-order error coefficient `c`. -/
theorem angular_graph_interpolation (K : lp E 2 →L[ℂ] lp E 2)
    (w : ℕ → ℝ) (hw : ∀ n, 0 < w n)
    {a c czero : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hczero : 0 ≤ czero)
    (hzero : ‖K‖ ≤ a + czero)
    (hone : ∀ v : lp E 2, MemAngularWeight (𝕜 := ℂ) w v →
      MemAngularWeight (𝕜 := ℂ) w (K v) ∧
      angularWeightNorm (𝕜 := ℂ) w (K v) ≤
        a * angularWeightNorm (𝕜 := ℂ) w v + c * ‖v‖)
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta' : theta ≤ 1)
    (v : lp E 2) (hv : MemAngularWeight (𝕜 := ℂ) (fun n => w n ^ theta) v) :
    MemAngularWeight (𝕜 := ℂ) (fun n => w n ^ theta) (K v) ∧
      angularWeightNorm (𝕜 := ℂ) (fun n => w n ^ theta) (K v) ≤
        (1 + a + czero) *
          (angularWeightNorm (𝕜 := ℂ) (fun n => w n ^ theta) v +
            (1 + c) ^ theta * ‖v‖) := by
  let b := angularGraphWeight w (1 + c)
  have hA : 0 ≤ 1 + c := by positivity
  have hb : ∀ n, 0 < b n := fun n =>
    (hw n).trans_le (le_angularGraphWeight_left w (1 + c) n)
  have hwb : ∀ n, |w n| ≤ |b n| := fun n => by
    rw [abs_of_pos (hw n), abs_of_pos (hb n)]
    exact le_angularGraphWeight_left w (1 + c) n
  have hcb : ∀ n, |c| ≤ |b n| := fun n => by
    rw [abs_of_nonneg hc, abs_of_pos (hb n)]
    exact (by linarith : c ≤ 1 + c).trans (le_angularGraphWeight_right w (1 + c) n)
  have hC : 0 ≤ 1 + a + czero := by positivity
  have hbase : ‖K‖ ≤ 1 + a + czero := hzero.trans (by linarith)
  have hhigh : ∀ u : lp E 2, MemAngularWeight (𝕜 := ℂ) b u →
      MemAngularWeight (𝕜 := ℂ) w (K u) ∧
      angularWeightNorm (𝕜 := ℂ) w (K u) ≤
        (1 + a + czero) * angularWeightNorm (𝕜 := ℂ) b u := by
    intro u hu
    obtain ⟨hmem, hbound⟩ := hone u (hu.mono hwb)
    have hprincipal := angularWeightNorm_mono hu hwb
    have herror := angularWeightNorm_mono hu hcb
    rw [angularWeightNorm_const, abs_of_nonneg hc] at herror
    refine ⟨hmem, hbound.trans ?_⟩
    calc
      a * angularWeightNorm (𝕜 := ℂ) w u + c * ‖u‖ ≤
          a * angularWeightNorm (𝕜 := ℂ) b u + angularWeightNorm (𝕜 := ℂ) b u :=
        add_le_add (mul_le_mul_of_nonneg_left hprincipal ha) herror
      _ ≤ (1 + a + czero) * angularWeightNorm (𝕜 := ℂ) b u := by
        nlinarith only [mul_nonneg hczero (angularWeightNorm_nonneg (𝕜 := ℂ) b u)]
  have hcompare : ∀ n, |b n ^ theta| ≤ w n ^ theta + (1 + c) ^ theta := by
    intro n
    rw [abs_of_nonneg (Real.rpow_nonneg (hb n).le theta)]
    exact angular_sqrt_rpow_le_add (hw n).le hA htheta htheta'
  have hconstant := memAngularWeight_const (𝕜 := ℂ) ((1 + c) ^ theta) v
  have hvb : MemAngularWeight (𝕜 := ℂ) (fun n => b n ^ theta) v :=
    hv.of_le_add hconstant hcompare
  have hweight : angularWeightNorm (𝕜 := ℂ) (fun n => b n ^ theta) v ≤
      angularWeightNorm (𝕜 := ℂ) (fun n => w n ^ theta) v +
        (1 + c) ^ theta * ‖v‖ := by
    have h := angularWeightNorm_le_add hv hconstant hcompare
    simpa only [angularWeightNorm_const, abs_of_nonneg (Real.rpow_nonneg hA theta)] using h
  obtain ⟨hmem, hbound⟩ := angular_three_lines K w b hw hb hC hbase hhigh
    htheta htheta' v hvb
  exact ⟨hmem, hbound.trans (mul_le_mul_of_nonneg_left hweight hC)⟩

/-- The interpolation estimate used by the angular commutator lemma.
Its prefactor depends on `a` and the base error `czero`, while the large
order-`m` error appears only as `(1+c)^(k/m)`. -/
theorem angular_sobolev_interpolation (K : lp E 2 →L[ℂ] lp E 2)
    {m : ℕ} (hm : 0 < m) {a c czero : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hczero : 0 ≤ czero)
    (hzero : ‖K‖ ≤ a + czero)
    (hone : ∀ v : lp E 2, MemAngularSobolev (𝕜 := ℂ) m v →
      MemAngularSobolev (𝕜 := ℂ) m (K v) ∧
      angularSobolevNorm (𝕜 := ℂ) m (K v) ≤
        a * angularSobolevNorm (𝕜 := ℂ) m v + c * ‖v‖)
    {k : ℕ} (hk : k ≤ m) (v : lp E 2) (hv : MemAngularSobolev (𝕜 := ℂ) k v) :
    MemAngularSobolev (𝕜 := ℂ) k (K v) ∧
      angularSobolevNorm (𝕜 := ℂ) k (K v) ≤
        (1 + a + czero) *
          (angularSobolevNorm (𝕜 := ℂ) k v + (1 + c) ^ ((k : ℝ) / m) * ‖v‖) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (k : ℝ) ≤ m := by exact_mod_cast hk
  have ht : 0 ≤ (k : ℝ) / m := div_nonneg (Nat.cast_nonneg _) hmR.le
  have ht' : (k : ℝ) / m ≤ 1 := (div_le_one hmR).mpr hkR
  have hexp : (m : ℝ) * ((k : ℝ) / m) = k := by field_simp
  have hpower : (fun n => (angularWeight n ^ m : ℝ) ^ ((k : ℝ) / m)) =
      (fun n => angularWeight n ^ k) := by
    funext n
    rw [← Real.rpow_natCast_mul (angularWeight_nonneg n) m, hexp, Real.rpow_natCast]
  have hv' : MemAngularWeight (𝕜 := ℂ)
      (fun n => (angularWeight n ^ m : ℝ) ^ ((k : ℝ) / m)) v := by
    rw [hpower]
    exact hv
  have h := angular_graph_interpolation K (fun n => angularWeight n ^ m)
    (fun n => pow_pos (angularWeight_pos n) m) ha hc hczero hzero hone ht ht' v hv'
  rw [hpower] at h
  exact h

end ContinuousFlexibility.Analysis
