module

public import ContinuousFlexibility.Radial.InnerCutNormalization

/-!
# The actual compressed model flux errors in physical normalization

All entries are made from the true R09 representatives of a single
localized construction. The physical height and density factors cancel
exactly, including when the central drift has been retained in kappa.
The only estimates supplied to the uniform envelope are geometric mass,
action and neighboring weight comparisons.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Radial

open Real
open ContinuousFlexibility.Statements
open scoped BigOperators Matrix.Norms.L2Operator

variable {B : BufferData} {C K : ℝ} (M : InnerBufferLocalizedData B C K)

def InnerBufferLocalizedData.modelFluxError : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k => bufferSign i * deriv (M.column k).p (bufferCut B i) -
    (if i = k then (M.column i).inwardEnergy else 0)

def InnerBufferLocalizedData.physicalFluxError (height : ℝ) (s : Fin 2 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k => height * s i * s k * M.modelFluxError i k

def innerPhysicalCutKappa (height : ℝ) (s k : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  height * s i ^ 2 * k i

theorem InnerBufferLocalizedData.energies_pos
    (hB : BufferHypotheses B) (hC : 0 < C) (i : Fin 2) :
    0 < (M.column i).inwardEnergy ∧ 0 < (M.column i).outwardEnergy :=
  ⟨(div_pos (buffer_mass_pos hB i) hC).trans_le (M.column i).inward_lower,
    (div_pos (buffer_mass_pos hB i) hC).trans_le (M.column i).outward_lower⟩

/-- The full compression energy is comparable to the positive inward
energy with a constant determined by the original R09 mass comparison. -/
theorem InnerBufferLocalizedData.energy_compare
    (hC : 0 < C) (i : Fin 2) :
    (M.column i).inwardEnergy + (M.column i).outwardEnergy ≤
      (1 + C ^ 2) * (M.column i).inwardEnergy := by
  have hm : B.mass i ≤ (M.column i).inwardEnergy * C :=
    (div_le_iff₀ hC).mp (M.column i).inward_lower
  have hm' := mul_le_mul_of_nonneg_left hm hC.le
  nlinarith only [hm', (M.column i).outward_upper]

theorem InnerBufferLocalizedData.error_entry_envelope
    (hB : BufferHypotheses B) (hC : 0 ≤ C) {massUpper t : ℝ}
    (hmass : ∀ i, B.mass i ≤ massUpper) (haction : ∀ i, t ≤ B.action i)
    (i k : Fin 2) :
    |M.modelFluxError i k /
      sqrt (((M.column i).inwardEnergy + (M.column i).outwardEnergy) *
        ((M.column k).inwardEnergy + (M.column k).outwardEnergy))| ≤
      C * B.B₀ * massUpper ^ 2 * exp (-2 * t) := by
  have hB0 : 0 < B.B₀ := hB.2.2.1
  have hupper : 0 ≤ massUpper := (buffer_mass_pos hB i).le.trans (hmass i)
  have hm : B.mass i * B.mass k ≤ massUpper ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul (hmass i) (hmass k) (buffer_mass_pos hB k).le hupper
  have he : exp (-B.action i - B.action k) ≤ exp (-2 * t) := by
    apply exp_le_exp.mpr
    linarith only [haction i, haction k]
  apply (M.flux_error i k).trans
  calc
    _ = (C * B.B₀) * (B.mass i * B.mass k) * exp (-B.action i - B.action k) := by ring
    _ ≤ (C * B.B₀) * massUpper ^ 2 * exp (-2 * t) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hm (mul_nonneg hC hB0.le)) he
        (exp_pos _).le (mul_nonneg (mul_nonneg hC hB0.le) (sq_nonneg _))

/-- The physical error is the same true conormal error, with the exact
physical kappa. Neither an entry estimate nor a matrix norm estimate is
assumed here. -/
theorem InnerBufferLocalizedData.physical_error_weighted_bound
    (hB : BufferHypotheses B) (hC : 0 < C)
    (height : ℝ) (s k W : Fin 2 → ℝ)
    (hh : 0 < height) (hs : ∀ i, 0 < s i) (hk : ∀ i, 0 < k i)
    (hW : ∀ i, 0 < W i)
    (henergy : ∀ i, (M.column i).inwardEnergy ≤ 2 * k i)
    {ratio massUpper t : ℝ} (hratio : 0 ≤ ratio)
    (hweights : ∀ i j, W i / W j ≤ ratio)
    (hmass : ∀ i, B.mass i ≤ massUpper) (haction : ∀ i, t ≤ B.action i)
    (sign : Bool) :
    ‖innerTwoCutWeightedError (innerPhysicalCutKappa height s k) W
      (M.physicalFluxError height s) sign‖ ≤
      4 * ratio * ((2 * (1 + C ^ 2)) *
        (C * B.B₀ * massUpper ^ 2 * exp (-2 * t))) := by
  let D : Fin 2 → ℝ := fun i => (M.column i).inwardEnergy + (M.column i).outwardEnergy
  let eta := C * B.B₀ * massUpper ^ 2 * exp (-2 * t)
  have hD : ∀ i, 0 < D i := fun i =>
    add_pos (M.energies_pos hB hC i).1 (M.energies_pos hB hC i).2
  have heta : 0 ≤ eta := by
    dsimp only [eta]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC.le hB.2.2.1.le) (sq_nonneg _)) (exp_pos _).le
  have hcompare (i : Fin 2) : D i ≤ (2 * (1 + C ^ 2)) * k i := by
    calc
      D i ≤ (1 + C ^ 2) * (M.column i).inwardEnergy := M.energy_compare hC i
      _ ≤ (1 + C ^ 2) * (2 * k i) :=
        mul_le_mul_of_nonneg_left (henergy i) (by positivity)
      _ = _ := by ring
  apply innerTwoCutWeightedError_norm_le
    (innerPhysicalCutKappa height s k) W (M.physicalFluxError height s)
      hW hratio (mul_nonneg (by positivity : 0 ≤ 2 * (1 + C ^ 2)) heta) hweights
  intro i j
  change |(height * s i * s j * M.modelFluxError i j) /
    sqrt ((height * s i ^ 2 * k i) * (height * s j ^ 2 * k j))| ≤ _
  rw [innerFluxHeight_normalization hh (hs i) (hs j) (hk i) (hk j)]
  exact innerCutEnergy_normalized_entry_bound (hD i) (hD j) (hk i) (hk j)
    (by positivity) heta (hcompare i) (hcompare j)
    (M.error_entry_envelope hB hC.le hmass haction i j)

end ContinuousFlexibility.Radial
