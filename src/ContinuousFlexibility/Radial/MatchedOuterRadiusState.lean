import ContinuousFlexibility.Radial.OuterFundamentalPair

/-!
# The same outer fundamental states after a radius dilation

All four actual state functions are precomposed with division by the
positive radius factor. The normalized entrance state, continuation
coefficients and determinant are retained. The physical companion uses
the actual profile and derivative laws and scales the boundary parameter
by profile height alone. No new Morse realization or deep-tail basis is
introduced.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set

private theorem matchedOuterRadius_mem_Ico {s a b x : ℝ} (hs : 0 < s)
    (hx : x ∈ Ico (s * a) (s * b)) : x / s ∈ Ico a b := by
  constructor
  · apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm a s] using hx.1
  · apply (div_lt_iff₀ hs).mpr
    simpa only [mul_comm b s] using hx.2

private theorem matchedOuterRadius_mul_div {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    s * x / s = x := by
  field_simp [hs]
  <;> ring

theorem OuterFirstOrderSystem.radius_comp
    {alpha beta u z : ℝ → ℝ} {a b s : ℝ}
    (h : OuterFirstOrderSystem alpha beta u z (Ico a b)) (hs : 0 < s) :
    OuterFirstOrderSystem (fun x => alpha (x / s) / s)
      (fun x => beta (x / s) / s)
      (fun x => u (x / s)) (fun x => z (x / s)) (Ico (s * a) (s * b)) := by
  intro x hx
  have hxs := matchedOuterRadius_mem_Ico hs hx
  have hdiv : HasDerivAt (fun y : ℝ => y / s) (1 / s) x :=
    (hasDerivAt_id x).div_const s
  constructor
  · exact (((h (x / s) hxs).1.comp x hdiv).congr_deriv (by ring))
  · exact (((h (x / s) hxs).2.comp x hdiv).congr_deriv (by ring))

variable {alpha beta P ZP Q ZQ : ℝ → ℝ} {a c b s : ℝ}

/-- The original normalized fundamental pair, in the dilated coordinate. -/
def OuterFundamentalStatePair.radiusScale
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) :
    OuterFundamentalStatePair (fun x => alpha (x / s) / s)
      (fun x => beta (x / s) / s)
      (fun x => P (x / s)) (fun x => ZP (x / s))
      (fun x => Q (x / s)) (fun x => ZQ (x / s))
      (s * a) (s * c) (s * b) where
  U := fun x => H.U (x / s)
  ZU := fun x => H.ZU (x / s)
  V := fun x => H.V (x / s)
  ZV := fun x => H.ZV (x / s)
  entrance := H.entrance
  scale := H.scale
  tailA := H.tailA
  tailB := H.tailB
  unit := H.unit
  scale_pos := H.scale_pos
  U_initial := by
    change (H.U (s * a / s), H.ZU (s * a / s)) = outerStatePerp H.entrance
    rw [matchedOuterRadius_mul_div hs.ne']
    exact H.U_initial
  V_initial := by
    change (H.V (s * a / s), H.ZV (s * a / s)) = H.entrance
    rw [matchedOuterRadius_mul_div hs.ne']
    exact H.V_initial
  U_system := H.U_system.radius_comp hs
  V_system := H.V_system.radius_comp hs
  U_tail := fun x hx => H.U_tail (x / s) (matchedOuterRadius_mem_Ico hs hx)
  ZU_tail := fun x hx => H.ZU_tail (x / s) (matchedOuterRadius_mem_Ico hs hx)
  V_tail := fun x hx => H.V_tail (x / s) (matchedOuterRadius_mem_Ico hs hx)
  ZV_tail := fun x hx => H.ZV_tail (x / s) (matchedOuterRadius_mem_Ico hs hx)
  determinant := fun x hx => H.determinant (x / s) (matchedOuterRadius_mem_Ico hs hx)

@[simp] theorem OuterFundamentalStatePair.radiusScale_U
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) (x : ℝ) :
    (H.radiusScale hs).U x = H.U (x / s) := rfl

@[simp] theorem OuterFundamentalStatePair.radiusScale_ZU
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) (x : ℝ) :
    (H.radiusScale hs).ZU x = H.ZU (x / s) := rfl

@[simp] theorem OuterFundamentalStatePair.radiusScale_V
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) (x : ℝ) :
    (H.radiusScale hs).V x = H.V (x / s) := rfl

@[simp] theorem OuterFundamentalStatePair.radiusScale_ZV
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) (x : ℝ) :
    (H.radiusScale hs).ZV x = H.ZV (x / s) := rfl

@[simp] theorem OuterFundamentalStatePair.radiusScale_entrance
    (H : OuterFundamentalStatePair alpha beta P ZP Q ZQ a c b) (hs : 0 < s) :
    (H.radiusScale hs).entrance = H.entrance := rfl

/-- The two actual physical coefficients have exactly the required radius
factor. The profile height cancels with the boundary-scale height. -/
theorem matchedOuterRadius_physical_coefficients
    {w W : ℝ → ℝ} {s height lam J x : ℝ}
    (hs : s ≠ 0) (hh : height ≠ 0) (hlam : lam ≠ 0)
    (hx : x ≠ 0) (hw : w (x / s) ≠ 0)
    (hprofile : W x = (height * s) * w (x / s))
    (hderiv : deriv W x = height * deriv w (x / s)) :
    (height * lam) / W x = (lam / w (x / s)) / s ∧
      J * deriv W x / ((height * lam) * x) =
        (J * deriv w (x / s) / (lam * (x / s))) / s := by
  constructor
  · rw [hprofile]
    field_simp [hs, hh, hw]
    <;> ring
  · rw [hderiv]
    field_simp [hs, hh, hlam, hx]
    <;> ring

/-- The same pair as an actual physical fundamental pair for the new
profile. The hypotheses are only the local profile identities on the
whole closed-at-entry tail; they do not assert an operator or norm bound. -/
def OuterFundamentalStatePair.radiusScale_of_profile
    {w W : ℝ → ℝ} {height lam J : ℝ}
    (H : OuterFundamentalStatePair (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) P ZP Q ZQ a c b)
    (hs : 0 < s) (hh : height ≠ 0) (hlam : lam ≠ 0)
    (hprofile : ∀ x ∈ Ico (s * a) (s * b), W x = (height * s) * w (x / s))
    (hderiv : ∀ x ∈ Ico (s * a) (s * b), deriv W x = height * deriv w (x / s))
    (hx : ∀ x ∈ Ico (s * a) (s * b), x ≠ 0)
    (hw : ∀ x ∈ Ico (s * a) (s * b), w (x / s) ≠ 0) :
    OuterFundamentalStatePair (fun x => (height * lam) / W x)
      (fun x => J * deriv W x / ((height * lam) * x))
      (fun x => P (x / s)) (fun x => ZP (x / s))
      (fun x => Q (x / s)) (fun x => ZQ (x / s))
      (s * a) (s * c) (s * b) := by
  let R := H.radiusScale hs
  have hc (x : ℝ) (hmem : x ∈ Ico (s * a) (s * b)) :=
    matchedOuterRadius_physical_coefficients hs.ne' hh hlam (hx x hmem) (hw x hmem)
      (hprofile x hmem) (hderiv x hmem)
  refine {
    U := R.U, ZU := R.ZU, V := R.V, ZV := R.ZV
    entrance := R.entrance, scale := R.scale, tailA := R.tailA, tailB := R.tailB
    unit := R.unit, scale_pos := R.scale_pos
    U_initial := R.U_initial, V_initial := R.V_initial
    U_system := ?_, V_system := ?_
    U_tail := R.U_tail, ZU_tail := R.ZU_tail, V_tail := R.V_tail, ZV_tail := R.ZV_tail
    determinant := R.determinant }
  · intro x hmem
    simpa only [(hc x hmem).1, (hc x hmem).2] using R.U_system x hmem
  · intro x hmem
    simpa only [(hc x hmem).1, (hc x hmem).2] using R.V_system x hmem

theorem OuterFundamentalStatePair.radiusScale_of_profile_fields
    {w W : ℝ → ℝ} {height lam J : ℝ}
    (H : OuterFundamentalStatePair (fun x => lam / w x)
      (fun x => J * deriv w x / (lam * x)) P ZP Q ZQ a c b)
    (hs : 0 < s) (hh : height ≠ 0) (hlam : lam ≠ 0)
    (hprofile : ∀ x ∈ Ico (s * a) (s * b), W x = (height * s) * w (x / s))
    (hderiv : ∀ x ∈ Ico (s * a) (s * b), deriv W x = height * deriv w (x / s))
    (hx : ∀ x ∈ Ico (s * a) (s * b), x ≠ 0)
    (hw : ∀ x ∈ Ico (s * a) (s * b), w (x / s) ≠ 0) :
    let R := H.radiusScale_of_profile hs hh hlam hprofile hderiv hx hw
    R.U = (fun x => H.U (x / s)) ∧ R.ZU = (fun x => H.ZU (x / s)) ∧
      R.V = (fun x => H.V (x / s)) ∧ R.ZV = (fun x => H.ZV (x / s)) ∧
      R.entrance = H.entrance := ⟨rfl, rfl, rfl, rfl, rfl⟩

end ContinuousFlexibility.Radial
