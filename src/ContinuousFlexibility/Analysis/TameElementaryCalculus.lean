import ContinuousFlexibility.Statements.Analysis
import ContinuousFlexibility.Analysis.ProjectiveJets

/-!
# Elementary smooth tame calculus

The derivative towers are genuine projective directional derivatives. This
module proves the linear, additive and bilinear parts of `TameCalculusTarget`.
The numerical estimates retain one high-order factor and fixed losses.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology BigOperators
open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

section Estimates

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The standard one-high-factor expression for a derivative of order `k`. -/
def tameJetSize (p : ℕ → Seminorm ℝ E) (k s loss base : ℕ)
    (x : E) (v : Fin k → E) : ℝ :=
  (1 + p (s + loss) x) * ∏ i, p base (v i) +
    ∑ i : Fin k, p (s + loss) (v i) *
      ∏ j ∈ Finset.univ.erase i, p base (v j)

theorem tameJetSize_nonneg (p : ℕ → Seminorm ℝ E) (k s loss base : ℕ)
    (x : E) (v : Fin k → E) : 0 ≤ tameJetSize p k s loss base x v := by
  unfold tameJetSize
  positivity

/-- Increasing the loss and the low order only increases the tame expression. -/
theorem tameJetSize_mono {p : ℕ → Seminorm ℝ E} (hp : Monotone p)
    {loss loss' base base' : ℕ} (hl : loss ≤ loss') (hb : base ≤ base')
    (k s : ℕ) (x : E) (v : Fin k → E) :
    tameJetSize p k s loss base x v ≤ tameJetSize p k s loss' base' x v := by
  unfold tameJetSize
  apply add_le_add
  · apply mul_le_mul
    · exact add_le_add (le_refl 1) (hp (Nat.add_le_add_left hl s) x)
    · exact Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
        (fun i _ => hp hb (v i))
    · positivity
    · positivity
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul
    · exact hp (Nat.add_le_add_left hl s) (v i)
    · exact Finset.prod_le_prod₀ (fun _ _ => apply_nonneg _ _)
        (fun j _ => hp hb (v j))
    · positivity
    · exact apply_nonneg _ _

theorem tameJetSize_zero (p : ℕ → Seminorm ℝ E) (s loss base : ℕ)
    (x : E) (v : Fin 0 → E) :
    tameJetSize p 0 s loss base x v = 1 + p (s + loss) x := by
  simp [tameJetSize]

theorem tameJetSize_one (p : ℕ → Seminorm ℝ E) (s loss base : ℕ)
    (x : E) (v : Fin 1 → E) :
    tameJetSize p 1 s loss base x v =
      (1 + p (s + loss) x) * p base (v 0) + p (s + loss) (v 0) := by
  simp [tameJetSize]

end Estimates

section Towers

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- The existing jet verification supplies precisely a `SmoothDirections` tower. -/
def smoothDirectionsOfJets {U : Set E} {f : E → F}
    (hU : IsOpen U) (J : ProjectiveJetFamily E F) (hJ : HasProjectiveJetsOn f J U) :
    SmoothDirections U f where
  open_domain := hU
  D := J
  zero := hJ.1
  continuous := hJ.2.1
  derivative := fun n x hx v w => hJ.2.2 n x hx w v

/-- The actual all-order tower of a continuous linear map. -/
def smoothDirectionsLinear (L : E →L[ℝ] F) : SmoothDirections univ L :=
  smoothDirectionsOfJets isOpen_univ (continuousLinearJets L)
    (hasProjectiveJetsOn_continuousLinear L univ)

/-- A fixed-loss continuous linear map is smooth tame. -/
theorem smoothTameOn_continuousLinear {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} (L : E →L[ℝ] F) {loss base : ℕ}
    (hL : IsTameLinear p q L.toLinearMap loss base) :
    SmoothTameOn p q univ L := by
  refine ⟨smoothDirectionsLinear L, ?_⟩
  intro k x0 _
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC⟩ := hL s hs
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro x _ _ v
  change q s (continuousLinearJets L k x v) ≤ C * tameJetSize p k s loss base x v
  cases k with
  | zero =>
      rw [tameJetSize_zero]
      change q s (L x) ≤ _
      exact (hC x).trans (mul_le_mul_of_nonneg_left (by linarith) C.coe_nonneg)
  | succ k =>
      cases k with
      | zero =>
          rw [tameJetSize_one]
          change q s (L (v 0)) ≤ _
          apply (hC (v 0)).trans
          apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
          have hpos : 0 ≤ (1 + p (s + loss) x) * p base (v 0) := by positivity
          linarith
      | succ k =>
          change q s 0 ≤ C * tameJetSize p (k + 2) s loss base x v
          rw [map_zero]
          exact mul_nonneg C.coe_nonneg (tameJetSize_nonneg _ _ _ _ _ _ _)

variable [IsTopologicalAddGroup F]

/-- Addition of genuine smooth directional towers. -/
def smoothDirectionsAdd {U : Set E} {f g : E → F}
    (J : SmoothDirections U f) (K : SmoothDirections U g) :
    SmoothDirections U (fun x => f x + g x) where
  open_domain := J.open_domain
  D := fun n x => J.D n x + K.D n x
  zero := fun x hx => by
    rw [add_apply, J.zero x hx, K.zero x hx]
  continuous := fun n => (J.continuous n).add (K.continuous n)
  derivative := fun n x hx v w => (J.derivative n x hx v w).add (K.derivative n x hx v w)

/-- Addition preserves smooth tame bounds on the original domain. -/
theorem smoothTameOn_add {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) {U : Set E} {f g : E → F}
    (hf : SmoothTameOn p q U f) (hg : SmoothTameOn p q U g) :
    SmoothTameOn p q U (fun x => f x + g x) := by
  obtain ⟨J, hJ⟩ := hf
  obtain ⟨K, hK⟩ := hg
  refine ⟨smoothDirectionsAdd J K, ?_⟩
  intro k x0 hx0
  obtain ⟨l1, b1, ε1, hε1, h1⟩ := hJ k x0 hx0
  obtain ⟨l2, b2, ε2, hε2, h2⟩ := hK k x0 hx0
  refine ⟨max l1 l2, max b1 b2, min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intro s hs
  obtain ⟨C1, hC1, h1'⟩ := h1 s ((le_max_left _ _).trans hs)
  obtain ⟨C2, hC2, h2'⟩ := h2 s ((le_max_right _ _).trans hs)
  refine ⟨C1 + C2, add_nonneg hC1 hC2, ?_⟩
  intro x hx hnear v
  have hn1 : p b1 (x - x0) < ε1 :=
    (hp (le_max_left _ _) _).trans_lt (hnear.trans_le (min_le_left _ _))
  have hn2 : p b2 (x - x0) < ε2 :=
    (hp (le_max_right _ _) _).trans_lt (hnear.trans_le (min_le_right _ _))
  have hb1 := (h1' x hx hn1 v).trans (mul_le_mul_of_nonneg_left
    (tameJetSize_mono hp (le_max_left l1 l2) (le_max_left b1 b2) k s x v) hC1)
  have hb2 := (h2' x hx hn2 v).trans (mul_le_mul_of_nonneg_left
    (tameJetSize_mono hp (le_max_right l1 l2) (le_max_right b1 b2) k s x v) hC2)
  change q s (J.D k x v + K.D k x v) ≤
    (C1 + C2) * tameJetSize p k s (max l1 l2) (max b1 b2) x v
  calc
    _ ≤ q s (J.D k x v) + q s (K.D k x v) := map_add_le_add _ _ _
    _ ≤ C1 * tameJetSize p k s (max l1 l2) (max b1 b2) x v +
        C2 * tameJetSize p k s (max l1 l2) (max b1 b2) x v := add_le_add hb1 hb2
    _ = _ := by ring

end Towers

section Quadratic

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

private theorem tameJetSize_two (p : ℕ → Seminorm ℝ E) (s loss base : ℕ)
    (x : E) (v : Fin 2 → E) :
    tameJetSize p 2 s loss base x v =
      (1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) +
        (p (s + loss) (v 0) * p base (v 1) + p (s + loss) (v 1) * p base (v 0)) := by
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simp only [tameJetSize, Fin.prod_univ_two, Fin.sum_univ_two, h0, h1,
    Finset.prod_singleton]

/-- A bilinear diagonal with the two-factor tame estimate is smooth tame.
Its third and all later derivatives are zero; no formal differentiation is assumed. -/
theorem smoothTameOn_quadratic {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (B : E [×2]→L[ℝ] F) {loss base : ℕ}
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      q s (bilinearJetValue B x y) ≤
        C * (p (s + loss) x * p base y + p base x * p (s + loss) y)) :
    SmoothTameOn p q univ (quadraticJetValue B) := by
  refine ⟨smoothDirectionsOfJets isOpen_univ (quadraticJets B)
    (hasProjectiveJetsOn_quadratic B univ), ?_⟩
  intro k x0 _
  refine ⟨loss, base, 1, zero_lt_one, ?_⟩
  intro s hs
  obtain ⟨C, hC, hbound⟩ := hB s hs
  let M : ℝ := 1 + p base x0
  have hM : 1 ≤ M := le_add_of_nonneg_right (apply_nonneg _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  refine ⟨2 * C * M, by positivity, ?_⟩
  intro x _ hnear v
  have hx : p base x ≤ M := by
    calc
      p base x = p base ((x - x0) + x0) := by rw [sub_add_cancel]
      _ ≤ p base (x - x0) + p base x0 := map_add_le_add _ _ _
      _ ≤ 1 + p base x0 := add_le_add hnear.le (le_refl (p base x0))
      _ = M := rfl
  have ha : 0 ≤ p (s + loss) x := apply_nonneg _ _
  change q s (quadraticJets B k x v) ≤ 2 * C * M * tameJetSize p k s loss base x v
  cases k with
  | zero =>
      rw [tameJetSize_zero]
      change q s (bilinearJetValue B x x) ≤ _
      calc
        _ ≤ C * (p (s + loss) x * p base x + p base x * p (s + loss) x) := hbound x x
        _ ≤ C * (p (s + loss) x * M + M * p (s + loss) x) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hx ha)
              (mul_le_mul_of_nonneg_right hx ha)) hC
        _ = (2 * C * M) * p (s + loss) x := by ring
        _ ≤ (2 * C * M) * (1 + p (s + loss) x) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  | succ k =>
      cases k with
      | zero =>
          rw [tameJetSize_one]
          change q s (quadraticJetFirst B x (v 0)) ≤ _
          rw [quadraticJetFirst_apply]
          have hv0 : 0 ≤ p (s + loss) (v 0) := apply_nonneg _ _
          have hvl : 0 ≤ p base (v 0) := apply_nonneg _ _
          have hax : p (s + loss) x ≤ M * (1 + p (s + loss) x) := by
            have ht := mul_le_mul_of_nonneg_right hM ha
            nlinarith
          calc
            _ ≤ q s (bilinearJetValue B (v 0) x) +
                q s (bilinearJetValue B x (v 0)) := map_add_le_add _ _ _
            _ ≤ C * (p (s + loss) (v 0) * p base x + p base (v 0) * p (s + loss) x) +
                C * (p (s + loss) x * p base (v 0) + p base x * p (s + loss) (v 0)) :=
              add_le_add (hbound (v 0) x) (hbound x (v 0))
            _ = 2 * C * (p (s + loss) (v 0) * p base x +
                p (s + loss) x * p base (v 0)) := by ring
            _ ≤ 2 * C * (p (s + loss) (v 0) * M +
                (M * (1 + p (s + loss) x)) * p base (v 0)) :=
              mul_le_mul_of_nonneg_left
                (add_le_add (mul_le_mul_of_nonneg_left hx hv0)
                  (mul_le_mul_of_nonneg_right hax hvl)) (by positivity)
            _ = _ := by ring
      | succ k =>
          cases k with
          | zero =>
              rw [tameJetSize_two]
              change q s (quadraticJetSecond B v) ≤ _
              rw [quadraticJetSecond_apply]
              let A : ℝ := p (s + loss) (v 0) * p base (v 1) +
                p (s + loss) (v 1) * p base (v 0)
              have hA : 0 ≤ A := by dsimp [A]; positivity
              have hrest : 0 ≤ (1 + p (s + loss) x) *
                  (p base (v 0) * p base (v 1)) := by positivity
              calc
                _ ≤ q s (bilinearJetValue B (v 0) (v 1)) +
                    q s (bilinearJetValue B (v 1) (v 0)) := map_add_le_add _ _ _
                _ ≤ C * (p (s + loss) (v 0) * p base (v 1) +
                    p base (v 0) * p (s + loss) (v 1)) +
                    C * (p (s + loss) (v 1) * p base (v 0) +
                    p base (v 1) * p (s + loss) (v 0)) :=
                  add_le_add (hbound (v 0) (v 1)) (hbound (v 1) (v 0))
                _ = 2 * C * A := by dsimp [A]; ring
                _ ≤ 2 * C * (M * A) :=
                  mul_le_mul_of_nonneg_left
                    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hM hA)
                    (by positivity)
                _ ≤ 2 * C * M *
                    ((1 + p (s + loss) x) * (p base (v 0) * p base (v 1)) + A) := by
                  rw [← mul_assoc]
                  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hrest) (by positivity)
          | succ k =>
              change q s 0 ≤ 2 * C * M * tameJetSize p (k + 3) s loss base x v
              rw [map_zero]
              exact mul_nonneg (by positivity) (tameJetSize_nonneg _ _ _ _ _ _ _)

end Quadratic

section BilinearContinuity

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] [IsTopologicalAddGroup E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℝ G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G]

/-- A bilinear tame estimate proves joint continuity in seminorm topologies.
This does not rely on an operator-space topology for the curried map. -/
theorem continuous_bilinear_of_tame {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    (hp : WithSeminorms p) (hq : WithSeminorms q) (hr : WithSeminorms r)
    (hrmono : Monotone r) (B : E →L[ℝ] F →L[ℝ] G) {loss base : ℕ}
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      r s (B x y) ≤ C * (p (s + loss) x * q base y + p base x * q (s + loss) y)) :
    Continuous (fun z : E × F => B z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z0
  apply (hr.tendsto_nhds _ _).mpr
  intro s ε hε
  let t : ℕ := max s base
  obtain ⟨C, hC, hbound⟩ := hB t (le_max_right _ _)
  let A : E × F → ℝ := fun z =>
    C * (p (t + loss) (z.1 - z0.1) * q base z.2 +
      p base (z.1 - z0.1) * q (t + loss) z.2) +
    C * (p (t + loss) z0.1 * q base (z.2 - z0.2) +
      p base z0.1 * q (t + loss) (z.2 - z0.2))
  have hpd (n : ℕ) : Continuous (fun z : E × F => p n (z.1 - z0.1)) :=
    (hp.continuous_seminorm n).comp (continuous_fst.sub continuous_const)
  have hqd (n : ℕ) : Continuous (fun z : E × F => q n (z.2 - z0.2)) :=
    (hq.continuous_seminorm n).comp (continuous_snd.sub continuous_const)
  have hqv (n : ℕ) : Continuous (fun z : E × F => q n z.2) :=
    (hq.continuous_seminorm n).comp continuous_snd
  have hA : Continuous A :=
    ((((hpd _).mul (hqv _)).add ((hpd _).mul (hqv _))).const_mul C).add
      ((((hqd _).const_mul _).add ((hqd _).const_mul _)).const_mul C)
  have hz : A z0 = 0 := by simp [A]
  have ht := hA.tendsto z0
  rw [hz] at ht
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with z hsmall
  have hid : B z.1 z.2 - B z0.1 z0.2 =
      B (z.1 - z0.1) z.2 + B z0.1 (z.2 - z0.2) := by
    simp only [map_sub, sub_apply]
    abel
  have hb : r s (B z.1 z.2 - B z0.1 z0.2) ≤ A z := by
    calc
      _ ≤ r t (B z.1 z.2 - B z0.1 z0.2) := hrmono (le_max_left _ _) _
      _ = r t (B (z.1 - z0.1) z.2 + B z0.1 (z.2 - z0.2)) := by rw [hid]
      _ ≤ r t (B (z.1 - z0.1) z.2) + r t (B z0.1 (z.2 - z0.2)) := map_add_le_add _ _ _
      _ ≤ A z := add_le_add (hbound (z.1 - z0.1) z.2) (hbound z0.1 (z.2 - z0.2))
  exact hb.trans_lt hsmall

/-- Encode an evaluation `B x y` as the diagonal of one genuine continuous bilinear map
on `E × F`. -/
def bilinearPairMultilinear (B : E →L[ℝ] F →L[ℝ] G)
    (hB : Continuous (fun z : E × F => B z.1 z.2)) :
    (E × F) [×2]→L[ℝ] G where
  toFun := fun v => B (v 0).1 (v 1).2
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [map_add, add_apply]
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [map_smul, smul_apply]
  cont := hB.comp (((continuous_apply 0).fst).prodMk ((continuous_apply 1).snd))

theorem bilinearPairMultilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (hB : Continuous (fun z : E × F => B z.1 z.2)) (v : Fin 2 → E × F) :
    bilinearPairMultilinear B hB v = B (v 0).1 (v 1).2 := rfl

theorem tamePairGrading_apply (p : ℕ → Seminorm ℝ E) (q : ℕ → Seminorm ℝ F)
    (s : ℕ) (z : E × F) : pairGrading p q s z = p s z.1 + q s z.2 := by
  simp only [pairGrading, add_apply, Seminorm.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]

/-- The bilinear clause of tame calculus, with its exact fixed-loss hypothesis. -/
theorem smoothTameOn_bilinear {p : ℕ → Seminorm ℝ E}
    {q : ℕ → Seminorm ℝ F} {r : ℕ → Seminorm ℝ G}
    (hp : WithSeminorms p) (hq : WithSeminorms q) (hr : WithSeminorms r)
    (hrmono : Monotone r) (B : E →L[ℝ] F →L[ℝ] G) {loss base : ℕ}
    (hB : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      r s (B x y) ≤ C * (p (s + loss) x * q base y + p base x * q (s + loss) y)) :
    SmoothTameOn (pairGrading p q) r univ (fun z : E × F => B z.1 z.2) := by
  have hcont := continuous_bilinear_of_tame hp hq hr hrmono B hB
  let A := bilinearPairMultilinear B hcont
  have hA : ∀ s, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : E × F,
      r s (bilinearJetValue A x y) ≤
        C * (pairGrading p q (s + loss) x * pairGrading p q base y +
          pairGrading p q base x * pairGrading p q (s + loss) y) := by
    intro s hs
    obtain ⟨C, hC, hbound⟩ := hB s hs
    refine ⟨C, hC, ?_⟩
    intro x y
    have hxy := hbound x.1 y.2
    change r s (B x.1 y.2) ≤ _
    apply hxy.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simp only [tamePairGrading_apply]
    apply add_le_add
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
    · exact mul_le_mul (le_add_of_nonneg_right (apply_nonneg _ _))
        (le_add_of_nonneg_left (apply_nonneg _ _)) (apply_nonneg _ _)
        (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  exact smoothTameOn_quadratic A hA

end BilinearContinuity

section TowerAdapters

variable {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]

/-- A smooth directional tower is an already verified projective jet family. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.hasProjectiveJetsOn
    {U : Set E} {f : E → F} (J : SmoothDirections U f) :
    HasProjectiveJetsOn f J.D U :=
  ⟨J.zero, J.continuous, fun n x hx w v => J.derivative n x hx v w⟩

/-- Order zero of the jointly continuous tower is continuity of the map itself. -/
theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.continuousOn
    {U : Set E} {f : E → F} (J : SmoothDirections U f) : ContinuousOn f U := by
  have hpair : Continuous (fun x : E => (x, (Fin.elim0 : Fin 0 → E))) :=
    continuous_id.prodMk continuous_const
  exact ((J.continuous 0).comp' hpair.continuousOn (fun x hx => ⟨hx, mem_univ _⟩)).congr
    (fun x hx => (J.zero x hx).symm)

/-- Pointwise agreement on the domain preserves the same derivative tower. -/
def _root_.ContinuousFlexibility.Statements.SmoothDirections.congr
    {U : Set E} {f g : E → F} (J : SmoothDirections U f)
    (hfg : ∀ x ∈ U, f x = g x) : SmoothDirections U g where
  open_domain := J.open_domain
  D := J.D
  zero := fun x hx => (J.zero x hx).trans (hfg x hx)
  continuous := J.continuous
  derivative := J.derivative

/-- Smooth tame estimates depend only on the map on its open domain. -/
theorem smoothTameOn_congr {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    {U : Set E} {f g : E → F} (hf : SmoothTameOn p q U f)
    (hfg : ∀ x ∈ U, f x = g x) : SmoothTameOn p q U g := by
  obtain ⟨J, hJ⟩ := hf
  exact ⟨J.congr hfg, hJ⟩

end TowerAdapters

section FixedOrderBounds

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- When the high and low orders coincide, every increment term is the same product. -/
theorem tameJetSize_sameOrder (p : ℕ → Seminorm ℝ E) (k s loss : ℕ)
    (x : E) (v : Fin k → E) :
    tameJetSize p k s loss (s + loss) x v =
      (1 + p (s + loss) x + k) * ∏ i, p (s + loss) (v i) := by
  have hterm (i : Fin k) : p (s + loss) (v i) *
      (∏ j ∈ Finset.univ.erase i, p (s + loss) (v j)) =
      ∏ j, p (s + loss) (v j) :=
    Finset.mul_prod_erase Finset.univ (fun j : Fin k => p (s + loss) (v j))
      (Finset.mem_univ i)
  unfold tameJetSize
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- A fixed output order of a tame jet is uniformly bounded by one low seminorm
in every increment, on one fixed low-seminorm neighborhood. -/
theorem tameJet_bound_fixedOrder {p : ℕ → Seminorm ℝ E} {q : ℕ → Seminorm ℝ F}
    (hp : Monotone p) (hq : Monotone q) {U : Set E} {k : ℕ}
    (A : E → (Fin k → E) → F) (x0 : E)
    (hA : ∃ loss base : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ℕ, base ≤ s → ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ U,
        p base (x - x0) < ε → ∀ v : Fin k → E,
        q s (A x v) ≤ C * tameJetSize p k s loss base x v)
    (m : ℕ) :
    ∃ base : ℕ, m ≤ base ∧ ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ x ∈ U, p base (x - x0) < ε → ∀ v : Fin k → E,
        q m (A x v) ≤ C * ∏ i, p base (v i) := by
  obtain ⟨loss, base, ε, hε, hbound⟩ := hA
  let s : ℕ := max m base
  let b : ℕ := s + loss
  have hbs : base ≤ s := le_max_right _ _
  have hsb : s ≤ b := Nat.le_add_right _ _
  obtain ⟨C, hC, hCbound⟩ := hbound s hbs
  let K : ℝ := 2 + p b x0 + k
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨b, (le_max_left _ _).trans hsb, min ε 1,
    C * K + 1, lt_min hε zero_lt_one, by positivity, ?_⟩
  intro x hx hnear v
  have hnear0 : p base (x - x0) < ε :=
    (hp (hbs.trans hsb) _).trans_lt (hnear.trans_le (min_le_left _ _))
  have hnear1 : p b (x - x0) < 1 := hnear.trans_le (min_le_right _ _)
  have hxsize : p b x ≤ 1 + p b x0 := by
    calc
      p b x = p b ((x - x0) + x0) := by rw [sub_add_cancel]
      _ ≤ p b (x - x0) + p b x0 := map_add_le_add _ _ _
      _ ≤ 1 + p b x0 := add_le_add hnear1.le (le_refl (p b x0))
  have hprod : 0 ≤ ∏ i, p b (v i) := Finset.prod_nonneg (fun i _ => apply_nonneg _ _)
  have hsize : tameJetSize p k s loss base x v ≤ K * ∏ i, p b (v i) := by
    calc
      _ ≤ tameJetSize p k s loss b x v :=
        tameJetSize_mono hp le_rfl (hbs.trans hsb) k s x v
      _ = (1 + p b x + k) * ∏ i, p b (v i) := tameJetSize_sameOrder p k s loss x v
      _ ≤ K * ∏ i, p b (v i) :=
        mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hprod
  calc
    q m (A x v) ≤ q s (A x v) := hq (le_max_left _ _) _
    _ ≤ C * tameJetSize p k s loss base x v := hCbound x hx hnear0 v
    _ ≤ C * (K * ∏ i, p b (v i)) := mul_le_mul_of_nonneg_left hsize hC
    _ = (C * K) * ∏ i, p b (v i) := by ring
    _ ≤ (C * K + 1) * ∏ i, p b (v i) :=
      mul_le_mul_of_nonneg_right (by linarith) hprod

end FixedOrderBounds

end ContinuousFlexibility.Analysis
