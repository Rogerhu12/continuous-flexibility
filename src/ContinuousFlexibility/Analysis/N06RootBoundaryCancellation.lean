import ContinuousFlexibility.Analysis.N06RootGreenDensity
import ContinuousFlexibility.Analysis.N06N05CurrentRootTransmission

/-!
# Signed root density and actual finite-mode cancellation

The angular change of variable contributes its absolute derivative, while
the radial chart contributes its actual sign. The original N05 graph gives
the physical value and conormal matching of every common finite angular
reconstruction. Those true identities cancel the oriented boundary density
computed from the existing coordinate principal coefficients.

The result concerns the actual transported density. Identifying it with a
particular closed endpoint value of the recorded canonical coefficient row
is a separate geometric statement, not an assumption hidden here.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- The existing transported principal row, paired with the actual test
traces and first derivatives of a canonical field. The physical point and
its canonical boundary point remain explicit. -/
def n06RootBoundaryDensity (A : SymmetricCoefficients)
    (F : PolarPoint → PolarPoint) (h Q Qr Qt W : PolarPoint → ℝ)
    (x p : PolarPoint) : ℝ :=
  (coordinatePrincipalDensity A F h).a x *
    (Q p * radialPartial W p - W p * Qr p) +
  (coordinatePrincipalDensity A F h).b x *
    (Q p * angularPartial W p - W p * Qt p)

private theorem mul_div_abs_self {a : ℝ} (ha : a ≠ 0) : a * (a / |a|) = |a| := by
  calc
    a * (a / |a|) = a * a / |a| := by ring
    _ = |a| * |a| / |a| := by rw [abs_mul_abs_self]
    _ = |a| := mul_div_cancel_right₀ _ (abs_ne_zero.mpr ha)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

/-- The exact signed angular Jacobian in the physical Green density.
The formula allows either radial orientation and either sign of the
angular derivative; nonvanishing follows from the true forward Jacobian. -/
theorem n06_current_root_green_signedDensity
    {m : ℕ} {r y σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (J : N06RootFirstJets (K.chart z m) (K.height z m) r y σ β H ρ κ Hr)
    (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ) (hr : r ∈ Icc (K.physicalLeft m) (K.physicalRight m))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (A : SymmetricCoefficients) {W : PolarPoint → ℝ}
    (hW : DifferentiableAt ℝ W (y, β θ)) :
    greenNormalFlux A.a A.b φ (fun p => K.height z m p * W (K.chart z m p)) (r, θ) =
      ((σ * ρ θ) / |σ * ρ θ|) * |deriv β θ| *
        n06RootBoundaryDensity A (K.chart z m) (K.height z m)
          Q.value Q.radial Q.angular W (r, θ) (y, β θ) := by
  have hJ := (h04.2.2.2.2.2.2.2.2.1 z hz hs m (r, θ) hr).2.2.1
  have hprod : (σ * ρ θ) * deriv β θ ≠ 0 := by
    simpa only [J.jacobian θ] using hJ
  have ha : σ * ρ θ ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have he := n06_current_root_green_density J Q h04 hz hs hφ hr hθ A hW
  change (σ * ρ θ) *
    greenNormalFlux A.a A.b φ (fun p => K.height z m p * W (K.chart z m p)) (r, θ) =
    |planeJacobian (K.chart z m) (r, θ)| *
      n06RootBoundaryDensity A (K.chart z m) (K.height z m)
        Q.value Q.radial Q.angular W (r, θ) (y, β θ) at he
  apply mul_left_cancel₀ ha
  rw [he, J.jacobian θ, abs_mul]
  calc
    _ = |σ * ρ θ| * (|deriv β θ| *
        n06RootBoundaryDensity A (K.chart z m) (K.height z m)
          Q.value Q.radial Q.angular W (r, θ) (y, β θ)) := by ring
    _ = ((σ * ρ θ) * ((σ * ρ θ) / |σ * ρ θ|)) * (|deriv β θ| *
        n06RootBoundaryDensity A (K.chart z m) (K.height z m)
          Q.value Q.radial Q.angular W (r, θ) (y, β θ)) := by
      rw [mul_div_abs_self ha]
    _ = _ := by ring

/-- Matching actual physical value and conormal cancels the oriented
transported boundary rows. The common angular derivative cancels by the
actual nonzero chart Jacobian, without an extra orientation hypothesis. -/
theorem n06_current_root_boundaryDensity_eq_of_value_conormal
    {ml mr : ℕ} {r yl yr σl σr : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml) r yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr) r yr σr β H ρ κ Hr)
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hφ : ContDiff ℝ ∞ φ)
    (hrl : r ∈ Icc (K.physicalLeft ml) (K.physicalRight ml))
    (hrr : r ∈ Icc (K.physicalLeft mr) (K.physicalRight mr))
    {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi)
    (A : SymmetricCoefficients) {Wl Wr : PolarPoint → ℝ}
    (hWl : DifferentiableAt ℝ Wl (yl, β θ))
    (hWr : DifferentiableAt ℝ Wr (yr, β θ))
    (hvalue : K.height z ml (r, θ) * Wl (K.chart z ml (r, θ)) =
      K.height z mr (r, θ) * Wr (K.chart z mr (r, θ)))
    (hflux : symmetricNormalFlux A.a A.b
        (fun p => K.height z ml p * Wl (K.chart z ml p)) (r, θ) =
      symmetricNormalFlux A.a A.b
        (fun p => K.height z mr p * Wr (K.chart z mr p)) (r, θ)) :
    ((σl * ρ θ) / |σl * ρ θ|) *
      n06RootBoundaryDensity A (K.chart z ml) (K.height z ml)
        Ql.value Ql.radial Ql.angular Wl (r, θ) (yl, β θ) =
    ((σr * ρ θ) / |σr * ρ θ|) *
      n06RootBoundaryDensity A (K.chart z mr) (K.height z mr)
        Qr.value Qr.radial Qr.angular Wr (r, θ) (yr, β θ) := by
  have hJ := (h04.2.2.2.2.2.2.2.2.1 z hz hs ml (r, θ) hrl).2.2.1
  have hβ : deriv β θ ≠ 0 := (mul_ne_zero_iff.mp
    (show (σl * ρ θ) * deriv β θ ≠ 0 by simpa only [Jl.jacobian θ] using hJ)).2
  have hg := n06_greenNormalFlux_eq_of_value_conormal hvalue hflux φ
  rw [n06_current_root_green_signedDensity Jl Ql h04 hz hs hφ hrl hθ A hWl,
    n06_current_root_green_signedDensity Jr Qr h04 hz hs hφ hrr hθ A hWr] at hg
  apply mul_left_cancel₀ (abs_ne_zero.mpr hβ)
  linear_combination hg

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

/-- Actual finite modes from one original graph element cancel the
oriented transported boundary densities. Matching is derived from the
original physical reference graph, rather than assumed of the modes. -/
theorem n06N05_finite_current_root_boundaryDensity
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {K : CanonicalData S} {V : VolumeModelData S K}
    {base loss b : ℕ} {ε : ℝ} {B : CanonicalDomainData S K V b}
    {z : AnnularState S × ℝ} {φ : PolarPoint → ℝ}
    (hS : IsPhysicalSpaces D T S)
    (h : NonlinearPropertiesThrough05 D T S C R L K V b B base loss ε)
    (hcoordinates : N05ControlledReferenceCoordinates D S C K)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (u : B.Space) (ml mr : ℕ) (s : Finset ℕ) (vl vr : ℕ → ℝ → ℝ)
    (hjoin : K.physicalRight ml = K.physicalLeft mr)
    (hcore : Icc (K.physicalLeft ml) (K.physicalRight mr) ⊆ radialCore D)
    {yl yr σl σr : ℝ} {β₀ H₀ ρ₀ κ₀ Hr₀ β H ρ κ Hr : ℝ → ℝ}
    (Jl₀ : N06RootFirstJets (K.chart (C.referenceState, 0) ml)
      (K.height (C.referenceState, 0) ml) (K.physicalRight ml) yl σl β₀ H₀ ρ₀ κ₀ Hr₀)
    (Jr₀ : N06RootFirstJets (K.chart (C.referenceState, 0) mr)
      (K.height (C.referenceState, 0) mr) (K.physicalRight ml) yr σr β₀ H₀ ρ₀ κ₀ Hr₀)
    (hH₀ : H₀ 0 ≠ 0) (hρ₀ : ρ₀ 0 ≠ 0)
    (Jl : N06RootFirstJets (K.chart z ml) (K.height z ml)
      (K.physicalRight ml) yl σl β H ρ κ Hr)
    (Jr : N06RootFirstJets (K.chart z mr) (K.height z mr)
      (K.physicalRight ml) yr σr β H ρ κ Hr)
    (Ql : N06CurrentHeightTestTraces S K z ml φ)
    (Qr : N06CurrentHeightTestTraces S K z mr φ)
    (hφ : ContDiff ℝ ∞ φ)
    (hvl : ∀ n ∈ s, ContDiff ℝ 1 (vl n))
    (hvr : ∀ n ∈ s, ContDiff ℝ 1 (vr n))
    (hmodeL : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 ml) n
      =ᵐ[MeasureTheory.volume.restrict (Ioo (K.left ml) (K.right ml))] vl n)
    (hmodeR : ∀ n ∈ s, n06HalfCosineCoefficient (u.val.1.1 mr) n
      =ᵐ[MeasureTheory.volume.restrict (Ioo (K.left mr) (K.right mr))] vr n)
    (A : SymmetricCoefficients) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    ((σl * ρ θ) / |σl * ρ θ|) *
      n06RootBoundaryDensity A (K.chart z ml) (K.height z ml)
        Ql.value Ql.radial Ql.angular (r11bFiniteSynthesis s vl referenceAngularBasis)
          (K.physicalRight ml, θ) (yl, β θ) =
    ((σr * ρ θ) / |σr * ρ θ|) *
      n06RootBoundaryDensity A (K.chart z mr) (K.height z mr)
        Qr.value Qr.radial Qr.angular (r11bFiniteSynthesis s vr referenceAngularBasis)
          (K.physicalRight ml, θ) (yr, β θ) := by
  have h04 : N04Properties D T S C L K base loss ε := h.1.2.2.2.2
  have hrl : K.physicalRight ml ∈ Icc (K.physicalLeft ml) (K.physicalRight ml) :=
    ⟨(h04.2.2.2.1 ml).1.le, le_rfl⟩
  have hrr : K.physicalRight ml ∈ Icc (K.physicalLeft mr) (K.physicalRight mr) := by
    rw [hjoin]
    exact ⟨le_rfl, (h04.2.2.2.1 mr).1.le⟩
  have hWl : ContDiff ℝ 1 (r11bFiniteSynthesis s vl referenceAngularBasis) :=
    ContDiff.sum (fun n hn => ((hvl n hn).comp contDiff_fst).mul
      (((contDiff_referenceAngularBasis n).of_le (by simp)).comp contDiff_snd))
  have hWr : ContDiff ℝ 1 (r11bFiniteSynthesis s vr referenceAngularBasis) :=
    ContDiff.sum (fun n hn => ((hvr n hn).comp contDiff_fst).mul
      (((contDiff_referenceAngularBasis n).of_le (by simp)).comp contDiff_snd))
  have hmatch := n06N05_finite_current_root_conormal hS h hcoordinates u ml mr s vl vr
    hjoin hcore Jl₀ Jr₀ hH₀ hρ₀ Jl Jr hvl hvr hmodeL hmodeR A.a A.b θ
  exact n06_current_root_boundaryDensity_eq_of_value_conormal Jl Jr Ql Qr h04 hz hs hφ
    hrl hrr hθ A (hWl.differentiable (by norm_num) _) (hWr.differentiable (by norm_num) _)
    hmatch.1 hmatch.2

end ContinuousFlexibility.Analysis
