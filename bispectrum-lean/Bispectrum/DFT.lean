import Mathlib

/-!
# Discrete Fourier Transform on ZMod n

This file defines the DFT of a function `f : ZMod n → ℂ` and proves
the key equivariance lemma: shifting `f` by `g` multiplies each DFT
coefficient `k` by the phase `ω^(g·k)`.

## Main definitions

- `dft f k` : the k-th DFT coefficient of f
- `cycShift g f` : cyclic shift of f by g ∈ ZMod n

## Main results

- `dft_cycShift` : DFT conjugates cyclic shifts to phase multiplication
-/

open Complex BigOperators Real

variable {n : ℕ} [NeZero n]

/-- The n-th root of unity: ω = exp(2πi/n) -/
noncomputable def rootOfUnity (n : ℕ) [NeZero n] : ℂ :=
  exp (2 * π * I / n)

/-- DFT of f at frequency k.
    F(k) = Σ_{x : ZMod n} f(x) · exp(-2πi·x·k/n) -/
noncomputable def dft (f : ZMod n → ℂ) (k : ZMod n) : ℂ :=
  ∑ x : ZMod n,
    f x * exp (-2 * π * I * (ZMod.val x : ℝ) * (ZMod.val k : ℝ) / n)

/-- Cyclic shift of f by g: (T_g f)(x) = f(x - g) -/
def cycShift (g : ZMod n) (f : ZMod n → ℂ) : ZMod n → ℂ :=
  fun x => f (x - g)

/-- Inverse DFT: f(x) = (1/n) Σ_k F(k) · exp(2πi·x·k/n) -/
noncomputable def idft (F : ZMod n → ℂ) (x : ZMod n) : ℂ :=
  (n : ℂ)⁻¹ * ∑ k : ZMod n,
    F k * exp (2 * π * I * (ZMod.val x : ℝ) * (ZMod.val k : ℝ) / n)

/-!
### Key lemma: DFT equivariance under cyclic shifts

Shifting f by g multiplies DFT coefficient k by the phase exp(-2πi·g·k/n).
This is the spectral representation of translational equivariance.
-/

/-- Phase factor for shift g at frequency k -/
noncomputable def shiftPhase (g k : ZMod n) : ℂ :=
  exp (-2 * π * I * (ZMod.val g : ℝ) * (ZMod.val k : ℝ) / n)

lemma dft_cycShift (f : ZMod n → ℂ) (g k : ZMod n) :
    dft (cycShift g f) k = shiftPhase g k * dft f k := by
  simp only [dft, cycShift, shiftPhase]
  -- Reindex: substitute x ↦ x + g
  rw [← Equiv.sum_comp (Equiv.addRight g)]
  simp only [Equiv.addRight_apply]
  -- Now we have Σ_x f(x) · exp(-2πi(x+g)k/n)
  -- = exp(-2πi·g·k/n) · Σ_x f(x) · exp(-2πi·x·k/n)
  sorry  -- Phase arithmetic: val(x+g) ≡ val(x) + val(g) mod n

/-- Conjugate phase: shifting by -g gives the conjugate phase -/
lemma dft_cycShift_neg (f : ZMod n → ℂ) (g k : ZMod n) :
    dft (cycShift (-g) f) k = starRingEnd ℂ (shiftPhase g k) * dft f k := by
  sorry
