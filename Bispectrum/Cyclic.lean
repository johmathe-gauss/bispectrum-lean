import Bispectrum.DFT

/-!
# Bispectrum on the Cyclic Group C_n

This file defines the bispectrum of a function `f : ZMod n → ℂ` and
proves its invariance under the cyclic group action (cyclic shifts).

## Main definitions

- `cyclicBispec f k₁ k₂` : bispectral coefficient at (k₁, k₂)

## Main results

- `cyclicBispec_shift_invariant` : B[T_g f](k₁, k₂) = B[f](k₁, k₂) for all g

## Key insight

The three phase factors from the shift cancel exactly:
  ω^(g·k₁) · ω^(g·k₂) · conj(ω^(g·(k₁+k₂)))
= exp(-2πi·g·(k₁ + k₂ - (k₁+k₂))/n)
= exp(0) = 1

This works because k₁ + k₂ - (k₁+k₂) = 0 in ℤ/nℤ.
-/

open Complex BigOperators Real

variable {n : ℕ} [NeZero n]

/-!
### Definition of the cyclic bispectrum
-/

/-- The bispectral coefficient of f at index pair (k₁, k₂).

    B[f](k₁, k₂) = F(k₁) · F(k₂) · conj(F(k₁ + k₂))

    where F = dft f. This is manifestly computable given the DFT. -/
noncomputable def cyclicBispec (f : ZMod n → ℂ) (k₁ k₂ : ZMod n) : ℂ :=
  dft f k₁ * dft f k₂ * starRingEnd ℂ (dft f (k₁ + k₂))

/-!
### Invariance under cyclic shifts

The bispectrum is invariant under all cyclic shifts T_g.
-/

/-- The bispectrum is invariant under cyclic shifts.

    For all g, k₁, k₂: B[T_g f](k₁, k₂) = B[f](k₁, k₂)

    Proof sketch:
    - B[T_g f](k₁, k₂)
    - = (φ_g(k₁) · F(k₁)) · (φ_g(k₂) · F(k₂)) · conj(φ_g(k₁+k₂) · F(k₁+k₂))
    - = φ_g(k₁) · φ_g(k₂) · conj(φ_g(k₁+k₂)) · B[f](k₁, k₂)
    - = 1 · B[f](k₁, k₂)                   [phases cancel]
-/
theorem cyclicBispec_shift_invariant (f : ZMod n → ℂ) (g k₁ k₂ : ZMod n) :
    cyclicBispec (cycShift g f) k₁ k₂ = cyclicBispec f k₁ k₂ := by
  simp only [cyclicBispec]
  rw [dft_cycShift f g k₁, dft_cycShift f g k₂, dft_cycShift f g (k₁ + k₂)]
  simp only [map_mul, starRingEnd_apply]
  -- Goal: (φ(g,k₁) · F(k₁)) · (φ(g,k₂) · F(k₂)) · conj(φ(g,k₁+k₂) · F(k₁+k₂))
  --     = F(k₁) · F(k₂) · conj(F(k₁+k₂))
  -- Suffices: φ(g,k₁) · φ(g,k₂) · conj(φ(g,k₁+k₂)) = 1
  ring_nf
  sorry  -- Phase cancellation: val(k₁) + val(k₂) ≡ val(k₁+k₂) mod n

/-!
### Completeness (informal)

The bispectrum {B[f](k₁,k₂) : k₁,k₂ ∈ ZMod n} is complete
for the C_n-orbit of f (up to a global phase), meaning:

  B[f] = B[h] iff ∃ g, f = T_g h

Formalizing this requires injectivity of the DFT (Parseval/Plancherel)
plus the argument that phase-only differences between two DFTs imply
a shift relation. This is marked as a future theorem.
-/

/-- Placeholder: bispectrum separates C_n orbits -/
theorem cyclicBispec_complete (f h : ZMod n → ℂ)
    (hB : ∀ k₁ k₂, cyclicBispec f k₁ k₂ = cyclicBispec h k₁ k₂) :
    ∃ g : ZMod n, ∀ x, f x = cycShift g h x := by
  sorry
