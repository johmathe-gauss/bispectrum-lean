# Notes on "Bispectral Signatures of Data" Draft

**Document**: "Bispectral Signatures of Data: The Different Flavors of Bispectra and G-Bispectra"
**Pages**: 43 pages
**Focus**: Systematic coverage of bispectra across domains and groups

---

## Document Structure (Complete)

| Section | Domain | Group | Pages |
|---|---|---|---|
| 1 | Preliminaries | — | 3 |
| 2 | Bispectrum-only Summary | — | 3 |
| 3 | Summary Table | — | 4 |
| 4 | Ω = (ℤ/nℤ, +) | Cyclic translations | 6–10 |
| 5 | Ω = (G, +) | Finite groups | 11–? |
| 6 | Ω = G (compact) | Compact groups (integral measure) | ~17–23 |
| 7 | Ω = S² | SO(3) on sphere | ~23–25 |
| 8 | Ω = (H, G, ·) | Homogeneous space | 26–29 |
| 9 | Ω = S¹ × ℝ*₊ | SO(2) — disk rotations | 29–? |
| 10 | Ω = S² × ℝ*₊ | SO(3) — ball rotations | ~33–? |
| 11 | Ω = H × ℝ | G — homogeneous × invariant | ~35–? |
| 12 | Ω = ℤ² | G via induced rep. (Steerable CNN) | ~37–41 |
| 14 | Scratch | working notes | 42–43 |

---

## Selective Bispectrum: Which Groups Have It?

### ✅ Section 4 — Cyclic Cn on ℤ/nℤ
**Full bispectrum**: β(f)_{k1,k2} = f̂_{k1} · f̂_{k2} · f̂*_{k1+k2}
**Selective version**: YES — n+1 coefficients {β(f)_{0,0}, β(f)_{1,0}, ..., β(f)_{1,n}} suffice
**Inversion**: YES — explicit iterative algorithm given:
1. β_{0,0} → |f̂(0)| and arg(f̂(0))
2. β_{1,0} → |f̂(1)|, set arg(f̂(1)) = 0 (translation ambiguity)
3. β_{1,k-1} → f̂(k) iteratively (Eqs. 8–10)

### ✅ Section 5 — Finite Groups G (including Dn, octahedral O)
**Full bispectrum**: β(f)_{ρ1,ρ2} = [F(f)_{ρ1} ⊗ F(f)_{ρ2}] C_{ρ1ρ2} [⊕_ρ F(f)_ρ]† C†_{ρ1ρ2}
For commutative G: β(f)_{ρ1,ρ2} = F(f)_{ρ1} F(f)_{ρ2} F(f)†_{ρ1⊗ρ2}
**Selective version**: YES — uses Kronecker product table; BFS on irreps determines L minimal pairs
(explicit D4 example: Kronecker table shown, 3 bispectral coefficients suffice for D4 with |D4|=8)
**Inversion**: YES — algorithm given (start from trivial rep ρ₀, bootstrap outward via β_{ρ,ρ₀} then Kronecker pairs)

### ❌ Section 6 — Compact Groups G (continuous, e.g. SO(3) itself)
**Full bispectrum**: β(f)_{ρ1,ρ2} = ∫_G T(f)_{g1,g2} [ρ1(g1)† ⊗ ρ2(g2)†] dg1 dg2
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED

### ❌ Section 7 — Sphere S² with SO(3)
Two variants given:
- **Vector bispectrum**: β^v(f)_{l1,l2}[l] = [F(f)_{l1} ⊗ F(f)_{l2}] C_{l1,l2} F'(f)†_l
  (uses vector-valued Fourier coefficients indexed by l; CG matrices link irreps)
- **Matrix bispectrum**: same formula with matrix Fourier transform
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED
Note: equivariance proof given in detail (SHT equivariance under SO(3))

### ❌ Section 8 — Homogeneous Space (H, G, ·) where H = G/G₀
(e.g. S² = SO(3)/SO(2))
**Full bispectrum**:
- Commutative G: β(f)_{ρ1,ρ2} = f̂_{ρ1} f̂_{ρ2} f̂†_{ρ1⊗ρ2}
- Non-commutative: same as compact group formula
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED
Key insight: lifted function f̃ on G inherits G₀-invariance; projection operator P₀(ρ) used

### ❌ Section 9 — Disk S¹ × ℝ*₊ with SO(2) rotations
**Full bispectrum**: defined via Fourier-Bessel transform F(f)_{nm} (uses Bessel functions J_m)
Equivariance: rotation by θ̃ gives F(θ̃∗f)_{nm} = exp(-imθ̃) F(f)_{nm}
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED

### ❌ Section 10 — Ball S² × ℝ*₊ with SO(3) rotations
Expansion: f(r,θ,φ) = Σ_{l,m} f̂^m_l r_l Y^m_l(θ,φ)
**Full bispectrum**: β(f)_{l1,l2}[l] = [F(f)_{l1} ⊗ F(f)_{l2}] C_{l1,l2} F'(f)†_l, |l1-l2| ≤ l ≤ l1+l2
(same formula as S² case, with radial extension)
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED

### ❌ Section 11 — Homogeneous × Invariant Space (H×ℝ, G)
**Full bispectrum**: same formula as homogeneous case (only Fourier transform varies)
**Selective version**: NOT DERIVED
**Inversion**: NOT DERIVED

### ⚠️ Section 12 — ℤ² with Steerable CNN (induced representation G = ℤ² ⋊ H)
Domain: 2D images with fiber; group action via induced representation T = Ind^G_H ρ_H
Bispectral coefficients on intertwining basis ^*_l (steerable output coefs)
Formula: **INCOMPLETE/BEING DEVELOPED**
Questions posed (open): "How do we generalize the bispectrum for non-commutative H when we don't have Fourier coefs, only intertwining basis coefs?"
**Selective version**: NOT DERIVED (formula itself not finished)
**Inversion**: NOT DERIVED

---

## Summary Table: Selective Bispectra

| Group/Domain | Selective? | Inversion? | Source |
|---|---|---|---|
| Cyclic Cn (Z/nZ) | ✅ YES (n+1 coefficients) | ✅ YES | §4, Eqs 8-10 |
| Finite groups (general) | ✅ YES (Kronecker BFS) | ✅ YES | §5, incl. D4 example |
| Dihedral Dn (as finite group) | ✅ YES (Kronecker BFS) | ✅ YES | §5 (D4 explicitly) |
| Compact groups G | ❌ Full only | ❌ No | §6 |
| Sphere S² / SO(3) | ❌ Full only | ❌ No | §7 |
| Homogeneous space (H,G) | ❌ Full only | ❌ No | §8 |
| Disk (SO(2)) | ❌ Full only | ❌ No | §9 |
| Ball (SO(3)) | ❌ Full only | ❌ No | §10 |
| H×ℝ (hom. × inv.) | ❌ Full only | ❌ No | §11 |
| ℤ² Steerable CNN | ⚠️ Incomplete | ❌ No | §12 |

**Key finding**: The draft provides full bispectrum formulas for all cases, but selective/reduced versions are only worked out for finite groups (cyclic and general finite, including dihedral and octahedral). All continuous groups (SO(2), SO(3), homogeneous spaces, disk, ball) get full bispectra only.

---

## Connection to Main Paper (arXiv:2407.07655)

The main paper proves selective bispectra for:
- **Cn**: Algorithm 1 (matches §4 of draft)
- **All commutative groups**: Algorithm 2 (matches §5 of draft, commutative case)
- **Dihedral Dn**: Algorithm 3 (matches §5 of draft, Dn instance)
- **Octahedral O and FO**: Appendix proofs (also §5 of draft)

**What neither paper addresses (selective versions)**:
- SO(2) acting on circle/disk
- SO(3) acting on S²
- Any continuous/Lie group case

This suggests an open research frontier: developing selective bispectra for the continuous group settings.

---

## Key Mathematical Notes (from section contents)

### Summary Table (Section 3)
Two variants of bispectrum defined throughout:
1. **Bispectrum-only** (Section 2): omitting triple correlation derivation
2. **Full derivation**: TC → Fourier → bispectrum (the main flow)

### CG Matrices
Throughout the document, Clebsch-Gordan matrices C_{ρ1,ρ2} appear. Key insight:
- For commutative groups: no CG needed (scalar Fourier transform)
- For compact groups and homogeneous spaces: full CG matrices required
- The document notes "TODO: proof?" for some commutative simplification steps

### Steerable Bispectrum (Sections 4.3, 5.3)
Each section has a subsection "Steerable Bispectrum: After G-Conv on Steerable Basis"
— computing bispectrum from the output of a G-convolution on a steerable basis.
This is relevant for neural network applications (computing bispectrum from conv output directly).

### D4 Kronecker Table (Stream 43)
Irreps: A1, A2, B1, B2, E
E⊗E = A1 + A2 + B1 + B2 (all 1D irreps appear in E⊗E → one step suffices!)
Bispectral coefficients needed: β_{A1,A1}, β_{E,A1}, β_{E,E} → 3 coefficients for D4 (|D4|=8)

### References in Document
- Kondor R. "Group theoretical methods in machine learning." Columbia PhD thesis (2008).
- Rudin W. "Fourier analysis on groups." Dover (1962).
- Kakarala R. "The bispectrum as a source of phase-sensitive invariants." JMIV 44, 341-353 (2012).
